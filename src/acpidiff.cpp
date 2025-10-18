// acpidiff.cpp
// C++17 ACPICA namespace builder and diff tool
// Parse-only. No interpreter execution.

#include <algorithm>
#include <array>
#include <cctype>
#include <cerrno>
#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <functional>
#include <glob.h>
#include <iostream>
#include <iomanip>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

extern "C" {
#include <acpi.h>
#include <accommon.h>
}

#ifdef __init
#undef __init
#endif

#ifdef USE_ACPICA_INTERNALS
// Prefer internal visibility for AML length and table ownership mapping
// These headers may exist in ACPICA dev packages; guarded by flag.
extern "C" {
# include <acparser.h>
# include <acnamesp.h>
# include <actables.h>
}
#endif

// ---------------- SHA-256 (small, public-domain style) ----------------
namespace tinysha256 {
struct Ctx { uint64_t len=0; uint32_t state[8]; uint8_t buf[64]; size_t idx=0; };
static inline uint32_t rotr(uint32_t x, uint32_t n){return (x>>n)|(x<<(32-n));}
static const uint32_t K[64]={
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
static void init(Ctx &c){c.len=0;c.idx=0;uint32_t s[8]={0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
  for(int i=0;i<8;i++) c.state[i]=s[i];}
static void compress(Ctx &c,const uint8_t *p){uint32_t w[64];for(int i=0;i<16;i++){w[i]=(uint32_t)p[4*i]<<24|(uint32_t)p[4*i+1]<<16|(uint32_t)p[4*i+2]<<8|(uint32_t)p[4*i+3];}
 for(int i=16;i<64;i++){uint32_t s0=rotr(w[i-15],7)^rotr(w[i-15],18)^(w[i-15]>>3);uint32_t s1=rotr(w[i-2],17)^rotr(w[i-2],19)^(w[i-2]>>10);w[i]=w[i-16]+s0+w[i-7]+s1;}
 uint32_t a=c.state[0],b=c.state[1],d=c.state[3],e=c.state[4],f=c.state[5],g=c.state[6],h=c.state[7],cc=c.state[2];
 for(int i=0;i<64;i++){uint32_t S1=rotr(e,6)^rotr(e,11)^rotr(e,25);uint32_t ch=(e&f)^(~e&g);uint32_t t1=h+S1+ch+K[i]+w[i];uint32_t S0=rotr(a,2)^rotr(a,13)^rotr(a,22);uint32_t maj=(a&cc)^(a&d)^(cc&d);uint32_t t2=S0+maj;h=g;g=f;f=e;e=d+t1;d=cc;cc=b;b=a;a=t1+t2;}
 c.state[0]+=a;c.state[1]+=b;c.state[2]+=cc;c.state[3]+=d;c.state[4]+=e;c.state[5]+=f;c.state[6]+=g;c.state[7]+=h;}
static void update(Ctx &c,const void*data,size_t len){const uint8_t* p=(const uint8_t*)data;while(len>0){size_t n=std::min(len,64-c.idx);memcpy(c.buf+c.idx,p,n);c.idx+=n;p+=n;len-=n;if(c.idx==64){compress(c,c.buf);c.len+=512;c.idx=0;}}}
static void final(Ctx &c,uint8_t out[32]){c.len+=c.idx*8;size_t i=c.idx; c.buf[i++]=0x80; if(i>56){while(i<64) c.buf[i++]=0; compress(c,c.buf); i=0;} while(i<56) c.buf[i++]=0; for(int j=7;j>=0;j--) c.buf[i++]=(uint8_t)((c.len>>((uint64_t)j*8))&0xFF); compress(c,c.buf); for(int k=0;k<8;k++){out[4*k]=(uint8_t)(c.state[k]>>24);out[4*k+1]=(uint8_t)(c.state[k]>>16);out[4*k+2]=(uint8_t)(c.state[k]>>8);out[4*k+3]=(uint8_t)c.state[k];}}
static std::string hex(const uint8_t d[32]){static const char*hex="0123456789abcdef";std::string s; s.resize(64); for(int i=0;i<32;i++){s[2*i]=hex[(d[i]>>4)&0xF]; s[2*i+1]=hex[d[i]&0xF];} return s;}
static std::string sha256(const void*data,size_t n){Ctx c;init(c);update(c,data,n);uint8_t out[32];final(c,out);return hex(out);} }
using tinysha256::sha256;

// ---------------- Data model ----------------

enum class Kind { Device, Method, Name, Region, Field, IndexField, BankField, Scope, Processor, ThermalZone, PowerResource, Mutex, Event, Package, Buffer, TableDigest, Unknown };

struct Node {
  std::string path;     // "\\_SB.PCI0.LPCB.EC0._REG"
  Kind kind{Kind::Unknown};
  std::string table_id; // "DSDT", "SSDT3", etc., or "UNKNOWN"
  struct Attrs {
    int arg_count{-1};
    bool serialized{false};
    size_t aml_len{0};
    std::string aml_sha256; // empty if not Method or unavailable
  } attrs;
  std::vector<std::unique_ptr<Node>> children;
  std::string node_hash;
  std::string subtree_hash;
};

struct Snapshot {
  std::unique_ptr<Node> root;
  std::unordered_map<std::string, Node*> by_path; // full path -> Node
};

struct ExtraTableDigest {
  std::string signature;
  std::string source_name;
  size_t length{0};
  std::string sha256;
};

static std::vector<ExtraTableDigest> gExtraTableDigests;

static std::string sanitizeIdentifier(const std::string &input){
  std::string out;
  out.reserve(input.size());
  bool lastUnderscore = false;
  for(char ch : input){
    unsigned char c = static_cast<unsigned char>(ch);
    char out_ch;
    if(std::isalnum(c)){
      out_ch = static_cast<char>(std::toupper(c));
    } else {
      out_ch = '_';
    }
    if(out_ch == '_'){
      if(lastUnderscore) continue;
      lastUnderscore = true;
    } else {
      lastUnderscore = false;
    }
    out.push_back(out_ch);
  }
  while(!out.empty() && out.back()=='_') out.pop_back();
  if(out.empty()) out = "BLOB";
  return out;
}

static void recordExtraTableDigest(const std::string &signature,
                                   const std::string &sourceName,
                                   const std::vector<uint8_t> &data){
  ExtraTableDigest entry;
  entry.signature = signature;
  entry.source_name = sourceName;
  entry.length = data.size();
  entry.sha256 = sha256(data.data(), data.size());
  gExtraTableDigests.push_back(std::move(entry));
}

static bool tableContainsAml(const ACPI_TABLE_HEADER *hdr, size_t blobSize){
  if(!hdr) return false;
  std::string sig(hdr->Signature, hdr->Signature + ACPI_NAMESEG_SIZE);
  if(sig == "DSDT" || sig == "SSDT" || sig == "PSDT" || sig == "OSDT"){
    return true;
  }
  if(sig.rfind("OEM", 0) == 0){
    return true;
  }
  size_t headerSize = sizeof(ACPI_TABLE_HEADER);
  if(blobSize < headerSize || hdr->Length <= headerSize){
    return false;
  }
  const uint8_t *aml = reinterpret_cast<const uint8_t*>(hdr) + headerSize;
  size_t amlLen = std::min(static_cast<size_t>(hdr->Length - headerSize),
                           blobSize - headerSize);
  if(amlLen == 0){
    return false;
  }
  // AML definition blocks start with the DefBlock opcode (0x10). If the first
  // opcode looks like a DefinitionBlock, treat the table as executable AML even
  // if the signature is non-standard.
  if(aml[0] == 0x10){
    return true;
  }
  return false;
}

static const char* kindName(Kind k){
  switch(k){
    case Kind::Device: return "Device"; case Kind::Method: return "Method"; case Kind::Name: return "Name";
    case Kind::Region: return "Region"; case Kind::Field: return "Field"; case Kind::IndexField: return "IndexField";
    case Kind::BankField: return "BankField"; case Kind::Scope: return "Scope"; case Kind::Processor: return "Processor";
    case Kind::ThermalZone: return "ThermalZone"; case Kind::PowerResource: return "PowerResource"; case Kind::Mutex: return "Mutex";
    case Kind::Event: return "Event"; case Kind::Package: return "Package"; case Kind::Buffer: return "Buffer"; case Kind::TableDigest: return "TableDigest"; default: return "Unknown"; }
}

static Kind mapTypeToKind(ACPI_OBJECT_TYPE t){
  switch(t){
    case ACPI_TYPE_DEVICE: return Kind::Device;
    case ACPI_TYPE_METHOD: return Kind::Method;
    case ACPI_TYPE_INTEGER: return Kind::Name;
    case ACPI_TYPE_STRING: return Kind::Name;
    case ACPI_TYPE_BUFFER: return Kind::Buffer;
    case ACPI_TYPE_REGION: return Kind::Region;
    case ACPI_TYPE_FIELD_UNIT: return Kind::Field;
#ifdef ACPI_TYPE_INDEX_FIELD
    case ACPI_TYPE_INDEX_FIELD: return Kind::IndexField;
#endif
#ifdef ACPI_TYPE_LOCAL_INDEX_FIELD
    case ACPI_TYPE_LOCAL_INDEX_FIELD: return Kind::IndexField;
#endif
#ifdef ACPI_TYPE_BANK_FIELD
    case ACPI_TYPE_BANK_FIELD: return Kind::BankField;
#endif
#ifdef ACPI_TYPE_LOCAL_BANK_FIELD
    case ACPI_TYPE_LOCAL_BANK_FIELD: return Kind::BankField;
#endif
    case ACPI_TYPE_LOCAL_SCOPE: return Kind::Scope;
    case ACPI_TYPE_PROCESSOR: return Kind::Processor;
    case ACPI_TYPE_THERMAL: return Kind::ThermalZone;
    case ACPI_TYPE_POWER: return Kind::PowerResource;
    case ACPI_TYPE_MUTEX: return Kind::Mutex;
    case ACPI_TYPE_EVENT: return Kind::Event;
    case ACPI_TYPE_PACKAGE: return Kind::Package;
    default: return Kind::Unknown;
  }
}

// ---------------- Utility ----------------

enum class LogSeverity { Info, Warning, Error };

static LogSeverity gLogThreshold = LogSeverity::Error;

static bool isSeverityEnabled(LogSeverity severity){
  return static_cast<int>(severity) >= static_cast<int>(gLogThreshold);
}

static bool isInfoEnabled(){
  return isSeverityEnabled(LogSeverity::Info);
}

static void logMessage(LogSeverity severity, const std::string &msg){
  if(!isSeverityEnabled(severity)) return;
  const char* label = nullptr;
  switch(severity){
    case LogSeverity::Info: label = "info"; break;
    case LogSeverity::Warning: label = "warn"; break;
    case LogSeverity::Error: label = "error"; break;
  }
  std::cerr << label << ": " << msg << "\n";
}

static void logInfo(const std::string &msg){ logMessage(LogSeverity::Info, msg); }
static void logWarn(const std::string &msg){ logMessage(LogSeverity::Warning, msg); }
static void logError(const std::string &msg){ logMessage(LogSeverity::Error, msg); }

static std::string formatStatus(ACPI_STATUS s){
  std::ostringstream oss;
  oss << "0x" << std::hex << std::uppercase << s;
  oss << std::nouppercase << std::dec;
  const char* msg = AcpiFormatException(s);
  if(msg && *msg) oss << " (" << msg << ")";
  return oss.str();
}

static void logStatus(const std::string &context, ACPI_STATUS s,
                      LogSeverity failureSeverity = LogSeverity::Error,
                      LogSeverity successSeverity = LogSeverity::Info){
  std::ostringstream oss;
  oss << context << ": " << formatStatus(s);
  logMessage(ACPI_FAILURE(s) ? failureSeverity : successSeverity, oss.str());
}

static std::string acpiNameToString(ACPI_NAME name){
  if(!name) return "<root>";
  char text[5];
  for(int i=0;i<4;i++){
    unsigned shift = 24 - static_cast<unsigned>(i)*8;
    unsigned char ch = static_cast<unsigned char>((name >> shift) & 0xFF);
    if(ch == 0 || !std::isprint(ch)) ch = '_';
    text[i] = static_cast<char>(ch);
  }
  text[4] = '\0';
  return std::string(text);
}

static ACPI_STATUS acpiExceptionHandler(ACPI_STATUS status, ACPI_NAME name,
                                        UINT16 opcode, UINT32 amlOffset,
                                        void* /*context*/){
  LogSeverity severity = LogSeverity::Error;
  if(status == AE_NO_HANDLER){
    severity = LogSeverity::Warning;
  }
  std::ostringstream oss;
  oss << "ACPICA exception " << formatStatus(status);
  if(name){
    oss << " in [" << acpiNameToString(name) << ']';
  }
  oss << " opcode=0x" << std::hex << opcode << " aml_offset=0x" << amlOffset;
  if(status == AE_NO_HANDLER){
    oss << " (no region handler installed; expected without firmware access)";
  } else if(status == AE_NOT_FOUND){
    oss << " (namespace lookup failure; tables may be incomplete)";
  }
  logMessage(severity, oss.str());
  return status;
}

static std::vector<uint8_t> readFile(const std::string &path){
  logInfo(std::string("Reading table file ") + path);
  std::ifstream f(path, std::ios::binary);
  if(!f) throw std::runtime_error("Failed to open file: "+path);
  f.seekg(0, std::ios::end);
  std::streamsize n = f.tellg();
  if(n <= 0) throw std::runtime_error("Empty ACPI blob: "+path);
  f.seekg(0);
  std::vector<uint8_t> buf((size_t)n);
  if(!f.read((char*)buf.data(), n)) throw std::runtime_error("Failed to read: "+path);
  logInfo(std::string("Read ") + std::to_string(buf.size()) + " bytes from " + path);
  if((size_t)n < sizeof(ACPI_TABLE_HEADER)){
    logWarn(std::string("Blob smaller than ACPI table header (" ) + std::to_string(buf.size()) + " bytes): " + path);
  }
  return buf;
}

static std::vector<std::string> expandGlobs(const std::vector<std::string>& inputs){
  std::vector<std::string> out;
  for(const auto &pat: inputs){
    logInfo(std::string("Expanding pattern ") + pat);
    glob_t g{}; int r = glob(pat.c_str(), 0, nullptr, &g);
    if(r==0){ for(size_t i=0;i<g.gl_pathc;i++) out.emplace_back(g.gl_pathv[i]); }
    else { out.push_back(pat); }
    globfree(&g);
  }
  // version-like sort
  auto natcmp=[](const std::string&a,const std::string&b){
    const char*pa=a.c_str(); const char*pb=b.c_str();
    while(*pa && *pb){
      if(std::isdigit(*pa) && std::isdigit(*pb)){
        unsigned long va=0,vb=0; while(std::isdigit(*pa)){va=va*10+(*pa-'0'); pa++;}
        while(std::isdigit(*pb)){vb=vb*10+(*pb-'0'); pb++;}
        if(va!=vb) return va<vb;
      } else {
        if(*pa!=*pb) return *pa<*pb;
        pa++;
        pb++;
      }
    }
    return std::strlen(pa)<std::strlen(pb);
  };
  std::sort(out.begin(), out.end(), natcmp);
  if(isInfoEnabled()){
    std::ostringstream oss;
    oss << "Expanded inputs to " << out.size() << " file(s):";
    for(const auto &p : out) oss << "\n  " << p;
    logInfo(oss.str());
  }
  return out;
}

// ---------------- ACPICA bootstrap ----------------

struct AcpiGuard {
  AcpiGuard(){
    ACPI_STATUS s;
    logInfo("Initializing ACPICA subsystem");
    s = AcpiInitializeSubsystem();
    logStatus("AcpiInitializeSubsystem returned", s);
    if(ACPI_FAILURE(s)) throw std::runtime_error("AcpiInitializeSubsystem failed");
    logInfo("Installing ACPICA exception handler");
    s = AcpiInstallExceptionHandler(&acpiExceptionHandler);
    logStatus("AcpiInstallExceptionHandler returned", s);
    if(ACPI_FAILURE(s)) throw std::runtime_error("AcpiInstallExceptionHandler failed");
    logInfo("Initializing ACPICA tables (32 entries, allow resize)");
    s = AcpiInitializeTables(nullptr, 32, TRUE);
    logStatus("AcpiInitializeTables returned", s, LogSeverity::Warning);
    if(s == AE_NOT_FOUND){
      // Expected when operating without firmware access; tables will be provided manually.
      logWarn("AcpiInitializeTables reported AE_NOT_FOUND; continuing with manual tables");
    } else if(ACPI_FAILURE(s)){
      throw std::runtime_error("AcpiInitializeTables failed");
    }
    logInfo("ACPICA initialization complete");
  }
  ~AcpiGuard(){
    logInfo("Terminating ACPICA subsystem");
    AcpiTerminate();
  }
};

static void loadTablesFromFiles(const std::vector<std::string>& files){
  gExtraTableDigests.clear();
  logInfo(std::string("Preparing to load ") + std::to_string(files.size()) + " table file(s)");
  for(const auto &p : files){
    auto buf = readFile(p);
    std::string filename = std::filesystem::path(p).filename().string();
    bool is_rsdp = buf.size() >= 8 && std::memcmp(buf.data(), "RSD PTR ", 8) == 0;
    bool is_facs = buf.size() >= 4 && std::memcmp(buf.data(), "FACS", 4) == 0;
    if(is_rsdp || is_facs){
      const char* label = is_rsdp ? "RSDP" : "FACS";
      logInfo(std::string("Recording non-AML structure ") + label + " from " + p +
              " for integrity diff (skipping AcpiLoadTable)");
      recordExtraTableDigest(label, filename, buf);
      continue;
    }
    if(buf.size() < sizeof(ACPI_TABLE_HEADER)){
      throw std::runtime_error("Too small to be an ACPI table with header: " + p);
    }
    auto *hdr = reinterpret_cast<ACPI_TABLE_HEADER*>(buf.data());
    if(hdr->Length != buf.size()){
      std::ostringstream oss;
      oss << "table length mismatch for "<<p<<" hdr="<<hdr->Length
          <<" bytes file="<<buf.size();
      logWarn(oss.str());
    }
    bool hasAml = tableContainsAml(hdr, buf.size());
    if(isInfoEnabled()){
      std::ostringstream oss;
      oss << (hasAml ? "Loading" : "Recording non-AML")
          << " table signature="
          << std::string(hdr->Signature, hdr->Signature + sizeof(hdr->Signature))
          << " oem_id="
          << std::string(hdr->OemId, hdr->OemId + sizeof(hdr->OemId))
          << " table_id="
          << std::string(hdr->OemTableId, hdr->OemTableId + sizeof(hdr->OemTableId))
          << " length=" << hdr->Length
          << " checksum=" << static_cast<int>(hdr->Checksum)
          << " revision=" << static_cast<int>(hdr->Revision);
      oss << std::hex << std::showbase
          << " oem_revision=" << hdr->OemRevision
          << " compiler_rev=" << hdr->AslCompilerRevision
          << std::dec << std::noshowbase
          << " compiler_id="
          << std::string(hdr->AslCompilerId, hdr->AslCompilerId + sizeof(hdr->AslCompilerId));
      logInfo(oss.str());
    }
    if(!hasAml){
      if(isInfoEnabled()){
        std::ostringstream oss;
        oss << "Recording data-only table signature="
            << std::string(hdr->Signature, hdr->Signature + sizeof(hdr->Signature))
            << " from " << p << " for integrity diff (skipping AcpiLoadTable)";
        logInfo(oss.str());
      }
      recordExtraTableDigest(std::string(hdr->Signature, hdr->Signature + sizeof(hdr->Signature)),
                             filename, buf);
      continue;
    }
    auto storage = std::make_unique<std::vector<uint8_t>>(std::move(buf));
    hdr = reinterpret_cast<ACPI_TABLE_HEADER*>(storage->data());
    ACPI_STATUS s = AcpiLoadTable(hdr, nullptr);
    if(ACPI_FAILURE(s)){
      std::ostringstream oss; oss << "AcpiLoadTable failed for "<<p<<" status="<<formatStatus(s);
      throw std::runtime_error(oss.str());
    }
    logStatus(std::string("AcpiLoadTable succeeded for ") + p, s);
    static std::vector<std::unique_ptr<std::vector<uint8_t>>> gLoadedTableBuffers;
    gLoadedTableBuffers.emplace_back(std::move(storage));
  }
  logInfo("Committing loaded tables to namespace");
  ACPI_STATUS s = AcpiLoadTables();
  logStatus("AcpiLoadTables returned", s);
  if(ACPI_FAILURE(s)) throw std::runtime_error("AcpiLoadTables failed");
}

// ---------------- Namespace walk and tree build ----------------

struct Node;

struct BuildCtx {
  std::unique_ptr<Node> root;
  std::unordered_map<std::string, Node*> by_path;
  std::unordered_map<ACPI_HANDLE, Node*> by_handle;
#ifdef USE_ACPICA_INTERNALS
  std::unordered_map<UINT16, std::string> owner_to_table;
#endif
};

static void injectExtraTableDigests(BuildCtx &ctx){
  if(!ctx.root) return;
  if(gExtraTableDigests.empty()) return;
  logInfo(std::string("Injecting ") + std::to_string(gExtraTableDigests.size()) +
          " non-AML table digest node(s)");
  for(const auto &extra : gExtraTableDigests){
    std::string label = sanitizeIdentifier(extra.signature);
    std::string base = "\\\\__TABLEDIGEST." + label;
    if(!extra.source_name.empty()){
      std::string source = sanitizeIdentifier(extra.source_name);
      if(!source.empty()) base += '.' + source;
    }
    std::string path = base;
    int counter = 1;
    while(ctx.by_path.find(path) != ctx.by_path.end()){
      path = base + '_' + std::to_string(counter++);
    }
    auto node = std::make_unique<Node>();
    node->path = path;
    node->kind = Kind::TableDigest;
    node->table_id = extra.signature.empty() ? label : extra.signature;
    node->attrs.aml_len = extra.length;
    node->attrs.aml_sha256 = extra.sha256;
    Node* raw = node.get();
    ctx.root->children.emplace_back(std::move(node));
    ctx.by_path[raw->path] = raw;
  }
  gExtraTableDigests.clear();
}

#ifdef USE_ACPICA_INTERNALS
static std::string tableTagFromDesc(ACPI_TABLE_DESC* d, size_t ssdt_index){
  std::string sig(d->Signature.Ascii);
  if(sig=="DSDT") return "DSDT";
  if(sig=="SSDT"){ return std::string("SSDT")+std::to_string(ssdt_index); }
  return sig;
}

static void buildOwnerMap(BuildCtx &ctx){
  ACPI_TABLE_DESC *list = AcpiGbl_RootTableList.Tables; UINT32 count = AcpiGbl_RootTableList.CurrentTableCount;
  size_t ssdt_idx=0;
  for(UINT32 i=0;i<count;i++){
    ACPI_TABLE_DESC *d = &list[i]; if(!d->Pointer) continue;
    UINT16 owner = d->OwnerId;
    std::string tag = tableTagFromDesc(d, ssdt_idx);
    if(std::string(d->Signature.Ascii)=="SSDT") ssdt_idx++;
    ctx.owner_to_table[owner]=tag;
  }
}
#endif

static ACPI_STATUS walkCb(ACPI_HANDLE Object, UINT32 /*NestingLevel*/, void* Ctx, void** /*ReturnValue*/){
  auto &ctx = *reinterpret_cast<BuildCtx*>(Ctx);
  ACPI_BUFFER buf{ ACPI_ALLOCATE_BUFFER, nullptr };
  ACPI_STATUS s = AcpiGetName(Object, ACPI_FULL_PATHNAME, &buf);
  if(ACPI_FAILURE(s)){
    logStatus("AcpiGetName failed", s, LogSeverity::Warning);
    return AE_OK;
  }
  std::string path((char*)buf.Pointer); AcpiOsFree(buf.Pointer);

  ACPI_OBJECT_TYPE t; s = AcpiGetType(Object, &t); if(ACPI_FAILURE(s)) t = ACPI_TYPE_ANY;
  logStatus(std::string("AcpiGetType for ") + path, s, LogSeverity::Warning);
  ACPI_DEVICE_INFO *info=nullptr; s = AcpiGetObjectInfo(Object, &info);
  if(ACPI_FAILURE(s)) logStatus(std::string("AcpiGetObjectInfo failed for ") + path, s, LogSeverity::Warning);
  else logStatus(std::string("AcpiGetObjectInfo returned for ") + path, s);
#ifdef USE_ACPICA_INTERNALS
  auto *ns_node = reinterpret_cast<acpi_namespace_node*>(Object);
#endif

  auto n = std::make_unique<Node>();
  n->path = path;
  n->kind = mapTypeToKind(t);
  n->table_id = "UNKNOWN";

  if(info){
    if(n->kind == Kind::Method){
      n->attrs.arg_count = info->ParamCount;
      n->attrs.serialized = (info->Flags & ACPI_METHOD_SERIALIZED) != 0;
    }
    AcpiOsFree(info);
  }

#ifdef USE_ACPICA_INTERNALS
  if(ns_node){
    auto it = ctx.owner_to_table.find(ns_node->OwnerId);
    if(it!=ctx.owner_to_table.end()) n->table_id = it->second;
  }

  if(n->kind == Kind::Method && ns_node){
    if(ns_node->Object && ns_node->Object->Common.Type==ACPI_TYPE_METHOD){
      auto &m = ns_node->Object->Method;
      n->attrs.aml_len = m.AmlLength;
      if(m.AmlStart && m.AmlLength){ n->attrs.aml_sha256 = sha256(m.AmlStart, m.AmlLength); }
    }
  }
#endif

  Node* parent = nullptr;
  ACPI_HANDLE ph{}; if(ACPI_SUCCESS(AcpiGetParent(Object, &ph))){ auto it=ctx.by_handle.find(ph); if(it!=ctx.by_handle.end()) parent=it->second; }
  if(!ctx.root){ ctx.root = std::make_unique<Node>(); ctx.root->path = "\\"; ctx.root->kind = Kind::Scope; ctx.root->table_id="ROOT"; parent = ctx.root.get(); }
  if(!parent) parent = ctx.root.get();
  Node* raw = n.get();
  parent->children.emplace_back(std::move(n));
  ctx.by_path[raw->path]=raw;
  ctx.by_handle[Object]=raw;
  return AE_OK;
}

static void computeHashes(Node* n){
  for(auto &ch : n->children) computeHashes(ch.get());
  std::ostringstream oss;
  oss << static_cast<int>(n->kind) << '|' << n->table_id << '|'
      << n->attrs.arg_count << '|' << (n->attrs.serialized?1:0) << '|' << n->attrs.aml_len << '|'
      << n->attrs.aml_sha256;
  auto s = oss.str();
  n->node_hash = sha256(s.data(), s.size());
  std::vector<std::string> kids; kids.reserve(n->children.size());
  for(auto &ch : n->children) kids.push_back(ch->subtree_hash);
  std::sort(kids.begin(), kids.end());
  std::string concat = n->node_hash; for(auto &h : kids) concat += h;
  n->subtree_hash = sha256(concat.data(), concat.size());
}

static Snapshot buildSnapshot(){
  logInfo("Building ACPI namespace snapshot");
  BuildCtx ctx;
#ifdef USE_ACPICA_INTERNALS
  buildOwnerMap(ctx);
#endif
  ACPI_STATUS s = AcpiWalkNamespace(ACPI_TYPE_ANY, ACPI_ROOT_OBJECT, UINT32_MAX, walkCb, nullptr, &ctx, nullptr);
  logStatus("AcpiWalkNamespace returned", s);
  if(ACPI_FAILURE(s)) throw std::runtime_error("AcpiWalkNamespace failed");
  if(!ctx.root) throw std::runtime_error("No namespace root built");
  injectExtraTableDigests(ctx);
  logInfo("Computing subtree hashes");
  computeHashes(ctx.root.get());
  Snapshot snap; snap.root = std::move(ctx.root); snap.by_path = std::move(ctx.by_path);
  logInfo(std::string("Snapshot contains ") + std::to_string(snap.by_path.size()) + " node(s)");
  return snap;
}

// ---------------- Diff ----------------

struct DiffItem { enum Kind2{Add,Del,Mod} k; std::string path; Kind nodeKind;
  size_t old_len=0, new_len=0; std::string old_sha, new_sha; };

static void diffSnapshots(const Snapshot &A, const Snapshot &B, std::vector<DiffItem> &out){
  logInfo("Diffing snapshots");
  if(A.root->subtree_hash == B.root->subtree_hash){
    logInfo("Snapshots identical; no differences detected");
    return;
  }
  std::set<std::string> all;
  for(auto &kv : A.by_path) all.insert(kv.first);
  for(auto &kv : B.by_path) all.insert(kv.first);
  size_t initial = out.size();
  for(const auto &p : all){
    auto ia = A.by_path.find(p), ib = B.by_path.find(p);
    if(ia==A.by_path.end()){ out.push_back({DiffItem::Add, p, ib->second->kind}); continue; }
    if(ib==B.by_path.end()){ out.push_back({DiffItem::Del, p, ia->second->kind}); continue; }
    Node* na = ia->second; Node* nb = ib->second;
    if(na->subtree_hash == nb->subtree_hash) continue;
    if(na->node_hash != nb->node_hash){
      DiffItem d; d.k=DiffItem::Mod; d.path=p; d.nodeKind=nb->kind;
      if(nb->kind==Kind::Method){ d.old_len=na->attrs.aml_len; d.new_len=nb->attrs.aml_len; d.old_sha=na->attrs.aml_sha256; d.new_sha=nb->attrs.aml_sha256; }
      out.push_back(std::move(d));
    }
  }
  logInfo(std::string("Diff identified ") + std::to_string(out.size()-initial) + " change(s)");
}

static void printDiff(const std::vector<DiffItem>& items){
  logInfo(std::string("Printing diff with ") + std::to_string(items.size()) + " change(s)");
  for(const auto &d : items){
    if(d.k==DiffItem::Add){ std::cout<<"+ "<<d.path<<" ("<<kindName(d.nodeKind)<<")\n"; }
    else if(d.k==DiffItem::Del){ std::cout<<"- "<<d.path<<" ("<<kindName(d.nodeKind)<<")\n"; }
    else {
      std::cout<<"~ "<<d.path<<" ("<<kindName(d.nodeKind)<<")";
      if(d.nodeKind==Kind::Method){
        std::cout<<" aml_len: "<<d.old_len<<"→"<<d.new_len;
        if(!d.old_sha.empty() || !d.new_sha.empty()) std::cout<<" aml_sha256: "<<(d.old_sha.empty()?"?":d.old_sha.substr(0,12))<<"…→"<<(d.new_sha.empty()?"?":d.new_sha.substr(0,12))<<"…";
      }
      std::cout<<"\n";
    }
  }
}

// ---------------- Printing ----------------

static void printTree(const Node* n, int depth=0){
  if(depth>0){
    std::cout<<n->path<<" ("<<kindName(n->kind)<<")";
    if(n->kind==Kind::Method){ std::cout<<" args="<<n->attrs.arg_count<<" ser="<<(n->attrs.serialized?1:0)<<" aml_len="<<n->attrs.aml_len; }
    std::cout<<" table="<<n->table_id<<"\n";
  }
  for(const auto &ch : n->children) printTree(ch.get(), depth+1);
}

// ---------------- CLI ----------------

struct Cli {
  std::vector<std::string> loadA, loadB;
  bool do_print=false, do_diff=false;
  LogSeverity verbosity = LogSeverity::Error;
};

static void usage(const char* argv0){
  std::cerr << "Usage:\n"
            << "  "<<argv0<<" [--verbosity LEVEL] --load DSDT.aml SSDT*.aml --print\n"
            << "  "<<argv0<<" [--verbosity LEVEL] --loadA A/DSDT.aml A/SSDT*.aml --loadB B/DSDT.aml B/SSDT*.aml --diff\n"
            << "Options:\n"
            << "  --verbosity LEVEL  Set logging verbosity (error, warning, info). Default: error.\n"
            << "  --verbose         Shorthand for --verbosity info.\n";
}

static LogSeverity parseVerbosityValue(const std::string &value){
  std::string lower;
  lower.reserve(value.size());
  for(char ch : value){
    lower.push_back(static_cast<char>(std::tolower(static_cast<unsigned char>(ch))));
  }
  if(lower == "error" || lower == "errors") return LogSeverity::Error;
  if(lower == "warning" || lower == "warnings" || lower == "warn") return LogSeverity::Warning;
  if(lower == "info" || lower == "information") return LogSeverity::Info;
  throw std::runtime_error("Invalid verbosity level: " + value);
}

static Cli parseCli(int argc, char** argv){
  Cli c; for(int i=1;i<argc;i++){
    std::string a=argv[i];
    if(a=="--load"||a=="--loadA"){ std::vector<std::string> pats; for(i=i+1;i<argc && argv[i][0]!='-'; i++){ pats.emplace_back(argv[i]); } i--; auto files=expandGlobs(pats); c.loadA=files; }
    else if(a=="--loadB"){ std::vector<std::string> pats; for(i=i+1;i<argc && argv[i][0]!='-'; i++){ pats.emplace_back(argv[i]); } i--; c.loadB=expandGlobs(pats); }
    else if(a=="--print"){ c.do_print=true; }
    else if(a=="--diff"){ c.do_diff=true; }
    else if(a=="--verbosity"){
      if(i+1 >= argc) throw std::runtime_error("--verbosity requires an argument");
      c.verbosity = parseVerbosityValue(argv[++i]);
    }
    else if(a=="--verbose"){ c.verbosity = LogSeverity::Info; }
    else { usage(argv[0]); throw std::runtime_error("Unknown arg: "+a); }
  }
  if(!c.do_print && !c.do_diff) throw std::runtime_error("Select --print or --diff");
  if(c.do_print && c.loadA.empty()) throw std::runtime_error("--print requires --load");
  if(c.do_diff && (c.loadA.empty()||c.loadB.empty())) throw std::runtime_error("--diff requires --loadA and --loadB");
  return c;
}

int main(int argc, char** argv){
  try{
    auto cli = parseCli(argc, argv);
    if(cli.do_print && cli.do_diff){ usage(argv[0]); return 1; }
    gLogThreshold = cli.verbosity;
    if(isInfoEnabled()) logInfo("Starting acpidiff");

    AcpiGuard guard;

    if(cli.do_print){
      logInfo("Loading tables for print mode");
      loadTablesFromFiles(cli.loadA);
      auto snap = buildSnapshot();
      logInfo("Printing namespace tree");
      printTree(snap.root.get());
      return 0;
    }

    if(cli.do_diff){
      logInfo("Loading tables for diff mode (set A)");
      loadTablesFromFiles(cli.loadA);
      auto snapA = buildSnapshot();
      logInfo("Terminating ACPICA before loading set B");
      AcpiTerminate();
      logInfo("Reinitializing ACPICA for set B");
      new (&guard) AcpiGuard();
      logInfo("Loading tables for diff mode (set B)");
      loadTablesFromFiles(cli.loadB);
      auto snapB = buildSnapshot();

      std::vector<DiffItem> items; items.reserve(128);
      diffSnapshots(snapA, snapB, items);
      logInfo("Printing diff results");
      printDiff(items);
      return 0;
    }
  } catch(const std::exception &e){ logError(e.what()); return 1; }
  return 0;
}
