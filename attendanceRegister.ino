#include "SPI.h"
#include "MFRC522.h"

#include <ESP8266WiFi.h>
#include <ESP8266HTTPClient.h>
#include <WiFiClient.h>

#include <TM1637Display.h>

#define CLK 5 //D1
#define DIO 4 //D2
TM1637Display display(CLK, DIO);

#define SEG_INTERVAL 5000

#define SUCCESS_LED 16 //D0
#define FAIL_LED 10 //S3

#define PIEZO_PIN 15 //D8
#define TONE_PITCH 930

#define RST_PIN 0 //D3
#define SS_PIN 2 //D4
MFRC522 rfid(SS_PIN, RST_PIN);

#define WIFI_SSID "Xiaomi_1CF4"
#define WIFI_PSK "9057353803"

#define INTERNAL_SERVER_ERROR 500
#define SERVICE_UNAVAILABLE 503

String baseURL = "http://cbsh-api.herokuapp.com";
String DEVICE_SERIAL = "DEVICE_0000";

String date = "";
String securityWord = "";

const uint8_t SEG_BLANK[] = {0x00, 0x00, 0x00, 0x00};
const uint8_t SEG_LOAD[] = {
  SEG_D,
  SEG_E,
  SEG_G,
  SEG_C
};

uint8_t segData[] = {0x00, 0x00, 0x00, 0x00};

unsigned long time_now = 0;
bool segBusy = false;

// SHA256 FUNCTIONS PART //////////

char hex[256];
uint8_t data[256];
int start = 0;
int seconds = 0;
uint8_t hash[32];
String pin;
#define SHA256_BLOCK_SIZE 32

typedef struct {
  uint8_t data[64];
  uint32_t datalen;
  unsigned long long bitlen;
  uint32_t state[8];
} SHA256_CTX;

void sha256_init(SHA256_CTX *ctx);
void sha256_update(SHA256_CTX *ctx, const uint8_t data[], size_t len);
void sha256_final(SHA256_CTX *ctx, uint8_t hash[]);

#define ROTLEFT(a,b) (((a) << (b)) | ((a) >> (32-(b))))
#define ROTRIGHT(a,b) (((a) >> (b)) | ((a) << (32-(b))))

#define CH(x,y,z) (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x,y,z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define EP0(x) (ROTRIGHT(x,2) ^ ROTRIGHT(x,13) ^ ROTRIGHT(x,22))
#define EP1(x) (ROTRIGHT(x,6) ^ ROTRIGHT(x,11) ^ ROTRIGHT(x,25))
#define SIG0(x) (ROTRIGHT(x,7) ^ ROTRIGHT(x,18) ^ ((x) >> 3))
#define SIG1(x) (ROTRIGHT(x,17) ^ ROTRIGHT(x,19) ^ ((x) >> 10))

static const uint32_t k[64] = {
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

void sha256_transform(SHA256_CTX *ctx, const uint8_t data[]) {
  uint32_t a, b, c, d, e, f, g, h, i, j, t1, t2, m[64];

  for (i = 0, j = 0; i < 16; ++i, j += 4)
    m[i] = ((uint32_t)data[j] << 24) | ((uint32_t)data[j + 1] << 16) | ((uint32_t)data[j + 2] << 8) | ((uint32_t)data[j + 3]);
  for ( ; i < 64; ++i)
    m[i] = SIG1(m[i - 2]) + m[i - 7] + SIG0(m[i - 15]) + m[i - 16];

  a = ctx->state[0];
  b = ctx->state[1];
  c = ctx->state[2];
  d = ctx->state[3];
  e = ctx->state[4];
  f = ctx->state[5];
  g = ctx->state[6];
  h = ctx->state[7];

  for (i = 0; i < 64; ++i) {
    t1 = h + EP1(e) + CH(e,f,g) + k[i] + m[i];
    t2 = EP0(a) + MAJ(a,b,c);
    h = g;
    g = f;
    f = e;
    e = d + t1;
    d = c;
    c = b;
    b = a;
    a = t1 + t2;
  }

  ctx->state[0] += a;
  ctx->state[1] += b;
  ctx->state[2] += c;
  ctx->state[3] += d;
  ctx->state[4] += e;
  ctx->state[5] += f;
  ctx->state[6] += g;
  ctx->state[7] += h;
}

void sha256_init(SHA256_CTX *ctx)
{
  ctx->datalen = 0;
  ctx->bitlen = 0;
  ctx->state[0] = 0x6a09e667;
  ctx->state[1] = 0xbb67ae85;
  ctx->state[2] = 0x3c6ef372;
  ctx->state[3] = 0xa54ff53a;
  ctx->state[4] = 0x510e527f;
  ctx->state[5] = 0x9b05688c;
  ctx->state[6] = 0x1f83d9ab;
  ctx->state[7] = 0x5be0cd19;
}

void sha256_update(SHA256_CTX *ctx, const uint8_t data[], size_t len) {
  uint32_t i;

  for (i = 0; i < len; ++i) {
    ctx->data[ctx->datalen] = data[i];
    ctx->datalen++;
    if (ctx->datalen == 64) {
      sha256_transform(ctx, ctx->data);
      ctx->bitlen += 512;
      ctx->datalen = 0;
    }
  }
}

void sha256_final(SHA256_CTX *ctx, uint8_t hash[]) {
  uint32_t i;

  i = ctx->datalen;

  // Pad whatever data is left in the buffer.
  if (ctx->datalen < 56) {
    ctx->data[i++] = 0x80;
    while (i < 56)
      ctx->data[i++] = 0x00;
  }
  else {
    ctx->data[i++] = 0x80;
    while (i < 64)
      ctx->data[i++] = 0x00;
    sha256_transform(ctx, ctx->data);
    memset(ctx->data, 0, 56);
  }

  // Append to the padding the total message's length in bits and transform.
  ctx->bitlen += ctx->datalen * 8;
  ctx->data[63] = ctx->bitlen;
  ctx->data[62] = ctx->bitlen >> 8;
  ctx->data[61] = ctx->bitlen >> 16;
  ctx->data[60] = ctx->bitlen >> 24;
  ctx->data[59] = ctx->bitlen >> 32;
  ctx->data[58] = ctx->bitlen >> 40;
  ctx->data[57] = ctx->bitlen >> 48;
  ctx->data[56] = ctx->bitlen >> 56;
  sha256_transform(ctx, ctx->data);

  // Since this implementation uses little endian byte ordering and SHA uses big endian,
  // reverse all the bytes when copying the final state to the output hash.
  for (i = 0; i < 4; ++i) {
    hash[i]      = (ctx->state[0] >> (24 - i * 8)) & 0x000000ff;
    hash[i + 4]  = (ctx->state[1] >> (24 - i * 8)) & 0x000000ff;
    hash[i + 8]  = (ctx->state[2] >> (24 - i * 8)) & 0x000000ff;
    hash[i + 12] = (ctx->state[3] >> (24 - i * 8)) & 0x000000ff;
    hash[i + 16] = (ctx->state[4] >> (24 - i * 8)) & 0x000000ff;
    hash[i + 20] = (ctx->state[5] >> (24 - i * 8)) & 0x000000ff;
    hash[i + 24] = (ctx->state[6] >> (24 - i * 8)) & 0x000000ff;
    hash[i + 28] = (ctx->state[7] >> (24 - i * 8)) & 0x000000ff;
  }
}

char *btoh(char *dest, uint8_t *src, int len) {
  char *d = dest;
  while( len-- ) sprintf(d, "%02x", (unsigned char)*src++), d += 2;
  return dest;
}

String SHA256(String data) 
{
  uint8_t data_buffer[data.length()];
  
  for(int i=0; i<data.length(); i++)
  {
    data_buffer[i] = (uint8_t)data.charAt(i);
  }
  
  SHA256_CTX ctx;
  ctx.datalen = 0;
  ctx.bitlen = 512;
  
  sha256_init(&ctx);
  sha256_update(&ctx, data_buffer, data.length());
  sha256_final(&ctx, hash);
  return(btoh(hex, hash, 32));
}


///////////////////////////////////////
// SHA256 FUNCTIONS PART END //////////
///////////////////////////////////////

uint8_t encodeCharacter(char character) {
  const uint8_t SEG_CHARACTER[] = {
    SEG_A | SEG_B | SEG_C | SEG_E | SEG_F | SEG_G, //0, A
    SEG_C | SEG_D | SEG_E | SEG_F | SEG_G, //1, b
    SEG_D | SEG_E | SEG_G, //2, C
    SEG_B | SEG_C | SEG_D | SEG_E | SEG_G, //3, d
    SEG_A | SEG_D | SEG_E | SEG_F | SEG_G, //4, E
    SEG_A | SEG_E | SEG_F | SEG_G, //5, F
    SEG_A | SEG_B | SEG_C | SEG_D | SEG_F | SEG_G, //6, g
    SEG_B | SEG_C | SEG_E | SEG_F | SEG_G, //7, H
    SEG_E, //8, i
    SEG_B | SEG_C | SEG_D, //9, J
    SEG_D | SEG_E | SEG_F, //10, L
    SEG_C | SEG_E | SEG_G, //11, n
    SEG_C | SEG_D | SEG_E | SEG_G, //12, o
    SEG_A | SEG_B | SEG_E | SEG_F | SEG_G, //13, P
    SEG_A | SEG_B | SEG_C | SEG_F | SEG_G, //14, q
    SEG_E | SEG_G, //15, r
    SEG_A | SEG_C | SEG_D | SEG_F | SEG_G, //16, S
    SEG_D | SEG_E | SEG_F | SEG_G, //17, t
    SEG_C | SEG_D | SEG_E, //18, u
    SEG_B | SEG_C | SEG_D | SEG_F | SEG_G, //19, y
    SEG_D, //20, _
    SEG_C | SEG_E | SEG_F | SEG_G, //21, h
    SEG_A | SEG_D | SEG_E | SEG_F //22, C
  };

  switch(character) {
    case 'a':
    case 'A':
      return SEG_CHARACTER[0];
    case 'b':
    case 'B':
      return SEG_CHARACTER[1];
    case 'c':
      return SEG_CHARACTER[2];
    case 'C':
      return SEG_CHARACTER[22];
    case 'd':
    case 'D':
      return SEG_CHARACTER[3];
    case 'e':
    case 'E':
      return SEG_CHARACTER[4];
    case 'f':
    case 'F':
      return SEG_CHARACTER[5];
    case 'g':
    case 'G':
      return SEG_CHARACTER[6];
    case 'H':
      return SEG_CHARACTER[7];
    case 'i':
    case 'I':
      return SEG_CHARACTER[8];
    case 'j':
    case 'J':
      return SEG_CHARACTER[9];
    case 'l':
    case 'L':
      return SEG_CHARACTER[10];
    case 'n':
    case 'N':
      return SEG_CHARACTER[11];
    case 'o':
    case 'O':
      return SEG_CHARACTER[12];
    case 'p':
    case 'P':
      return SEG_CHARACTER[13];
    case 'q':
    case 'Q':
      return SEG_CHARACTER[14];
    case 'r':
    case 'R':
      return SEG_CHARACTER[15];
    case 's':
    case 'S':
      return SEG_CHARACTER[16];
    case 't':
    case 'T':
      return SEG_CHARACTER[17];
    case 'u':
    case 'U':
      return SEG_CHARACTER[18];
    case 'y':
    case 'Y':
      return SEG_CHARACTER[19];
    case '_':
      return SEG_CHARACTER[20];
    case 'h':
      return SEG_CHARACTER[21];
    case '0':
      return display.encodeDigit(0);
    case '1':
      return display.encodeDigit(1);
    case '2':
      return display.encodeDigit(2);
    case '3':
      return display.encodeDigit(3);
    case '4':
      return display.encodeDigit(4);
    case '5':
      return display.encodeDigit(5);
    case '6':
      return display.encodeDigit(6);
    case '7':
      return display.encodeDigit(7);
    case '8':
      return display.encodeDigit(8);
    case '9':
      return display.encodeDigit(9);
    default:
      return 0x00;
  }
};

void writeCharacter(String output, bool logg = true) {
  if(logg) {
    for(int i = 0; i < 4; i++) {
      segData[i] = encodeCharacter(output[i]);
    }
    display.setSegments(segData);
  } else {
    uint8_t segmentTemp[] = {0x00, 0x00, 0x00, 0x00};
    for(int i = 0; i < 4; i++) {
      segmentTemp[i] = encodeCharacter(output[i]);
    }
    display.setSegments(segmentTemp);
  }
}

String rfidSerial(byte *buffer, byte bufferSize) {
  char cardSerialArr[bufferSize];
  for (byte i = 0; i < bufferSize; i++){
    cardSerialArr[i] = buffer[i];
  }
  
  String serialString(cardSerialArr);
  return serialString;
}

String createAttendForm(String cardCredential) {
  String verificationString = SHA256(date + cardCredential + securityWord);
  
  String form;
  form += "{";
  form += "\"credential\":\"" + cardCredential + "\",";
  form += "\"verificationString\":\"" + verificationString + "\",";
  form += "\"deviceSerial\":\"" + DEVICE_SERIAL;
  form += "\"}";

  return form;
}

bool updateInfo() {
  if(WiFi.status() == WL_CONNECTED) {    
    WiFiClient client;
    HTTPClient http;

    http.begin(client, (baseURL + "/info/today").c_str());
    int httpResponseCode = http.GET();

    if(httpResponseCode == 200) {
      date = http.getString();
      Serial.println(date);
    } else {
      Serial.println("date fail");
      return false;
    }
    http.end();

    http.begin(client, (baseURL + "/info/securityWord").c_str());
    httpResponseCode = http.GET();
    
    if(httpResponseCode == 200) {
      securityWord = http.getString();
      Serial.println(securityWord);
      return true;
    } else {
      Serial.println("securityWord fail");
      return false;
    }
    http.end();
    
  } else {
    return false;
  }
}

bool tryUpdateInfo(int times = 0, int delayPhaseCount = 6) {
  if(times == 0) {
    while(true) {
      Serial.println("Try updateInfo");
      bool success = updateInfo();
      Serial.println(success);
      if(success) {
        Serial.println("updateInfo success");
        return true;
      } else {
        Serial.println("updateInfo fail");
        Serial.println("RE");
        for(int j = delayPhaseCount; j > 0; j--) {
          writeCharacter("ftch");
          delay(1000);
          writeCharacter("err");
          delay(1000);
          for(int k = 2; k < 5; k++) {
            writeCharacter("re" + String(j*5-k < 10 ? " " : "") + String(j*5-k));
            delay(1000);
          }
          writeCharacter("try_");
        }
      }
    }
  } else {
    bool success = updateInfo();
    if(success) {
      return true;
    } else {
      for(int i = 0; i < times-1; i++) {
        for(int j = delayPhaseCount; j > 0; j--) {
          writeCharacter("sver");
          delay(1000);
          writeCharacter("err");
          delay(1000);
          for(int k = 2; k < 5; k++) {
            writeCharacter("re" + String(j*5-k < 10 ? "x" : "") + String(j*5-k));
            delay(1000);
          }
          writeCharacter("try_");
        }
        bool success = updateInfo();
        if(success) {
          display.setSegments(segData);
          return true;
        }
      }
    }
    return false;
  }
}

void success() {
  digitalWrite(SUCCESS_LED, HIGH);
  tone(PIEZO_PIN, TONE_PITCH, 50);
  delay(50);
  digitalWrite(SUCCESS_LED, LOW);
  delay(50);
  digitalWrite(SUCCESS_LED, HIGH);
  tone(PIEZO_PIN, TONE_PITCH, 50);
  delay(50);
  digitalWrite(SUCCESS_LED, LOW);
  delay(50);
  digitalWrite(SUCCESS_LED, HIGH);
  tone(PIEZO_PIN, TONE_PITCH, 50);
  segBusy = true;
  time_now = millis();
}

void fail() {
  for(int i = 0; i < 4; i++) {
    digitalWrite(FAIL_LED, HIGH);
    tone(PIEZO_PIN, TONE_PITCH, 50);
    delay(50);
    digitalWrite(FAIL_LED, LOW);
    tone(PIEZO_PIN, TONE_PITCH, 50);
    delay(50);
  }
  digitalWrite(FAIL_LED, HIGH);
  segBusy = true;
  time_now = millis();
}

void initStat() {
  digitalWrite(SUCCESS_LED, LOW);
  digitalWrite(FAIL_LED, LOW);
  segBusy = false;
}

///////////////////////////////////
//// FUNCTIONS END ////////////////
///////////////////////////////////

void setup() {
  pinMode(FAIL_LED, OUTPUT);
  pinMode(SUCCESS_LED, OUTPUT);
  digitalWrite(FAIL_LED, LOW);
  digitalWrite(SUCCESS_LED, LOW);
  
  Serial.begin(9600);
  SPI.begin();
  rfid.PCD_Init();

  display.setBrightness(0x0a);

  WiFi.mode(WIFI_STA);
  WiFi.begin(WIFI_SSID, WIFI_PSK);

  segData[0] = encodeCharacter('n');
  segData[1] = encodeCharacter('e');
  segData[2] = encodeCharacter('t');
  segData[3] = 0x00;

  int loadIndex = 0;
  while (WiFi.status() != WL_CONNECTED) {
    segData[3] = SEG_LOAD[loadIndex];
    display.setSegments(segData);
    delay(100);
    
    loadIndex++;
    if(loadIndex > 3) loadIndex = 0;
  }

  writeCharacter("init", true);
  
  tryUpdateInfo();

  writeCharacter("stby", true);
}

void loop() {  
  if(segBusy) {
    if(millis() - time_now >= SEG_INTERVAL) {
      time_now = millis();

      initStat();
      writeCharacter("stby");
    }
  }
  
  //Look for new cards
  if(!rfid.PICC_IsNewCardPresent()){
    return;
  }
  //Select one of cards
  if(!rfid.PICC_ReadCardSerial()){
    return;
  }

  initStat();
  writeCharacter("tagd", true);

  tone(PIEZO_PIN, TONE_PITCH, 50);

  MFRC522::PICC_Type piccType = rfid.PICC_GetType(rfid.uid.sak);

  String cardSerial = rfidSerial(rfid.uid.uidByte, rfid.uid.size) + rfid.PICC_GetTypeName(piccType);
  String cardCredential = SHA256(cardSerial);

  Serial.println(SHA256(cardSerial));

  if(WiFi.status() == WL_CONNECTED) {
    WiFiClient client;
    HTTPClient http;

    http.begin(client, baseURL + "/attendance");
    http.addHeader("Content-Type", "application/json");
    
    int httpResponseCode = http.POST(createAttendForm(cardCredential));
    String payload = http.getString();  
    if(httpResponseCode == 200) {
      if(payload[0] == '1' || payload[0] == '2' || payload[0] == '3') {
        writeCharacter(payload);
        success();
      } else {
        if(payload == "E002") {
          tryUpdateInfo(5, 0);
  
          if(WiFi.status() == WL_CONNECTED) {
            WiFiClient client;
            HTTPClient http;
        
            http.begin(client, baseURL + "/attendance");
            http.addHeader("Content-Type", "application/json");
            
            int httpResponseCode = http.POST(createAttendForm(cardCredential));
            String payload = http.getString();
            if(httpResponseCode == 200) {
              
              if(payload[0] == '1' || payload[0] == '2' || payload[0] == '3') {
                writeCharacter(payload);
                success();
              } else {
                writeCharacter(payload);
                fail();
              }
              
            } else {
              writeCharacter("E" + String(httpResponseCode));
              fail();
            }
            http.end();
          } else {
            writeCharacter("netE");
            fail();
          }
        } else {
          writeCharacter(payload);
          fail();
        }
        http.end();
      }
    } else {
      writeCharacter("E" + String(httpResponseCode));
      fail();
    }
    http.end();
  } else {
    writeCharacter("netE");
    fail();
  }
  
  rfid.PICC_HaltA();
  rfid.PCD_StopCrypto1();
}
