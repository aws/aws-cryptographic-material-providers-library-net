// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.1.0.0
// Command Line Options: -stdin -noVerify -vcsCores:2 -compileTarget:cs -spillTargetCode:3 -runAllTests:1 -compile:0 -optimizeErasableDatatypeWrapper:0 -quantifierSyntax:3 -unicodeChar:0 -functionSyntax:3 -useRuntimeLib -out runtimes/net/tests/TestsFromDafny -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/StandardLibrary/src/Index.dfy -library:src/Index.dfy
// the_program

method {:verify false} {:main} _Test__Main_()























































module TestAwsCryptographyPrimitivesAesKdfCtr {

  import Primitives = Aws.Cryptography.Primitives

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened AesKdfCtr
  method {:test} AesKdfCtrTests()
  {
    var key: seq<uint8> := [138, 39, 30, 72, 206, 182, 214, 144, 245, 34, 28, 219, 204, 175, 198, 23, 132, 234, 125, 246, 130, 54, 251, 60, 137, 120, 166, 245, 0, 150, 79, 107];
    var nonce: seq<uint8> := [66, 32, 73, 11, 207, 79, 97, 80, 11, 22, 236, 247, 42, 6, 222, 165];
    var goal: seq<uint8> := [143, 128, 174, 191, 9, 171, 140, 22, 40, 143, 11, 239, 249, 101, 61, 120, 176, 23, 233, 210, 125, 72, 114, 70, 209, 170, 206, 96, 24, 112, 215, 169, 100, 136, 162, 231, 208, 24, 135, 121, 223, 13, 239, 180];
    var result :- expect Stream(nonce, key, 44);
    expect |result| == 44, ""expectation violation""
    expect goal == result, ""expectation violation""
    key := [212, 191, 10, 32, 13, 55, 22, 101, 189, 182, 186, 119, 202, 16, 175, 49, 103, 82, 87, 190, 13, 142, 103, 201, 98, 84, 228, 47, 142, 96, 61, 167];
    nonce := [135, 1, 132, 66, 198, 216, 26, 105, 47, 97, 246, 192, 186, 187, 54, 129];
    goal := [11, 154, 37, 42, 116, 143, 238, 68, 62, 135, 225, 71, 98, 224, 135, 18];
    result :- expect Stream(nonce, key, 16);
    expect |result| == 16, ""expectation violation""
    expect goal == result, ""expectation violation""
    key := [106, 72, 42, 47, 58, 213, 111, 196, 126, 37, 46, 203, 150, 153, 188, 53, 32, 194, 159, 196, 221, 90, 124, 70, 45, 252, 99, 98, 42, 68, 94, 19];
    nonce := [13, 247, 32, 159, 220, 254, 69, 218, 42, 110, 159, 42, 209, 244, 79, 232];
    goal := [150, 218, 139, 126, 166, 233, 178, 123, 229, 210, 40, 218, 141, 26, 127, 208, 124, 197, 212, 69, 251, 71, 73, 90, 47, 134, 46, 7, 215, 208, 194, 180, 174, 110, 1, 57, 16, 37, 16, 235, 93, 138, 25, 180, 85, 16, 229, 165, 238, 36, 56, 131, 247, 31, 64, 23, 249, 67, 153, 94, 23, 243, 69, 11];
    result :- expect Stream(nonce, key, 64);
    expect |result| == 64, ""expectation violation""
    expect goal == result, ""expectation violation""
  }
}

module {:extern ""AesKdfCtr""} AesKdfCtr {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes
  function method {:extern ""AesKdfCtrStream""} Stream(nonce: seq<uint8>, key: seq<uint8>, length: uint32): (res: Result<seq<uint8>, Types.OpaqueError>)
    requires |nonce| == 16
    requires |key| == 32
    ensures res.Success? ==> |res.value| == length as nat
    decreases nonce, key, length
}

module TestAwsCryptographyPrimitivesHMacDigest {

  import Primitives = Aws.Cryptography.Primitives

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes

  import Digest

  import opened Wrappers
  method {:test} DigestTests()
  {
    var client :- expect Primitives.AtomicPrimitives();
    HmacSHA_256(client);
    HmacSHA_384(client);
    HmacSHA_512(client);
  }

  method HmacSHA_256(client: Types.IAwsCryptographicPrimitivesClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
    decreases client
  {
    var _ /* _v0 */ :- expect BasicHMacTest(client := client, input := Types.HMacInput(digestAlgorithm := Types.SHA_256, key := [1, 1, 1, 1], message := [97, 115, 100, 102]), expectedDigest := [93, 12, 86, 145, 123, 239, 169, 72, 195, 226, 204, 179, 103, 94, 195, 83, 134, 128, 226, 185, 184, 203, 98, 100, 115, 32, 7, 44, 172, 11, 81, 16]);
  }

  method HmacSHA_384(client: Types.IAwsCryptographicPrimitivesClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
    decreases client
  {
    var _ /* _v1 */ :- expect BasicHMacTest(client := client, input := Types.HMacInput(digestAlgorithm := Types.SHA_384, key := [1, 1, 1, 1], message := [97, 115, 100, 102]), expectedDigest := [219, 44, 51, 60, 217, 57, 186, 208, 8, 69, 115, 185, 190, 136, 136, 1, 69, 143, 151, 148, 7, 66, 149, 193, 16, 225, 51, 85, 92, 176, 139, 249, 56, 93, 189, 11, 150, 21, 135, 54, 153, 37, 76, 68, 70, 77, 154, 124]);
  }

  method HmacSHA_512(client: Types.IAwsCryptographicPrimitivesClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
    decreases client
  {
    var _ /* _v2 */ :- expect BasicHMacTest(client := client, input := Types.HMacInput(digestAlgorithm := Types.SHA_512, key := [1, 1, 1, 1], message := [97, 115, 100, 102]), expectedDigest := [49, 213, 21, 219, 23, 169, 195, 39, 177, 1, 15, 162, 233, 182, 208, 84, 226, 3, 27, 120, 75, 78, 85, 46, 220, 5, 166, 206, 79, 47, 25, 94, 88, 119, 211, 192, 148, 23, 252, 155, 98, 218, 97, 225, 38, 93, 83, 113, 139, 95, 101, 222, 154, 98, 244, 206, 88, 229, 6, 115, 226, 188, 152, 173]);
  }

  function method BasicHMacTest(nameonly client: Types.IAwsCryptographicPrimitivesClient, nameonly input: Types.HMacInput, nameonly expectedDigest: seq<uint8>): Result<(), Types.Error>
    requires client.ValidState()
    ensures client.ValidState()
    decreases client, input, expectedDigest
  {
    var output: seq<uint8> :- client.HMac(input); Need(|output| == Digest.Length(input.digestAlgorithm), Types.AwsCryptographicPrimitivesError(message := ""Error"")); Need(output == expectedDigest, Types.AwsCryptographicPrimitivesError(message := ""Error"")); Success(())
  }
}

module TestAwsCryptographyPrimitivesDigest {

  import Primitives = Aws.Cryptography.Primitives

  import opened UInt = StandardLibrary.UInt

  import Digest
  method {:test} DigestTests()
  {
    BasicDigestTest(digestAlgorithm := Primitives.Types.SHA_256, message := [97, 115, 100, 102], expectedDigest := [240, 228, 194, 247, 108, 88, 145, 110, 194, 88, 242, 70, 133, 27, 234, 9, 29, 20, 212, 36, 122, 47, 195, 225, 134, 148, 70, 27, 24, 22, 225, 59]);
    BasicDigestTest(digestAlgorithm := Primitives.Types.SHA_384, message := [97, 115, 100, 102], expectedDigest := [166, 158, 125, 243, 11, 36, 192, 66, 236, 84, 12, 203, 189, 191, 177, 86, 44, 133, 120, 112, 56, 200, 133, 116, 156, 30, 64, 142, 45, 98, 250, 54, 100, 44, 208, 7, 95, 163, 81, 232, 34, 226, 184, 165, 145, 57, 205, 157]);
    BasicDigestTest(digestAlgorithm := Primitives.Types.SHA_512, message := [97, 115, 100, 102], expectedDigest := [64, 27, 9, 234, 179, 192, 19, 212, 202, 84, 146, 43, 184, 2, 190, 200, 253, 83, 24, 25, 43, 10, 117, 242, 1, 216, 179, 114, 116, 41, 8, 15, 179, 55, 89, 26, 189, 62, 68, 69, 59, 149, 69, 85, 183, 160, 129, 46, 16, 129, 195, 155, 116, 2, 147, 247, 101, 234, 231, 49, 245, 166, 94, 209]);
  }

  method BasicDigestTest(nameonly digestAlgorithm: Primitives.Types.DigestAlgorithm, nameonly message: seq<uint8>, nameonly expectedDigest: seq<uint8>)
    decreases digestAlgorithm, message, expectedDigest
  {
    var client :- expect Primitives.AtomicPrimitives();
    var input := Primitives.Types.DigestInput(digestAlgorithm := digestAlgorithm, message := message);
    var output :- expect client.Digest(input);
    expect |output| == Digest.Length(digestAlgorithm), ""expectation violation""
    expect output == expectedDigest, ""expectation violation""
  }
}

module TestAwsCryptographyPrimitivesHMAC {

  import Primitives = Aws.Cryptography.Primitives

  import opened UInt = StandardLibrary.UInt

  import Digest
  method {:test} HMACTests()
  {
    BasicHMACTest(digestAlgorithm := Primitives.Types.SHA_256, key := [1, 2, 3, 4], message := [97, 115, 100, 102], expectedDigest := [55, 107, 186, 241, 51, 255, 154, 169, 106, 133, 2, 248, 54, 230, 193, 147, 212, 179, 154, 66, 43, 52, 108, 181, 144, 152, 19, 101, 117, 99, 204, 134]);
    BasicHMACTest(digestAlgorithm := Primitives.Types.SHA_384, key := [1, 2, 3, 4], message := [97, 115, 100, 102], expectedDigest := [90, 206, 234, 81, 173, 76, 235, 148, 203, 139, 195, 46, 251, 14, 97, 110, 146, 49, 147, 24, 240, 1, 17, 231, 58, 104, 146, 53, 144, 167, 11, 112, 7, 39, 122, 15, 58, 53, 144, 91, 16, 223, 51, 98, 30, 88, 23, 166]);
    BasicHMACTest(digestAlgorithm := Primitives.Types.SHA_512, key := [1, 2, 3, 4], message := [97, 115, 100, 102], expectedDigest := [100, 23, 173, 215, 39, 67, 51, 165, 149, 53, 87, 84, 145, 58, 221, 155, 239, 182, 249, 134, 147, 191, 143, 224, 140, 165, 190, 221, 183, 15, 6, 102, 203, 77, 238, 64, 10, 138, 61, 64, 219, 79, 248, 249, 90, 102, 217, 188, 13, 2, 101, 96, 217, 242, 73, 254, 190, 217, 134, 33, 163, 137, 151, 183]);
  }

  method BasicHMACTest(nameonly digestAlgorithm: Primitives.Types.DigestAlgorithm, nameonly key: seq<uint8>, nameonly message: seq<uint8>, nameonly expectedDigest: seq<uint8>)
    decreases digestAlgorithm, key, message, expectedDigest
  {
    var client :- expect Primitives.AtomicPrimitives();
    var input := Primitives.Types.HMacInput(digestAlgorithm := digestAlgorithm, key := key, message := message);
    var output :- expect client.HMac(input);
    expect |output| == Digest.Length(digestAlgorithm), ""expectation violation""
    expect output == expectedDigest, ""expectation violation""
  }
}

module TestAwsCryptographyPrimitivesAES {

  import Primitives = Aws.Cryptography.Primitives

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Digest
  method {:test} AESDecryptTests()
  {
    BasicAESDecryptTest(Primitives.Types.AESDecryptInput(encAlg := Primitives.Types.AES_GCM(keyLength := 32 as int32, tagLength := 16 as int32, ivLength := 12 as int32), key := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], cipherTxt := [102, 165, 173, 47], authTag := [54, 200, 18, 56, 172, 194, 174, 23, 239, 151, 47, 180, 143, 232, 142, 184], iv := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], aad := [3, 3, 3, 3]), [97, 115, 100, 102]);
  }

  method {:test} AESEncryptTests()
  {
    BasicAESEncryptTest(Primitives.Types.AESEncryptInput(encAlg := Primitives.Types.AES_GCM(keyLength := 32 as int32, tagLength := 16 as int32, ivLength := 12 as int32), iv := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], key := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], msg := [97, 115, 100, 102], aad := [3, 3, 3, 3]));
  }

  method BasicAESDecryptTest(input: Primitives.Types.AESDecryptInput, expectedOutput: seq<uint8>)
    decreases input, expectedOutput
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.AESDecrypt(input);
    expect output == expectedOutput, ""expectation violation""
  }

  method BasicAESEncryptTest(input: Primitives.Types.AESEncryptInput)
    decreases input
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.AESEncrypt(input);
    var decryptInput := Primitives.Types.AESDecryptInput(encAlg := input.encAlg, key := input.key, cipherTxt := output.cipherText, authTag := output.authTag, iv := input.iv, aad := input.aad);
    BasicAESDecryptTest(decryptInput, input.msg);
  }
}

module {:options ""-functionSyntax:4""} TestAwsCryptographyPrimitivesRSA {

  import Primitives = Aws.Cryptography.Primitives

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import UTF8
  const RSA_PUBLIC_2048 := ""-----BEGIN PUBLIC KEY-----\n"" + ""MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAqBvECLsPdF1J5DOkaA1n\n"" + ""UrGwNT9ard3KSMaPypla/5Jhz0veCz1OSjnx35+FE3q7omHQBmKRs6XDkj4tJ5vh\n"" + ""1baw2yzgIAqW9lOXK64GiYy0maH2NfRxGbj5LhVq5T4YOkKh9D3GFbfT9/NpcsOZ\n"" + ""M2HDX8Z+M0HM3XymtcfpHk5o6QF1lbBW+rDJEcYhPN0obBufCXaasgsBRP5Ei2b5\n"" + ""18xpy9M19By1yuC9mlNcpE5v5A8fq/qLLT4s34/6dnVxKX6gIoWDzDrUNrnPe0p5\n"" + ""pqZ1SHalrELMf/liXPrf94+0cF8g1fYVGGo+MZsG5/HRngLiskP25w5smMT51U1y\n"" + ""gQIDAQAB\n"" + ""-----END PUBLIC KEY-----""
  const RSA_PUBLIC_3072 := ""-----BEGIN PUBLIC KEY-----\n"" + ""MIIBojANBgkqhkiG9w0BAQEFAAOCAY8AMIIBigKCAYEAnrUonUAKKpZE+LbQfq6I\n"" + ""gAR//GNnT7L6P3LCboXu44StJtvVyAmHZXPgdkxxT1EKLFx+Tys3B7jhgno9cs67\n"" + ""Scf0pLjJAmXOVHa6881oxi5zeP0e6+KzOPugg3C+EknS2PSHTLsdTrkgZU+oUjde\n"" + ""AgRSgmWrp8aMM1WpoLmNcWC/Pi0mSziVnIzE3WhkZ2Ccetz/viRL60VHlTwNQPVa\n"" + ""7fqbcSqBxm/VjDzYvDwzmU+4GNEs5hrA2IFDxxsYZAU8HdASQM18A8W7n0Okaa4e\n"" + ""c4svyKVFkncbNCqetynLU0A5ny7I5WVXV7DNi2VMjD/mZsEt8IrwfuWSMKuIPxs/\n"" + ""Nb/4Psr7ZvbKSlaMwEpyReHvYYqM7dd6A4Y9FirnrpAPaqlfm8UFtHKQvUckxRoR\n"" + ""05kzNN2jIRJtMwGpn+40tiei7eBGMmIn41/dnkM7GOJau4BarSJMiREK1yH9hh1C\n"" + ""GbrQu6i0F9G0uBDITen9/uPX9cxK5pNHAxeWzr2UP1UzAgMBAAE=\n"" + ""-----END PUBLIC KEY-----""
  const RSA_PUBLIC_4096 := ""-----BEGIN PUBLIC KEY-----\n"" + ""MIICIjANBgkqhkiG9w0BAQEFAAOCAg8AMIICCgKCAgEAs86OIUN9RbdEdyQb2tGQ\n"" + ""miDmmeJaYKanLB0lfWiuO85kJK8edZyLkHIzps81qwgVSzbMCBB7QGcMyPbb3wbE\n"" + ""B4EJ32v3cuMVUs6sOvOYV4g1c1Hi1WVqnCeH+3RSFBfb7RL7SvSUmilX2tNV6uZy\n"" + ""BmMSGBJ/IMzxoHjKSFn6r1ttwov8X5DmNTyIp4qG3qyL1qhpla1bUE5Nb6uMHI2v\n"" + ""qMM+8zSPcRN40CfaQATxevNs/69++XJ+5L1nKU9fMwust1GEbtJ6cIBwAuqlyMm9\n"" + ""CnZ+tn56FEVPrUrsQX35QRNjbi0jjKI8ItkdyJ5fLixCjJ20tCo5jeL5KJ32Rjuw\n"" + ""BlB2KQrgdw5VEMrMlTJz9oozUv8GFzjtS4kx+tAsWhji5s0jry4QFYG01Q4ezVPb\n"" + ""TYdxg1Yz265EyLmF0+/ZQtO1kQc7tXHD5Gzzwyqot/UdJwlXStUGB2yEe62HQ2LT\n"" + ""9Ly3V7rUDJzO44zuFVjqchRPYWNdiYl8BVP/ak2bMtcowk06T9bo1tRf4HJWfpIM\n"" + ""GF27MXqykKHxcmOb0UfGIfI0eUtkid4gJdCxhidiILj6SHpEr+oa/Oogz01rVCdm\n"" + ""mbWmgFxmiKse8NXNQR+7qhMYX5GgdeSbp/Lg24HF9mvnd0S2wHkC86lGyQtvzrsd\n"" + ""DdUJZ2jqiKvMLdMKNFHFGGUCAwEAAQ==\n"" + ""-----END PUBLIC KEY-----""

  method {:test} RSAEncryptTests()
  {
    var client :- expect Primitives.AtomicPrimitives();
    var keys := client.GenerateRSAKeyPair(input := Primitives.Types.GenerateRSAKeyPairInput(lengthBits := 2048 as Primitives.Types.RSAModulusLengthBits));
    expect keys.Success?, ""expectation violation""
    BasicRSAEncryptTest(Primitives.Types.RSAEncryptInput(padding := Primitives.Types.RSAPaddingMode.OAEP_SHA256, publicKey := keys.value.publicKey.pem, plaintext := [97, 115, 100, 102]), keys.value);
  }

  method {:test} GetRSAKeyModulusLength()
  {
    var client :- expect Primitives.AtomicPrimitives();
    var publicKey2048 :- expect UTF8.Encode(RSA_PUBLIC_2048);
    var length2048 :- expect client.GetRSAKeyModulusLength(Primitives.Types.GetRSAKeyModulusLengthInput(publicKey := publicKey2048));
    expect length2048.length == 2048, ""expectation violation""
    var publicKey3072 :- expect UTF8.Encode(RSA_PUBLIC_3072);
    var length3072 :- expect client.GetRSAKeyModulusLength(Primitives.Types.GetRSAKeyModulusLengthInput(publicKey := publicKey3072));
    expect length3072.length == 3072, ""expectation violation""
    var publicKey4096 :- expect UTF8.Encode(RSA_PUBLIC_4096);
    var length4096 :- expect client.GetRSAKeyModulusLength(Primitives.Types.GetRSAKeyModulusLengthInput(publicKey := publicKey4096));
    expect length4096.length == 4096, ""expectation violation""
  }

  method BasicRSADecryptTests(input: Primitives.Types.RSADecryptInput, expectedOutput: seq<uint8>)
    decreases input, expectedOutput
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.RSADecrypt(input);
    expect output == expectedOutput, ""expectation violation""
  }

  method BasicRSAEncryptTest(input: Primitives.Types.RSAEncryptInput, keypair: Primitives.Types.GenerateRSAKeyPairOutput)
    decreases input, keypair
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.RSAEncrypt(input);
    var decryptInput := Primitives.Types.RSADecryptInput(padding := input.padding, privateKey := keypair.privateKey.pem, cipherText := output);
    BasicRSADecryptTests(decryptInput, input.plaintext);
  }

  method {:test} TestingPemParsingInRSAEncryptionForRSAKeyPairStoredInPEM()
  {
    var allPadding := set p: Primitives.Types.RSAPaddingMode | true :: p;
    var PublicKeyFromGenerateRSAKeyPairPemBytes :- expect UTF8.Encode(StaticPublicKeyFromGenerateRSAKeyPair());
    var PrivateKeyFromGenerateRSAKeyPairPemBytes :- expect UTF8.Encode(StaticPrivateKeyFromGenerateRSAKeyPair());
    var KeyFromGenerateRSAKeyPair := Primitives.Types.GenerateRSAKeyPairOutput(publicKey := Primitives.Types.RSAPublicKey(lengthBits := 2048, pem := PublicKeyFromGenerateRSAKeyPairPemBytes), privateKey := Primitives.Types.RSAPrivateKey(lengthBits := 2048, pem := PrivateKeyFromGenerateRSAKeyPairPemBytes));
    while allPadding != {}
      decreases allPadding
    {
      var padding :| padding in allPadding;
      BasicRSAEncryptTest(Primitives.Types.RSAEncryptInput(padding := padding, publicKey := KeyFromGenerateRSAKeyPair.publicKey.pem, plaintext := [97, 115, 100, 102]), KeyFromGenerateRSAKeyPair);
      allPadding := allPadding - {padding};
    }
  }

  method {:test} TestingPemParsingInRSAEncryptionForOnlyRSAPrivateKeyStoredInPEM()
  {
    var allPadding := set p: Primitives.Types.RSAPaddingMode | true :: p;
    var PublicKeyFromTestVectorsPemBytes :- expect UTF8.Encode(StaticPublicKeyFromTestVectors());
    var PrivateKeyFromTestVectorsPemBytes :- expect UTF8.Encode(StaticPrivateKeyFromTestVectors());
    var KeyFromTestVectorsPair := Primitives.Types.GenerateRSAKeyPairOutput(publicKey := Primitives.Types.RSAPublicKey(lengthBits := 4096, pem := PublicKeyFromTestVectorsPemBytes), privateKey := Primitives.Types.RSAPrivateKey(lengthBits := 4096, pem := PrivateKeyFromTestVectorsPemBytes));
    while allPadding != {}
      decreases allPadding
    {
      var padding :| padding in allPadding;
      BasicRSAEncryptTest(Primitives.Types.RSAEncryptInput(padding := padding, publicKey := KeyFromTestVectorsPair.publicKey.pem, plaintext := [97, 115, 100, 102]), KeyFromTestVectorsPair);
      allPadding := allPadding - {padding};
    }
  }

  function method {:fuel 0, 0} StaticPublicKeyFromGenerateRSAKeyPair(): string
  {
    ""-----BEGIN PUBLIC KEY-----\n"" + ""MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEA0RbkftAm30eFm+o6JraW\n"" + ""AbWR+2grPfQk3i3w4eCsZHDQib6iUwX0MVADd2DjTnlkYa1DytDHRKfWHjtTniQ/\n"" + ""EdKbENIFC5mLgh1Max7n9nQ6bmo4EvH2s4pUr3YBSys/dXpRDUCD/Mt4G+qDE8DT\n"" + ""NSe8dqX5U44HwImQmKzvLYvD5gUY7eM5co4ZpfYrlRRVNkpv5qVNK7bz9KvQmKfP\n"" + ""bQfzyvOZgSqQyHKfxbCM6ByE8Dd0NoI1ALwBY8wCXn/+6q4xLWTywu4nGIXs5Vt7\n"" + ""vrMqwHSvYaNQKjUyPjsG3xPMwKruh30mGzc2KlKLZ+MiV+SNAiooqVkL6CxH4yJc\n"" + ""NwIDAQAB\n"" + ""-----END PUBLIC KEY-----\n""
  }

  function method {:fuel 0, 0} StaticPrivateKeyFromGenerateRSAKeyPair(): string
  {
    ""-----BEGIN PRIVATE KEY-----\n"" + ""MIIEvgIBADANBgkqhkiG9w0BAQEFAASCBKgwggSkAgEAAoIBAQDRFuR+0CbfR4Wb\n"" + ""6jomtpYBtZH7aCs99CTeLfDh4KxkcNCJvqJTBfQxUAN3YONOeWRhrUPK0MdEp9Ye\n"" + ""O1OeJD8R0psQ0gULmYuCHUxrHuf2dDpuajgS8fazilSvdgFLKz91elENQIP8y3gb\n"" + ""6oMTwNM1J7x2pflTjgfAiZCYrO8ti8PmBRjt4zlyjhml9iuVFFU2Sm/mpU0rtvP0\n"" + ""q9CYp89tB/PK85mBKpDIcp/FsIzoHITwN3Q2gjUAvAFjzAJef/7qrjEtZPLC7icY\n"" + ""hezlW3u+syrAdK9ho1AqNTI+OwbfE8zAqu6HfSYbNzYqUotn4yJX5I0CKiipWQvo\n"" + ""LEfjIlw3AgMBAAECggEAWe7DTCpCtgHg3X2jEnixT73lsuGMy+KBoxDWjYkiDTea\n"" + ""8sxMrHIgpL86JnRFgMDk5MBuKsOfGhAooCs7XYdQm11fNh5nbiRWZZotftu1wQMg\n"" + ""CNLmGHv7dSD4KNoUV10cN+7rAsyvmKF5oWQ+idYD4labkNr1wTMTcYSZ7ZlgbNFr\n"" + ""ZFwsZizD4RrpwwyrpZ25f/H95p9fQrZXrB3Wt5aNn0uhTcQL0KfnvMamZNPfxj9b\n"" + ""j6CWpyXtFOMc8nuT4fKOh7q4A87UsduBBhdAk4m4m98WvlIZIUW89w3kzIfr9zCT\n"" + ""VxflBzeEDSM8+Sy1TJNRBBwhRnQ/gNLLD+e6/O/MTQKBgQD/vRxZvyJkWaRYkGeS\n"" + ""VVAZQJOSQUPpVC5U3y2ghV8Dm30BfMEtySdD9hXd635X7e0dvIqwxJAwFgJ+SYT2\n"" + ""NNE8wiIKolQH1h01cYK+kwAohB6vQPLymYwzc9HNcevCDFkt7VVRgnwUHk6BXz4T\n"" + ""LsF/jYTUdzCyFfjYWGTOEh7PkwKBgQDRTZSe2Tqua2Groi75tmXMAzI6jQsiBqTn\n"" + ""Jv0es+IMWZyh2yMy9x6numM7IBBamgt+6hNEKaUmQxoEFbo0dUsEx35RH2Pdkr8X\n"" + ""IuXuh3IdRgRCV9WxnecBD32Cci9qLN1aaVJHfdA2dW4LAb7m4/GeuiS/8ZatXEm2\n"" + ""Kf0YZAx/TQKBgEpbQtX5U9eXlMhHXEXY1kwxUXbx0PwThNEaftqwTJrw55y6GDTm\n"" + ""yqrg7ySyJu8L96hwvGZ/EGlazOjJGYa4fqnKzDkJT6NjpuR2F4yvkxk0qPNN0BWn\n"" + ""fXMsVrEEUYb/LiLDYc4sQUVcNnk5JwRO0OX0UM2xxg/RgaPtt4mPDTRPAoGBAJsY\n"" + ""1izv5CAjyniY8h5xHvYS2EGzCrDoI4J2zdLWkYd9UChQbsDxhnHcGHRTykqZJDOj\n"" + ""2SsFgS/dQYYNY7JDyJd+DQioLiSe/aNzZNdg3xr6K2XOGLhJvkh25han7qLLJCw/\n"" + ""J416mbQBSM43OPN3rjBk1560s2c7oBOxAa/1U51xAoGBAOYFMvdk6H359yaJGmsN\n"" + ""kY7lS6heh4cHfSM7Hw02lh/ovasdQm+afcnDWEW0XQYM6KQCcJiwbIK/kPkVsvJe\n"" + ""o6gynyWoHrrQuRdmffPvzT50paccJuupeHAtfOAue5y57FQUc4Xm4Qj3P7cQJr9z\n"" + ""UMCUAooEJcdmAUyVUy5BQc7P\n"" + ""-----END PRIVATE KEY-----\n""
  }

  function method {:fuel 0, 0} StaticPublicKeyFromTestVectors(): string
  {
    ""-----BEGIN PUBLIC KEY-----\n"" + ""MIICIjANBgkqhkiG9w0BAQEFAAOCAg8AMIICCgKCAgEAs7RoNYEPAIws89VV+kra\n"" + ""rVv/4wbdmUAaAKWgWuxZi5na9GJSmnhCkqyLRm7wPbQY4LCoa5/IMUxkHLsYDPdu\n"" + ""udY0Qm0GcoxOlvJKHYo4RjF7HyiS34D6dvyO4Gd3aq0mZHoxSGCxW/7hf03wEMzc\n"" + ""iVJXWHXhaI0lD6nrzIEgLrE4L+3V2LeAQjvZsTKd+bYMqeZOL2syiVVIAU8POwAG\n"" + ""GVBroJoveFm/SUp6lCiN0M2kTeyQA2ax3QTtZSAa8nwrI7U52XOzVmdMicJsy2Pg\n"" + ""uW98te3MuODdK24yNkHIkYameP/Umf/SJshUJQd5a/TUp3XE+HhOWAumx22tIDlC\n"" + ""vZS11cuk2fp0WeHUnXaC19N5qWKfvHEKSugzty/z3lGP7ItFhrF2X1qJHeAAsL11\n"" + ""kjo6Lc48KsE1vKvbnW4VLyB3wdNiVvmUNO29tPXwaR0Q5Gbr3jk3nUzdkEHouHWQ\n"" + ""41lubOHCCBN3V13mh/MgtNhESHjfmmOnh54ErD9saA1d7CjTf8g2wqmjEqvGSW6N\n"" + ""q7zhcWR2tp1olflS7oHzul4/I3hnkfL6Kb2xAWWaQKvg3mtsY2OPlzFEP0tR5UcH\n"" + ""Pfp5CeS1Xzg7hN6vRICW6m4l3u2HJFld2akDMm1vnSz8RCbPW7jp7YBxUkWJmypM\n"" + ""tG7Yv2aGZXGbUtM8o1cZarECAwEAAQ==\n"" + ""-----END PUBLIC KEY-----""
  }

  function method {:fuel 0, 0} StaticPrivateKeyFromTestVectors(): string
  {
    ""-----BEGIN PRIVATE KEY-----\n"" + ""MIIJQgIBADANBgkqhkiG9w0BAQEFAASCCSwwggkoAgEAAoICAQCztGg1gQ8AjCzz\n"" + ""1VX6StqtW//jBt2ZQBoApaBa7FmLmdr0YlKaeEKSrItGbvA9tBjgsKhrn8gxTGQc\n"" + ""uxgM92651jRCbQZyjE6W8kodijhGMXsfKJLfgPp2/I7gZ3dqrSZkejFIYLFb/uF/\n"" + ""TfAQzNyJUldYdeFojSUPqevMgSAusTgv7dXYt4BCO9mxMp35tgyp5k4vazKJVUgB\n"" + ""Tw87AAYZUGugmi94Wb9JSnqUKI3QzaRN7JADZrHdBO1lIBryfCsjtTnZc7NWZ0yJ\n"" + ""wmzLY+C5b3y17cy44N0rbjI2QciRhqZ4/9SZ/9ImyFQlB3lr9NSndcT4eE5YC6bH\n"" + ""ba0gOUK9lLXVy6TZ+nRZ4dSddoLX03mpYp+8cQpK6DO3L/PeUY/si0WGsXZfWokd\n"" + ""4ACwvXWSOjotzjwqwTW8q9udbhUvIHfB02JW+ZQ07b209fBpHRDkZuveOTedTN2Q\n"" + ""Qei4dZDjWW5s4cIIE3dXXeaH8yC02ERIeN+aY6eHngSsP2xoDV3sKNN/yDbCqaMS\n"" + ""q8ZJbo2rvOFxZHa2nWiV+VLugfO6Xj8jeGeR8vopvbEBZZpAq+Dea2xjY4+XMUQ/\n"" + ""S1HlRwc9+nkJ5LVfODuE3q9EgJbqbiXe7YckWV3ZqQMybW+dLPxEJs9buOntgHFS\n"" + ""RYmbKky0bti/ZoZlcZtS0zyjVxlqsQIDAQABAoICAEr3m/GWIXgNAkPGX9PGnmtr\n"" + ""0dgX6SIhh7d1YOwNZV3DlYAV9HfUa5Fcwc1kQny7QRWbHOepBI7sW2dQ9buTDXIh\n"" + ""VjPP37yxo6d89EZWfxtpUP+yoXL0D4jL257qCvtJuJZ6E00qaVMDhXbiQKABlo8C\n"" + ""9sVEiABhwXBDZsctpwtTiykTgv6hrrPy2+H8R8MAm0/VcBCAG9kG5r8FCEmIvQKa\n"" + ""dgvNxrfiWNZuZ6yfLmpJH54SbhG9Kb4WbCKfvh4ihqyi0btRdSM6fMeLgG9o/zrc\n"" + ""s54B0kHeLOYNVo0j7FQpZBFeSIbmHfln4RKBh7ntrTke/Ejbh3NbiPvxWSP0P067\n"" + ""SYWPkQpip2q0ION81wSQZ1haP2GewFFu4IEjG3DlqqpKKGLqXrmjMufnildVFpBx\n"" + ""ir+MgvgQfEBoGEx0aElyO7QuRYaEiXeb/BhMZeC5O65YhJrWSuTVizh3xgJWjgfV\n"" + ""aYwYgxN8SBXBhXLIVvnPhadTqsW1C/aevLOk110eSFWcHf+FCK781ykIzcpXoRGX\n"" + ""OwWcZzC/fmSABS0yH56ow+I0tjdLIEEMhoa4/kkamioHOJ4yyB+W1DO6/DnMyQlx\n"" + ""g7y2WsAaIEBoWUARy776k70xPPMtYAxzFXI9KhqRVrPfeaRZ+ojeyLyr3GQGyyoo\n"" + ""cuGRdMUblsmODv4ixmOxAoIBAQDvkznvVYNdP3Eg5vQeLm/qsP6dLejLijBLeq9i\n"" + ""7DZH2gRpKcflXZxCkRjsKDDE+fgDcBYEp2zYfRIVvgrxlTQZdaSG+GoDcbjbNQn3\n"" + ""djCCtOOACioN/vg2zFlX4Bs6Q+NaV7g5qP5SUaxUBjuHLe7Nc+ZkyheMHuNYVLvk\n"" + ""HL/IoWyANpZYjMUU3xMbL/J29Gz7CPGr8Si28TihAHGfcNgn8S04OQZhTX+bU805\n"" + ""/+7B4XW47Mthg/u7hlqFl+YIAaSJYvWkEaVP1A9I7Ve0aMDSMWwzTg9cle2uVaL3\n"" + ""+PTzWY5coBlHKjqAg9ufhYSDhAqBd/JOSlv8RwcA3PDXJ6C/AoIBAQDABmXXYQky\n"" + ""7phExXBvkLtJt2TBGjjwulf4R8TC6W5F51jJuoqY/mTqYcLcOn2nYGVwoFvPsy/Q\n"" + ""CTjfODwJBXzbloXtYFR3PWAeL1Y6+7Cm+koMWIPJyVbD5Fzm+gZStM0GwP8FhDt2\n"" + ""Wt8fWEyXmoLdAy6RAwiEmCagEh8o+13oBfwnBllbz7TxaErsUuR+XVgl/iHwztdv\n"" + ""cdJKyRgaFfWSh9aiO7EMV2rBGWsoX09SRvprPFAGx8Ffm7YcqIk34QXsQyc45Dyn\n"" + ""CwkvypxHoaB3ot/48FeFm9IubApb/ctv+EgkBfL4S4bdwRXS1rt+0+QihBoFyP2o\n"" + ""J91cdm4hEWCPAoIBAQC6l11hFaYZo0bWDGsHcr2B+dZkzxPoKznQH76n+jeQoLIc\n"" + ""wgjJkK4afm39yJOrZtEOxGaxu0CgIFFMk9ZsL/wC9EhvQt02z4TdXiLkFK5VrtMd\n"" + ""r0zv16y06VWQhqBOMf/KJlX6uq9RqADi9HO6pkC+zc0cpPXQEWKaMmygju+kMG2U\n"" + ""Mm/IieMZjWCRJTfgBCE5J88qTsqaKagkZXcZakdAXKwOhQN+F2EStiM6UCZB5PrO\n"" + ""S8dfrO8ML+ki8Zqck8L1qhiNb5zkXtKExy4u+gNr8khGcT6vqqoSxOoH3mPRgOfL\n"" + ""Jnppne8wlwIf7Vq3H8ka6zPSXEHma999gZcmy9t7AoIBAGbQhiLl79j3a0wXMvZp\n"" + ""Vf5IVYgXFDnAbG2hb7a06bhAAIgyexcjzsC4C2+DWdgOgwHkuoPg+062QV8zauGh\n"" + ""sJKaa6cHlvIpSJeg3NjD/nfJN3CYzCd0yCIm2Z9Ka6xI5iYhm+pGPNhIG4Na8deS\n"" + ""gVL46yv1pc/o73VxfoGg5UzgN3xlp97Cva0sHEGguHr4W8Qr59xZw3wGQ4SLW35M\n"" + ""F6qXVNKUh12GSMCPbZK2RXBWVKqqJmca+WzJoJ6DlsT2lQdFhXCus9L007xlDXxF\n"" + ""C/hCmw1dEl+VaNo2Ou26W/zdwTKYhNlxBwsg4SB8nPNxXIsmlBBY54froFhriNfn\n"" + ""x/0CggEAUzz+VMtjoEWw2HSHLOXrO4EmwJniNgiiwfX3DfZE4tMNZgqZwLkq67ns\n"" + ""T0n3b0XfAOOkLgMZrUoOxPHkxFeyLLf7pAEJe7QNB+Qilw8e2zVqtiJrRk6uDIGJ\n"" + ""Sv+yM52zkImZAe2jOdU3KeUZxSMmb5vIoiPBm+tb2WupAg3YdpKn1/jWTpVmV/+G\n"" + ""UtTLVE6YpAyFp1gMxhutE9vfIS94ek+vt03AoEOlltt6hqZfv3xmY8vGuAjlnj12\n"" + ""zHaq+fhCRPsbsZkzJ9nIVdXYnNIEGtMGNnxax7tYRej/UXqyazbxHiJ0iPF4PeDn\n"" + ""dzxtGxpeTBi+KhKlca8SlCdCqYwG6Q==\n"" + ""-----END PRIVATE KEY-----""
  }
}

module TestKDF {

  import Primitives = Aws.Cryptography.Primitives

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Digest

  import KdfCtr
  method KdfRawDeriveTest(ikm: seq<uint8>, info: seq<uint8>, L: Primitives.Types.PositiveInteger, expectedOKM: seq<uint8>)
    requires |ikm| == 32 && L == 32 && 4 + |info| < INT32_MAX_LIMIT
    decreases ikm, info, L, expectedOKM
  {
    var output := KdfCtr.RawDerive(ikm, info, L, 0);
    if output.Success? {
      expect |output.value| == L as nat, ""expectation violation""
      expect output.value == expectedOKM, ""expectation violation""
    }
  }

  method KdfTest(input: Primitives.Types.KdfCtrInput, expectedOKM: seq<uint8>)
    decreases input, expectedOKM
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.KdfCounterMode(input);
    expect |output| == input.expectedLength as nat, ""expectation violation""
    expect output == expectedOKM, ""expectation violation""
  }
}

module TestKDFK_TestVectors {

  import Primitives = Aws.Cryptography.Primitives

  import UTF8

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened TestKDF
  datatype InternalTestVector = InternalTestVector(nameonly name: string, nameonly hash: Primitives.Types.DigestAlgorithm, nameonly IKM: seq<uint8>, nameonly info: seq<uint8>, nameonly L: Primitives.Types.PositiveInteger, nameonly OKM: seq<uint8>)

  datatype TestVector = TestVector(nameonly name: string, nameonly hash: Primitives.Types.DigestAlgorithm, nameonly IKM: seq<uint8>, nameonly info: seq<uint8>, nameonly purpose: seq<uint8>, nameonly L: Primitives.Types.PositiveInteger, nameonly OKM: seq<uint8>)

  const PURPOSE: UTF8.ValidUTF8Bytes := UTF8.EncodeAscii(""aws-kms-hierarchy"")
  const rawTestVectors: seq<InternalTestVector> := [b1, b2, b3, b4, b5]
  const testVectors: seq<TestVector> := [c1, c2, c3, c4, c5]
  const b1 := InternalTestVector(name := ""B.1  Test Case 1"", hash := Primitives.Types.SHA_256, IKM := [226, 4, 214, 212, 102, 170, 213, 7, 255, 175, 109, 109, 171, 10, 91, 38, 21, 44, 158, 33, 231, 100, 55, 4, 100, 227, 96, 200, 251, 199, 101, 198], info := [123, 3, 185, 141, 159, 148, 184, 153, 229, 145, 243, 239, 38, 75, 113, 177, 147, 251, 167, 4, 60, 126, 149, 60, 222, 35, 188, 83, 132, 188, 26, 98, 147, 88, 1, 21, 250, 227, 73, 95, 216, 69, 218, 219, 208, 43, 214, 69, 92, 244, 141, 15, 98, 179, 62, 98, 54, 74, 58, 128], L := 32, OKM := [119, 13, 250, 182, 166, 164, 164, 190, 224, 37, 127, 243, 53, 33, 63, 120, 216, 40, 123, 79, 213, 55, 213, 193, 255, 250, 149, 105, 16, 231, 199, 121])
  const b2 := InternalTestVector(name := ""B.2  Test Case 2"", hash := Primitives.Types.SHA_256, IKM := [174, 238, 202, 96, 246, 137, 164, 65, 177, 59, 12, 188, 212, 65, 216, 45, 240, 207, 135, 218, 194, 54, 41, 13, 236, 232, 147, 29, 248, 215, 3, 23], info := [88, 142, 192, 65, 229, 115, 59, 112, 49, 33, 44, 85, 56, 239, 228, 246, 170, 250, 76, 218, 139, 146, 93, 38, 31, 90, 38, 136, 240, 7, 179, 172, 36, 14, 225, 41, 145, 231, 123, 140, 184, 83, 134, 120, 97, 89, 102, 22, 74, 129, 135, 43, 209, 207, 203, 251, 57, 164, 244, 80], L := 32, OKM := [62, 129, 214, 17, 60, 238, 60, 82, 158, 206, 223, 248, 154, 105, 153, 206, 37, 182, 24, 193, 94, 225, 209, 157, 69, 203, 55, 106, 28, 142, 35, 116])
  const b3 := InternalTestVector(name := ""B.3  Test Case 3"", hash := Primitives.Types.SHA_256, IKM := [149, 200, 247, 110, 17, 54, 126, 181, 85, 38, 162, 179, 147, 174, 144, 101, 131, 209, 203, 221, 71, 150, 33, 70, 245, 6, 204, 124, 172, 18, 244, 100], info := [202, 214, 14, 144, 75, 158, 156, 139, 254, 180, 168, 26, 127, 103, 211, 189, 220, 192, 94, 100, 37, 88, 112, 64, 55, 112, 243, 83, 58, 230, 221, 99, 76, 234, 165, 108, 83, 230, 136, 189, 19, 122, 230, 1, 137, 53, 243, 75, 159, 176, 132, 234, 72, 228, 198, 136, 246, 187, 179, 136], L := 32, OKM := [202, 250, 92, 160, 63, 95, 190, 42, 36, 32, 4, 171, 203, 211, 222, 16, 89, 199, 64, 123, 30, 229, 121, 37, 81, 36, 175, 24, 155, 224, 181, 86])
  const b4 := InternalTestVector(name := ""B.4  Test Case 4"", hash := Primitives.Types.SHA_256, IKM := [77, 5, 57, 31, 214, 251, 30, 41, 46, 120, 171, 150, 25, 177, 183, 42, 125, 99, 238, 89, 215, 67, 93, 215, 24, 151, 185, 255, 126, 231, 174, 112], info := [240, 120, 230, 249, 183, 248, 45, 100, 85, 79, 166, 182, 4, 200, 8, 241, 155, 31, 106, 214, 114, 125, 183, 170, 111, 28, 134, 105, 78, 16, 75, 82, 86, 200, 180, 3, 153, 25, 100, 100, 129, 215, 234, 36, 82, 199, 44, 23, 163, 232, 215, 211, 145, 98, 133, 70, 10, 165, 235, 129], L := 32, OKM := [107, 22, 232, 245, 59, 131, 26, 165, 232, 107, 249, 122, 92, 79, 163, 125, 8, 155, 193, 114, 218, 90, 30, 127, 102, 45, 212, 165, 149, 51, 154, 183])
  const b5 := InternalTestVector(name := ""B.5  Test Case 5"", hash := Primitives.Types.SHA_256, IKM := [15, 104, 168, 47, 241, 103, 22, 52, 204, 145, 54, 197, 100, 169, 224, 42, 118, 118, 33, 221, 116, 161, 191, 92, 36, 18, 155, 128, 130, 20, 183, 82], info := [100, 133, 153, 128, 156, 44, 78, 124, 106, 94, 108, 68, 159, 0, 49, 235, 245, 92, 54, 97, 168, 149, 180, 77, 176, 87, 46, 232, 128, 131, 177, 244, 177, 38, 2, 170, 85, 252, 29, 241, 80, 166, 90, 109, 110, 237, 160, 170, 121, 164, 52, 161, 3, 155, 145, 181, 165, 143, 199, 241], L := 32, OKM := [226, 151, 100, 15, 119, 104, 72, 93, 74, 110, 124, 254, 36, 95, 139, 250, 132, 112, 13, 153, 118, 38, 146, 234, 26, 66, 92, 204, 2, 117, 232, 245])
  const c1 := TestVector(name := ""C.1 Test Case 1"", hash := Primitives.Types.SHA_256, IKM := [125, 201, 189, 252, 37, 52, 4, 124, 254, 99, 233, 235, 41, 123, 119, 82, 81, 73, 237, 125, 74, 252, 233, 198, 68, 15, 53, 14, 97, 239, 62, 208], info := [119, 218, 233, 62, 104, 155, 88, 29, 62, 6, 235, 1, 200, 211, 186, 2], purpose := PURPOSE, L := 32, OKM := [188, 232, 152, 114, 85, 137, 174, 192, 143, 152, 52, 179, 184, 15, 220, 63, 241, 115, 144, 126, 85, 116, 231, 41, 253, 206, 18, 124, 247, 109, 183, 204])
  const c2 := TestVector(name := ""C.2 Test Case 2"", hash := Primitives.Types.SHA_256, IKM := [80, 22, 113, 23, 118, 68, 10, 32, 75, 169, 199, 192, 255, 220, 214, 60, 182, 1, 126, 147, 171, 233, 110, 177, 35, 145, 217, 129, 30, 9, 80, 159], info := [210, 241, 192, 158, 103, 66, 27, 35, 143, 66, 168, 189, 82, 171, 211, 252], purpose := PURPOSE, L := 32, OKM := [54, 206, 174, 72, 237, 133, 85, 156, 93, 53, 120, 152, 118, 82, 89, 33, 114, 98, 204, 236, 138, 57, 162, 118, 85, 92, 199, 232, 240, 252, 92, 97])
  const c3 := TestVector(name := ""C.3 Test Case 3"", hash := Primitives.Types.SHA_256, IKM := [57, 90, 16, 46, 83, 54, 189, 241, 27, 242, 237, 236, 246, 66, 54, 226, 74, 112, 79, 156, 208, 13, 148, 71, 117, 211, 139, 57, 73, 69, 122, 236], info := [51, 15, 183, 124, 82, 229, 249, 86, 117, 148, 237, 162, 27, 243, 173, 108], purpose := PURPOSE, L := 32, OKM := [22, 55, 236, 141, 159, 163, 250, 236, 86, 47, 225, 103, 156, 225, 228, 146, 166, 45, 244, 39, 136, 163, 205, 200, 116, 193, 20, 147, 112, 254, 210, 194])
  const c4 := TestVector(name := ""C.4 Test Case 4"", hash := Primitives.Types.SHA_256, IKM := [152, 192, 25, 223, 239, 154, 175, 67, 237, 250, 184, 146, 228, 243, 227, 1, 128, 247, 228, 152, 142, 131, 149, 41, 60, 70, 244, 58, 166, 234, 86, 189], info := [243, 160, 102, 127, 219, 137, 115, 38, 187, 216, 48, 80, 151, 168, 148, 71], purpose := PURPOSE, L := 32, OKM := [191, 112, 86, 234, 220, 233, 122, 154, 100, 188, 230, 238, 239, 155, 54, 32, 97, 35, 51, 160, 121, 235, 42, 64, 145, 105, 15, 153, 162, 89, 9, 156])
  const c5 := TestVector(name := ""C.5 Test Case 5"", hash := Primitives.Types.SHA_256, IKM := [166, 236, 116, 51, 140, 189, 192, 175, 42, 154, 51, 26, 208, 149, 76, 159, 174, 162, 207, 4, 108, 232, 196, 240, 12, 57, 228, 155, 97, 75, 42, 66], info := [236, 169, 233, 45, 43, 25, 122, 243, 152, 191, 154, 55, 45, 134, 159, 220], purpose := PURPOSE, L := 32, OKM := [156, 11, 20, 251, 100, 227, 163, 161, 30, 45, 242, 2, 248, 246, 44, 11, 88, 132, 189, 175, 95, 96, 61, 44, 98, 160, 212, 136, 140, 222, 57, 151])

  method {:test} ExpectInternalTestVectors()
  {
    for i: int := 0 to |rawTestVectors| {
      ExpectRawDeriveTestVector(rawTestVectors[i]);
    }
    for i: int := 0 to |testVectors| {
      ExpectTestVector(testVectors[i]);
    }
  }

  method ExpectRawDeriveTestVector(vector: InternalTestVector)
    decreases vector
  {
    var InternalTestVector(name, hash, IKM, info, L, OKM) := vector;
    print name + ""\n"";
    expect |IKM| == 32 && L == 32 && 4 + |info| < INT32_MAX_LIMIT, ""expectation violation""
    TestKDF.KdfRawDeriveTest(IKM, info, L, OKM);
  }

  method ExpectTestVector(vector: TestVector)
    decreases vector
  {
    var TestVector(name, hash, IKM, info, purpose, L, OKM) := vector;
    print name + ""\n"";
    TestKDF.KdfTest(Primitives.Types.KdfCtrInput(digestAlgorithm := hash, ikm := IKM, expectedLength := L, purpose := Some(purpose), nonce := Some(info)), OKM);
  }
}

module TestHKDF_Rfc5869TestVectors {

  import Primitives = Aws.Cryptography.Primitives

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened TestAwsCryptographyPrimitivesHKDF
  datatype RFCTestVector = RFCTestVector(nameonly name: string, nameonly hash: Primitives.Types.DigestAlgorithm, nameonly IKM: seq<uint8>, nameonly salt: seq<uint8>, nameonly info: seq<uint8>, nameonly L: Primitives.Types.PositiveInteger, nameonly PRK: seq<uint8>, nameonly OKM: seq<uint8>)

  const testVectors: seq<RFCTestVector> := [a1, a2, a3]
  const a1 := RFCTestVector(name := ""A.1.  Test Case 1"", hash := Primitives.Types.SHA_256, IKM := [11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11], salt := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], info := [240, 241, 242, 243, 244, 245, 246, 247, 248, 249], L := 42 as int32, PRK := [7, 119, 9, 54, 44, 46, 50, 223, 13, 220, 63, 13, 196, 123, 186, 99, 144, 182, 199, 59, 181, 15, 156, 49, 34, 236, 132, 74, 215, 194, 179, 229], OKM := [60, 178, 95, 37, 250, 172, 213, 122, 144, 67, 79, 100, 208, 54, 47, 42, 45, 45, 10, 144, 207, 26, 90, 76, 93, 176, 45, 86, 236, 196, 197, 191, 52, 0, 114, 8, 213, 184, 135, 24, 88, 101])
  const {:vcs_split_on_every_assert} a2 := RFCTestVector(name := ""A.2.  Test Case 2"", hash := Primitives.Types.SHA_256, IKM := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79], salt := [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175], info := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255], L := 82 as int32, PRK := [6, 166, 184, 140, 88, 83, 54, 26, 6, 16, 76, 156, 235, 53, 180, 92, 239, 118, 0, 20, 144, 70, 113, 1, 74, 25, 63, 64, 193, 95, 194, 68], OKM := [177, 30, 57, 141, 200, 3, 39, 161, 200, 231, 247, 140, 89, 106, 73, 52, 79, 1, 46, 218, 45, 78, 250, 216, 160, 80, 204, 76, 25, 175, 169, 124, 89, 4, 90, 153, 202, 199, 130, 114, 113, 203, 65, 198, 94, 89, 14, 9, 218, 50, 117, 96, 12, 47, 9, 184, 54, 119, 147, 169, 172, 163, 219, 113, 204, 48, 197, 129, 121, 236, 62, 135, 193, 76, 1, 213, 193, 243, 67, 79, 29, 135])
  const a3 := RFCTestVector(name := ""A.3.  Test Case 3"", hash := Primitives.Types.SHA_256, IKM := [11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11], salt := [], info := [], L := 42 as int32, PRK := [25, 239, 36, 163, 44, 113, 123, 22, 127, 51, 169, 29, 111, 100, 139, 223, 150, 89, 103, 118, 175, 219, 99, 119, 172, 67, 76, 28, 41, 60, 203, 4], OKM := [141, 164, 231, 117, 165, 99, 193, 143, 113, 95, 128, 42, 6, 60, 90, 49, 184, 161, 31, 92, 94, 225, 135, 158, 195, 69, 78, 95, 60, 115, 141, 45, 157, 32, 19, 149, 250, 164, 182, 26, 150, 200])

  method {:test} ExpectRFCTestVectors()
  {
    for i: int := 0 to |testVectors| {
      ExpectTestVector(testVectors[i]);
    }
  }

  method ExpectTestVector(vector: RFCTestVector)
    decreases vector
  {
    var RFCTestVector(name, hash, IKM, salt, info, L, PRK, OKM) := vector;
    print name + ""\n"";
    BasicExtractTest(Primitives.Types.HkdfExtractInput(digestAlgorithm := hash, salt := if |salt| > 0 then Some(salt) else None, ikm := IKM), PRK);
    BasicExpandTest(Primitives.Types.HkdfExpandInput(digestAlgorithm := hash, prk := PRK, info := info, expectedLength := L), OKM);
    BasicHkdfTest(Primitives.Types.HkdfInput(digestAlgorithm := hash, salt := if |salt| > 0 then Some(salt) else None, ikm := IKM, info := info, expectedLength := L), OKM);
  }
}

module TestAwsCryptographyPrimitivesHKDF {

  import Primitives = Aws.Cryptography.Primitives

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Digest
  method {:test} TestCase1()
  {
    var hash := Primitives.Types.SHA_256;
    var IKM := [11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11];
    var salt := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
    var info := [240, 241, 242, 243, 244, 245, 246, 247, 248, 249];
    var L := 42;
    var PRK := [7, 119, 9, 54, 44, 46, 50, 223, 13, 220, 63, 13, 196, 123, 186, 99, 144, 182, 199, 59, 181, 15, 156, 49, 34, 236, 132, 74, 215, 194, 179, 229];
    var OKM := [60, 178, 95, 37, 250, 172, 213, 122, 144, 67, 79, 100, 208, 54, 47, 42, 45, 45, 10, 144, 207, 26, 90, 76, 93, 176, 45, 86, 236, 196, 197, 191, 52, 0, 114, 8, 213, 184, 135, 24, 88, 101];
    BasicExtractTest(Primitives.Types.HkdfExtractInput(digestAlgorithm := hash, salt := Some(salt), ikm := IKM), PRK);
    BasicExpandTest(Primitives.Types.HkdfExpandInput(digestAlgorithm := hash, prk := PRK, info := info, expectedLength := L), OKM);
    BasicHkdfTest(Primitives.Types.HkdfInput(digestAlgorithm := hash, salt := Some(salt), ikm := IKM, info := info, expectedLength := L), OKM);
  }

  method BasicExtractTest(input: Primitives.Types.HkdfExtractInput, expectedPRK: seq<uint8>)
    decreases input, expectedPRK
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.HkdfExtract(input);
    expect |output| == Digest.Length(input.digestAlgorithm), ""expectation violation""
    expect output == expectedPRK, ""expectation violation""
  }

  method BasicExpandTest(input: Primitives.Types.HkdfExpandInput, expectedOKM: seq<uint8>)
    decreases input, expectedOKM
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.HkdfExpand(input);
    expect |output| == input.expectedLength as nat, ""expectation violation""
    expect output == expectedOKM, ""expectation violation""
  }

  method BasicHkdfTest(input: Primitives.Types.HkdfInput, expectedOKM: seq<uint8>)
    decreases input, expectedOKM
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.Hkdf(input);
    expect |output| == input.expectedLength as nat, ""expectation violation""
    expect output == expectedOKM, ""expectation violation""
  }
}

module ConstantTimeTest {

  import ConstantTime
  method {:test} ConstantTimeTest()
  {
    expect ConstantTime.Equals([], []), ""expectation violation""
    expect ConstantTime.Equals([1], [1]), ""expectation violation""
    expect !ConstantTime.Equals([1], [2]), ""expectation violation""
    expect ConstantTime.Equals([1, 2, 3], [1, 2, 3]), ""expectation violation""
    expect !ConstantTime.Equals([2, 2, 3], [1, 2, 3]), ""expectation violation""
    expect !ConstantTime.Equals([1, 2, 3], [1, 2, 4]), ""expectation violation""
  }
}

module ConstantTime {

  import opened UInt = StandardLibrary.UInt
  function method {:tailrecursion} Compare(a: seq<uint8>, b: seq<uint8>, acc: bv8 := 0): bv8
    requires |a| == |b|
    decreases a, b, acc
  {
    if |a| == 0 then
      acc
    else
      var x: bv8 := a[0] as bv8 ^ b[0] as bv8; Compare(a[1..], b[1..], x | acc)
  }

  predicate method Equals(a: seq<uint8>, b: seq<uint8>)
    requires |a| == |b|
    decreases a, b
  {
    Compare(a, b) == 0
  }
}

module TestAwsCryptographyPrimitivesGenerateRandomBytes {

  import Primitives = Aws.Cryptography.Primitives

  import opened UInt = StandardLibrary.UInt
  method {:test} BasicGenerateRandomBytes()
  {
    var client :- expect Primitives.AtomicPrimitives();
    var length := 5 as int32;
    var input := Primitives.Types.GenerateRandomBytesInput(length := length);
    var output := client.GenerateRandomBytes(input);
    var value :- expect output;
    expect |value| == length as int, ""expectation violation""
  }
}

module TestSignature {

  import Primitives = Aws.Cryptography.Primitives

  import opened UInt = StandardLibrary.UInt

  import Types = Aws.Cryptography.Primitives.Types

  import UTF8

  import opened Wrappers

  import Signature
  const P256: Types.ECDSASignatureAlgorithm := Types.ECDSASignatureAlgorithm.ECDSA_P256
  const P384: Types.ECDSASignatureAlgorithm := Types.ECDSASignatureAlgorithm.ECDSA_P384

  method RequireGoodKeyLengths(alg: Types.ECDSASignatureAlgorithm, sigKeyPair: Signature.SignatureKeyPair)
    decreases alg, sigKeyPair
  {
    expect |sigKeyPair.verificationKey| == Signature.FieldSize(alg), ""expectation violation""
  }

  method YCompression(alg: Types.ECDSASignatureAlgorithm, fieldSize: nat)
    decreases alg, fieldSize
  {
    var res :- expect Signature.ExternKeyGen(alg);
    RequireGoodKeyLengths(alg, res);
    var public, secret := res.verificationKey, res.signingKey;
    expect 0 < |secret|, ""expectation violation""
    expect |public| == 1 + (fieldSize + 7) / 8, ""expectation violation""
    expect public[0] == 2 || public[0] == 3, ""expectation violation""
  }

  method VerifyMessage(alg: Types.ECDSASignatureAlgorithm)
    decreases alg
  {
    var message :- expect UTF8.Encode(""Hello, World!"");
    var genInput := Types.GenerateECDSASignatureKeyInput(signatureAlgorithm := alg);
    var keys :- expect Signature.ExternKeyGen(alg);
    RequireGoodKeyLengths(alg, keys);
    var signature :- expect Signature.Sign(alg, keys.signingKey, message);
    var shouldBeTrue :- expect Signature.Verify(alg, keys.verificationKey, message, signature);
    expect shouldBeTrue, ""expectation violation""
    var shouldBeFalse :- expect Signature.Verify(alg, keys.verificationKey, message + [1], signature);
    expect !shouldBeFalse, ""expectation violation""
  }

  method {:test} YCompression384()
  {
    YCompression(P384, 384);
  }

  method {:test} YCompression256()
  {
    YCompression(P256, 256);
  }

  method {:test} VerifyMessage384()
  {
    VerifyMessage(P384);
  }

  method {:test} VerifyMessage256()
  {
    VerifyMessage(P256);
  }
}

module Aws {

  module Cryptography {

      }
}

module JSON {

  
  
  
  
  
  
  
  module Utils {

    
    
    
    
    
    
    module Views {

      
          }
  }

  module ZeroCopy {

    
    
      }

  module ConcreteSyntax {

    
      }
}
")]

namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System
namespace Aws_mCryptography_Compile {

} // end of namespace Aws_mCryptography_Compile
namespace Aws_Compile {

} // end of namespace Aws_Compile
namespace AesKdfCtr {

} // end of namespace AesKdfCtr
namespace TestAwsCryptographyPrimitivesAesKdfCtr_Compile {

  public partial class __default {
    public static void AesKdfCtrTests()
    {
      Dafny.ISequence<byte> _0_key;
      _0_key = Dafny.Sequence<byte>.FromElements((byte)(138), (byte)(39), (byte)(30), (byte)(72), (byte)(206), (byte)(182), (byte)(214), (byte)(144), (byte)(245), (byte)(34), (byte)(28), (byte)(219), (byte)(204), (byte)(175), (byte)(198), (byte)(23), (byte)(132), (byte)(234), (byte)(125), (byte)(246), (byte)(130), (byte)(54), (byte)(251), (byte)(60), (byte)(137), (byte)(120), (byte)(166), (byte)(245), (byte)(0), (byte)(150), (byte)(79), (byte)(107));
      Dafny.ISequence<byte> _1_nonce;
      _1_nonce = Dafny.Sequence<byte>.FromElements((byte)(66), (byte)(32), (byte)(73), (byte)(11), (byte)(207), (byte)(79), (byte)(97), (byte)(80), (byte)(11), (byte)(22), (byte)(236), (byte)(247), (byte)(42), (byte)(6), (byte)(222), (byte)(165));
      Dafny.ISequence<byte> _2_goal;
      _2_goal = Dafny.Sequence<byte>.FromElements((byte)(143), (byte)(128), (byte)(174), (byte)(191), (byte)(9), (byte)(171), (byte)(140), (byte)(22), (byte)(40), (byte)(143), (byte)(11), (byte)(239), (byte)(249), (byte)(101), (byte)(61), (byte)(120), (byte)(176), (byte)(23), (byte)(233), (byte)(210), (byte)(125), (byte)(72), (byte)(114), (byte)(70), (byte)(209), (byte)(170), (byte)(206), (byte)(96), (byte)(24), (byte)(112), (byte)(215), (byte)(169), (byte)(100), (byte)(136), (byte)(162), (byte)(231), (byte)(208), (byte)(24), (byte)(135), (byte)(121), (byte)(223), (byte)(13), (byte)(239), (byte)(180));
      Dafny.ISequence<byte> _3_result;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _4_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      _4_valueOrError0 = AesKdfCtr.__default.AesKdfCtrStream(_1_nonce, _0_key, 44U);
      if (!(!((_4_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAesKdfCtr.dfy(18,15): " + _4_valueOrError0);}
      _3_result = (_4_valueOrError0).Extract();
      if (!((new BigInteger((_3_result).Count)) == (new BigInteger(44)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAesKdfCtr.dfy(19,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_2_goal).Equals(_3_result))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAesKdfCtr.dfy(20,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _0_key = Dafny.Sequence<byte>.FromElements((byte)(212), (byte)(191), (byte)(10), (byte)(32), (byte)(13), (byte)(55), (byte)(22), (byte)(101), (byte)(189), (byte)(182), (byte)(186), (byte)(119), (byte)(202), (byte)(16), (byte)(175), (byte)(49), (byte)(103), (byte)(82), (byte)(87), (byte)(190), (byte)(13), (byte)(142), (byte)(103), (byte)(201), (byte)(98), (byte)(84), (byte)(228), (byte)(47), (byte)(142), (byte)(96), (byte)(61), (byte)(167));
      _1_nonce = Dafny.Sequence<byte>.FromElements((byte)(135), (byte)(1), (byte)(132), (byte)(66), (byte)(198), (byte)(216), (byte)(26), (byte)(105), (byte)(47), (byte)(97), (byte)(246), (byte)(192), (byte)(186), (byte)(187), (byte)(54), (byte)(129));
      _2_goal = Dafny.Sequence<byte>.FromElements((byte)(11), (byte)(154), (byte)(37), (byte)(42), (byte)(116), (byte)(143), (byte)(238), (byte)(68), (byte)(62), (byte)(135), (byte)(225), (byte)(71), (byte)(98), (byte)(224), (byte)(135), (byte)(18));
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _5_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      _5_valueOrError1 = AesKdfCtr.__default.AesKdfCtrStream(_1_nonce, _0_key, 16U);
      if (!(!((_5_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAesKdfCtr.dfy(25,11): " + _5_valueOrError1);}
      _3_result = (_5_valueOrError1).Extract();
      if (!((new BigInteger((_3_result).Count)) == (new BigInteger(16)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAesKdfCtr.dfy(26,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_2_goal).Equals(_3_result))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAesKdfCtr.dfy(27,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _0_key = Dafny.Sequence<byte>.FromElements((byte)(106), (byte)(72), (byte)(42), (byte)(47), (byte)(58), (byte)(213), (byte)(111), (byte)(196), (byte)(126), (byte)(37), (byte)(46), (byte)(203), (byte)(150), (byte)(153), (byte)(188), (byte)(53), (byte)(32), (byte)(194), (byte)(159), (byte)(196), (byte)(221), (byte)(90), (byte)(124), (byte)(70), (byte)(45), (byte)(252), (byte)(99), (byte)(98), (byte)(42), (byte)(68), (byte)(94), (byte)(19));
      _1_nonce = Dafny.Sequence<byte>.FromElements((byte)(13), (byte)(247), (byte)(32), (byte)(159), (byte)(220), (byte)(254), (byte)(69), (byte)(218), (byte)(42), (byte)(110), (byte)(159), (byte)(42), (byte)(209), (byte)(244), (byte)(79), (byte)(232));
      _2_goal = Dafny.Sequence<byte>.FromElements((byte)(150), (byte)(218), (byte)(139), (byte)(126), (byte)(166), (byte)(233), (byte)(178), (byte)(123), (byte)(229), (byte)(210), (byte)(40), (byte)(218), (byte)(141), (byte)(26), (byte)(127), (byte)(208), (byte)(124), (byte)(197), (byte)(212), (byte)(69), (byte)(251), (byte)(71), (byte)(73), (byte)(90), (byte)(47), (byte)(134), (byte)(46), (byte)(7), (byte)(215), (byte)(208), (byte)(194), (byte)(180), (byte)(174), (byte)(110), (byte)(1), (byte)(57), (byte)(16), (byte)(37), (byte)(16), (byte)(235), (byte)(93), (byte)(138), (byte)(25), (byte)(180), (byte)(85), (byte)(16), (byte)(229), (byte)(165), (byte)(238), (byte)(36), (byte)(56), (byte)(131), (byte)(247), (byte)(31), (byte)(64), (byte)(23), (byte)(249), (byte)(67), (byte)(153), (byte)(94), (byte)(23), (byte)(243), (byte)(69), (byte)(11));
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _6_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      _6_valueOrError2 = AesKdfCtr.__default.AesKdfCtrStream(_1_nonce, _0_key, 64U);
      if (!(!((_6_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAesKdfCtr.dfy(32,11): " + _6_valueOrError2);}
      _3_result = (_6_valueOrError2).Extract();
      if (!((new BigInteger((_3_result).Count)) == (new BigInteger(64)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAesKdfCtr.dfy(33,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_2_goal).Equals(_3_result))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAesKdfCtr.dfy(34,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestAwsCryptographyPrimitivesAesKdfCtr_Compile
namespace TestAwsCryptographyPrimitivesHMacDigest_Compile {

  public partial class __default {
    public static void DigestTests()
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _7_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _8_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out0;
      _out0 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _8_valueOrError0 = _out0;
      if (!(!((_8_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestHMAC.dfy(14,15): " + _8_valueOrError0);}
      _7_client = (_8_valueOrError0).Extract();
      TestAwsCryptographyPrimitivesHMacDigest_Compile.__default.HmacSHA__256(_7_client);
      TestAwsCryptographyPrimitivesHMacDigest_Compile.__default.HmacSHA__384(_7_client);
      TestAwsCryptographyPrimitivesHMacDigest_Compile.__default.HmacSHA__512(_7_client);
    }
    public static void HmacSHA__256(software.amazon.cryptography.primitives.internaldafny.types.IAwsCryptographicPrimitivesClient client)
    {
      _System._ITuple0 _9___v0;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.primitives.internaldafny.types._IError> _10_valueOrError0 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _10_valueOrError0 = TestAwsCryptographyPrimitivesHMacDigest_Compile.__default.BasicHMacTest(client, software.amazon.cryptography.primitives.internaldafny.types.HMacInput.create(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(1), (byte)(1), (byte)(1)), Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102))), Dafny.Sequence<byte>.FromElements((byte)(93), (byte)(12), (byte)(86), (byte)(145), (byte)(123), (byte)(239), (byte)(169), (byte)(72), (byte)(195), (byte)(226), (byte)(204), (byte)(179), (byte)(103), (byte)(94), (byte)(195), (byte)(83), (byte)(134), (byte)(128), (byte)(226), (byte)(185), (byte)(184), (byte)(203), (byte)(98), (byte)(100), (byte)(115), (byte)(32), (byte)(7), (byte)(44), (byte)(172), (byte)(11), (byte)(81), (byte)(16)));
      if (!(!((_10_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestHMAC.dfy(26,10): " + _10_valueOrError0);}
      _9___v0 = (_10_valueOrError0).Extract();
    }
    public static void HmacSHA__384(software.amazon.cryptography.primitives.internaldafny.types.IAwsCryptographicPrimitivesClient client)
    {
      _System._ITuple0 _11___v1;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.primitives.internaldafny.types._IError> _12_valueOrError0 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _12_valueOrError0 = TestAwsCryptographyPrimitivesHMacDigest_Compile.__default.BasicHMacTest(client, software.amazon.cryptography.primitives.internaldafny.types.HMacInput.create(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__384(), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(1), (byte)(1), (byte)(1)), Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102))), Dafny.Sequence<byte>.FromElements((byte)(219), (byte)(44), (byte)(51), (byte)(60), (byte)(217), (byte)(57), (byte)(186), (byte)(208), (byte)(8), (byte)(69), (byte)(115), (byte)(185), (byte)(190), (byte)(136), (byte)(136), (byte)(1), (byte)(69), (byte)(143), (byte)(151), (byte)(148), (byte)(7), (byte)(66), (byte)(149), (byte)(193), (byte)(16), (byte)(225), (byte)(51), (byte)(85), (byte)(92), (byte)(176), (byte)(139), (byte)(249), (byte)(56), (byte)(93), (byte)(189), (byte)(11), (byte)(150), (byte)(21), (byte)(135), (byte)(54), (byte)(153), (byte)(37), (byte)(76), (byte)(68), (byte)(70), (byte)(77), (byte)(154), (byte)(124)));
      if (!(!((_12_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestHMAC.dfy(47,10): " + _12_valueOrError0);}
      _11___v1 = (_12_valueOrError0).Extract();
    }
    public static void HmacSHA__512(software.amazon.cryptography.primitives.internaldafny.types.IAwsCryptographicPrimitivesClient client)
    {
      _System._ITuple0 _13___v2;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.primitives.internaldafny.types._IError> _14_valueOrError0 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _14_valueOrError0 = TestAwsCryptographyPrimitivesHMacDigest_Compile.__default.BasicHMacTest(client, software.amazon.cryptography.primitives.internaldafny.types.HMacInput.create(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__512(), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(1), (byte)(1), (byte)(1)), Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102))), Dafny.Sequence<byte>.FromElements((byte)(49), (byte)(213), (byte)(21), (byte)(219), (byte)(23), (byte)(169), (byte)(195), (byte)(39), (byte)(177), (byte)(1), (byte)(15), (byte)(162), (byte)(233), (byte)(182), (byte)(208), (byte)(84), (byte)(226), (byte)(3), (byte)(27), (byte)(120), (byte)(75), (byte)(78), (byte)(85), (byte)(46), (byte)(220), (byte)(5), (byte)(166), (byte)(206), (byte)(79), (byte)(47), (byte)(25), (byte)(94), (byte)(88), (byte)(119), (byte)(211), (byte)(192), (byte)(148), (byte)(23), (byte)(252), (byte)(155), (byte)(98), (byte)(218), (byte)(97), (byte)(225), (byte)(38), (byte)(93), (byte)(83), (byte)(113), (byte)(139), (byte)(95), (byte)(101), (byte)(222), (byte)(154), (byte)(98), (byte)(244), (byte)(206), (byte)(88), (byte)(229), (byte)(6), (byte)(115), (byte)(226), (byte)(188), (byte)(152), (byte)(173)));
      if (!(!((_14_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestHMAC.dfy(69,10): " + _14_valueOrError0);}
      _13___v2 = (_14_valueOrError0).Extract();
    }
    public static Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.primitives.internaldafny.types._IError> BasicHMacTest(software.amazon.cryptography.primitives.internaldafny.types.IAwsCryptographicPrimitivesClient client, software.amazon.cryptography.primitives.internaldafny.types._IHMacInput input, Dafny.ISequence<byte> expectedDigest)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _15_valueOrError0 = (client).HMac(input);
      if ((_15_valueOrError0).IsFailure()) {
        return (_15_valueOrError0).PropagateFailure<_System._ITuple0>();
      } else {
        Dafny.ISequence<byte> _16_output = (_15_valueOrError0).Extract();
        Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _17_valueOrError1 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((new BigInteger((_16_output).Count)) == (Digest_Compile.__default.Length((input).dtor_digestAlgorithm)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Error")));
        if ((_17_valueOrError1).IsFailure()) {
          return (_17_valueOrError1).PropagateFailure<_System._ITuple0>();
        } else {
          Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _18_valueOrError2 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((_16_output).Equals(expectedDigest), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Error")));
          if ((_18_valueOrError2).IsFailure()) {
            return (_18_valueOrError2).PropagateFailure<_System._ITuple0>();
          } else {
            return Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(_System.Tuple0.create());
          }
        }
      }
    }
  }
} // end of namespace TestAwsCryptographyPrimitivesHMacDigest_Compile
namespace TestAwsCryptographyPrimitivesDigest_Compile {

  public partial class __default {
    public static void DigestTests()
    {
      TestAwsCryptographyPrimitivesDigest_Compile.__default.BasicDigestTest(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102)), Dafny.Sequence<byte>.FromElements((byte)(240), (byte)(228), (byte)(194), (byte)(247), (byte)(108), (byte)(88), (byte)(145), (byte)(110), (byte)(194), (byte)(88), (byte)(242), (byte)(70), (byte)(133), (byte)(27), (byte)(234), (byte)(9), (byte)(29), (byte)(20), (byte)(212), (byte)(36), (byte)(122), (byte)(47), (byte)(195), (byte)(225), (byte)(134), (byte)(148), (byte)(70), (byte)(27), (byte)(24), (byte)(22), (byte)(225), (byte)(59)));
      TestAwsCryptographyPrimitivesDigest_Compile.__default.BasicDigestTest(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__384(), Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102)), Dafny.Sequence<byte>.FromElements((byte)(166), (byte)(158), (byte)(125), (byte)(243), (byte)(11), (byte)(36), (byte)(192), (byte)(66), (byte)(236), (byte)(84), (byte)(12), (byte)(203), (byte)(189), (byte)(191), (byte)(177), (byte)(86), (byte)(44), (byte)(133), (byte)(120), (byte)(112), (byte)(56), (byte)(200), (byte)(133), (byte)(116), (byte)(156), (byte)(30), (byte)(64), (byte)(142), (byte)(45), (byte)(98), (byte)(250), (byte)(54), (byte)(100), (byte)(44), (byte)(208), (byte)(7), (byte)(95), (byte)(163), (byte)(81), (byte)(232), (byte)(34), (byte)(226), (byte)(184), (byte)(165), (byte)(145), (byte)(57), (byte)(205), (byte)(157)));
      TestAwsCryptographyPrimitivesDigest_Compile.__default.BasicDigestTest(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__512(), Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102)), Dafny.Sequence<byte>.FromElements((byte)(64), (byte)(27), (byte)(9), (byte)(234), (byte)(179), (byte)(192), (byte)(19), (byte)(212), (byte)(202), (byte)(84), (byte)(146), (byte)(43), (byte)(184), (byte)(2), (byte)(190), (byte)(200), (byte)(253), (byte)(83), (byte)(24), (byte)(25), (byte)(43), (byte)(10), (byte)(117), (byte)(242), (byte)(1), (byte)(216), (byte)(179), (byte)(114), (byte)(116), (byte)(41), (byte)(8), (byte)(15), (byte)(179), (byte)(55), (byte)(89), (byte)(26), (byte)(189), (byte)(62), (byte)(68), (byte)(69), (byte)(59), (byte)(149), (byte)(69), (byte)(85), (byte)(183), (byte)(160), (byte)(129), (byte)(46), (byte)(16), (byte)(129), (byte)(195), (byte)(155), (byte)(116), (byte)(2), (byte)(147), (byte)(247), (byte)(101), (byte)(234), (byte)(231), (byte)(49), (byte)(245), (byte)(166), (byte)(94), (byte)(209)));
    }
    public static void BasicDigestTest(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> message, Dafny.ISequence<byte> expectedDigest)
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _19_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _20_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out1;
      _out1 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _20_valueOrError0 = _out1;
      if (!(!((_20_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestDigest.dfy(61,15): " + _20_valueOrError0);}
      _19_client = (_20_valueOrError0).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IDigestInput _21_input;
      _21_input = software.amazon.cryptography.primitives.internaldafny.types.DigestInput.create(digestAlgorithm, message);
      Dafny.ISequence<byte> _22_output;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _23_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out2;
      _out2 = (_19_client).Digest(_21_input);
      _23_valueOrError1 = _out2;
      if (!(!((_23_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestDigest.dfy(68,15): " + _23_valueOrError1);}
      _22_output = (_23_valueOrError1).Extract();
      if (!((new BigInteger((_22_output).Count)) == (Digest_Compile.__default.Length(digestAlgorithm)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestDigest.dfy(69,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_22_output).Equals(expectedDigest))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestDigest.dfy(70,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestAwsCryptographyPrimitivesDigest_Compile
namespace TestAwsCryptographyPrimitivesHMAC_Compile {

  public partial class __default {
    public static void HMACTests()
    {
      TestAwsCryptographyPrimitivesHMAC_Compile.__default.BasicHMACTest(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(2), (byte)(3), (byte)(4)), Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102)), Dafny.Sequence<byte>.FromElements((byte)(55), (byte)(107), (byte)(186), (byte)(241), (byte)(51), (byte)(255), (byte)(154), (byte)(169), (byte)(106), (byte)(133), (byte)(2), (byte)(248), (byte)(54), (byte)(230), (byte)(193), (byte)(147), (byte)(212), (byte)(179), (byte)(154), (byte)(66), (byte)(43), (byte)(52), (byte)(108), (byte)(181), (byte)(144), (byte)(152), (byte)(19), (byte)(101), (byte)(117), (byte)(99), (byte)(204), (byte)(134)));
      TestAwsCryptographyPrimitivesHMAC_Compile.__default.BasicHMACTest(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__384(), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(2), (byte)(3), (byte)(4)), Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102)), Dafny.Sequence<byte>.FromElements((byte)(90), (byte)(206), (byte)(234), (byte)(81), (byte)(173), (byte)(76), (byte)(235), (byte)(148), (byte)(203), (byte)(139), (byte)(195), (byte)(46), (byte)(251), (byte)(14), (byte)(97), (byte)(110), (byte)(146), (byte)(49), (byte)(147), (byte)(24), (byte)(240), (byte)(1), (byte)(17), (byte)(231), (byte)(58), (byte)(104), (byte)(146), (byte)(53), (byte)(144), (byte)(167), (byte)(11), (byte)(112), (byte)(7), (byte)(39), (byte)(122), (byte)(15), (byte)(58), (byte)(53), (byte)(144), (byte)(91), (byte)(16), (byte)(223), (byte)(51), (byte)(98), (byte)(30), (byte)(88), (byte)(23), (byte)(166)));
      TestAwsCryptographyPrimitivesHMAC_Compile.__default.BasicHMACTest(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__512(), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(2), (byte)(3), (byte)(4)), Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102)), Dafny.Sequence<byte>.FromElements((byte)(100), (byte)(23), (byte)(173), (byte)(215), (byte)(39), (byte)(67), (byte)(51), (byte)(165), (byte)(149), (byte)(53), (byte)(87), (byte)(84), (byte)(145), (byte)(58), (byte)(221), (byte)(155), (byte)(239), (byte)(182), (byte)(249), (byte)(134), (byte)(147), (byte)(191), (byte)(143), (byte)(224), (byte)(140), (byte)(165), (byte)(190), (byte)(221), (byte)(183), (byte)(15), (byte)(6), (byte)(102), (byte)(203), (byte)(77), (byte)(238), (byte)(64), (byte)(10), (byte)(138), (byte)(61), (byte)(64), (byte)(219), (byte)(79), (byte)(248), (byte)(249), (byte)(90), (byte)(102), (byte)(217), (byte)(188), (byte)(13), (byte)(2), (byte)(101), (byte)(96), (byte)(217), (byte)(242), (byte)(73), (byte)(254), (byte)(190), (byte)(217), (byte)(134), (byte)(33), (byte)(163), (byte)(137), (byte)(151), (byte)(183)));
    }
    public static void BasicHMACTest(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> key, Dafny.ISequence<byte> message, Dafny.ISequence<byte> expectedDigest)
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _24_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _25_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out3;
      _out3 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _25_valueOrError0 = _out3;
      if (!(!((_25_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHMAC.dfy(66,15): " + _25_valueOrError0);}
      _24_client = (_25_valueOrError0).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IHMacInput _26_input;
      _26_input = software.amazon.cryptography.primitives.internaldafny.types.HMacInput.create(digestAlgorithm, key, message);
      Dafny.ISequence<byte> _27_output;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _28_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      _28_valueOrError1 = (_24_client).HMac(_26_input);
      if (!(!((_28_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHMAC.dfy(74,15): " + _28_valueOrError1);}
      _27_output = (_28_valueOrError1).Extract();
      if (!((new BigInteger((_27_output).Count)) == (Digest_Compile.__default.Length(digestAlgorithm)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHMAC.dfy(75,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_27_output).Equals(expectedDigest))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHMAC.dfy(76,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestAwsCryptographyPrimitivesHMAC_Compile
namespace TestAwsCryptographyPrimitivesAES_Compile {

  public partial class __default {
    public static void AESDecryptTests()
    {
      TestAwsCryptographyPrimitivesAES_Compile.__default.BasicAESDecryptTest(software.amazon.cryptography.primitives.internaldafny.types.AESDecryptInput.create(software.amazon.cryptography.primitives.internaldafny.types.AES__GCM.create((int)(32), (int)(16), (int)(12)), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1)), Dafny.Sequence<byte>.FromElements((byte)(102), (byte)(165), (byte)(173), (byte)(47)), Dafny.Sequence<byte>.FromElements((byte)(54), (byte)(200), (byte)(18), (byte)(56), (byte)(172), (byte)(194), (byte)(174), (byte)(23), (byte)(239), (byte)(151), (byte)(47), (byte)(180), (byte)(143), (byte)(232), (byte)(142), (byte)(184)), Dafny.Sequence<byte>.FromElements((byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2)), Dafny.Sequence<byte>.FromElements((byte)(3), (byte)(3), (byte)(3), (byte)(3))), Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102)));
    }
    public static void AESEncryptTests()
    {
      TestAwsCryptographyPrimitivesAES_Compile.__default.BasicAESEncryptTest(software.amazon.cryptography.primitives.internaldafny.types.AESEncryptInput.create(software.amazon.cryptography.primitives.internaldafny.types.AES__GCM.create((int)(32), (int)(16), (int)(12)), Dafny.Sequence<byte>.FromElements((byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2), (byte)(2)), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1), (byte)(1)), Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102)), Dafny.Sequence<byte>.FromElements((byte)(3), (byte)(3), (byte)(3), (byte)(3))));
    }
    public static void BasicAESDecryptTest(software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput input, Dafny.ISequence<byte> expectedOutput)
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _29_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _30_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out4;
      _out4 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _30_valueOrError0 = _out4;
      if (!(!((_30_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAES.dfy(99,15): " + _30_valueOrError0);}
      _29_client = (_30_valueOrError0).Extract();
      Dafny.ISequence<byte> _31_output;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _32_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out5;
      _out5 = (_29_client).AESDecrypt(input);
      _32_valueOrError1 = _out5;
      if (!(!((_32_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAES.dfy(100,15): " + _32_valueOrError1);}
      _31_output = (_32_valueOrError1).Extract();
      if (!((_31_output).Equals(expectedOutput))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAES.dfy(101,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void BasicAESEncryptTest(software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput input)
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _33_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _34_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out6;
      _out6 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _34_valueOrError0 = _out6;
      if (!(!((_34_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAES.dfy(108,15): " + _34_valueOrError0);}
      _33_client = (_34_valueOrError0).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput _35_output;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _36_valueOrError1 = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _out7;
      _out7 = (_33_client).AESEncrypt(input);
      _36_valueOrError1 = _out7;
      if (!(!((_36_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAES.dfy(109,15): " + _36_valueOrError1);}
      _35_output = (_36_valueOrError1).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput _37_decryptInput;
      _37_decryptInput = software.amazon.cryptography.primitives.internaldafny.types.AESDecryptInput.create((input).dtor_encAlg, (input).dtor_key, (_35_output).dtor_cipherText, (_35_output).dtor_authTag, (input).dtor_iv, (input).dtor_aad);
      TestAwsCryptographyPrimitivesAES_Compile.__default.BasicAESDecryptTest(_37_decryptInput, (input).dtor_msg);
    }
  }
} // end of namespace TestAwsCryptographyPrimitivesAES_Compile
namespace TestAwsCryptographyPrimitivesRSA_Compile {

  public partial class __default {
    public static void RSAEncryptTests()
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _38_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _39_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out8;
      _out8 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _39_valueOrError0 = _out8;
      if (!(!((_39_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(51,15): " + _39_valueOrError0);}
      _38_client = (_39_valueOrError0).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _40_keys;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _out9;
      _out9 = (_38_client).GenerateRSAKeyPair(software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairInput.create((int)(2048)));
      _40_keys = _out9;
      if (!((_40_keys).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(53,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      TestAwsCryptographyPrimitivesRSA_Compile.__default.BasicRSAEncryptTest(software.amazon.cryptography.primitives.internaldafny.types.RSAEncryptInput.create(software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.create_OAEP__SHA256(), (((_40_keys).dtor_value).dtor_publicKey).dtor_pem, Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102))), (_40_keys).dtor_value);
    }
    public static void GetRSAKeyModulusLength()
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _41_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _42_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out10;
      _out10 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _42_valueOrError0 = _out10;
      if (!(!((_42_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(67,15): " + _42_valueOrError0);}
      _41_client = (_42_valueOrError0).Extract();
      Dafny.ISequence<byte> _43_publicKey2048;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _44_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _44_valueOrError1 = UTF8.__default.Encode(TestAwsCryptographyPrimitivesRSA_Compile.__default.RSA__PUBLIC__2048);
      if (!(!((_44_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(71,22): " + _44_valueOrError1);}
      _43_publicKey2048 = (_44_valueOrError1).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput _45_length2048;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _46_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      _46_valueOrError2 = (_41_client).GetRSAKeyModulusLength(software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthInput.create(_43_publicKey2048));
      if (!(!((_46_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(72,19): " + _46_valueOrError2);}
      _45_length2048 = (_46_valueOrError2).Extract();
      if (!(((_45_length2048).dtor_length) == (2048))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(74,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<byte> _47_publicKey3072;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _48_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _48_valueOrError3 = UTF8.__default.Encode(TestAwsCryptographyPrimitivesRSA_Compile.__default.RSA__PUBLIC__3072);
      if (!(!((_48_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(77,22): " + _48_valueOrError3);}
      _47_publicKey3072 = (_48_valueOrError3).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput _49_length3072;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _50_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      _50_valueOrError4 = (_41_client).GetRSAKeyModulusLength(software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthInput.create(_47_publicKey3072));
      if (!(!((_50_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(78,19): " + _50_valueOrError4);}
      _49_length3072 = (_50_valueOrError4).Extract();
      if (!(((_49_length3072).dtor_length) == (3072))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(80,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<byte> _51_publicKey4096;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _52_valueOrError5 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _52_valueOrError5 = UTF8.__default.Encode(TestAwsCryptographyPrimitivesRSA_Compile.__default.RSA__PUBLIC__4096);
      if (!(!((_52_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(83,22): " + _52_valueOrError5);}
      _51_publicKey4096 = (_52_valueOrError5).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput _53_length4096;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _54_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      _54_valueOrError6 = (_41_client).GetRSAKeyModulusLength(software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthInput.create(_51_publicKey4096));
      if (!(!((_54_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(84,19): " + _54_valueOrError6);}
      _53_length4096 = (_54_valueOrError6).Extract();
      if (!(((_53_length4096).dtor_length) == (4096))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(86,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void BasicRSADecryptTests(software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput input, Dafny.ISequence<byte> expectedOutput)
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _55_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _56_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out11;
      _out11 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _56_valueOrError0 = _out11;
      if (!(!((_56_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(94,15): " + _56_valueOrError0);}
      _55_client = (_56_valueOrError0).Extract();
      Dafny.ISequence<byte> _57_output;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _58_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out12;
      _out12 = (_55_client).RSADecrypt(input);
      _58_valueOrError1 = _out12;
      if (!(!((_58_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(95,15): " + _58_valueOrError1);}
      _57_output = (_58_valueOrError1).Extract();
      if (!((_57_output).Equals(expectedOutput))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(97,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void BasicRSAEncryptTest(software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput input, software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput keypair)
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _59_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _60_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out13;
      _out13 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _60_valueOrError0 = _out13;
      if (!(!((_60_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(106,15): " + _60_valueOrError0);}
      _59_client = (_60_valueOrError0).Extract();
      Dafny.ISequence<byte> _61_output;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _62_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out14;
      _out14 = (_59_client).RSAEncrypt(input);
      _62_valueOrError1 = _out14;
      if (!(!((_62_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(107,15): " + _62_valueOrError1);}
      _61_output = (_62_valueOrError1).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput _63_decryptInput;
      _63_decryptInput = software.amazon.cryptography.primitives.internaldafny.types.RSADecryptInput.create((input).dtor_padding, ((keypair).dtor_privateKey).dtor_pem, _61_output);
      TestAwsCryptographyPrimitivesRSA_Compile.__default.BasicRSADecryptTests(_63_decryptInput, (input).dtor_plaintext);
    }
    public static void TestingPemParsingInRSAEncryptionForRSAKeyPairStoredInPEM()
    {
      Dafny.ISet<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode> _64_allPadding;
      _64_allPadding = ((System.Func<Dafny.ISet<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>>)(() => {
        var _coll0 = new System.Collections.Generic.List<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>();
        foreach (software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode _compr_0 in software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.AllSingletonConstructors) {
          software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode _65_p = (software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode)_compr_0;
          if (true) {
            _coll0.Add(_65_p);
          }
        }
        return Dafny.Set<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>.FromCollection(_coll0);
      }))();
      Dafny.ISequence<byte> _66_PublicKeyFromGenerateRSAKeyPairPemBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _67_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _67_valueOrError0 = UTF8.__default.Encode(TestAwsCryptographyPrimitivesRSA_Compile.__default.StaticPublicKeyFromGenerateRSAKeyPair());
      if (!(!((_67_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(121,48): " + _67_valueOrError0);}
      _66_PublicKeyFromGenerateRSAKeyPairPemBytes = (_67_valueOrError0).Extract();
      Dafny.ISequence<byte> _68_PrivateKeyFromGenerateRSAKeyPairPemBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _69_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _69_valueOrError1 = UTF8.__default.Encode(TestAwsCryptographyPrimitivesRSA_Compile.__default.StaticPrivateKeyFromGenerateRSAKeyPair());
      if (!(!((_69_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(122,49): " + _69_valueOrError1);}
      _68_PrivateKeyFromGenerateRSAKeyPairPemBytes = (_69_valueOrError1).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _70_KeyFromGenerateRSAKeyPair;
      _70_KeyFromGenerateRSAKeyPair = software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairOutput.create(software.amazon.cryptography.primitives.internaldafny.types.RSAPublicKey.create(2048, _66_PublicKeyFromGenerateRSAKeyPairPemBytes), software.amazon.cryptography.primitives.internaldafny.types.RSAPrivateKey.create(2048, _68_PrivateKeyFromGenerateRSAKeyPairPemBytes));
      while (!(_64_allPadding).Equals(Dafny.Set<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>.FromElements())) {
        software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode _71_padding;
        foreach (software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode _assign_such_that_0 in (_64_allPadding).Elements) {
          _71_padding = (software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode)_assign_such_that_0;
          if ((_64_allPadding).Contains(_71_padding)) {
            goto after__ASSIGN_SUCH_THAT_0;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 136)");
      after__ASSIGN_SUCH_THAT_0: ;
        TestAwsCryptographyPrimitivesRSA_Compile.__default.BasicRSAEncryptTest(software.amazon.cryptography.primitives.internaldafny.types.RSAEncryptInput.create(_71_padding, ((_70_KeyFromGenerateRSAKeyPair).dtor_publicKey).dtor_pem, Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102))), _70_KeyFromGenerateRSAKeyPair);
        _64_allPadding = Dafny.Set<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>.Difference(_64_allPadding, Dafny.Set<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>.FromElements(_71_padding));
      }
    }
    public static void TestingPemParsingInRSAEncryptionForOnlyRSAPrivateKeyStoredInPEM()
    {
      Dafny.ISet<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode> _72_allPadding;
      _72_allPadding = ((System.Func<Dafny.ISet<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>>)(() => {
        var _coll1 = new System.Collections.Generic.List<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>();
        foreach (software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode _compr_1 in software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.AllSingletonConstructors) {
          software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode _73_p = (software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode)_compr_1;
          if (true) {
            _coll1.Add(_73_p);
          }
        }
        return Dafny.Set<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>.FromCollection(_coll1);
      }))();
      Dafny.ISequence<byte> _74_PublicKeyFromTestVectorsPemBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _75_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _75_valueOrError0 = UTF8.__default.Encode(TestAwsCryptographyPrimitivesRSA_Compile.__default.StaticPublicKeyFromTestVectors());
      if (!(!((_75_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(154,41): " + _75_valueOrError0);}
      _74_PublicKeyFromTestVectorsPemBytes = (_75_valueOrError0).Extract();
      Dafny.ISequence<byte> _76_PrivateKeyFromTestVectorsPemBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _77_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _77_valueOrError1 = UTF8.__default.Encode(TestAwsCryptographyPrimitivesRSA_Compile.__default.StaticPrivateKeyFromTestVectors());
      if (!(!((_77_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestRSA.dfy(155,42): " + _77_valueOrError1);}
      _76_PrivateKeyFromTestVectorsPemBytes = (_77_valueOrError1).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _78_KeyFromTestVectorsPair;
      _78_KeyFromTestVectorsPair = software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairOutput.create(software.amazon.cryptography.primitives.internaldafny.types.RSAPublicKey.create(4096, _74_PublicKeyFromTestVectorsPemBytes), software.amazon.cryptography.primitives.internaldafny.types.RSAPrivateKey.create(4096, _76_PrivateKeyFromTestVectorsPemBytes));
      while (!(_72_allPadding).Equals(Dafny.Set<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>.FromElements())) {
        software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode _79_padding;
        foreach (software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode _assign_such_that_1 in (_72_allPadding).Elements) {
          _79_padding = (software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode)_assign_such_that_1;
          if ((_72_allPadding).Contains(_79_padding)) {
            goto after__ASSIGN_SUCH_THAT_1;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 169)");
      after__ASSIGN_SUCH_THAT_1: ;
        TestAwsCryptographyPrimitivesRSA_Compile.__default.BasicRSAEncryptTest(software.amazon.cryptography.primitives.internaldafny.types.RSAEncryptInput.create(_79_padding, ((_78_KeyFromTestVectorsPair).dtor_publicKey).dtor_pem, Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102))), _78_KeyFromTestVectorsPair);
        _72_allPadding = Dafny.Set<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>.Difference(_72_allPadding, Dafny.Set<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>.FromElements(_79_padding));
      }
    }
    public static Dafny.ISequence<char> StaticPublicKeyFromGenerateRSAKeyPair() {
      return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("-----BEGIN PUBLIC KEY-----\n"), Dafny.Sequence<char>.FromString("MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEA0RbkftAm30eFm+o6JraW\n")), Dafny.Sequence<char>.FromString("AbWR+2grPfQk3i3w4eCsZHDQib6iUwX0MVADd2DjTnlkYa1DytDHRKfWHjtTniQ/\n")), Dafny.Sequence<char>.FromString("EdKbENIFC5mLgh1Max7n9nQ6bmo4EvH2s4pUr3YBSys/dXpRDUCD/Mt4G+qDE8DT\n")), Dafny.Sequence<char>.FromString("NSe8dqX5U44HwImQmKzvLYvD5gUY7eM5co4ZpfYrlRRVNkpv5qVNK7bz9KvQmKfP\n")), Dafny.Sequence<char>.FromString("bQfzyvOZgSqQyHKfxbCM6ByE8Dd0NoI1ALwBY8wCXn/+6q4xLWTywu4nGIXs5Vt7\n")), Dafny.Sequence<char>.FromString("vrMqwHSvYaNQKjUyPjsG3xPMwKruh30mGzc2KlKLZ+MiV+SNAiooqVkL6CxH4yJc\n")), Dafny.Sequence<char>.FromString("NwIDAQAB\n")), Dafny.Sequence<char>.FromString("-----END PUBLIC KEY-----\n"));
    }
    public static Dafny.ISequence<char> StaticPrivateKeyFromGenerateRSAKeyPair() {
      return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("-----BEGIN PRIVATE KEY-----\n"), Dafny.Sequence<char>.FromString("MIIEvgIBADANBgkqhkiG9w0BAQEFAASCBKgwggSkAgEAAoIBAQDRFuR+0CbfR4Wb\n")), Dafny.Sequence<char>.FromString("6jomtpYBtZH7aCs99CTeLfDh4KxkcNCJvqJTBfQxUAN3YONOeWRhrUPK0MdEp9Ye\n")), Dafny.Sequence<char>.FromString("O1OeJD8R0psQ0gULmYuCHUxrHuf2dDpuajgS8fazilSvdgFLKz91elENQIP8y3gb\n")), Dafny.Sequence<char>.FromString("6oMTwNM1J7x2pflTjgfAiZCYrO8ti8PmBRjt4zlyjhml9iuVFFU2Sm/mpU0rtvP0\n")), Dafny.Sequence<char>.FromString("q9CYp89tB/PK85mBKpDIcp/FsIzoHITwN3Q2gjUAvAFjzAJef/7qrjEtZPLC7icY\n")), Dafny.Sequence<char>.FromString("hezlW3u+syrAdK9ho1AqNTI+OwbfE8zAqu6HfSYbNzYqUotn4yJX5I0CKiipWQvo\n")), Dafny.Sequence<char>.FromString("LEfjIlw3AgMBAAECggEAWe7DTCpCtgHg3X2jEnixT73lsuGMy+KBoxDWjYkiDTea\n")), Dafny.Sequence<char>.FromString("8sxMrHIgpL86JnRFgMDk5MBuKsOfGhAooCs7XYdQm11fNh5nbiRWZZotftu1wQMg\n")), Dafny.Sequence<char>.FromString("CNLmGHv7dSD4KNoUV10cN+7rAsyvmKF5oWQ+idYD4labkNr1wTMTcYSZ7ZlgbNFr\n")), Dafny.Sequence<char>.FromString("ZFwsZizD4RrpwwyrpZ25f/H95p9fQrZXrB3Wt5aNn0uhTcQL0KfnvMamZNPfxj9b\n")), Dafny.Sequence<char>.FromString("j6CWpyXtFOMc8nuT4fKOh7q4A87UsduBBhdAk4m4m98WvlIZIUW89w3kzIfr9zCT\n")), Dafny.Sequence<char>.FromString("VxflBzeEDSM8+Sy1TJNRBBwhRnQ/gNLLD+e6/O/MTQKBgQD/vRxZvyJkWaRYkGeS\n")), Dafny.Sequence<char>.FromString("VVAZQJOSQUPpVC5U3y2ghV8Dm30BfMEtySdD9hXd635X7e0dvIqwxJAwFgJ+SYT2\n")), Dafny.Sequence<char>.FromString("NNE8wiIKolQH1h01cYK+kwAohB6vQPLymYwzc9HNcevCDFkt7VVRgnwUHk6BXz4T\n")), Dafny.Sequence<char>.FromString("LsF/jYTUdzCyFfjYWGTOEh7PkwKBgQDRTZSe2Tqua2Groi75tmXMAzI6jQsiBqTn\n")), Dafny.Sequence<char>.FromString("Jv0es+IMWZyh2yMy9x6numM7IBBamgt+6hNEKaUmQxoEFbo0dUsEx35RH2Pdkr8X\n")), Dafny.Sequence<char>.FromString("IuXuh3IdRgRCV9WxnecBD32Cci9qLN1aaVJHfdA2dW4LAb7m4/GeuiS/8ZatXEm2\n")), Dafny.Sequence<char>.FromString("Kf0YZAx/TQKBgEpbQtX5U9eXlMhHXEXY1kwxUXbx0PwThNEaftqwTJrw55y6GDTm\n")), Dafny.Sequence<char>.FromString("yqrg7ySyJu8L96hwvGZ/EGlazOjJGYa4fqnKzDkJT6NjpuR2F4yvkxk0qPNN0BWn\n")), Dafny.Sequence<char>.FromString("fXMsVrEEUYb/LiLDYc4sQUVcNnk5JwRO0OX0UM2xxg/RgaPtt4mPDTRPAoGBAJsY\n")), Dafny.Sequence<char>.FromString("1izv5CAjyniY8h5xHvYS2EGzCrDoI4J2zdLWkYd9UChQbsDxhnHcGHRTykqZJDOj\n")), Dafny.Sequence<char>.FromString("2SsFgS/dQYYNY7JDyJd+DQioLiSe/aNzZNdg3xr6K2XOGLhJvkh25han7qLLJCw/\n")), Dafny.Sequence<char>.FromString("J416mbQBSM43OPN3rjBk1560s2c7oBOxAa/1U51xAoGBAOYFMvdk6H359yaJGmsN\n")), Dafny.Sequence<char>.FromString("kY7lS6heh4cHfSM7Hw02lh/ovasdQm+afcnDWEW0XQYM6KQCcJiwbIK/kPkVsvJe\n")), Dafny.Sequence<char>.FromString("o6gynyWoHrrQuRdmffPvzT50paccJuupeHAtfOAue5y57FQUc4Xm4Qj3P7cQJr9z\n")), Dafny.Sequence<char>.FromString("UMCUAooEJcdmAUyVUy5BQc7P\n")), Dafny.Sequence<char>.FromString("-----END PRIVATE KEY-----\n"));
    }
    public static Dafny.ISequence<char> StaticPublicKeyFromTestVectors() {
      return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("-----BEGIN PUBLIC KEY-----\n"), Dafny.Sequence<char>.FromString("MIICIjANBgkqhkiG9w0BAQEFAAOCAg8AMIICCgKCAgEAs7RoNYEPAIws89VV+kra\n")), Dafny.Sequence<char>.FromString("rVv/4wbdmUAaAKWgWuxZi5na9GJSmnhCkqyLRm7wPbQY4LCoa5/IMUxkHLsYDPdu\n")), Dafny.Sequence<char>.FromString("udY0Qm0GcoxOlvJKHYo4RjF7HyiS34D6dvyO4Gd3aq0mZHoxSGCxW/7hf03wEMzc\n")), Dafny.Sequence<char>.FromString("iVJXWHXhaI0lD6nrzIEgLrE4L+3V2LeAQjvZsTKd+bYMqeZOL2syiVVIAU8POwAG\n")), Dafny.Sequence<char>.FromString("GVBroJoveFm/SUp6lCiN0M2kTeyQA2ax3QTtZSAa8nwrI7U52XOzVmdMicJsy2Pg\n")), Dafny.Sequence<char>.FromString("uW98te3MuODdK24yNkHIkYameP/Umf/SJshUJQd5a/TUp3XE+HhOWAumx22tIDlC\n")), Dafny.Sequence<char>.FromString("vZS11cuk2fp0WeHUnXaC19N5qWKfvHEKSugzty/z3lGP7ItFhrF2X1qJHeAAsL11\n")), Dafny.Sequence<char>.FromString("kjo6Lc48KsE1vKvbnW4VLyB3wdNiVvmUNO29tPXwaR0Q5Gbr3jk3nUzdkEHouHWQ\n")), Dafny.Sequence<char>.FromString("41lubOHCCBN3V13mh/MgtNhESHjfmmOnh54ErD9saA1d7CjTf8g2wqmjEqvGSW6N\n")), Dafny.Sequence<char>.FromString("q7zhcWR2tp1olflS7oHzul4/I3hnkfL6Kb2xAWWaQKvg3mtsY2OPlzFEP0tR5UcH\n")), Dafny.Sequence<char>.FromString("Pfp5CeS1Xzg7hN6vRICW6m4l3u2HJFld2akDMm1vnSz8RCbPW7jp7YBxUkWJmypM\n")), Dafny.Sequence<char>.FromString("tG7Yv2aGZXGbUtM8o1cZarECAwEAAQ==\n")), Dafny.Sequence<char>.FromString("-----END PUBLIC KEY-----"));
    }
    public static Dafny.ISequence<char> StaticPrivateKeyFromTestVectors() {
      return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("-----BEGIN PRIVATE KEY-----\n"), Dafny.Sequence<char>.FromString("MIIJQgIBADANBgkqhkiG9w0BAQEFAASCCSwwggkoAgEAAoICAQCztGg1gQ8AjCzz\n")), Dafny.Sequence<char>.FromString("1VX6StqtW//jBt2ZQBoApaBa7FmLmdr0YlKaeEKSrItGbvA9tBjgsKhrn8gxTGQc\n")), Dafny.Sequence<char>.FromString("uxgM92651jRCbQZyjE6W8kodijhGMXsfKJLfgPp2/I7gZ3dqrSZkejFIYLFb/uF/\n")), Dafny.Sequence<char>.FromString("TfAQzNyJUldYdeFojSUPqevMgSAusTgv7dXYt4BCO9mxMp35tgyp5k4vazKJVUgB\n")), Dafny.Sequence<char>.FromString("Tw87AAYZUGugmi94Wb9JSnqUKI3QzaRN7JADZrHdBO1lIBryfCsjtTnZc7NWZ0yJ\n")), Dafny.Sequence<char>.FromString("wmzLY+C5b3y17cy44N0rbjI2QciRhqZ4/9SZ/9ImyFQlB3lr9NSndcT4eE5YC6bH\n")), Dafny.Sequence<char>.FromString("ba0gOUK9lLXVy6TZ+nRZ4dSddoLX03mpYp+8cQpK6DO3L/PeUY/si0WGsXZfWokd\n")), Dafny.Sequence<char>.FromString("4ACwvXWSOjotzjwqwTW8q9udbhUvIHfB02JW+ZQ07b209fBpHRDkZuveOTedTN2Q\n")), Dafny.Sequence<char>.FromString("Qei4dZDjWW5s4cIIE3dXXeaH8yC02ERIeN+aY6eHngSsP2xoDV3sKNN/yDbCqaMS\n")), Dafny.Sequence<char>.FromString("q8ZJbo2rvOFxZHa2nWiV+VLugfO6Xj8jeGeR8vopvbEBZZpAq+Dea2xjY4+XMUQ/\n")), Dafny.Sequence<char>.FromString("S1HlRwc9+nkJ5LVfODuE3q9EgJbqbiXe7YckWV3ZqQMybW+dLPxEJs9buOntgHFS\n")), Dafny.Sequence<char>.FromString("RYmbKky0bti/ZoZlcZtS0zyjVxlqsQIDAQABAoICAEr3m/GWIXgNAkPGX9PGnmtr\n")), Dafny.Sequence<char>.FromString("0dgX6SIhh7d1YOwNZV3DlYAV9HfUa5Fcwc1kQny7QRWbHOepBI7sW2dQ9buTDXIh\n")), Dafny.Sequence<char>.FromString("VjPP37yxo6d89EZWfxtpUP+yoXL0D4jL257qCvtJuJZ6E00qaVMDhXbiQKABlo8C\n")), Dafny.Sequence<char>.FromString("9sVEiABhwXBDZsctpwtTiykTgv6hrrPy2+H8R8MAm0/VcBCAG9kG5r8FCEmIvQKa\n")), Dafny.Sequence<char>.FromString("dgvNxrfiWNZuZ6yfLmpJH54SbhG9Kb4WbCKfvh4ihqyi0btRdSM6fMeLgG9o/zrc\n")), Dafny.Sequence<char>.FromString("s54B0kHeLOYNVo0j7FQpZBFeSIbmHfln4RKBh7ntrTke/Ejbh3NbiPvxWSP0P067\n")), Dafny.Sequence<char>.FromString("SYWPkQpip2q0ION81wSQZ1haP2GewFFu4IEjG3DlqqpKKGLqXrmjMufnildVFpBx\n")), Dafny.Sequence<char>.FromString("ir+MgvgQfEBoGEx0aElyO7QuRYaEiXeb/BhMZeC5O65YhJrWSuTVizh3xgJWjgfV\n")), Dafny.Sequence<char>.FromString("aYwYgxN8SBXBhXLIVvnPhadTqsW1C/aevLOk110eSFWcHf+FCK781ykIzcpXoRGX\n")), Dafny.Sequence<char>.FromString("OwWcZzC/fmSABS0yH56ow+I0tjdLIEEMhoa4/kkamioHOJ4yyB+W1DO6/DnMyQlx\n")), Dafny.Sequence<char>.FromString("g7y2WsAaIEBoWUARy776k70xPPMtYAxzFXI9KhqRVrPfeaRZ+ojeyLyr3GQGyyoo\n")), Dafny.Sequence<char>.FromString("cuGRdMUblsmODv4ixmOxAoIBAQDvkznvVYNdP3Eg5vQeLm/qsP6dLejLijBLeq9i\n")), Dafny.Sequence<char>.FromString("7DZH2gRpKcflXZxCkRjsKDDE+fgDcBYEp2zYfRIVvgrxlTQZdaSG+GoDcbjbNQn3\n")), Dafny.Sequence<char>.FromString("djCCtOOACioN/vg2zFlX4Bs6Q+NaV7g5qP5SUaxUBjuHLe7Nc+ZkyheMHuNYVLvk\n")), Dafny.Sequence<char>.FromString("HL/IoWyANpZYjMUU3xMbL/J29Gz7CPGr8Si28TihAHGfcNgn8S04OQZhTX+bU805\n")), Dafny.Sequence<char>.FromString("/+7B4XW47Mthg/u7hlqFl+YIAaSJYvWkEaVP1A9I7Ve0aMDSMWwzTg9cle2uVaL3\n")), Dafny.Sequence<char>.FromString("+PTzWY5coBlHKjqAg9ufhYSDhAqBd/JOSlv8RwcA3PDXJ6C/AoIBAQDABmXXYQky\n")), Dafny.Sequence<char>.FromString("7phExXBvkLtJt2TBGjjwulf4R8TC6W5F51jJuoqY/mTqYcLcOn2nYGVwoFvPsy/Q\n")), Dafny.Sequence<char>.FromString("CTjfODwJBXzbloXtYFR3PWAeL1Y6+7Cm+koMWIPJyVbD5Fzm+gZStM0GwP8FhDt2\n")), Dafny.Sequence<char>.FromString("Wt8fWEyXmoLdAy6RAwiEmCagEh8o+13oBfwnBllbz7TxaErsUuR+XVgl/iHwztdv\n")), Dafny.Sequence<char>.FromString("cdJKyRgaFfWSh9aiO7EMV2rBGWsoX09SRvprPFAGx8Ffm7YcqIk34QXsQyc45Dyn\n")), Dafny.Sequence<char>.FromString("CwkvypxHoaB3ot/48FeFm9IubApb/ctv+EgkBfL4S4bdwRXS1rt+0+QihBoFyP2o\n")), Dafny.Sequence<char>.FromString("J91cdm4hEWCPAoIBAQC6l11hFaYZo0bWDGsHcr2B+dZkzxPoKznQH76n+jeQoLIc\n")), Dafny.Sequence<char>.FromString("wgjJkK4afm39yJOrZtEOxGaxu0CgIFFMk9ZsL/wC9EhvQt02z4TdXiLkFK5VrtMd\n")), Dafny.Sequence<char>.FromString("r0zv16y06VWQhqBOMf/KJlX6uq9RqADi9HO6pkC+zc0cpPXQEWKaMmygju+kMG2U\n")), Dafny.Sequence<char>.FromString("Mm/IieMZjWCRJTfgBCE5J88qTsqaKagkZXcZakdAXKwOhQN+F2EStiM6UCZB5PrO\n")), Dafny.Sequence<char>.FromString("S8dfrO8ML+ki8Zqck8L1qhiNb5zkXtKExy4u+gNr8khGcT6vqqoSxOoH3mPRgOfL\n")), Dafny.Sequence<char>.FromString("Jnppne8wlwIf7Vq3H8ka6zPSXEHma999gZcmy9t7AoIBAGbQhiLl79j3a0wXMvZp\n")), Dafny.Sequence<char>.FromString("Vf5IVYgXFDnAbG2hb7a06bhAAIgyexcjzsC4C2+DWdgOgwHkuoPg+062QV8zauGh\n")), Dafny.Sequence<char>.FromString("sJKaa6cHlvIpSJeg3NjD/nfJN3CYzCd0yCIm2Z9Ka6xI5iYhm+pGPNhIG4Na8deS\n")), Dafny.Sequence<char>.FromString("gVL46yv1pc/o73VxfoGg5UzgN3xlp97Cva0sHEGguHr4W8Qr59xZw3wGQ4SLW35M\n")), Dafny.Sequence<char>.FromString("F6qXVNKUh12GSMCPbZK2RXBWVKqqJmca+WzJoJ6DlsT2lQdFhXCus9L007xlDXxF\n")), Dafny.Sequence<char>.FromString("C/hCmw1dEl+VaNo2Ou26W/zdwTKYhNlxBwsg4SB8nPNxXIsmlBBY54froFhriNfn\n")), Dafny.Sequence<char>.FromString("x/0CggEAUzz+VMtjoEWw2HSHLOXrO4EmwJniNgiiwfX3DfZE4tMNZgqZwLkq67ns\n")), Dafny.Sequence<char>.FromString("T0n3b0XfAOOkLgMZrUoOxPHkxFeyLLf7pAEJe7QNB+Qilw8e2zVqtiJrRk6uDIGJ\n")), Dafny.Sequence<char>.FromString("Sv+yM52zkImZAe2jOdU3KeUZxSMmb5vIoiPBm+tb2WupAg3YdpKn1/jWTpVmV/+G\n")), Dafny.Sequence<char>.FromString("UtTLVE6YpAyFp1gMxhutE9vfIS94ek+vt03AoEOlltt6hqZfv3xmY8vGuAjlnj12\n")), Dafny.Sequence<char>.FromString("zHaq+fhCRPsbsZkzJ9nIVdXYnNIEGtMGNnxax7tYRej/UXqyazbxHiJ0iPF4PeDn\n")), Dafny.Sequence<char>.FromString("dzxtGxpeTBi+KhKlca8SlCdCqYwG6Q==\n")), Dafny.Sequence<char>.FromString("-----END PRIVATE KEY-----"));
    }
    public static Dafny.ISequence<char> RSA__PUBLIC__2048 { get {
      return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("-----BEGIN PUBLIC KEY-----\n"), Dafny.Sequence<char>.FromString("MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAqBvECLsPdF1J5DOkaA1n\n")), Dafny.Sequence<char>.FromString("UrGwNT9ard3KSMaPypla/5Jhz0veCz1OSjnx35+FE3q7omHQBmKRs6XDkj4tJ5vh\n")), Dafny.Sequence<char>.FromString("1baw2yzgIAqW9lOXK64GiYy0maH2NfRxGbj5LhVq5T4YOkKh9D3GFbfT9/NpcsOZ\n")), Dafny.Sequence<char>.FromString("M2HDX8Z+M0HM3XymtcfpHk5o6QF1lbBW+rDJEcYhPN0obBufCXaasgsBRP5Ei2b5\n")), Dafny.Sequence<char>.FromString("18xpy9M19By1yuC9mlNcpE5v5A8fq/qLLT4s34/6dnVxKX6gIoWDzDrUNrnPe0p5\n")), Dafny.Sequence<char>.FromString("pqZ1SHalrELMf/liXPrf94+0cF8g1fYVGGo+MZsG5/HRngLiskP25w5smMT51U1y\n")), Dafny.Sequence<char>.FromString("gQIDAQAB\n")), Dafny.Sequence<char>.FromString("-----END PUBLIC KEY-----"));
    } }
    public static Dafny.ISequence<char> RSA__PUBLIC__3072 { get {
      return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("-----BEGIN PUBLIC KEY-----\n"), Dafny.Sequence<char>.FromString("MIIBojANBgkqhkiG9w0BAQEFAAOCAY8AMIIBigKCAYEAnrUonUAKKpZE+LbQfq6I\n")), Dafny.Sequence<char>.FromString("gAR//GNnT7L6P3LCboXu44StJtvVyAmHZXPgdkxxT1EKLFx+Tys3B7jhgno9cs67\n")), Dafny.Sequence<char>.FromString("Scf0pLjJAmXOVHa6881oxi5zeP0e6+KzOPugg3C+EknS2PSHTLsdTrkgZU+oUjde\n")), Dafny.Sequence<char>.FromString("AgRSgmWrp8aMM1WpoLmNcWC/Pi0mSziVnIzE3WhkZ2Ccetz/viRL60VHlTwNQPVa\n")), Dafny.Sequence<char>.FromString("7fqbcSqBxm/VjDzYvDwzmU+4GNEs5hrA2IFDxxsYZAU8HdASQM18A8W7n0Okaa4e\n")), Dafny.Sequence<char>.FromString("c4svyKVFkncbNCqetynLU0A5ny7I5WVXV7DNi2VMjD/mZsEt8IrwfuWSMKuIPxs/\n")), Dafny.Sequence<char>.FromString("Nb/4Psr7ZvbKSlaMwEpyReHvYYqM7dd6A4Y9FirnrpAPaqlfm8UFtHKQvUckxRoR\n")), Dafny.Sequence<char>.FromString("05kzNN2jIRJtMwGpn+40tiei7eBGMmIn41/dnkM7GOJau4BarSJMiREK1yH9hh1C\n")), Dafny.Sequence<char>.FromString("GbrQu6i0F9G0uBDITen9/uPX9cxK5pNHAxeWzr2UP1UzAgMBAAE=\n")), Dafny.Sequence<char>.FromString("-----END PUBLIC KEY-----"));
    } }
    public static Dafny.ISequence<char> RSA__PUBLIC__4096 { get {
      return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("-----BEGIN PUBLIC KEY-----\n"), Dafny.Sequence<char>.FromString("MIICIjANBgkqhkiG9w0BAQEFAAOCAg8AMIICCgKCAgEAs86OIUN9RbdEdyQb2tGQ\n")), Dafny.Sequence<char>.FromString("miDmmeJaYKanLB0lfWiuO85kJK8edZyLkHIzps81qwgVSzbMCBB7QGcMyPbb3wbE\n")), Dafny.Sequence<char>.FromString("B4EJ32v3cuMVUs6sOvOYV4g1c1Hi1WVqnCeH+3RSFBfb7RL7SvSUmilX2tNV6uZy\n")), Dafny.Sequence<char>.FromString("BmMSGBJ/IMzxoHjKSFn6r1ttwov8X5DmNTyIp4qG3qyL1qhpla1bUE5Nb6uMHI2v\n")), Dafny.Sequence<char>.FromString("qMM+8zSPcRN40CfaQATxevNs/69++XJ+5L1nKU9fMwust1GEbtJ6cIBwAuqlyMm9\n")), Dafny.Sequence<char>.FromString("CnZ+tn56FEVPrUrsQX35QRNjbi0jjKI8ItkdyJ5fLixCjJ20tCo5jeL5KJ32Rjuw\n")), Dafny.Sequence<char>.FromString("BlB2KQrgdw5VEMrMlTJz9oozUv8GFzjtS4kx+tAsWhji5s0jry4QFYG01Q4ezVPb\n")), Dafny.Sequence<char>.FromString("TYdxg1Yz265EyLmF0+/ZQtO1kQc7tXHD5Gzzwyqot/UdJwlXStUGB2yEe62HQ2LT\n")), Dafny.Sequence<char>.FromString("9Ly3V7rUDJzO44zuFVjqchRPYWNdiYl8BVP/ak2bMtcowk06T9bo1tRf4HJWfpIM\n")), Dafny.Sequence<char>.FromString("GF27MXqykKHxcmOb0UfGIfI0eUtkid4gJdCxhidiILj6SHpEr+oa/Oogz01rVCdm\n")), Dafny.Sequence<char>.FromString("mbWmgFxmiKse8NXNQR+7qhMYX5GgdeSbp/Lg24HF9mvnd0S2wHkC86lGyQtvzrsd\n")), Dafny.Sequence<char>.FromString("DdUJZ2jqiKvMLdMKNFHFGGUCAwEAAQ==\n")), Dafny.Sequence<char>.FromString("-----END PUBLIC KEY-----"));
    } }
  }
} // end of namespace TestAwsCryptographyPrimitivesRSA_Compile
namespace TestKDF_Compile {

  public partial class __default {
    public static void KdfRawDeriveTest(Dafny.ISequence<byte> ikm, Dafny.ISequence<byte> info, int L, Dafny.ISequence<byte> expectedOKM)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _80_output;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out15;
      _out15 = KdfCtr_Compile.__default.RawDerive(ikm, info, L, 0);
      _80_output = _out15;
      if ((_80_output).is_Success) {
        if (!((new BigInteger(((_80_output).dtor_value).Count)) == (new BigInteger(L)))) {
          throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestKDF.dfy(30,6): " + Dafny.Sequence<char>.FromString("expectation violation"));}
        if (!(((_80_output).dtor_value).Equals(expectedOKM))) {
          throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestKDF.dfy(31,6): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      }
    }
    public static void KdfTest(software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput input, Dafny.ISequence<byte> expectedOKM)
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _81_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _82_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out16;
      _out16 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _82_valueOrError0 = _out16;
      if (!(!((_82_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestKDF.dfy(40,15): " + _82_valueOrError0);}
      _81_client = (_82_valueOrError0).Extract();
      Dafny.ISequence<byte> _83_output;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _84_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out17;
      _out17 = (_81_client).KdfCounterMode(input);
      _84_valueOrError1 = _out17;
      if (!(!((_84_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestKDF.dfy(42,15): " + _84_valueOrError1);}
      _83_output = (_84_valueOrError1).Extract();
      if (!((new BigInteger((_83_output).Count)) == (new BigInteger((input).dtor_expectedLength)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestKDF.dfy(43,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_83_output).Equals(expectedOKM))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestKDF.dfy(44,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestKDF_Compile
namespace TestKDFK__TestVectors_Compile {

  public interface _IInternalTestVector {
    bool is_InternalTestVector { get; }
    Dafny.ISequence<char> dtor_name { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_hash { get; }
    Dafny.ISequence<byte> dtor_IKM { get; }
    Dafny.ISequence<byte> dtor_info { get; }
    int dtor_L { get; }
    Dafny.ISequence<byte> dtor_OKM { get; }
    _IInternalTestVector DowncastClone();
  }
  public class InternalTestVector : _IInternalTestVector {
    public readonly Dafny.ISequence<char> _name;
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _hash;
    public readonly Dafny.ISequence<byte> _IKM;
    public readonly Dafny.ISequence<byte> _info;
    public readonly int _L;
    public readonly Dafny.ISequence<byte> _OKM;
    public InternalTestVector(Dafny.ISequence<char> name, software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm hash, Dafny.ISequence<byte> IKM, Dafny.ISequence<byte> info, int L, Dafny.ISequence<byte> OKM) {
      this._name = name;
      this._hash = hash;
      this._IKM = IKM;
      this._info = info;
      this._L = L;
      this._OKM = OKM;
    }
    public _IInternalTestVector DowncastClone() {
      if (this is _IInternalTestVector dt) { return dt; }
      return new InternalTestVector(_name, _hash, _IKM, _info, _L, _OKM);
    }
    public override bool Equals(object other) {
      var oth = other as TestKDFK__TestVectors_Compile.InternalTestVector;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._hash, oth._hash) && object.Equals(this._IKM, oth._IKM) && object.Equals(this._info, oth._info) && this._L == oth._L && object.Equals(this._OKM, oth._OKM);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hash));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._IKM));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._info));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._L));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._OKM));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestKDFK__TestVectors_Compile.InternalTestVector.InternalTestVector";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._hash);
      s += ", ";
      s += Dafny.Helpers.ToString(this._IKM);
      s += ", ";
      s += Dafny.Helpers.ToString(this._info);
      s += ", ";
      s += Dafny.Helpers.ToString(this._L);
      s += ", ";
      s += Dafny.Helpers.ToString(this._OKM);
      s += ")";
      return s;
    }
    private static readonly TestKDFK__TestVectors_Compile._IInternalTestVector theDefault = create(Dafny.Sequence<char>.Empty, software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, 0, Dafny.Sequence<byte>.Empty);
    public static TestKDFK__TestVectors_Compile._IInternalTestVector Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestKDFK__TestVectors_Compile._IInternalTestVector> _TYPE = new Dafny.TypeDescriptor<TestKDFK__TestVectors_Compile._IInternalTestVector>(TestKDFK__TestVectors_Compile.InternalTestVector.Default());
    public static Dafny.TypeDescriptor<TestKDFK__TestVectors_Compile._IInternalTestVector> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IInternalTestVector create(Dafny.ISequence<char> name, software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm hash, Dafny.ISequence<byte> IKM, Dafny.ISequence<byte> info, int L, Dafny.ISequence<byte> OKM) {
      return new InternalTestVector(name, hash, IKM, info, L, OKM);
    }
    public static _IInternalTestVector create_InternalTestVector(Dafny.ISequence<char> name, software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm hash, Dafny.ISequence<byte> IKM, Dafny.ISequence<byte> info, int L, Dafny.ISequence<byte> OKM) {
      return create(name, hash, IKM, info, L, OKM);
    }
    public bool is_InternalTestVector { get { return true; } }
    public Dafny.ISequence<char> dtor_name {
      get {
        return this._name;
      }
    }
    public software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_hash {
      get {
        return this._hash;
      }
    }
    public Dafny.ISequence<byte> dtor_IKM {
      get {
        return this._IKM;
      }
    }
    public Dafny.ISequence<byte> dtor_info {
      get {
        return this._info;
      }
    }
    public int dtor_L {
      get {
        return this._L;
      }
    }
    public Dafny.ISequence<byte> dtor_OKM {
      get {
        return this._OKM;
      }
    }
  }

  public interface _ITestVector {
    bool is_TestVector { get; }
    Dafny.ISequence<char> dtor_name { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_hash { get; }
    Dafny.ISequence<byte> dtor_IKM { get; }
    Dafny.ISequence<byte> dtor_info { get; }
    Dafny.ISequence<byte> dtor_purpose { get; }
    int dtor_L { get; }
    Dafny.ISequence<byte> dtor_OKM { get; }
    _ITestVector DowncastClone();
  }
  public class TestVector : _ITestVector {
    public readonly Dafny.ISequence<char> _name;
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _hash;
    public readonly Dafny.ISequence<byte> _IKM;
    public readonly Dafny.ISequence<byte> _info;
    public readonly Dafny.ISequence<byte> _purpose;
    public readonly int _L;
    public readonly Dafny.ISequence<byte> _OKM;
    public TestVector(Dafny.ISequence<char> name, software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm hash, Dafny.ISequence<byte> IKM, Dafny.ISequence<byte> info, Dafny.ISequence<byte> purpose, int L, Dafny.ISequence<byte> OKM) {
      this._name = name;
      this._hash = hash;
      this._IKM = IKM;
      this._info = info;
      this._purpose = purpose;
      this._L = L;
      this._OKM = OKM;
    }
    public _ITestVector DowncastClone() {
      if (this is _ITestVector dt) { return dt; }
      return new TestVector(_name, _hash, _IKM, _info, _purpose, _L, _OKM);
    }
    public override bool Equals(object other) {
      var oth = other as TestKDFK__TestVectors_Compile.TestVector;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._hash, oth._hash) && object.Equals(this._IKM, oth._IKM) && object.Equals(this._info, oth._info) && object.Equals(this._purpose, oth._purpose) && this._L == oth._L && object.Equals(this._OKM, oth._OKM);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hash));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._IKM));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._info));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._purpose));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._L));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._OKM));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestKDFK__TestVectors_Compile.TestVector.TestVector";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._hash);
      s += ", ";
      s += Dafny.Helpers.ToString(this._IKM);
      s += ", ";
      s += Dafny.Helpers.ToString(this._info);
      s += ", ";
      s += Dafny.Helpers.ToString(this._purpose);
      s += ", ";
      s += Dafny.Helpers.ToString(this._L);
      s += ", ";
      s += Dafny.Helpers.ToString(this._OKM);
      s += ")";
      return s;
    }
    private static readonly TestKDFK__TestVectors_Compile._ITestVector theDefault = create(Dafny.Sequence<char>.Empty, software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, 0, Dafny.Sequence<byte>.Empty);
    public static TestKDFK__TestVectors_Compile._ITestVector Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestKDFK__TestVectors_Compile._ITestVector> _TYPE = new Dafny.TypeDescriptor<TestKDFK__TestVectors_Compile._ITestVector>(TestKDFK__TestVectors_Compile.TestVector.Default());
    public static Dafny.TypeDescriptor<TestKDFK__TestVectors_Compile._ITestVector> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITestVector create(Dafny.ISequence<char> name, software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm hash, Dafny.ISequence<byte> IKM, Dafny.ISequence<byte> info, Dafny.ISequence<byte> purpose, int L, Dafny.ISequence<byte> OKM) {
      return new TestVector(name, hash, IKM, info, purpose, L, OKM);
    }
    public static _ITestVector create_TestVector(Dafny.ISequence<char> name, software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm hash, Dafny.ISequence<byte> IKM, Dafny.ISequence<byte> info, Dafny.ISequence<byte> purpose, int L, Dafny.ISequence<byte> OKM) {
      return create(name, hash, IKM, info, purpose, L, OKM);
    }
    public bool is_TestVector { get { return true; } }
    public Dafny.ISequence<char> dtor_name {
      get {
        return this._name;
      }
    }
    public software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_hash {
      get {
        return this._hash;
      }
    }
    public Dafny.ISequence<byte> dtor_IKM {
      get {
        return this._IKM;
      }
    }
    public Dafny.ISequence<byte> dtor_info {
      get {
        return this._info;
      }
    }
    public Dafny.ISequence<byte> dtor_purpose {
      get {
        return this._purpose;
      }
    }
    public int dtor_L {
      get {
        return this._L;
      }
    }
    public Dafny.ISequence<byte> dtor_OKM {
      get {
        return this._OKM;
      }
    }
  }

  public partial class __default {
    public static void ExpectInternalTestVectors()
    {
      BigInteger _hi0 = new BigInteger((TestKDFK__TestVectors_Compile.__default.rawTestVectors).Count);
      for (BigInteger _85_i = BigInteger.Zero; _85_i < _hi0; _85_i++) {
        TestKDFK__TestVectors_Compile.__default.ExpectRawDeriveTestVector((TestKDFK__TestVectors_Compile.__default.rawTestVectors).Select(_85_i));
      }
      BigInteger _hi1 = new BigInteger((TestKDFK__TestVectors_Compile.__default.testVectors).Count);
      for (BigInteger _86_i = BigInteger.Zero; _86_i < _hi1; _86_i++) {
        TestKDFK__TestVectors_Compile.__default.ExpectTestVector((TestKDFK__TestVectors_Compile.__default.testVectors).Select(_86_i));
      }
    }
    public static void ExpectRawDeriveTestVector(TestKDFK__TestVectors_Compile._IInternalTestVector vector)
    {
      TestKDFK__TestVectors_Compile._IInternalTestVector _let_tmp_rhs0 = vector;
      Dafny.ISequence<char> _87_name = _let_tmp_rhs0.dtor_name;
      software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _88_hash = _let_tmp_rhs0.dtor_hash;
      Dafny.ISequence<byte> _89_IKM = _let_tmp_rhs0.dtor_IKM;
      Dafny.ISequence<byte> _90_info = _let_tmp_rhs0.dtor_info;
      int _91_L = _let_tmp_rhs0.dtor_L;
      Dafny.ISequence<byte> _92_OKM = _let_tmp_rhs0.dtor_OKM;
      Dafny.Helpers.Print((Dafny.Sequence<char>.Concat(_87_name, Dafny.Sequence<char>.FromString("\n"))));
      if (!((((new BigInteger((_89_IKM).Count)) == (new BigInteger(32))) && ((_91_L) == (32))) && (((new BigInteger(4)) + (new BigInteger((_90_info).Count))) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestKDF_TestVectors.dfy(297,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      TestKDF_Compile.__default.KdfRawDeriveTest(_89_IKM, _90_info, _91_L, _92_OKM);
    }
    public static void ExpectTestVector(TestKDFK__TestVectors_Compile._ITestVector vector)
    {
      TestKDFK__TestVectors_Compile._ITestVector _let_tmp_rhs1 = vector;
      Dafny.ISequence<char> _93_name = _let_tmp_rhs1.dtor_name;
      software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _94_hash = _let_tmp_rhs1.dtor_hash;
      Dafny.ISequence<byte> _95_IKM = _let_tmp_rhs1.dtor_IKM;
      Dafny.ISequence<byte> _96_info = _let_tmp_rhs1.dtor_info;
      Dafny.ISequence<byte> _97_purpose = _let_tmp_rhs1.dtor_purpose;
      int _98_L = _let_tmp_rhs1.dtor_L;
      Dafny.ISequence<byte> _99_OKM = _let_tmp_rhs1.dtor_OKM;
      Dafny.Helpers.Print((Dafny.Sequence<char>.Concat(_93_name, Dafny.Sequence<char>.FromString("\n"))));
      TestKDF_Compile.__default.KdfTest(software.amazon.cryptography.primitives.internaldafny.types.KdfCtrInput.create(_94_hash, _95_IKM, _98_L, Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_97_purpose), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_96_info)), _99_OKM);
    }
    public static TestKDFK__TestVectors_Compile._IInternalTestVector b1 { get {
      return TestKDFK__TestVectors_Compile.InternalTestVector.create(Dafny.Sequence<char>.FromString("B.1  Test Case 1"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(226), (byte)(4), (byte)(214), (byte)(212), (byte)(102), (byte)(170), (byte)(213), (byte)(7), (byte)(255), (byte)(175), (byte)(109), (byte)(109), (byte)(171), (byte)(10), (byte)(91), (byte)(38), (byte)(21), (byte)(44), (byte)(158), (byte)(33), (byte)(231), (byte)(100), (byte)(55), (byte)(4), (byte)(100), (byte)(227), (byte)(96), (byte)(200), (byte)(251), (byte)(199), (byte)(101), (byte)(198)), Dafny.Sequence<byte>.FromElements((byte)(123), (byte)(3), (byte)(185), (byte)(141), (byte)(159), (byte)(148), (byte)(184), (byte)(153), (byte)(229), (byte)(145), (byte)(243), (byte)(239), (byte)(38), (byte)(75), (byte)(113), (byte)(177), (byte)(147), (byte)(251), (byte)(167), (byte)(4), (byte)(60), (byte)(126), (byte)(149), (byte)(60), (byte)(222), (byte)(35), (byte)(188), (byte)(83), (byte)(132), (byte)(188), (byte)(26), (byte)(98), (byte)(147), (byte)(88), (byte)(1), (byte)(21), (byte)(250), (byte)(227), (byte)(73), (byte)(95), (byte)(216), (byte)(69), (byte)(218), (byte)(219), (byte)(208), (byte)(43), (byte)(214), (byte)(69), (byte)(92), (byte)(244), (byte)(141), (byte)(15), (byte)(98), (byte)(179), (byte)(62), (byte)(98), (byte)(54), (byte)(74), (byte)(58), (byte)(128)), 32, Dafny.Sequence<byte>.FromElements((byte)(119), (byte)(13), (byte)(250), (byte)(182), (byte)(166), (byte)(164), (byte)(164), (byte)(190), (byte)(224), (byte)(37), (byte)(127), (byte)(243), (byte)(53), (byte)(33), (byte)(63), (byte)(120), (byte)(216), (byte)(40), (byte)(123), (byte)(79), (byte)(213), (byte)(55), (byte)(213), (byte)(193), (byte)(255), (byte)(250), (byte)(149), (byte)(105), (byte)(16), (byte)(231), (byte)(199), (byte)(121)));
    } }
    public static TestKDFK__TestVectors_Compile._IInternalTestVector b2 { get {
      return TestKDFK__TestVectors_Compile.InternalTestVector.create(Dafny.Sequence<char>.FromString("B.2  Test Case 2"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(174), (byte)(238), (byte)(202), (byte)(96), (byte)(246), (byte)(137), (byte)(164), (byte)(65), (byte)(177), (byte)(59), (byte)(12), (byte)(188), (byte)(212), (byte)(65), (byte)(216), (byte)(45), (byte)(240), (byte)(207), (byte)(135), (byte)(218), (byte)(194), (byte)(54), (byte)(41), (byte)(13), (byte)(236), (byte)(232), (byte)(147), (byte)(29), (byte)(248), (byte)(215), (byte)(3), (byte)(23)), Dafny.Sequence<byte>.FromElements((byte)(88), (byte)(142), (byte)(192), (byte)(65), (byte)(229), (byte)(115), (byte)(59), (byte)(112), (byte)(49), (byte)(33), (byte)(44), (byte)(85), (byte)(56), (byte)(239), (byte)(228), (byte)(246), (byte)(170), (byte)(250), (byte)(76), (byte)(218), (byte)(139), (byte)(146), (byte)(93), (byte)(38), (byte)(31), (byte)(90), (byte)(38), (byte)(136), (byte)(240), (byte)(7), (byte)(179), (byte)(172), (byte)(36), (byte)(14), (byte)(225), (byte)(41), (byte)(145), (byte)(231), (byte)(123), (byte)(140), (byte)(184), (byte)(83), (byte)(134), (byte)(120), (byte)(97), (byte)(89), (byte)(102), (byte)(22), (byte)(74), (byte)(129), (byte)(135), (byte)(43), (byte)(209), (byte)(207), (byte)(203), (byte)(251), (byte)(57), (byte)(164), (byte)(244), (byte)(80)), 32, Dafny.Sequence<byte>.FromElements((byte)(62), (byte)(129), (byte)(214), (byte)(17), (byte)(60), (byte)(238), (byte)(60), (byte)(82), (byte)(158), (byte)(206), (byte)(223), (byte)(248), (byte)(154), (byte)(105), (byte)(153), (byte)(206), (byte)(37), (byte)(182), (byte)(24), (byte)(193), (byte)(94), (byte)(225), (byte)(209), (byte)(157), (byte)(69), (byte)(203), (byte)(55), (byte)(106), (byte)(28), (byte)(142), (byte)(35), (byte)(116)));
    } }
    public static TestKDFK__TestVectors_Compile._IInternalTestVector b3 { get {
      return TestKDFK__TestVectors_Compile.InternalTestVector.create(Dafny.Sequence<char>.FromString("B.3  Test Case 3"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(149), (byte)(200), (byte)(247), (byte)(110), (byte)(17), (byte)(54), (byte)(126), (byte)(181), (byte)(85), (byte)(38), (byte)(162), (byte)(179), (byte)(147), (byte)(174), (byte)(144), (byte)(101), (byte)(131), (byte)(209), (byte)(203), (byte)(221), (byte)(71), (byte)(150), (byte)(33), (byte)(70), (byte)(245), (byte)(6), (byte)(204), (byte)(124), (byte)(172), (byte)(18), (byte)(244), (byte)(100)), Dafny.Sequence<byte>.FromElements((byte)(202), (byte)(214), (byte)(14), (byte)(144), (byte)(75), (byte)(158), (byte)(156), (byte)(139), (byte)(254), (byte)(180), (byte)(168), (byte)(26), (byte)(127), (byte)(103), (byte)(211), (byte)(189), (byte)(220), (byte)(192), (byte)(94), (byte)(100), (byte)(37), (byte)(88), (byte)(112), (byte)(64), (byte)(55), (byte)(112), (byte)(243), (byte)(83), (byte)(58), (byte)(230), (byte)(221), (byte)(99), (byte)(76), (byte)(234), (byte)(165), (byte)(108), (byte)(83), (byte)(230), (byte)(136), (byte)(189), (byte)(19), (byte)(122), (byte)(230), (byte)(1), (byte)(137), (byte)(53), (byte)(243), (byte)(75), (byte)(159), (byte)(176), (byte)(132), (byte)(234), (byte)(72), (byte)(228), (byte)(198), (byte)(136), (byte)(246), (byte)(187), (byte)(179), (byte)(136)), 32, Dafny.Sequence<byte>.FromElements((byte)(202), (byte)(250), (byte)(92), (byte)(160), (byte)(63), (byte)(95), (byte)(190), (byte)(42), (byte)(36), (byte)(32), (byte)(4), (byte)(171), (byte)(203), (byte)(211), (byte)(222), (byte)(16), (byte)(89), (byte)(199), (byte)(64), (byte)(123), (byte)(30), (byte)(229), (byte)(121), (byte)(37), (byte)(81), (byte)(36), (byte)(175), (byte)(24), (byte)(155), (byte)(224), (byte)(181), (byte)(86)));
    } }
    public static TestKDFK__TestVectors_Compile._IInternalTestVector b4 { get {
      return TestKDFK__TestVectors_Compile.InternalTestVector.create(Dafny.Sequence<char>.FromString("B.4  Test Case 4"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(77), (byte)(5), (byte)(57), (byte)(31), (byte)(214), (byte)(251), (byte)(30), (byte)(41), (byte)(46), (byte)(120), (byte)(171), (byte)(150), (byte)(25), (byte)(177), (byte)(183), (byte)(42), (byte)(125), (byte)(99), (byte)(238), (byte)(89), (byte)(215), (byte)(67), (byte)(93), (byte)(215), (byte)(24), (byte)(151), (byte)(185), (byte)(255), (byte)(126), (byte)(231), (byte)(174), (byte)(112)), Dafny.Sequence<byte>.FromElements((byte)(240), (byte)(120), (byte)(230), (byte)(249), (byte)(183), (byte)(248), (byte)(45), (byte)(100), (byte)(85), (byte)(79), (byte)(166), (byte)(182), (byte)(4), (byte)(200), (byte)(8), (byte)(241), (byte)(155), (byte)(31), (byte)(106), (byte)(214), (byte)(114), (byte)(125), (byte)(183), (byte)(170), (byte)(111), (byte)(28), (byte)(134), (byte)(105), (byte)(78), (byte)(16), (byte)(75), (byte)(82), (byte)(86), (byte)(200), (byte)(180), (byte)(3), (byte)(153), (byte)(25), (byte)(100), (byte)(100), (byte)(129), (byte)(215), (byte)(234), (byte)(36), (byte)(82), (byte)(199), (byte)(44), (byte)(23), (byte)(163), (byte)(232), (byte)(215), (byte)(211), (byte)(145), (byte)(98), (byte)(133), (byte)(70), (byte)(10), (byte)(165), (byte)(235), (byte)(129)), 32, Dafny.Sequence<byte>.FromElements((byte)(107), (byte)(22), (byte)(232), (byte)(245), (byte)(59), (byte)(131), (byte)(26), (byte)(165), (byte)(232), (byte)(107), (byte)(249), (byte)(122), (byte)(92), (byte)(79), (byte)(163), (byte)(125), (byte)(8), (byte)(155), (byte)(193), (byte)(114), (byte)(218), (byte)(90), (byte)(30), (byte)(127), (byte)(102), (byte)(45), (byte)(212), (byte)(165), (byte)(149), (byte)(51), (byte)(154), (byte)(183)));
    } }
    public static TestKDFK__TestVectors_Compile._IInternalTestVector b5 { get {
      return TestKDFK__TestVectors_Compile.InternalTestVector.create(Dafny.Sequence<char>.FromString("B.5  Test Case 5"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(15), (byte)(104), (byte)(168), (byte)(47), (byte)(241), (byte)(103), (byte)(22), (byte)(52), (byte)(204), (byte)(145), (byte)(54), (byte)(197), (byte)(100), (byte)(169), (byte)(224), (byte)(42), (byte)(118), (byte)(118), (byte)(33), (byte)(221), (byte)(116), (byte)(161), (byte)(191), (byte)(92), (byte)(36), (byte)(18), (byte)(155), (byte)(128), (byte)(130), (byte)(20), (byte)(183), (byte)(82)), Dafny.Sequence<byte>.FromElements((byte)(100), (byte)(133), (byte)(153), (byte)(128), (byte)(156), (byte)(44), (byte)(78), (byte)(124), (byte)(106), (byte)(94), (byte)(108), (byte)(68), (byte)(159), (byte)(0), (byte)(49), (byte)(235), (byte)(245), (byte)(92), (byte)(54), (byte)(97), (byte)(168), (byte)(149), (byte)(180), (byte)(77), (byte)(176), (byte)(87), (byte)(46), (byte)(232), (byte)(128), (byte)(131), (byte)(177), (byte)(244), (byte)(177), (byte)(38), (byte)(2), (byte)(170), (byte)(85), (byte)(252), (byte)(29), (byte)(241), (byte)(80), (byte)(166), (byte)(90), (byte)(109), (byte)(110), (byte)(237), (byte)(160), (byte)(170), (byte)(121), (byte)(164), (byte)(52), (byte)(161), (byte)(3), (byte)(155), (byte)(145), (byte)(181), (byte)(165), (byte)(143), (byte)(199), (byte)(241)), 32, Dafny.Sequence<byte>.FromElements((byte)(226), (byte)(151), (byte)(100), (byte)(15), (byte)(119), (byte)(104), (byte)(72), (byte)(93), (byte)(74), (byte)(110), (byte)(124), (byte)(254), (byte)(36), (byte)(95), (byte)(139), (byte)(250), (byte)(132), (byte)(112), (byte)(13), (byte)(153), (byte)(118), (byte)(38), (byte)(146), (byte)(234), (byte)(26), (byte)(66), (byte)(92), (byte)(204), (byte)(2), (byte)(117), (byte)(232), (byte)(245)));
    } }
    public static Dafny.ISequence<TestKDFK__TestVectors_Compile._IInternalTestVector> rawTestVectors { get {
      return Dafny.Sequence<TestKDFK__TestVectors_Compile._IInternalTestVector>.FromElements(TestKDFK__TestVectors_Compile.__default.b1, TestKDFK__TestVectors_Compile.__default.b2, TestKDFK__TestVectors_Compile.__default.b3, TestKDFK__TestVectors_Compile.__default.b4, TestKDFK__TestVectors_Compile.__default.b5);
    } }
    public static Dafny.ISequence<byte> PURPOSE { get {
      return UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("aws-kms-hierarchy"));
    } }
    public static TestKDFK__TestVectors_Compile._ITestVector c1 { get {
      return TestKDFK__TestVectors_Compile.TestVector.create(Dafny.Sequence<char>.FromString("C.1 Test Case 1"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(125), (byte)(201), (byte)(189), (byte)(252), (byte)(37), (byte)(52), (byte)(4), (byte)(124), (byte)(254), (byte)(99), (byte)(233), (byte)(235), (byte)(41), (byte)(123), (byte)(119), (byte)(82), (byte)(81), (byte)(73), (byte)(237), (byte)(125), (byte)(74), (byte)(252), (byte)(233), (byte)(198), (byte)(68), (byte)(15), (byte)(53), (byte)(14), (byte)(97), (byte)(239), (byte)(62), (byte)(208)), Dafny.Sequence<byte>.FromElements((byte)(119), (byte)(218), (byte)(233), (byte)(62), (byte)(104), (byte)(155), (byte)(88), (byte)(29), (byte)(62), (byte)(6), (byte)(235), (byte)(1), (byte)(200), (byte)(211), (byte)(186), (byte)(2)), TestKDFK__TestVectors_Compile.__default.PURPOSE, 32, Dafny.Sequence<byte>.FromElements((byte)(188), (byte)(232), (byte)(152), (byte)(114), (byte)(85), (byte)(137), (byte)(174), (byte)(192), (byte)(143), (byte)(152), (byte)(52), (byte)(179), (byte)(184), (byte)(15), (byte)(220), (byte)(63), (byte)(241), (byte)(115), (byte)(144), (byte)(126), (byte)(85), (byte)(116), (byte)(231), (byte)(41), (byte)(253), (byte)(206), (byte)(18), (byte)(124), (byte)(247), (byte)(109), (byte)(183), (byte)(204)));
    } }
    public static TestKDFK__TestVectors_Compile._ITestVector c2 { get {
      return TestKDFK__TestVectors_Compile.TestVector.create(Dafny.Sequence<char>.FromString("C.2 Test Case 2"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(80), (byte)(22), (byte)(113), (byte)(23), (byte)(118), (byte)(68), (byte)(10), (byte)(32), (byte)(75), (byte)(169), (byte)(199), (byte)(192), (byte)(255), (byte)(220), (byte)(214), (byte)(60), (byte)(182), (byte)(1), (byte)(126), (byte)(147), (byte)(171), (byte)(233), (byte)(110), (byte)(177), (byte)(35), (byte)(145), (byte)(217), (byte)(129), (byte)(30), (byte)(9), (byte)(80), (byte)(159)), Dafny.Sequence<byte>.FromElements((byte)(210), (byte)(241), (byte)(192), (byte)(158), (byte)(103), (byte)(66), (byte)(27), (byte)(35), (byte)(143), (byte)(66), (byte)(168), (byte)(189), (byte)(82), (byte)(171), (byte)(211), (byte)(252)), TestKDFK__TestVectors_Compile.__default.PURPOSE, 32, Dafny.Sequence<byte>.FromElements((byte)(54), (byte)(206), (byte)(174), (byte)(72), (byte)(237), (byte)(133), (byte)(85), (byte)(156), (byte)(93), (byte)(53), (byte)(120), (byte)(152), (byte)(118), (byte)(82), (byte)(89), (byte)(33), (byte)(114), (byte)(98), (byte)(204), (byte)(236), (byte)(138), (byte)(57), (byte)(162), (byte)(118), (byte)(85), (byte)(92), (byte)(199), (byte)(232), (byte)(240), (byte)(252), (byte)(92), (byte)(97)));
    } }
    public static TestKDFK__TestVectors_Compile._ITestVector c3 { get {
      return TestKDFK__TestVectors_Compile.TestVector.create(Dafny.Sequence<char>.FromString("C.3 Test Case 3"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(57), (byte)(90), (byte)(16), (byte)(46), (byte)(83), (byte)(54), (byte)(189), (byte)(241), (byte)(27), (byte)(242), (byte)(237), (byte)(236), (byte)(246), (byte)(66), (byte)(54), (byte)(226), (byte)(74), (byte)(112), (byte)(79), (byte)(156), (byte)(208), (byte)(13), (byte)(148), (byte)(71), (byte)(117), (byte)(211), (byte)(139), (byte)(57), (byte)(73), (byte)(69), (byte)(122), (byte)(236)), Dafny.Sequence<byte>.FromElements((byte)(51), (byte)(15), (byte)(183), (byte)(124), (byte)(82), (byte)(229), (byte)(249), (byte)(86), (byte)(117), (byte)(148), (byte)(237), (byte)(162), (byte)(27), (byte)(243), (byte)(173), (byte)(108)), TestKDFK__TestVectors_Compile.__default.PURPOSE, 32, Dafny.Sequence<byte>.FromElements((byte)(22), (byte)(55), (byte)(236), (byte)(141), (byte)(159), (byte)(163), (byte)(250), (byte)(236), (byte)(86), (byte)(47), (byte)(225), (byte)(103), (byte)(156), (byte)(225), (byte)(228), (byte)(146), (byte)(166), (byte)(45), (byte)(244), (byte)(39), (byte)(136), (byte)(163), (byte)(205), (byte)(200), (byte)(116), (byte)(193), (byte)(20), (byte)(147), (byte)(112), (byte)(254), (byte)(210), (byte)(194)));
    } }
    public static TestKDFK__TestVectors_Compile._ITestVector c4 { get {
      return TestKDFK__TestVectors_Compile.TestVector.create(Dafny.Sequence<char>.FromString("C.4 Test Case 4"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(152), (byte)(192), (byte)(25), (byte)(223), (byte)(239), (byte)(154), (byte)(175), (byte)(67), (byte)(237), (byte)(250), (byte)(184), (byte)(146), (byte)(228), (byte)(243), (byte)(227), (byte)(1), (byte)(128), (byte)(247), (byte)(228), (byte)(152), (byte)(142), (byte)(131), (byte)(149), (byte)(41), (byte)(60), (byte)(70), (byte)(244), (byte)(58), (byte)(166), (byte)(234), (byte)(86), (byte)(189)), Dafny.Sequence<byte>.FromElements((byte)(243), (byte)(160), (byte)(102), (byte)(127), (byte)(219), (byte)(137), (byte)(115), (byte)(38), (byte)(187), (byte)(216), (byte)(48), (byte)(80), (byte)(151), (byte)(168), (byte)(148), (byte)(71)), TestKDFK__TestVectors_Compile.__default.PURPOSE, 32, Dafny.Sequence<byte>.FromElements((byte)(191), (byte)(112), (byte)(86), (byte)(234), (byte)(220), (byte)(233), (byte)(122), (byte)(154), (byte)(100), (byte)(188), (byte)(230), (byte)(238), (byte)(239), (byte)(155), (byte)(54), (byte)(32), (byte)(97), (byte)(35), (byte)(51), (byte)(160), (byte)(121), (byte)(235), (byte)(42), (byte)(64), (byte)(145), (byte)(105), (byte)(15), (byte)(153), (byte)(162), (byte)(89), (byte)(9), (byte)(156)));
    } }
    public static TestKDFK__TestVectors_Compile._ITestVector c5 { get {
      return TestKDFK__TestVectors_Compile.TestVector.create(Dafny.Sequence<char>.FromString("C.5 Test Case 5"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(166), (byte)(236), (byte)(116), (byte)(51), (byte)(140), (byte)(189), (byte)(192), (byte)(175), (byte)(42), (byte)(154), (byte)(51), (byte)(26), (byte)(208), (byte)(149), (byte)(76), (byte)(159), (byte)(174), (byte)(162), (byte)(207), (byte)(4), (byte)(108), (byte)(232), (byte)(196), (byte)(240), (byte)(12), (byte)(57), (byte)(228), (byte)(155), (byte)(97), (byte)(75), (byte)(42), (byte)(66)), Dafny.Sequence<byte>.FromElements((byte)(236), (byte)(169), (byte)(233), (byte)(45), (byte)(43), (byte)(25), (byte)(122), (byte)(243), (byte)(152), (byte)(191), (byte)(154), (byte)(55), (byte)(45), (byte)(134), (byte)(159), (byte)(220)), TestKDFK__TestVectors_Compile.__default.PURPOSE, 32, Dafny.Sequence<byte>.FromElements((byte)(156), (byte)(11), (byte)(20), (byte)(251), (byte)(100), (byte)(227), (byte)(163), (byte)(161), (byte)(30), (byte)(45), (byte)(242), (byte)(2), (byte)(248), (byte)(246), (byte)(44), (byte)(11), (byte)(88), (byte)(132), (byte)(189), (byte)(175), (byte)(95), (byte)(96), (byte)(61), (byte)(44), (byte)(98), (byte)(160), (byte)(212), (byte)(136), (byte)(140), (byte)(222), (byte)(57), (byte)(151)));
    } }
    public static Dafny.ISequence<TestKDFK__TestVectors_Compile._ITestVector> testVectors { get {
      return Dafny.Sequence<TestKDFK__TestVectors_Compile._ITestVector>.FromElements(TestKDFK__TestVectors_Compile.__default.c1, TestKDFK__TestVectors_Compile.__default.c2, TestKDFK__TestVectors_Compile.__default.c3, TestKDFK__TestVectors_Compile.__default.c4, TestKDFK__TestVectors_Compile.__default.c5);
    } }
  }
} // end of namespace TestKDFK__TestVectors_Compile
namespace TestAwsCryptographyPrimitivesHKDF_Compile {

  public partial class __default {
    public static void TestCase1()
    {
      software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _100_hash;
      _100_hash = software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256();
      Dafny.ISequence<byte> _101_IKM;
      _101_IKM = Dafny.Sequence<byte>.FromElements((byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11));
      Dafny.ISequence<byte> _102_salt;
      _102_salt = Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1), (byte)(2), (byte)(3), (byte)(4), (byte)(5), (byte)(6), (byte)(7), (byte)(8), (byte)(9), (byte)(10), (byte)(11), (byte)(12));
      Dafny.ISequence<byte> _103_info;
      _103_info = Dafny.Sequence<byte>.FromElements((byte)(240), (byte)(241), (byte)(242), (byte)(243), (byte)(244), (byte)(245), (byte)(246), (byte)(247), (byte)(248), (byte)(249));
      int _104_L;
      _104_L = 42;
      Dafny.ISequence<byte> _105_PRK;
      _105_PRK = Dafny.Sequence<byte>.FromElements((byte)(7), (byte)(119), (byte)(9), (byte)(54), (byte)(44), (byte)(46), (byte)(50), (byte)(223), (byte)(13), (byte)(220), (byte)(63), (byte)(13), (byte)(196), (byte)(123), (byte)(186), (byte)(99), (byte)(144), (byte)(182), (byte)(199), (byte)(59), (byte)(181), (byte)(15), (byte)(156), (byte)(49), (byte)(34), (byte)(236), (byte)(132), (byte)(74), (byte)(215), (byte)(194), (byte)(179), (byte)(229));
      Dafny.ISequence<byte> _106_OKM;
      _106_OKM = Dafny.Sequence<byte>.FromElements((byte)(60), (byte)(178), (byte)(95), (byte)(37), (byte)(250), (byte)(172), (byte)(213), (byte)(122), (byte)(144), (byte)(67), (byte)(79), (byte)(100), (byte)(208), (byte)(54), (byte)(47), (byte)(42), (byte)(45), (byte)(45), (byte)(10), (byte)(144), (byte)(207), (byte)(26), (byte)(90), (byte)(76), (byte)(93), (byte)(176), (byte)(45), (byte)(86), (byte)(236), (byte)(196), (byte)(197), (byte)(191), (byte)(52), (byte)(0), (byte)(114), (byte)(8), (byte)(213), (byte)(184), (byte)(135), (byte)(24), (byte)(88), (byte)(101));
      TestAwsCryptographyPrimitivesHKDF_Compile.__default.BasicExtractTest(software.amazon.cryptography.primitives.internaldafny.types.HkdfExtractInput.create(_100_hash, Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_102_salt), _101_IKM), _105_PRK);
      TestAwsCryptographyPrimitivesHKDF_Compile.__default.BasicExpandTest(software.amazon.cryptography.primitives.internaldafny.types.HkdfExpandInput.create(_100_hash, _105_PRK, _103_info, _104_L), _106_OKM);
      TestAwsCryptographyPrimitivesHKDF_Compile.__default.BasicHkdfTest(software.amazon.cryptography.primitives.internaldafny.types.HkdfInput.create(_100_hash, Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_102_salt), _101_IKM, _103_info, _104_L), _106_OKM);
    }
    public static void BasicExtractTest(software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput input, Dafny.ISequence<byte> expectedPRK)
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _107_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _108_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out18;
      _out18 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _108_valueOrError0 = _out18;
      if (!(!((_108_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(86,15): " + _108_valueOrError0);}
      _107_client = (_108_valueOrError0).Extract();
      Dafny.ISequence<byte> _109_output;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _110_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out19;
      _out19 = (_107_client).HkdfExtract(input);
      _110_valueOrError1 = _out19;
      if (!(!((_110_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(88,15): " + _110_valueOrError1);}
      _109_output = (_110_valueOrError1).Extract();
      if (!((new BigInteger((_109_output).Count)) == (Digest_Compile.__default.Length((input).dtor_digestAlgorithm)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(89,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_109_output).Equals(expectedPRK))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(90,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void BasicExpandTest(software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput input, Dafny.ISequence<byte> expectedOKM)
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _111_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _112_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out20;
      _out20 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _112_valueOrError0 = _out20;
      if (!(!((_112_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(98,15): " + _112_valueOrError0);}
      _111_client = (_112_valueOrError0).Extract();
      Dafny.ISequence<byte> _113_output;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _114_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out21;
      _out21 = (_111_client).HkdfExpand(input);
      _114_valueOrError1 = _out21;
      if (!(!((_114_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(100,15): " + _114_valueOrError1);}
      _113_output = (_114_valueOrError1).Extract();
      if (!((new BigInteger((_113_output).Count)) == (new BigInteger((input).dtor_expectedLength)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(101,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_113_output).Equals(expectedOKM))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(102,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void BasicHkdfTest(software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput input, Dafny.ISequence<byte> expectedOKM)
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _115_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _116_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out22;
      _out22 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _116_valueOrError0 = _out22;
      if (!(!((_116_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(110,15): " + _116_valueOrError0);}
      _115_client = (_116_valueOrError0).Extract();
      Dafny.ISequence<byte> _117_output;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _118_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out23;
      _out23 = (_115_client).Hkdf(input);
      _118_valueOrError1 = _out23;
      if (!(!((_118_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(112,15): " + _118_valueOrError1);}
      _117_output = (_118_valueOrError1).Extract();
      if (!((new BigInteger((_117_output).Count)) == (new BigInteger((input).dtor_expectedLength)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(113,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_117_output).Equals(expectedOKM))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestAwsCryptographyPrimitivesHKDF.dfy(114,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestAwsCryptographyPrimitivesHKDF_Compile
namespace TestHKDF__Rfc5869TestVectors_Compile {

  public interface _IRFCTestVector {
    bool is_RFCTestVector { get; }
    Dafny.ISequence<char> dtor_name { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_hash { get; }
    Dafny.ISequence<byte> dtor_IKM { get; }
    Dafny.ISequence<byte> dtor_salt { get; }
    Dafny.ISequence<byte> dtor_info { get; }
    int dtor_L { get; }
    Dafny.ISequence<byte> dtor_PRK { get; }
    Dafny.ISequence<byte> dtor_OKM { get; }
    _IRFCTestVector DowncastClone();
  }
  public class RFCTestVector : _IRFCTestVector {
    public readonly Dafny.ISequence<char> _name;
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _hash;
    public readonly Dafny.ISequence<byte> _IKM;
    public readonly Dafny.ISequence<byte> _salt;
    public readonly Dafny.ISequence<byte> _info;
    public readonly int _L;
    public readonly Dafny.ISequence<byte> _PRK;
    public readonly Dafny.ISequence<byte> _OKM;
    public RFCTestVector(Dafny.ISequence<char> name, software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm hash, Dafny.ISequence<byte> IKM, Dafny.ISequence<byte> salt, Dafny.ISequence<byte> info, int L, Dafny.ISequence<byte> PRK, Dafny.ISequence<byte> OKM) {
      this._name = name;
      this._hash = hash;
      this._IKM = IKM;
      this._salt = salt;
      this._info = info;
      this._L = L;
      this._PRK = PRK;
      this._OKM = OKM;
    }
    public _IRFCTestVector DowncastClone() {
      if (this is _IRFCTestVector dt) { return dt; }
      return new RFCTestVector(_name, _hash, _IKM, _salt, _info, _L, _PRK, _OKM);
    }
    public override bool Equals(object other) {
      var oth = other as TestHKDF__Rfc5869TestVectors_Compile.RFCTestVector;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._hash, oth._hash) && object.Equals(this._IKM, oth._IKM) && object.Equals(this._salt, oth._salt) && object.Equals(this._info, oth._info) && this._L == oth._L && object.Equals(this._PRK, oth._PRK) && object.Equals(this._OKM, oth._OKM);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hash));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._IKM));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._salt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._info));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._L));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PRK));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._OKM));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestHKDF__Rfc5869TestVectors_Compile.RFCTestVector.RFCTestVector";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._hash);
      s += ", ";
      s += Dafny.Helpers.ToString(this._IKM);
      s += ", ";
      s += Dafny.Helpers.ToString(this._salt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._info);
      s += ", ";
      s += Dafny.Helpers.ToString(this._L);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PRK);
      s += ", ";
      s += Dafny.Helpers.ToString(this._OKM);
      s += ")";
      return s;
    }
    private static readonly TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector theDefault = create(Dafny.Sequence<char>.Empty, software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, 0, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector> _TYPE = new Dafny.TypeDescriptor<TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector>(TestHKDF__Rfc5869TestVectors_Compile.RFCTestVector.Default());
    public static Dafny.TypeDescriptor<TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRFCTestVector create(Dafny.ISequence<char> name, software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm hash, Dafny.ISequence<byte> IKM, Dafny.ISequence<byte> salt, Dafny.ISequence<byte> info, int L, Dafny.ISequence<byte> PRK, Dafny.ISequence<byte> OKM) {
      return new RFCTestVector(name, hash, IKM, salt, info, L, PRK, OKM);
    }
    public static _IRFCTestVector create_RFCTestVector(Dafny.ISequence<char> name, software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm hash, Dafny.ISequence<byte> IKM, Dafny.ISequence<byte> salt, Dafny.ISequence<byte> info, int L, Dafny.ISequence<byte> PRK, Dafny.ISequence<byte> OKM) {
      return create(name, hash, IKM, salt, info, L, PRK, OKM);
    }
    public bool is_RFCTestVector { get { return true; } }
    public Dafny.ISequence<char> dtor_name {
      get {
        return this._name;
      }
    }
    public software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_hash {
      get {
        return this._hash;
      }
    }
    public Dafny.ISequence<byte> dtor_IKM {
      get {
        return this._IKM;
      }
    }
    public Dafny.ISequence<byte> dtor_salt {
      get {
        return this._salt;
      }
    }
    public Dafny.ISequence<byte> dtor_info {
      get {
        return this._info;
      }
    }
    public int dtor_L {
      get {
        return this._L;
      }
    }
    public Dafny.ISequence<byte> dtor_PRK {
      get {
        return this._PRK;
      }
    }
    public Dafny.ISequence<byte> dtor_OKM {
      get {
        return this._OKM;
      }
    }
  }

  public partial class __default {
    public static void ExpectRFCTestVectors()
    {
      BigInteger _hi2 = new BigInteger((TestHKDF__Rfc5869TestVectors_Compile.__default.testVectors).Count);
      for (BigInteger _119_i = BigInteger.Zero; _119_i < _hi2; _119_i++) {
        TestHKDF__Rfc5869TestVectors_Compile.__default.ExpectTestVector((TestHKDF__Rfc5869TestVectors_Compile.__default.testVectors).Select(_119_i));
      }
    }
    public static void ExpectTestVector(TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector vector)
    {
      TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector _let_tmp_rhs2 = vector;
      Dafny.ISequence<char> _120_name = _let_tmp_rhs2.dtor_name;
      software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _121_hash = _let_tmp_rhs2.dtor_hash;
      Dafny.ISequence<byte> _122_IKM = _let_tmp_rhs2.dtor_IKM;
      Dafny.ISequence<byte> _123_salt = _let_tmp_rhs2.dtor_salt;
      Dafny.ISequence<byte> _124_info = _let_tmp_rhs2.dtor_info;
      int _125_L = _let_tmp_rhs2.dtor_L;
      Dafny.ISequence<byte> _126_PRK = _let_tmp_rhs2.dtor_PRK;
      Dafny.ISequence<byte> _127_OKM = _let_tmp_rhs2.dtor_OKM;
      Dafny.Helpers.Print((Dafny.Sequence<char>.Concat(_120_name, Dafny.Sequence<char>.FromString("\n"))));
      TestAwsCryptographyPrimitivesHKDF_Compile.__default.BasicExtractTest(software.amazon.cryptography.primitives.internaldafny.types.HkdfExtractInput.create(_121_hash, (((new BigInteger((_123_salt).Count)).Sign == 1) ? (Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_123_salt)) : (Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None())), _122_IKM), _126_PRK);
      TestAwsCryptographyPrimitivesHKDF_Compile.__default.BasicExpandTest(software.amazon.cryptography.primitives.internaldafny.types.HkdfExpandInput.create(_121_hash, _126_PRK, _124_info, _125_L), _127_OKM);
      TestAwsCryptographyPrimitivesHKDF_Compile.__default.BasicHkdfTest(software.amazon.cryptography.primitives.internaldafny.types.HkdfInput.create(_121_hash, (((new BigInteger((_123_salt).Count)).Sign == 1) ? (Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_123_salt)) : (Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None())), _122_IKM, _124_info, _125_L), _127_OKM);
    }
    public static TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector a1 { get {
      return TestHKDF__Rfc5869TestVectors_Compile.RFCTestVector.create(Dafny.Sequence<char>.FromString("A.1.  Test Case 1"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11)), Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1), (byte)(2), (byte)(3), (byte)(4), (byte)(5), (byte)(6), (byte)(7), (byte)(8), (byte)(9), (byte)(10), (byte)(11), (byte)(12)), Dafny.Sequence<byte>.FromElements((byte)(240), (byte)(241), (byte)(242), (byte)(243), (byte)(244), (byte)(245), (byte)(246), (byte)(247), (byte)(248), (byte)(249)), (int)(42), Dafny.Sequence<byte>.FromElements((byte)(7), (byte)(119), (byte)(9), (byte)(54), (byte)(44), (byte)(46), (byte)(50), (byte)(223), (byte)(13), (byte)(220), (byte)(63), (byte)(13), (byte)(196), (byte)(123), (byte)(186), (byte)(99), (byte)(144), (byte)(182), (byte)(199), (byte)(59), (byte)(181), (byte)(15), (byte)(156), (byte)(49), (byte)(34), (byte)(236), (byte)(132), (byte)(74), (byte)(215), (byte)(194), (byte)(179), (byte)(229)), Dafny.Sequence<byte>.FromElements((byte)(60), (byte)(178), (byte)(95), (byte)(37), (byte)(250), (byte)(172), (byte)(213), (byte)(122), (byte)(144), (byte)(67), (byte)(79), (byte)(100), (byte)(208), (byte)(54), (byte)(47), (byte)(42), (byte)(45), (byte)(45), (byte)(10), (byte)(144), (byte)(207), (byte)(26), (byte)(90), (byte)(76), (byte)(93), (byte)(176), (byte)(45), (byte)(86), (byte)(236), (byte)(196), (byte)(197), (byte)(191), (byte)(52), (byte)(0), (byte)(114), (byte)(8), (byte)(213), (byte)(184), (byte)(135), (byte)(24), (byte)(88), (byte)(101)));
    } }
    public static TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector a2 { get {
      return TestHKDF__Rfc5869TestVectors_Compile.RFCTestVector.create(Dafny.Sequence<char>.FromString("A.2.  Test Case 2"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1), (byte)(2), (byte)(3), (byte)(4), (byte)(5), (byte)(6), (byte)(7), (byte)(8), (byte)(9), (byte)(10), (byte)(11), (byte)(12), (byte)(13), (byte)(14), (byte)(15), (byte)(16), (byte)(17), (byte)(18), (byte)(19), (byte)(20), (byte)(21), (byte)(22), (byte)(23), (byte)(24), (byte)(25), (byte)(26), (byte)(27), (byte)(28), (byte)(29), (byte)(30), (byte)(31), (byte)(32), (byte)(33), (byte)(34), (byte)(35), (byte)(36), (byte)(37), (byte)(38), (byte)(39), (byte)(40), (byte)(41), (byte)(42), (byte)(43), (byte)(44), (byte)(45), (byte)(46), (byte)(47), (byte)(48), (byte)(49), (byte)(50), (byte)(51), (byte)(52), (byte)(53), (byte)(54), (byte)(55), (byte)(56), (byte)(57), (byte)(58), (byte)(59), (byte)(60), (byte)(61), (byte)(62), (byte)(63), (byte)(64), (byte)(65), (byte)(66), (byte)(67), (byte)(68), (byte)(69), (byte)(70), (byte)(71), (byte)(72), (byte)(73), (byte)(74), (byte)(75), (byte)(76), (byte)(77), (byte)(78), (byte)(79)), Dafny.Sequence<byte>.FromElements((byte)(96), (byte)(97), (byte)(98), (byte)(99), (byte)(100), (byte)(101), (byte)(102), (byte)(103), (byte)(104), (byte)(105), (byte)(106), (byte)(107), (byte)(108), (byte)(109), (byte)(110), (byte)(111), (byte)(112), (byte)(113), (byte)(114), (byte)(115), (byte)(116), (byte)(117), (byte)(118), (byte)(119), (byte)(120), (byte)(121), (byte)(122), (byte)(123), (byte)(124), (byte)(125), (byte)(126), (byte)(127), (byte)(128), (byte)(129), (byte)(130), (byte)(131), (byte)(132), (byte)(133), (byte)(134), (byte)(135), (byte)(136), (byte)(137), (byte)(138), (byte)(139), (byte)(140), (byte)(141), (byte)(142), (byte)(143), (byte)(144), (byte)(145), (byte)(146), (byte)(147), (byte)(148), (byte)(149), (byte)(150), (byte)(151), (byte)(152), (byte)(153), (byte)(154), (byte)(155), (byte)(156), (byte)(157), (byte)(158), (byte)(159), (byte)(160), (byte)(161), (byte)(162), (byte)(163), (byte)(164), (byte)(165), (byte)(166), (byte)(167), (byte)(168), (byte)(169), (byte)(170), (byte)(171), (byte)(172), (byte)(173), (byte)(174), (byte)(175)), Dafny.Sequence<byte>.FromElements((byte)(176), (byte)(177), (byte)(178), (byte)(179), (byte)(180), (byte)(181), (byte)(182), (byte)(183), (byte)(184), (byte)(185), (byte)(186), (byte)(187), (byte)(188), (byte)(189), (byte)(190), (byte)(191), (byte)(192), (byte)(193), (byte)(194), (byte)(195), (byte)(196), (byte)(197), (byte)(198), (byte)(199), (byte)(200), (byte)(201), (byte)(202), (byte)(203), (byte)(204), (byte)(205), (byte)(206), (byte)(207), (byte)(208), (byte)(209), (byte)(210), (byte)(211), (byte)(212), (byte)(213), (byte)(214), (byte)(215), (byte)(216), (byte)(217), (byte)(218), (byte)(219), (byte)(220), (byte)(221), (byte)(222), (byte)(223), (byte)(224), (byte)(225), (byte)(226), (byte)(227), (byte)(228), (byte)(229), (byte)(230), (byte)(231), (byte)(232), (byte)(233), (byte)(234), (byte)(235), (byte)(236), (byte)(237), (byte)(238), (byte)(239), (byte)(240), (byte)(241), (byte)(242), (byte)(243), (byte)(244), (byte)(245), (byte)(246), (byte)(247), (byte)(248), (byte)(249), (byte)(250), (byte)(251), (byte)(252), (byte)(253), (byte)(254), (byte)(255)), (int)(82), Dafny.Sequence<byte>.FromElements((byte)(6), (byte)(166), (byte)(184), (byte)(140), (byte)(88), (byte)(83), (byte)(54), (byte)(26), (byte)(6), (byte)(16), (byte)(76), (byte)(156), (byte)(235), (byte)(53), (byte)(180), (byte)(92), (byte)(239), (byte)(118), (byte)(0), (byte)(20), (byte)(144), (byte)(70), (byte)(113), (byte)(1), (byte)(74), (byte)(25), (byte)(63), (byte)(64), (byte)(193), (byte)(95), (byte)(194), (byte)(68)), Dafny.Sequence<byte>.FromElements((byte)(177), (byte)(30), (byte)(57), (byte)(141), (byte)(200), (byte)(3), (byte)(39), (byte)(161), (byte)(200), (byte)(231), (byte)(247), (byte)(140), (byte)(89), (byte)(106), (byte)(73), (byte)(52), (byte)(79), (byte)(1), (byte)(46), (byte)(218), (byte)(45), (byte)(78), (byte)(250), (byte)(216), (byte)(160), (byte)(80), (byte)(204), (byte)(76), (byte)(25), (byte)(175), (byte)(169), (byte)(124), (byte)(89), (byte)(4), (byte)(90), (byte)(153), (byte)(202), (byte)(199), (byte)(130), (byte)(114), (byte)(113), (byte)(203), (byte)(65), (byte)(198), (byte)(94), (byte)(89), (byte)(14), (byte)(9), (byte)(218), (byte)(50), (byte)(117), (byte)(96), (byte)(12), (byte)(47), (byte)(9), (byte)(184), (byte)(54), (byte)(119), (byte)(147), (byte)(169), (byte)(172), (byte)(163), (byte)(219), (byte)(113), (byte)(204), (byte)(48), (byte)(197), (byte)(129), (byte)(121), (byte)(236), (byte)(62), (byte)(135), (byte)(193), (byte)(76), (byte)(1), (byte)(213), (byte)(193), (byte)(243), (byte)(67), (byte)(79), (byte)(29), (byte)(135)));
    } }
    public static TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector a3 { get {
      return TestHKDF__Rfc5869TestVectors_Compile.RFCTestVector.create(Dafny.Sequence<char>.FromString("A.3.  Test Case 3"), software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256(), Dafny.Sequence<byte>.FromElements((byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11), (byte)(11)), Dafny.Sequence<byte>.FromElements(), Dafny.Sequence<byte>.FromElements(), (int)(42), Dafny.Sequence<byte>.FromElements((byte)(25), (byte)(239), (byte)(36), (byte)(163), (byte)(44), (byte)(113), (byte)(123), (byte)(22), (byte)(127), (byte)(51), (byte)(169), (byte)(29), (byte)(111), (byte)(100), (byte)(139), (byte)(223), (byte)(150), (byte)(89), (byte)(103), (byte)(118), (byte)(175), (byte)(219), (byte)(99), (byte)(119), (byte)(172), (byte)(67), (byte)(76), (byte)(28), (byte)(41), (byte)(60), (byte)(203), (byte)(4)), Dafny.Sequence<byte>.FromElements((byte)(141), (byte)(164), (byte)(231), (byte)(117), (byte)(165), (byte)(99), (byte)(193), (byte)(143), (byte)(113), (byte)(95), (byte)(128), (byte)(42), (byte)(6), (byte)(60), (byte)(90), (byte)(49), (byte)(184), (byte)(161), (byte)(31), (byte)(92), (byte)(94), (byte)(225), (byte)(135), (byte)(158), (byte)(195), (byte)(69), (byte)(78), (byte)(95), (byte)(60), (byte)(115), (byte)(141), (byte)(45), (byte)(157), (byte)(32), (byte)(19), (byte)(149), (byte)(250), (byte)(164), (byte)(182), (byte)(26), (byte)(150), (byte)(200)));
    } }
    public static Dafny.ISequence<TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector> testVectors { get {
      return Dafny.Sequence<TestHKDF__Rfc5869TestVectors_Compile._IRFCTestVector>.FromElements(TestHKDF__Rfc5869TestVectors_Compile.__default.a1, TestHKDF__Rfc5869TestVectors_Compile.__default.a2, TestHKDF__Rfc5869TestVectors_Compile.__default.a3);
    } }
  }
} // end of namespace TestHKDF__Rfc5869TestVectors_Compile
namespace ConstantTime_Compile {

  public partial class __default {
    public static byte Compare(Dafny.ISequence<byte> a, Dafny.ISequence<byte> b, byte acc)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((a).Count)).Sign == 0) {
        return acc;
      } else {
        byte _128_x = (byte)(((byte)((a).Select(BigInteger.Zero))) ^ ((byte)((b).Select(BigInteger.Zero))));
        Dafny.ISequence<byte> _in0 = (a).Drop(BigInteger.One);
        Dafny.ISequence<byte> _in1 = (b).Drop(BigInteger.One);
        byte _in2 = (byte)((_128_x) | (acc));
        a = _in0;
        b = _in1;
        acc = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static bool Equals(Dafny.ISequence<byte> a, Dafny.ISequence<byte> b)
    {
      return (ConstantTime_Compile.__default.Compare(a, b, (byte)(0))) == ((byte)(0));
    }
  }
} // end of namespace ConstantTime_Compile
namespace ConstantTimeTest_Compile {

  public partial class __default {
    public static void ConstantTimeTest()
    {
      if (!(ConstantTime_Compile.__default.Equals(Dafny.Sequence<byte>.FromElements(), Dafny.Sequence<byte>.FromElements()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/ConstantTime.dfy(10,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(ConstantTime_Compile.__default.Equals(Dafny.Sequence<byte>.FromElements((byte)(1)), Dafny.Sequence<byte>.FromElements((byte)(1))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/ConstantTime.dfy(11,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(!(ConstantTime_Compile.__default.Equals(Dafny.Sequence<byte>.FromElements((byte)(1)), Dafny.Sequence<byte>.FromElements((byte)(2)))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/ConstantTime.dfy(12,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(ConstantTime_Compile.__default.Equals(Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(2), (byte)(3)), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(2), (byte)(3))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/ConstantTime.dfy(13,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(!(ConstantTime_Compile.__default.Equals(Dafny.Sequence<byte>.FromElements((byte)(2), (byte)(2), (byte)(3)), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(2), (byte)(3)))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/ConstantTime.dfy(14,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(!(ConstantTime_Compile.__default.Equals(Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(2), (byte)(3)), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(2), (byte)(4)))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/ConstantTime.dfy(15,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace ConstantTimeTest_Compile
namespace TestAwsCryptographyPrimitivesGenerateRandomBytes_Compile {

  public partial class __default {
    public static void BasicGenerateRandomBytes()
    {
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _129_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _130_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out24;
      _out24 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _130_valueOrError0 = _out24;
      if (!(!((_130_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestGenerateRandomBytes.dfy(11,15): " + _130_valueOrError0);}
      _129_client = (_130_valueOrError0).Extract();
      int _131_length;
      _131_length = (int)(5);
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRandomBytesInput _132_input;
      _132_input = software.amazon.cryptography.primitives.internaldafny.types.GenerateRandomBytesInput.create(_131_length);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _133_output;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out25;
      _out25 = (_129_client).GenerateRandomBytes(_132_input);
      _133_output = _out25;
      Dafny.ISequence<byte> _134_value;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _135_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      _135_valueOrError1 = _133_output;
      if (!(!((_135_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestGenerateRandomBytes.dfy(20,14): " + _135_valueOrError1);}
      _134_value = (_135_valueOrError1).Extract();
      if (!((new BigInteger((_134_value).Count)) == (new BigInteger(_131_length)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestGenerateRandomBytes.dfy(21,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestAwsCryptographyPrimitivesGenerateRandomBytes_Compile
namespace TestSignature_Compile {

  public partial class __default {
    public static void RequireGoodKeyLengths(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm alg, Signature._ISignatureKeyPair sigKeyPair)
    {
      if (!((new BigInteger(((sigKeyPair).dtor_verificationKey).Count)) == (Signature.__default.FieldSize(alg)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(24,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void YCompression(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm alg, BigInteger fieldSize)
    {
      Signature._ISignatureKeyPair _136_res;
      Wrappers_Compile._IResult<Signature._ISignatureKeyPair, software.amazon.cryptography.primitives.internaldafny.types._IError> _137_valueOrError0 = Wrappers_Compile.Result<Signature._ISignatureKeyPair, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Signature.SignatureKeyPair.Default());
      Wrappers_Compile._IResult<Signature._ISignatureKeyPair, software.amazon.cryptography.primitives.internaldafny.types._IError> _out26;
      _out26 = Signature.ECDSA.ExternKeyGen(alg);
      _137_valueOrError0 = _out26;
      if (!(!((_137_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(28,12): " + _137_valueOrError0);}
      _136_res = (_137_valueOrError0).Extract();
      TestSignature_Compile.__default.RequireGoodKeyLengths(alg, _136_res);
      Dafny.ISequence<byte> _138_public;
      Dafny.ISequence<byte> _139_secret;
      Dafny.ISequence<byte> _rhs0 = (_136_res).dtor_verificationKey;
      Dafny.ISequence<byte> _rhs1 = (_136_res).dtor_signingKey;
      _138_public = _rhs0;
      _139_secret = _rhs1;
      if (!((new BigInteger((_139_secret).Count)).Sign == 1)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(33,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((new BigInteger((_138_public).Count)) == ((BigInteger.One) + (Dafny.Helpers.EuclideanDivision((fieldSize) + (new BigInteger(7)), new BigInteger(8)))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(34,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_138_public).Select(BigInteger.Zero)) == ((byte)(2))) || (((_138_public).Select(BigInteger.Zero)) == ((byte)(3))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(35,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void VerifyMessage(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm alg)
    {
      Dafny.ISequence<byte> _140_message;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _141_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _141_valueOrError0 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("Hello, World!"));
      if (!(!((_141_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(39,16): " + _141_valueOrError0);}
      _140_message = (_141_valueOrError0).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput _142_genInput;
      _142_genInput = software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyInput.create(alg);
      Signature._ISignatureKeyPair _143_keys;
      Wrappers_Compile._IResult<Signature._ISignatureKeyPair, software.amazon.cryptography.primitives.internaldafny.types._IError> _144_valueOrError1 = Wrappers_Compile.Result<Signature._ISignatureKeyPair, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Signature.SignatureKeyPair.Default());
      Wrappers_Compile._IResult<Signature._ISignatureKeyPair, software.amazon.cryptography.primitives.internaldafny.types._IError> _out27;
      _out27 = Signature.ECDSA.ExternKeyGen(alg);
      _144_valueOrError1 = _out27;
      if (!(!((_144_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(41,13): " + _144_valueOrError1);}
      _143_keys = (_144_valueOrError1).Extract();
      TestSignature_Compile.__default.RequireGoodKeyLengths(alg, _143_keys);
      Dafny.ISequence<byte> _145_signature;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _146_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out28;
      _out28 = Signature.ECDSA.Sign(alg, (_143_keys).dtor_signingKey, _140_message);
      _146_valueOrError2 = _out28;
      if (!(!((_146_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(44,18): " + _146_valueOrError2);}
      _145_signature = (_146_valueOrError2).Extract();
      bool _147_shouldBeTrue;
      Wrappers_Compile._IResult<bool, software.amazon.cryptography.primitives.internaldafny.types._IError> _148_valueOrError3 = Wrappers_Compile.Result<bool, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(false);
      _148_valueOrError3 = Signature.ECDSA.Verify(alg, (_143_keys).dtor_verificationKey, _140_message, _145_signature);
      if (!(!((_148_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(45,21): " + _148_valueOrError3);}
      _147_shouldBeTrue = (_148_valueOrError3).Extract();
      if (!(_147_shouldBeTrue)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(46,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      bool _149_shouldBeFalse;
      Wrappers_Compile._IResult<bool, software.amazon.cryptography.primitives.internaldafny.types._IError> _150_valueOrError4 = Wrappers_Compile.Result<bool, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(false);
      _150_valueOrError4 = Signature.ECDSA.Verify(alg, (_143_keys).dtor_verificationKey, Dafny.Sequence<byte>.Concat(_140_message, Dafny.Sequence<byte>.FromElements((byte)(1))), _145_signature);
      if (!(!((_150_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(48,22): " + _150_valueOrError4);}
      _149_shouldBeFalse = (_150_valueOrError4).Extract();
      if (!(!(_149_shouldBeFalse))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/test/TestSignature.dfy(49,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void YCompression384()
    {
      TestSignature_Compile.__default.YCompression(TestSignature_Compile.__default.P384, new BigInteger(384));
    }
    public static void YCompression256()
    {
      TestSignature_Compile.__default.YCompression(TestSignature_Compile.__default.P256, new BigInteger(256));
    }
    public static void VerifyMessage384()
    {
      TestSignature_Compile.__default.VerifyMessage(TestSignature_Compile.__default.P384);
    }
    public static void VerifyMessage256()
    {
      TestSignature_Compile.__default.VerifyMessage(TestSignature_Compile.__default.P256);
    }
    public static software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm P384 { get {
      return software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm.create_ECDSA__P384();
    } }
    public static software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm P256 { get {
      return software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm.create_ECDSA__P256();
    } }
  }
} // end of namespace TestSignature_Compile
namespace JSON_mUtils_mViews_Compile {

} // end of namespace JSON_mUtils_mViews_Compile
namespace JSON_mUtils_Compile {

} // end of namespace JSON_mUtils_Compile
namespace JSON_mConcreteSyntax_Compile {

} // end of namespace JSON_mConcreteSyntax_Compile
namespace JSON_mZeroCopy_Compile {

} // end of namespace JSON_mZeroCopy_Compile
namespace JSON_Compile {

} // end of namespace JSON_Compile
namespace _module {

  public partial class __default {
    public static void __Test____Main__(Dafny.ISequence<Dafny.ISequence<char>> __noArgsParameter)
    {
      bool _151_success;
      _151_success = true;
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesAesKdfCtr.AesKdfCtrTests: ")));
      try {
        {
          TestAwsCryptographyPrimitivesAesKdfCtr_Compile.__default.AesKdfCtrTests();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _152_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_152_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesHMacDigest.DigestTests: ")));
      try {
        {
          TestAwsCryptographyPrimitivesHMacDigest_Compile.__default.DigestTests();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _153_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_153_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesDigest.DigestTests: ")));
      try {
        {
          TestAwsCryptographyPrimitivesDigest_Compile.__default.DigestTests();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _154_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_154_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesHMAC.HMACTests: ")));
      try {
        {
          TestAwsCryptographyPrimitivesHMAC_Compile.__default.HMACTests();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _155_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_155_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesAES.AESDecryptTests: ")));
      try {
        {
          TestAwsCryptographyPrimitivesAES_Compile.__default.AESDecryptTests();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _156_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_156_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesAES.AESEncryptTests: ")));
      try {
        {
          TestAwsCryptographyPrimitivesAES_Compile.__default.AESEncryptTests();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _157_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_157_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesRSA.RSAEncryptTests: ")));
      try {
        {
          TestAwsCryptographyPrimitivesRSA_Compile.__default.RSAEncryptTests();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _158_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_158_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesRSA.GetRSAKeyModulusLength: ")));
      try {
        {
          TestAwsCryptographyPrimitivesRSA_Compile.__default.GetRSAKeyModulusLength();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _159_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_159_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesRSA.TestingPemParsingInRSAEncryptionForRSAKeyPairStoredInPEM: ")));
      try {
        {
          TestAwsCryptographyPrimitivesRSA_Compile.__default.TestingPemParsingInRSAEncryptionForRSAKeyPairStoredInPEM();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _160_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_160_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesRSA.TestingPemParsingInRSAEncryptionForOnlyRSAPrivateKeyStoredInPEM: ")));
      try {
        {
          TestAwsCryptographyPrimitivesRSA_Compile.__default.TestingPemParsingInRSAEncryptionForOnlyRSAPrivateKeyStoredInPEM();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _161_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_161_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestKDFK_TestVectors.ExpectInternalTestVectors: ")));
      try {
        {
          TestKDFK__TestVectors_Compile.__default.ExpectInternalTestVectors();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _162_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_162_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesHKDF.TestCase1: ")));
      try {
        {
          TestAwsCryptographyPrimitivesHKDF_Compile.__default.TestCase1();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _163_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_163_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestHKDF_Rfc5869TestVectors.ExpectRFCTestVectors: ")));
      try {
        {
          TestHKDF__Rfc5869TestVectors_Compile.__default.ExpectRFCTestVectors();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _164_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_164_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"ConstantTimeTest.ConstantTimeTest: ")));
      try {
        {
          ConstantTimeTest_Compile.__default.ConstantTimeTest();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _165_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_165_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsCryptographyPrimitivesGenerateRandomBytes.BasicGenerateRandomBytes: ")));
      try {
        {
          TestAwsCryptographyPrimitivesGenerateRandomBytes_Compile.__default.BasicGenerateRandomBytes();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _166_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_166_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSignature.YCompression384: ")));
      try {
        {
          TestSignature_Compile.__default.YCompression384();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _167_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_167_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSignature.YCompression256: ")));
      try {
        {
          TestSignature_Compile.__default.YCompression256();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _168_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_168_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSignature.VerifyMessage384: ")));
      try {
        {
          TestSignature_Compile.__default.VerifyMessage384();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _169_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_169_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSignature.VerifyMessage256: ")));
      try {
        {
          TestSignature_Compile.__default.VerifyMessage256();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _170_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_170_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _151_success = false;
        }
      }
      if (!(_151_success)) {
        throw new Dafny.HaltException("<stdin>(1,0): " + Dafny.Sequence<char>.FromString(@"Test failures occurred: see above.
"));}
    }
  }
} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => _module.__default.__Test____Main__(Dafny.Sequence<Dafny.ISequence<char>>.FromMainArguments(args)));
  }
}
