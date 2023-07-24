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
// Command Line Options: -stdin -noVerify -vcsCores:2 -compileTarget:cs -spillTargetCode:3 -compile:0 -optimizeErasableDatatypeWrapper:0 -quantifierSyntax:3 -unicodeChar:0 -functionSyntax:3 -useRuntimeLib -out runtimes/net/ImplementationFromDafny -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/StandardLibrary/src/Index.dfy
// the_program








































module {:extern ""software.amazon.cryptography.primitives.internaldafny.types""} AwsCryptographyPrimitivesTypes {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8
  datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)

  datatype AES_CTR = AES_CTR(nameonly keyLength: SymmetricKeyLength, nameonly nonceLength: Uint8Bits)

  datatype AES_GCM = AES_GCM(nameonly keyLength: SymmetricKeyLength, nameonly tagLength: Uint8Bytes, nameonly ivLength: Uint8Bits)

  datatype AESDecryptInput = AESDecryptInput(nameonly encAlg: AES_GCM, nameonly key: seq<uint8>, nameonly cipherTxt: seq<uint8>, nameonly authTag: seq<uint8>, nameonly iv: seq<uint8>, nameonly aad: seq<uint8>)

  datatype AESEncryptInput = AESEncryptInput(nameonly encAlg: AES_GCM, nameonly iv: seq<uint8>, nameonly key: seq<uint8>, nameonly msg: seq<uint8>, nameonly aad: seq<uint8>)

  datatype AESEncryptOutput = AESEncryptOutput(nameonly cipherText: seq<uint8>, nameonly authTag: seq<uint8>)

  datatype AesKdfCtrInput = AesKdfCtrInput(nameonly ikm: seq<uint8>, nameonly expectedLength: PositiveInteger, nameonly nonce: Option<seq<uint8>>)

  class IAwsCryptographicPrimitivesClientCallHistory {
    ghost constructor ()
    {
      GenerateRandomBytes := [];
      Digest := [];
      HMac := [];
      HkdfExtract := [];
      HkdfExpand := [];
      Hkdf := [];
      KdfCounterMode := [];
      AesKdfCounterMode := [];
      AESEncrypt := [];
      AESDecrypt := [];
      GenerateRSAKeyPair := [];
      GetRSAKeyModulusLength := [];
      RSADecrypt := [];
      RSAEncrypt := [];
      GenerateECDSASignatureKey := [];
      ECDSASign := [];
      ECDSAVerify := [];
    }

    ghost var GenerateRandomBytes: seq<DafnyCallEvent<GenerateRandomBytesInput, Result<seq<uint8>, Error>>>
    ghost var Digest: seq<DafnyCallEvent<DigestInput, Result<seq<uint8>, Error>>>
    ghost var HMac: seq<DafnyCallEvent<HMacInput, Result<seq<uint8>, Error>>>
    ghost var HkdfExtract: seq<DafnyCallEvent<HkdfExtractInput, Result<seq<uint8>, Error>>>
    ghost var HkdfExpand: seq<DafnyCallEvent<HkdfExpandInput, Result<seq<uint8>, Error>>>
    ghost var Hkdf: seq<DafnyCallEvent<HkdfInput, Result<seq<uint8>, Error>>>
    ghost var KdfCounterMode: seq<DafnyCallEvent<KdfCtrInput, Result<seq<uint8>, Error>>>
    ghost var AesKdfCounterMode: seq<DafnyCallEvent<AesKdfCtrInput, Result<seq<uint8>, Error>>>
    ghost var AESEncrypt: seq<DafnyCallEvent<AESEncryptInput, Result<AESEncryptOutput, Error>>>
    ghost var AESDecrypt: seq<DafnyCallEvent<AESDecryptInput, Result<seq<uint8>, Error>>>
    ghost var GenerateRSAKeyPair: seq<DafnyCallEvent<GenerateRSAKeyPairInput, Result<GenerateRSAKeyPairOutput, Error>>>
    ghost var GetRSAKeyModulusLength: seq<DafnyCallEvent<GetRSAKeyModulusLengthInput, Result<GetRSAKeyModulusLengthOutput, Error>>>
    ghost var RSADecrypt: seq<DafnyCallEvent<RSADecryptInput, Result<seq<uint8>, Error>>>
    ghost var RSAEncrypt: seq<DafnyCallEvent<RSAEncryptInput, Result<seq<uint8>, Error>>>
    ghost var GenerateECDSASignatureKey: seq<DafnyCallEvent<GenerateECDSASignatureKeyInput, Result<GenerateECDSASignatureKeyOutput, Error>>>
    ghost var ECDSASign: seq<DafnyCallEvent<ECDSASignInput, Result<seq<uint8>, Error>>>
    ghost var ECDSAVerify: seq<DafnyCallEvent<ECDSAVerifyInput, Result<bool, Error>>>
  }

  trait {:termination false} IAwsCryptographicPrimitivesClient {
    ghost const Modifies: set<object>

    predicate ValidState()
      ensures ValidState() ==> History in Modifies

    ghost const History: IAwsCryptographicPrimitivesClientCallHistory

    predicate GenerateRandomBytesEnsuresPublicly(input: GenerateRandomBytesInput, output: Result<seq<uint8>, Error>)
      decreases input, output

    method GenerateRandomBytes(input: GenerateRandomBytesInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GenerateRandomBytes
      ensures true && ValidState()
      ensures GenerateRandomBytesEnsuresPublicly(input, output)
      ensures History.GenerateRandomBytes == old(History.GenerateRandomBytes) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate DigestEnsuresPublicly(input: DigestInput, output: Result<seq<uint8>, Error>)
      decreases input, output

    method Digest(input: DigestInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`Digest
      ensures true && ValidState()
      ensures DigestEnsuresPublicly(input, output)
      ensures History.Digest == old(History.Digest) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    function method HMac(input: HMacInput): (output: Result<seq<uint8>, Error>)
      decreases input

    predicate HkdfExtractEnsuresPublicly(input: HkdfExtractInput, output: Result<seq<uint8>, Error>)
      decreases input, output

    method HkdfExtract(input: HkdfExtractInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`HkdfExtract
      ensures true && ValidState()
      ensures HkdfExtractEnsuresPublicly(input, output)
      ensures History.HkdfExtract == old(History.HkdfExtract) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate HkdfExpandEnsuresPublicly(input: HkdfExpandInput, output: Result<seq<uint8>, Error>)
      decreases input, output

    method HkdfExpand(input: HkdfExpandInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`HkdfExpand
      ensures true && ValidState()
      ensures HkdfExpandEnsuresPublicly(input, output)
      ensures History.HkdfExpand == old(History.HkdfExpand) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate HkdfEnsuresPublicly(input: HkdfInput, output: Result<seq<uint8>, Error>)
      decreases input, output

    method Hkdf(input: HkdfInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`Hkdf
      ensures true && ValidState()
      ensures HkdfEnsuresPublicly(input, output)
      ensures History.Hkdf == old(History.Hkdf) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate KdfCounterModeEnsuresPublicly(input: KdfCtrInput, output: Result<seq<uint8>, Error>)
      decreases input, output

    method KdfCounterMode(input: KdfCtrInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`KdfCounterMode
      ensures true && ValidState()
      ensures KdfCounterModeEnsuresPublicly(input, output)
      ensures History.KdfCounterMode == old(History.KdfCounterMode) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate AesKdfCounterModeEnsuresPublicly(input: AesKdfCtrInput, output: Result<seq<uint8>, Error>)
      decreases input, output

    method AesKdfCounterMode(input: AesKdfCtrInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`AesKdfCounterMode
      ensures true && ValidState()
      ensures AesKdfCounterModeEnsuresPublicly(input, output)
      ensures History.AesKdfCounterMode == old(History.AesKdfCounterMode) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate AESEncryptEnsuresPublicly(input: AESEncryptInput, output: Result<AESEncryptOutput, Error>)
      decreases input, output

    method AESEncrypt(input: AESEncryptInput) returns (output: Result<AESEncryptOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`AESEncrypt
      ensures true && ValidState()
      ensures AESEncryptEnsuresPublicly(input, output)
      ensures History.AESEncrypt == old(History.AESEncrypt) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate AESDecryptEnsuresPublicly(input: AESDecryptInput, output: Result<seq<uint8>, Error>)
      decreases input, output

    method AESDecrypt(input: AESDecryptInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`AESDecrypt
      ensures true && ValidState()
      ensures AESDecryptEnsuresPublicly(input, output)
      ensures History.AESDecrypt == old(History.AESDecrypt) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate GenerateRSAKeyPairEnsuresPublicly(input: GenerateRSAKeyPairInput, output: Result<GenerateRSAKeyPairOutput, Error>)
      decreases input, output

    method GenerateRSAKeyPair(input: GenerateRSAKeyPairInput) returns (output: Result<GenerateRSAKeyPairOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GenerateRSAKeyPair
      ensures true && ValidState()
      ensures GenerateRSAKeyPairEnsuresPublicly(input, output)
      ensures History.GenerateRSAKeyPair == old(History.GenerateRSAKeyPair) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    function method GetRSAKeyModulusLength(input: GetRSAKeyModulusLengthInput): (output: Result<GetRSAKeyModulusLengthOutput, Error>)
      decreases input

    predicate RSADecryptEnsuresPublicly(input: RSADecryptInput, output: Result<seq<uint8>, Error>)
      decreases input, output

    method RSADecrypt(input: RSADecryptInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`RSADecrypt
      ensures true && ValidState()
      ensures RSADecryptEnsuresPublicly(input, output)
      ensures History.RSADecrypt == old(History.RSADecrypt) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate RSAEncryptEnsuresPublicly(input: RSAEncryptInput, output: Result<seq<uint8>, Error>)
      decreases input, output

    method RSAEncrypt(input: RSAEncryptInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`RSAEncrypt
      ensures true && ValidState()
      ensures RSAEncryptEnsuresPublicly(input, output)
      ensures History.RSAEncrypt == old(History.RSAEncrypt) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate GenerateECDSASignatureKeyEnsuresPublicly(input: GenerateECDSASignatureKeyInput, output: Result<GenerateECDSASignatureKeyOutput, Error>)
      decreases input, output

    method GenerateECDSASignatureKey(input: GenerateECDSASignatureKeyInput) returns (output: Result<GenerateECDSASignatureKeyOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GenerateECDSASignatureKey
      ensures true && ValidState()
      ensures GenerateECDSASignatureKeyEnsuresPublicly(input, output)
      ensures History.GenerateECDSASignatureKey == old(History.GenerateECDSASignatureKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate ECDSASignEnsuresPublicly(input: ECDSASignInput, output: Result<seq<uint8>, Error>)
      decreases input, output

    method ECDSASign(input: ECDSASignInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ECDSASign
      ensures true && ValidState()
      ensures ECDSASignEnsuresPublicly(input, output)
      ensures History.ECDSASign == old(History.ECDSASign) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate ECDSAVerifyEnsuresPublicly(input: ECDSAVerifyInput, output: Result<bool, Error>)
      decreases input, output

    method ECDSAVerify(input: ECDSAVerifyInput) returns (output: Result<bool, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ECDSAVerify
      ensures true && ValidState()
      ensures ECDSAVerifyEnsuresPublicly(input, output)
      ensures History.ECDSAVerify == old(History.ECDSAVerify) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
  }

  datatype CryptoConfig = CryptoConfig

  datatype DigestAlgorithm = SHA_512 | SHA_384 | SHA_256

  datatype DigestInput = DigestInput(nameonly digestAlgorithm: DigestAlgorithm, nameonly message: seq<uint8>)

  datatype ECDSASignatureAlgorithm = ECDSA_P384 | ECDSA_P256

  datatype ECDSASignInput = ECDSASignInput(nameonly signatureAlgorithm: ECDSASignatureAlgorithm, nameonly signingKey: seq<uint8>, nameonly message: seq<uint8>)

  datatype ECDSAVerifyInput = ECDSAVerifyInput(nameonly signatureAlgorithm: ECDSASignatureAlgorithm, nameonly verificationKey: seq<uint8>, nameonly message: seq<uint8>, nameonly signature: seq<uint8>)

  datatype GenerateECDSASignatureKeyInput = GenerateECDSASignatureKeyInput(nameonly signatureAlgorithm: ECDSASignatureAlgorithm)

  datatype GenerateECDSASignatureKeyOutput = GenerateECDSASignatureKeyOutput(nameonly signatureAlgorithm: ECDSASignatureAlgorithm, nameonly verificationKey: seq<uint8>, nameonly signingKey: seq<uint8>)

  datatype GenerateRandomBytesInput = GenerateRandomBytesInput(nameonly length: PositiveInteger)

  datatype GenerateRSAKeyPairInput = GenerateRSAKeyPairInput(nameonly lengthBits: RSAModulusLengthBitsToGenerate)

  datatype GenerateRSAKeyPairOutput = GenerateRSAKeyPairOutput(nameonly publicKey: RSAPublicKey, nameonly privateKey: RSAPrivateKey)

  datatype GetRSAKeyModulusLengthInput = GetRSAKeyModulusLengthInput(nameonly publicKey: seq<uint8>)

  datatype GetRSAKeyModulusLengthOutput = GetRSAKeyModulusLengthOutput(nameonly length: RSAModulusLengthBits)

  datatype HkdfExpandInput = HkdfExpandInput(nameonly digestAlgorithm: DigestAlgorithm, nameonly prk: seq<uint8>, nameonly info: seq<uint8>, nameonly expectedLength: PositiveInteger)

  datatype HkdfExtractInput = HkdfExtractInput(nameonly digestAlgorithm: DigestAlgorithm, nameonly salt: Option<seq<uint8>>, nameonly ikm: seq<uint8>)

  datatype HkdfInput = HkdfInput(nameonly digestAlgorithm: DigestAlgorithm, nameonly salt: Option<seq<uint8>>, nameonly ikm: seq<uint8>, nameonly info: seq<uint8>, nameonly expectedLength: PositiveInteger)

  datatype HMacInput = HMacInput(nameonly digestAlgorithm: DigestAlgorithm, nameonly key: seq<uint8>, nameonly message: seq<uint8>)

  datatype KdfCtrInput = KdfCtrInput(nameonly digestAlgorithm: DigestAlgorithm, nameonly ikm: seq<uint8>, nameonly expectedLength: PositiveInteger, nameonly purpose: Option<seq<uint8>>, nameonly nonce: Option<seq<uint8>>)

  type PositiveInteger = x: int32
    | IsValid_PositiveInteger(x)
    witness *

  datatype RSADecryptInput = RSADecryptInput(nameonly padding: RSAPaddingMode, nameonly privateKey: seq<uint8>, nameonly cipherText: seq<uint8>)

  datatype RSAEncryptInput = RSAEncryptInput(nameonly padding: RSAPaddingMode, nameonly publicKey: seq<uint8>, nameonly plaintext: seq<uint8>)

  type RSAModulusLengthBits = x: int32
    | IsValid_RSAModulusLengthBits(x)
    witness *

  type RSAModulusLengthBitsToGenerate = x: int32
    | IsValid_RSAModulusLengthBitsToGenerate(x)
    witness *

  datatype RSAPaddingMode = PKCS1 | OAEP_SHA1 | OAEP_SHA256 | OAEP_SHA384 | OAEP_SHA512

  datatype RSAPrivateKey = RSAPrivateKey(nameonly lengthBits: RSAModulusLengthBits, nameonly pem: seq<uint8>)

  datatype RSAPublicKey = RSAPublicKey(nameonly lengthBits: RSAModulusLengthBits, nameonly pem: seq<uint8>)

  type SymmetricKeyLength = x: int32
    | IsValid_SymmetricKeyLength(x)
    witness *

  type Uint8Bits = x: int32
    | IsValid_Uint8Bits(x)
    witness *

  type Uint8Bytes = x: int32
    | IsValid_Uint8Bytes(x)
    witness *

  datatype Error = AwsCryptographicPrimitivesError(nameonly message: string) | CollectionOfErrors(list: seq<Error>, nameonly message: string) | Opaque(obj: object)

  type OpaqueError = e: Error
    | e.Opaque?
    witness *

  predicate method IsValid_PositiveInteger(x: int32)
    decreases x
  {
    0 <= x
  }

  predicate method IsValid_RSAModulusLengthBits(x: int32)
    decreases x
  {
    81 <= x
  }

  predicate method IsValid_RSAModulusLengthBitsToGenerate(x: int32)
    decreases x
  {
    81 <= x <= 4096
  }

  predicate method IsValid_SymmetricKeyLength(x: int32)
    decreases x
  {
    1 <= x <= 32
  }

  predicate method IsValid_Uint8Bits(x: int32)
    decreases x
  {
    0 <= x <= 255
  }

  predicate method IsValid_Uint8Bytes(x: int32)
    decreases x
  {
    0 <= x <= 32
  }
}

abstract module AbstractAwsCryptographyPrimitivesService {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = AwsCryptographyPrimitivesTypes

  import Operations : AbstractAwsCryptographyPrimitivesOperations
  class AtomicPrimitivesClient extends IAwsCryptographicPrimitivesClient {
    constructor (config: Operations.InternalConfig)
      requires Operations.ValidInternalConfig?(config)
      ensures ValidState() && fresh(History) && this.config == config

    const config: Operations.InternalConfig

    predicate ValidState()
      ensures ValidState() ==> Operations.ValidInternalConfig?(config) && History !in Operations.ModifiesInternalConfig(config) && Modifies == Operations.ModifiesInternalConfig(config) + {History}

    predicate GenerateRandomBytesEnsuresPublicly(input: GenerateRandomBytesInput, output: Result<seq<uint8>, Error>)
      decreases input, output
    {
      Operations.GenerateRandomBytesEnsuresPublicly(input, output)
    }

    method GenerateRandomBytes(input: GenerateRandomBytesInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GenerateRandomBytes
      ensures true && ValidState()
      ensures GenerateRandomBytesEnsuresPublicly(input, output)
      ensures History.GenerateRandomBytes == old(History.GenerateRandomBytes) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.GenerateRandomBytes(config, input);
      History.GenerateRandomBytes := History.GenerateRandomBytes + [DafnyCallEvent(input, output)];
    }

    predicate DigestEnsuresPublicly(input: DigestInput, output: Result<seq<uint8>, Error>)
      decreases input, output
    {
      Operations.DigestEnsuresPublicly(input, output)
    }

    method Digest(input: DigestInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`Digest
      ensures true && ValidState()
      ensures DigestEnsuresPublicly(input, output)
      ensures History.Digest == old(History.Digest) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.Digest(config, input);
      History.Digest := History.Digest + [DafnyCallEvent(input, output)];
    }

    function method HMac(input: HMacInput): (output: Result<seq<uint8>, Error>)
      decreases input
    {
      Operations.HMac(config, input)
    }

    predicate HkdfExtractEnsuresPublicly(input: HkdfExtractInput, output: Result<seq<uint8>, Error>)
      decreases input, output
    {
      Operations.HkdfExtractEnsuresPublicly(input, output)
    }

    method HkdfExtract(input: HkdfExtractInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`HkdfExtract
      ensures true && ValidState()
      ensures HkdfExtractEnsuresPublicly(input, output)
      ensures History.HkdfExtract == old(History.HkdfExtract) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.HkdfExtract(config, input);
      History.HkdfExtract := History.HkdfExtract + [DafnyCallEvent(input, output)];
    }

    predicate HkdfExpandEnsuresPublicly(input: HkdfExpandInput, output: Result<seq<uint8>, Error>)
      decreases input, output
    {
      Operations.HkdfExpandEnsuresPublicly(input, output)
    }

    method HkdfExpand(input: HkdfExpandInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`HkdfExpand
      ensures true && ValidState()
      ensures HkdfExpandEnsuresPublicly(input, output)
      ensures History.HkdfExpand == old(History.HkdfExpand) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.HkdfExpand(config, input);
      History.HkdfExpand := History.HkdfExpand + [DafnyCallEvent(input, output)];
    }

    predicate HkdfEnsuresPublicly(input: HkdfInput, output: Result<seq<uint8>, Error>)
      decreases input, output
    {
      Operations.HkdfEnsuresPublicly(input, output)
    }

    method Hkdf(input: HkdfInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`Hkdf
      ensures true && ValidState()
      ensures HkdfEnsuresPublicly(input, output)
      ensures History.Hkdf == old(History.Hkdf) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.Hkdf(config, input);
      History.Hkdf := History.Hkdf + [DafnyCallEvent(input, output)];
    }

    predicate KdfCounterModeEnsuresPublicly(input: KdfCtrInput, output: Result<seq<uint8>, Error>)
      decreases input, output
    {
      Operations.KdfCounterModeEnsuresPublicly(input, output)
    }

    method KdfCounterMode(input: KdfCtrInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`KdfCounterMode
      ensures true && ValidState()
      ensures KdfCounterModeEnsuresPublicly(input, output)
      ensures History.KdfCounterMode == old(History.KdfCounterMode) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.KdfCounterMode(config, input);
      History.KdfCounterMode := History.KdfCounterMode + [DafnyCallEvent(input, output)];
    }

    predicate AesKdfCounterModeEnsuresPublicly(input: AesKdfCtrInput, output: Result<seq<uint8>, Error>)
      decreases input, output
    {
      Operations.AesKdfCounterModeEnsuresPublicly(input, output)
    }

    method AesKdfCounterMode(input: AesKdfCtrInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`AesKdfCounterMode
      ensures true && ValidState()
      ensures AesKdfCounterModeEnsuresPublicly(input, output)
      ensures History.AesKdfCounterMode == old(History.AesKdfCounterMode) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.AesKdfCounterMode(config, input);
      History.AesKdfCounterMode := History.AesKdfCounterMode + [DafnyCallEvent(input, output)];
    }

    predicate AESEncryptEnsuresPublicly(input: AESEncryptInput, output: Result<AESEncryptOutput, Error>)
      decreases input, output
    {
      Operations.AESEncryptEnsuresPublicly(input, output)
    }

    method AESEncrypt(input: AESEncryptInput) returns (output: Result<AESEncryptOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`AESEncrypt
      ensures true && ValidState()
      ensures AESEncryptEnsuresPublicly(input, output)
      ensures History.AESEncrypt == old(History.AESEncrypt) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.AESEncrypt(config, input);
      History.AESEncrypt := History.AESEncrypt + [DafnyCallEvent(input, output)];
    }

    predicate AESDecryptEnsuresPublicly(input: AESDecryptInput, output: Result<seq<uint8>, Error>)
      decreases input, output
    {
      Operations.AESDecryptEnsuresPublicly(input, output)
    }

    method AESDecrypt(input: AESDecryptInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`AESDecrypt
      ensures true && ValidState()
      ensures AESDecryptEnsuresPublicly(input, output)
      ensures History.AESDecrypt == old(History.AESDecrypt) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.AESDecrypt(config, input);
      History.AESDecrypt := History.AESDecrypt + [DafnyCallEvent(input, output)];
    }

    predicate GenerateRSAKeyPairEnsuresPublicly(input: GenerateRSAKeyPairInput, output: Result<GenerateRSAKeyPairOutput, Error>)
      decreases input, output
    {
      Operations.GenerateRSAKeyPairEnsuresPublicly(input, output)
    }

    method GenerateRSAKeyPair(input: GenerateRSAKeyPairInput) returns (output: Result<GenerateRSAKeyPairOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GenerateRSAKeyPair
      ensures true && ValidState()
      ensures GenerateRSAKeyPairEnsuresPublicly(input, output)
      ensures History.GenerateRSAKeyPair == old(History.GenerateRSAKeyPair) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.GenerateRSAKeyPair(config, input);
      History.GenerateRSAKeyPair := History.GenerateRSAKeyPair + [DafnyCallEvent(input, output)];
    }

    function method GetRSAKeyModulusLength(input: GetRSAKeyModulusLengthInput): (output: Result<GetRSAKeyModulusLengthOutput, Error>)
      decreases input
    {
      Operations.GetRSAKeyModulusLength(config, input)
    }

    predicate RSADecryptEnsuresPublicly(input: RSADecryptInput, output: Result<seq<uint8>, Error>)
      decreases input, output
    {
      Operations.RSADecryptEnsuresPublicly(input, output)
    }

    method RSADecrypt(input: RSADecryptInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`RSADecrypt
      ensures true && ValidState()
      ensures RSADecryptEnsuresPublicly(input, output)
      ensures History.RSADecrypt == old(History.RSADecrypt) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.RSADecrypt(config, input);
      History.RSADecrypt := History.RSADecrypt + [DafnyCallEvent(input, output)];
    }

    predicate RSAEncryptEnsuresPublicly(input: RSAEncryptInput, output: Result<seq<uint8>, Error>)
      decreases input, output
    {
      Operations.RSAEncryptEnsuresPublicly(input, output)
    }

    method RSAEncrypt(input: RSAEncryptInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`RSAEncrypt
      ensures true && ValidState()
      ensures RSAEncryptEnsuresPublicly(input, output)
      ensures History.RSAEncrypt == old(History.RSAEncrypt) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.RSAEncrypt(config, input);
      History.RSAEncrypt := History.RSAEncrypt + [DafnyCallEvent(input, output)];
    }

    predicate GenerateECDSASignatureKeyEnsuresPublicly(input: GenerateECDSASignatureKeyInput, output: Result<GenerateECDSASignatureKeyOutput, Error>)
      decreases input, output
    {
      Operations.GenerateECDSASignatureKeyEnsuresPublicly(input, output)
    }

    method GenerateECDSASignatureKey(input: GenerateECDSASignatureKeyInput) returns (output: Result<GenerateECDSASignatureKeyOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GenerateECDSASignatureKey
      ensures true && ValidState()
      ensures GenerateECDSASignatureKeyEnsuresPublicly(input, output)
      ensures History.GenerateECDSASignatureKey == old(History.GenerateECDSASignatureKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.GenerateECDSASignatureKey(config, input);
      History.GenerateECDSASignatureKey := History.GenerateECDSASignatureKey + [DafnyCallEvent(input, output)];
    }

    predicate ECDSASignEnsuresPublicly(input: ECDSASignInput, output: Result<seq<uint8>, Error>)
      decreases input, output
    {
      Operations.ECDSASignEnsuresPublicly(input, output)
    }

    method ECDSASign(input: ECDSASignInput) returns (output: Result<seq<uint8>, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ECDSASign
      ensures true && ValidState()
      ensures ECDSASignEnsuresPublicly(input, output)
      ensures History.ECDSASign == old(History.ECDSASign) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.ECDSASign(config, input);
      History.ECDSASign := History.ECDSASign + [DafnyCallEvent(input, output)];
    }

    predicate ECDSAVerifyEnsuresPublicly(input: ECDSAVerifyInput, output: Result<bool, Error>)
      decreases input, output
    {
      Operations.ECDSAVerifyEnsuresPublicly(input, output)
    }

    method ECDSAVerify(input: ECDSAVerifyInput) returns (output: Result<bool, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ECDSAVerify
      ensures true && ValidState()
      ensures ECDSAVerifyEnsuresPublicly(input, output)
      ensures History.ECDSAVerify == old(History.ECDSAVerify) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.ECDSAVerify(config, input);
      History.ECDSAVerify := History.ECDSAVerify + [DafnyCallEvent(input, output)];
    }
  }

  function method DefaultCryptoConfig(): CryptoConfig

  method AtomicPrimitives(config: CryptoConfig := DefaultCryptoConfig()) returns (res: Result<AtomicPrimitivesClient, Error>)
    ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
    decreases config
}

abstract module AbstractAwsCryptographyPrimitivesOperations {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = AwsCryptographyPrimitivesTypes
  type InternalConfig

  predicate ValidInternalConfig?(config: InternalConfig)

  function ModifiesInternalConfig(config: InternalConfig): set<object>

  predicate GenerateRandomBytesEnsuresPublicly(input: GenerateRandomBytesInput, output: Result<seq<uint8>, Error>)
    decreases input, output

  method GenerateRandomBytes(config: InternalConfig, input: GenerateRandomBytesInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GenerateRandomBytesEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate DigestEnsuresPublicly(input: DigestInput, output: Result<seq<uint8>, Error>)
    decreases input, output

  method Digest(config: InternalConfig, input: DigestInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures DigestEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  function method HMac(config: InternalConfig, input: HMacInput): (output: Result<seq<uint8>, Error>)
    decreases input

  predicate HkdfExtractEnsuresPublicly(input: HkdfExtractInput, output: Result<seq<uint8>, Error>)
    decreases input, output

  method HkdfExtract(config: InternalConfig, input: HkdfExtractInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures HkdfExtractEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate HkdfExpandEnsuresPublicly(input: HkdfExpandInput, output: Result<seq<uint8>, Error>)
    decreases input, output

  method HkdfExpand(config: InternalConfig, input: HkdfExpandInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures HkdfExpandEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate HkdfEnsuresPublicly(input: HkdfInput, output: Result<seq<uint8>, Error>)
    decreases input, output

  method Hkdf(config: InternalConfig, input: HkdfInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures HkdfEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate KdfCounterModeEnsuresPublicly(input: KdfCtrInput, output: Result<seq<uint8>, Error>)
    decreases input, output

  method KdfCounterMode(config: InternalConfig, input: KdfCtrInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures KdfCounterModeEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate AesKdfCounterModeEnsuresPublicly(input: AesKdfCtrInput, output: Result<seq<uint8>, Error>)
    decreases input, output

  method AesKdfCounterMode(config: InternalConfig, input: AesKdfCtrInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures AesKdfCounterModeEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate AESEncryptEnsuresPublicly(input: AESEncryptInput, output: Result<AESEncryptOutput, Error>)
    decreases input, output

  method AESEncrypt(config: InternalConfig, input: AESEncryptInput) returns (output: Result<AESEncryptOutput, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures AESEncryptEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate AESDecryptEnsuresPublicly(input: AESDecryptInput, output: Result<seq<uint8>, Error>)
    decreases input, output

  method AESDecrypt(config: InternalConfig, input: AESDecryptInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures AESDecryptEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate GenerateRSAKeyPairEnsuresPublicly(input: GenerateRSAKeyPairInput, output: Result<GenerateRSAKeyPairOutput, Error>)
    decreases input, output

  method GenerateRSAKeyPair(config: InternalConfig, input: GenerateRSAKeyPairInput) returns (output: Result<GenerateRSAKeyPairOutput, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GenerateRSAKeyPairEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  function method GetRSAKeyModulusLength(config: InternalConfig, input: GetRSAKeyModulusLengthInput): (output: Result<GetRSAKeyModulusLengthOutput, Error>)
    decreases input

  predicate RSADecryptEnsuresPublicly(input: RSADecryptInput, output: Result<seq<uint8>, Error>)
    decreases input, output

  method RSADecrypt(config: InternalConfig, input: RSADecryptInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures RSADecryptEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate RSAEncryptEnsuresPublicly(input: RSAEncryptInput, output: Result<seq<uint8>, Error>)
    decreases input, output

  method RSAEncrypt(config: InternalConfig, input: RSAEncryptInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures RSAEncryptEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate GenerateECDSASignatureKeyEnsuresPublicly(input: GenerateECDSASignatureKeyInput, output: Result<GenerateECDSASignatureKeyOutput, Error>)
    decreases input, output

  method GenerateECDSASignatureKey(config: InternalConfig, input: GenerateECDSASignatureKeyInput) returns (output: Result<GenerateECDSASignatureKeyOutput, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GenerateECDSASignatureKeyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate ECDSASignEnsuresPublicly(input: ECDSASignInput, output: Result<seq<uint8>, Error>)
    decreases input, output

  method ECDSASign(config: InternalConfig, input: ECDSASignInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ECDSASignEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate ECDSAVerifyEnsuresPublicly(input: ECDSAVerifyInput, output: Result<bool, Error>)
    decreases input, output

  method ECDSAVerify(config: InternalConfig, input: ECDSAVerifyInput) returns (output: Result<bool, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ECDSAVerifyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
}

module AwsCryptographyPrimitivesOperations refines AbstractAwsCryptographyPrimitivesOperations {

  import Random

  import AESEncryption

  import D = Digest

  import WrappedHMAC

  import WrappedHKDF

  import Signature

  import KdfCtr

  import RSAEncryption
  datatype Config = Config

  type InternalConfig = Config

  predicate ValidInternalConfig?(config: InternalConfig)
    decreases config
  {
    true
  }

  function ModifiesInternalConfig(config: InternalConfig): set<object>
    decreases config
  {
    {}
  }

  predicate GenerateRandomBytesEnsuresPublicly(input: GenerateRandomBytesInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    output.Success? ==>
      |output.value| == input.length as int
  }

  method GenerateRandomBytes(config: InternalConfig, input: GenerateRandomBytesInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GenerateRandomBytesEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := Random.GenerateBytes(input.length);
  }

  predicate DigestEnsuresPublicly(input: DigestInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    output.Success? ==>
      |output.value| == D.Length(input.digestAlgorithm)
  }

  method Digest(config: InternalConfig, input: DigestInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures DigestEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := D.Digest(input);
  }

  predicate HMacEnsuresPublicly(input: HMacInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    true
  }

  function method HMac(config: InternalConfig, input: HMacInput): (output: Result<seq<uint8>, Error>)
    decreases config, input
  {
    WrappedHMAC.Digest(input)
  }

  predicate HkdfExtractEnsuresPublicly(input: HkdfExtractInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    true
  }

  method HkdfExtract(config: InternalConfig, input: HkdfExtractInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures HkdfExtractEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := WrappedHKDF.Extract(input);
  }

  predicate HkdfExpandEnsuresPublicly(input: HkdfExpandInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    output.Success? ==>
      true &&
      |output.value| == input.expectedLength as nat
  }

  method HkdfExpand(config: InternalConfig, input: HkdfExpandInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures HkdfExpandEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := WrappedHKDF.Expand(input);
  }

  predicate HkdfEnsuresPublicly(input: HkdfInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    output.Success? ==>
      true &&
      |output.value| == input.expectedLength as nat
  }

  method Hkdf(config: InternalConfig, input: HkdfInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures HkdfEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := WrappedHKDF.Hkdf(input);
  }

  predicate KdfCounterModeEnsuresPublicly(input: KdfCtrInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    output.Success? ==>
      true &&
      |output.value| == input.expectedLength as nat
  }

  method KdfCounterMode(config: InternalConfig, input: KdfCtrInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures KdfCounterModeEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := KdfCtr.KdfCounterMode(input);
  }

  predicate AesKdfCounterModeEnsuresPublicly(input: AesKdfCtrInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    output.Success? ==>
      true &&
      |output.value| == input.expectedLength as nat
  }

  method AesKdfCounterMode(config: InternalConfig, input: AesKdfCtrInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures AesKdfCounterModeEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := Failure(Types.AwsCryptographicPrimitivesError(message := ""Implement""));
  }

  predicate AESEncryptEnsuresPublicly(input: AESEncryptInput, output: Result<AESEncryptOutput, Error>)
    decreases input, output
  {
    true &&
    output.Success? ==>
      |output.value.cipherText| == |input.msg| &&
      |output.value.authTag| == input.encAlg.tagLength as nat
  }

  method AESEncrypt(config: InternalConfig, input: AESEncryptInput) returns (output: Result<AESEncryptOutput, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures AESEncryptEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := AESEncryption.AESEncrypt(input);
  }

  predicate AESDecryptEnsuresPublicly(input: AESDecryptInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    true &&
    output.Success? ==>
      true &&
      |output.value| == |input.cipherTxt|
  }

  method AESDecrypt(config: InternalConfig, input: AESDecryptInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures AESDecryptEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := AESEncryption.AESDecrypt(input);
  }

  predicate GenerateRSAKeyPairEnsuresPublicly(input: GenerateRSAKeyPairInput, output: Result<GenerateRSAKeyPairOutput, Error>)
    decreases input, output
  {
    true
  }

  method GenerateRSAKeyPair(config: InternalConfig, input: GenerateRSAKeyPairInput) returns (output: Result<GenerateRSAKeyPairOutput, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GenerateRSAKeyPairEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    var publicKey, privateKey := RSAEncryption.GenerateKeyPair(input.lengthBits);
    output := Success(GenerateRSAKeyPairOutput(publicKey := publicKey, privateKey := privateKey));
  }

  predicate GetRSAKeyModulusLengthEnsuresPublicly(input: GetRSAKeyModulusLengthInput, output: Result<GetRSAKeyModulusLengthOutput, Error>)
    decreases input, output
  {
    true
  }

  function method GetRSAKeyModulusLength(config: InternalConfig, input: GetRSAKeyModulusLengthInput): (output: Result<GetRSAKeyModulusLengthOutput, Error>)
    decreases config, input
  {
    var length: Types.RSAModulusLengthBits :- RSAEncryption.GetRSAKeyModulusLength(input.publicKey); Success(GetRSAKeyModulusLengthOutput(length := length))
  }

  predicate RSADecryptEnsuresPublicly(input: RSADecryptInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    true
  }

  method RSADecrypt(config: InternalConfig, input: RSADecryptInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures RSADecryptEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := RSAEncryption.Decrypt(input);
  }

  predicate RSAEncryptEnsuresPublicly(input: RSAEncryptInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    true
  }

  method RSAEncrypt(config: InternalConfig, input: RSAEncryptInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures RSAEncryptEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := RSAEncryption.Encrypt(input);
  }

  predicate GenerateECDSASignatureKeyEnsuresPublicly(input: GenerateECDSASignatureKeyInput, output: Result<GenerateECDSASignatureKeyOutput, Error>)
    decreases input, output
  {
    true
  }

  method GenerateECDSASignatureKey(config: InternalConfig, input: GenerateECDSASignatureKeyInput) returns (output: Result<GenerateECDSASignatureKeyOutput, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GenerateECDSASignatureKeyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := Signature.KeyGen(input);
  }

  predicate ECDSASignEnsuresPublicly(input: ECDSASignInput, output: Result<seq<uint8>, Error>)
    decreases input, output
  {
    true
  }

  method ECDSASign(config: InternalConfig, input: ECDSASignInput) returns (output: Result<seq<uint8>, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ECDSASignEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := Signature.Sign(input.signatureAlgorithm, input.signingKey, input.message);
  }

  predicate ECDSAVerifyEnsuresPublicly(input: ECDSAVerifyInput, output: Result<bool, Error>)
    decreases input, output
  {
    true
  }

  method ECDSAVerify(config: InternalConfig, input: ECDSAVerifyInput) returns (output: Result<bool, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ECDSAVerifyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    output := Signature.Verify(input.signatureAlgorithm, input.verificationKey, input.message, input.signature);
  }

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = AwsCryptographyPrimitivesTypes
}

module Random {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import ExternRandom

  import Types = AwsCryptographyPrimitivesTypes
  method GenerateBytes(i: int32) returns (res: Result<seq<uint8>, Types.Error>)
    requires 0 <= i
    ensures res.Success? ==> |res.value| == i as int
    decreases i
  {
    var value :- ExternRandom.GenerateBytes(i);
    :- Need(|value| == i as int, Types.AwsCryptographicPrimitivesError(message := ""Incorrect length from ExternRandom.""));
    return Success(value);
  }
}

module {:extern ""ExternRandom""} ExternRandom {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes
  method {:extern} GenerateBytes(i: int32) returns (res: Result<seq<uint8>, Types.OpaqueError>)
    decreases i
}

module {:options ""-functionSyntax:4""} WrappedHMAC {

  import opened StandardLibrary

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes

  import HMAC
  function method Digest(input: Types.HMacInput): (output: Result<seq<uint8>, Types.Error>)
    decreases input
  {
    Need(0 < |input.key|, Types.AwsCryptographicPrimitivesError(message := ""Key MUST NOT be 0 bytes."")); Need(|input.message| < INT32_MAX_LIMIT, Types.AwsCryptographicPrimitivesError(message := ""Message over INT32_MAX_LIMIT"")); var value: seq<uint8> :- HMAC.Digest(input); Success(value)
  }
}

module {:options ""-functionSyntax:4""} {:extern ""HMAC""} HMAC {

  import opened Wrappers

  import opened StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes

  import HashDigest = Digest
  class {:extern ""HMac""} HMac {
    function {:extern} GetKey(): seq<uint8>
      reads this
      decreases {this}

    function {:extern} GetDigest(): Types.DigestAlgorithm
      reads this
      decreases {this}

    function {:extern} GetInputSoFar(): seq<uint8>
      reads this
      decreases {this}

    static method {:extern} Build(digest: Types.DigestAlgorithm) returns (output: Result<HMac, Types.Error>)
      ensures output.Success? ==> output.value.GetDigest() == digest && output.value.GetInputSoFar() == [] && fresh(output.value)
      decreases digest

    method {:extern ""Init""} Init(key: seq<uint8>)
      requires 0 < |key|
      modifies this
      ensures this.GetKey() == key
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetInputSoFar() == []
      decreases key

    method {:extern ""BlockUpdate""} Update(input: seq<uint8>)
      requires |this.GetKey()| > 0
      requires |input| < INT32_MAX_LIMIT
      modifies this
      ensures this.GetInputSoFar() == old(this.GetInputSoFar()) + input
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetKey() == old(this.GetKey())
      decreases input

    method {:extern ""GetResult""} GetResult() returns (s: seq<uint8>)
      requires |this.GetKey()| > 0
      modifies this
      ensures |s| == HashDigest.Length(this.GetDigest())
      ensures this.GetInputSoFar() == []
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetKey() == old(this.GetKey())
      ensures this.HashSignature(old(this.GetInputSoFar()), s)

    predicate method {:axiom} HashSignature(message: seq<uint8>, s: seq<uint8>)
      decreases message, s
  }

  function method {:extern ""Digest""} Digest(input: Types.HMacInput): (output: Result<seq<uint8>, Types.Error>)
    ensures output.Success? ==> |output.value| == HashDigest.Length(input.digestAlgorithm)
    decreases input
}

module Digest {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes

  import ExternDigest
  function method Length(digestAlgorithm: Types.DigestAlgorithm): nat
    decreases digestAlgorithm
  {
    match digestAlgorithm
    case SHA_512() =>
      64
    case SHA_384() =>
      48
    case SHA_256() =>
      32
    case SHA_1 =>
      20
  }

  method Digest(input: Types.DigestInput) returns (res: Result<seq<uint8>, Types.Error>)
    ensures res.Success? ==> |res.value| == Length(input.digestAlgorithm)
    decreases input
  {
    var DigestInput(digestAlgorithm, message) := input;
    var value :- ExternDigest.Digest(digestAlgorithm, message);
    :- Need(|value| == Length(digestAlgorithm), Types.AwsCryptographicPrimitivesError(message := ""Incorrect length digest from ExternDigest.""));
    return Success(value);
  }
}

module {:extern ""ExternDigest""} ExternDigest {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes
  method {:extern} Digest(alg: Types.DigestAlgorithm, msg: seq<uint8>) returns (res: Result<seq<uint8>, Types.Error>)
    decreases alg, msg
}

module WrappedHKDF {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import StandardLibrary

  import Types = AwsCryptographyPrimitivesTypes

  import HMAC

  import HKDF

  import Digest
  method Extract(input: Types.HkdfExtractInput) returns (output: Result<seq<uint8>, Types.Error>)
    decreases input
  {
    :- Need((input.salt.None? || |input.salt.value| != 0) && |input.ikm| < INT32_MAX_LIMIT, Types.AwsCryptographicPrimitivesError(message := ""HKDF Extract needs a salt and reasonable ikm.""));
    var HkdfExtractInput(digestAlgorithm, salt, ikm) := input;
    var hmac :- HMAC.HMac.Build(digestAlgorithm);
    var prk := HKDF.Extract(hmac, salt.UnwrapOr(StandardLibrary.Fill(0, Digest.Length(digestAlgorithm))), ikm, digestAlgorithm);
    return Success(prk);
  }

  method Expand(input: Types.HkdfExpandInput) returns (output: Result<seq<uint8>, Types.Error>)
    ensures output.Success? ==> |output.value| == input.expectedLength as nat
    decreases input
  {
    :- Need(1 <= input.expectedLength as int <= 255 * Digest.Length(input.digestAlgorithm) && |input.info| < INT32_MAX_LIMIT && Digest.Length(input.digestAlgorithm) == |input.prk|, Types.AwsCryptographicPrimitivesError(message := ""HKDF Expand needs valid input.""));
    var HkdfExpandInput(digestAlgorithm, prk, info, expectedLength) := input;
    var hmac :- HMAC.HMac.Build(digestAlgorithm);
    var omk, _ /* _v0 */ := HKDF.Expand(hmac, prk, info, expectedLength as int, digestAlgorithm);
    return Success(omk);
  }

  method Hkdf(input: Types.HkdfInput) returns (output: Result<seq<uint8>, Types.Error>)
    ensures output.Success? ==> |output.value| == input.expectedLength as nat
    decreases input
  {
    :- Need(1 <= input.expectedLength as int <= 255 * Digest.Length(input.digestAlgorithm) && (input.salt.None? || |input.salt.value| != 0) && |input.info| < INT32_MAX_LIMIT && |input.ikm| < INT32_MAX_LIMIT, Types.AwsCryptographicPrimitivesError(message := ""Wrapped Hkdf input is invalid.""));
    var HkdfInput(digest, salt, ikm, info, expectedLength) := input;
    var okm := HKDF.Hkdf(digest, salt, ikm, info, expectedLength as int);
    return Success(okm);
  }
}

module HKDF {

  import opened HMAC

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes

  import Digest
  method Extract(hmac: HMac, salt: seq<uint8>, ikm: seq<uint8>, ghost digest: Types.DigestAlgorithm)
      returns (prk: seq<uint8>)
    requires hmac.GetDigest() == digest
    requires |salt| != 0
    requires |ikm| < INT32_MAX_LIMIT
    modifies hmac
    ensures Digest.Length(hmac.GetDigest()) == |prk|
    ensures hmac.GetKey() == salt
    ensures hmac.GetDigest() == digest
    decreases hmac, salt, ikm, digest
  {
    hmac.Init(salt);
    hmac.Update(ikm);
    assert hmac.GetInputSoFar() == ikm;
    prk := hmac.GetResult();
    return prk;
  }

  predicate T(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 0 <= n < 256
    decreases n
  {
    if n == 0 then
      [] == res
    else
      ghost var nMinusOne: int := n - 1; exists prev1: seq<uint8>, prev2: seq<uint8> {:trigger prev1 + prev2} {:trigger Ti(hmac, info, n, prev2), T(hmac, info, nMinusOne, prev1)} :: T(hmac, info, nMinusOne, prev1) && Ti(hmac, info, n, prev2) && prev1 + prev2 == res
  }

  predicate Ti(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 0 <= n < 256
    decreases n, 1
  {
    if n == 0 then
      res == []
    else
      exists prev: seq<uint8> {:trigger hmac.HashSignature(prev, res)} {:trigger PreTi(hmac, info, n, prev)} :: PreTi(hmac, info, n, prev) && hmac.HashSignature(prev, res)
  }

  predicate PreTi(hmac: HMac, info: seq<uint8>, n: nat, res: seq<uint8>)
    requires 1 <= n < 256
    decreases n, 0
  {
    ghost var nMinusOne: int := n - 1;
    exists prev: seq<uint8> {:trigger prev + info} {:trigger Ti(hmac, info, nMinusOne, prev)} | Ti(hmac, info, nMinusOne, prev) :: 
      res == prev + info + [n as uint8]
  }

  method Expand(hmac: HMac, prk: seq<uint8>, info: seq<uint8>, expectedLength: int, digest: Types.DigestAlgorithm)
      returns (okm: seq<uint8>, ghost okmUnabridged: seq<uint8>)
    requires hmac.GetDigest() == digest
    requires 1 <= expectedLength <= 255 * Digest.Length(hmac.GetDigest())
    requires |info| < INT32_MAX_LIMIT
    requires Digest.Length(hmac.GetDigest()) == |prk|
    modifies hmac
    ensures |okm| == expectedLength
    ensures hmac.GetKey() == prk
    ensures hmac.GetDigest() == digest
    ensures var n: int := (Digest.Length(digest) + expectedLength - 1) / Digest.Length(digest); T(hmac, info, n, okmUnabridged) && (|okmUnabridged| <= expectedLength ==> okm == okmUnabridged) && (expectedLength < |okmUnabridged| ==> okm == okmUnabridged[..expectedLength])
    decreases hmac, prk, info, expectedLength, digest
  {
    var hashLength := Digest.Length(digest);
    var n := (hashLength + expectedLength - 1) / hashLength;
    assert 0 <= n < 256;
    hmac.Init(prk);
    var t_prev := [];
    var t_n := t_prev;
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant |t_prev| == if i == 1 then 0 else hashLength
      invariant hashLength == |prk|
      invariant |t_n| == (i - 1) * hashLength
      invariant hmac.GetKey() == prk
      invariant hmac.GetDigest() == digest
      invariant hmac.GetInputSoFar() == []
      invariant T(hmac, info, i - 1, t_n)
      invariant Ti(hmac, info, i - 1, t_prev)
      decreases n - i
    {
      hmac.Update(t_prev);
      hmac.Update(info);
      hmac.Update([i as uint8]);
      assert hmac.GetInputSoFar() == t_prev + info + [i as uint8];
      t_prev := hmac.GetResult();
      assert Ti(hmac, info, i, t_prev);
      t_n := t_n + t_prev;
      i := i + 1;
      assert T(hmac, info, i - 1, t_n);
    }
    okm := t_n;
    okmUnabridged := okm;
    assert T(hmac, info, n, okmUnabridged);
    if expectedLength < |okm| {
      okm := okm[..expectedLength];
    }
  }

  method Hkdf(digest: Types.DigestAlgorithm, salt: Option<seq<uint8>>, ikm: seq<uint8>, info: seq<uint8>, L: int)
      returns (okm: seq<uint8>)
    requires 0 <= L <= 255 * Digest.Length(digest)
    requires salt.None? || |salt.value| != 0
    requires |info| < INT32_MAX_LIMIT
    requires |ikm| < INT32_MAX_LIMIT
    ensures |okm| == L
    decreases digest, salt, ikm, info, L
  {
    if L == 0 {
      return [];
    }
    var hmac :- expect HMac.Build(digest);
    var hashLength := Digest.Length(digest);
    var nonEmptySalt: seq<uint8>;
    match salt {
      case {:split false} None() =>
        nonEmptySalt := StandardLibrary.Fill(0, hashLength);
      case {:split false} Some(s) =>
        nonEmptySalt := s;
    }
    var prk := Extract(hmac, nonEmptySalt, ikm, digest);
    ghost var okmUnabridged;
    okm, okmUnabridged := Expand(hmac, prk, info, L, digest);
  }
}

module KdfCtr {

  import opened StandardLibrary

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import UTF8

  import Types = AwsCryptographyPrimitivesTypes

  import HMAC

  import Digest
  const SEPARATION_INDICATOR: seq<uint8> := [0]
  const COUNTER_START_VALUE: uint32 := 1

  method KdfCounterMode(input: Types.KdfCtrInput) returns (output: Result<seq<uint8>, Types.Error>)
    ensures output.Success? ==> |output.value| == input.expectedLength as nat
    decreases input
  {
    :- Need(input.digestAlgorithm == Types.DigestAlgorithm.SHA_256 && |input.ikm| == 32 && input.nonce.Some? && |input.nonce.value| == 16 && input.expectedLength == 32 && 0 < (input.expectedLength as int * 8) as int < INT32_MAX_LIMIT, Types.AwsCryptographicPrimitivesError(message := ""Kdf in Counter Mode input is invalid.""));
    var ikm := input.ikm;
    var label_ := input.purpose.UnwrapOr([]);
    var info := input.nonce.UnwrapOr([]);
    var okm := [];
    var internalLength: uint32 := (4 + |SEPARATION_INDICATOR| + 4) as uint32;
    :- Need(true && internalLength as int + |label_| + |info| < INT32_MAX_LIMIT, Types.AwsCryptographicPrimitivesError(message := ""Input Length exceeds INT32_MAX_LIMIT""));
    var lengthBits: seq<uint8> := UInt.UInt32ToSeq((input.expectedLength * 8) as uint32);
    var explicitInfo := label_ + SEPARATION_INDICATOR + info + lengthBits;
    :- Need(4 + |explicitInfo| < INT32_MAX_LIMIT, Types.AwsCryptographicPrimitivesError(message := ""PRF input length exceeds INT32_MAX_LIMIT.""));
    okm :- RawDerive(ikm, explicitInfo, input.expectedLength, 0);
    return Success(okm);
  }

  method RawDerive(ikm: seq<uint8>, explicitInfo: seq<uint8>, length: int32, offset: int32)
      returns (output: Result<seq<uint8>, Types.Error>)
    requires |ikm| == 32 && length == 32 && 4 + |explicitInfo| < INT32_MAX_LIMIT && length as int + Digest.Length(Types.DigestAlgorithm.SHA_256) < INT32_MAX_LIMIT - 1
    ensures output.Success? ==> |output.value| == length as int
    decreases ikm, explicitInfo, length, offset
  {
    var derivationMac := Types.DigestAlgorithm.SHA_256;
    var hmac :- HMAC.HMac.Build(derivationMac);
    hmac.Init(key := ikm);
    var macLengthBytes := Digest.Length(derivationMac) as int32;
    var iterations := (length + macLengthBytes - 1) / macLengthBytes;
    var buffer := [];
    var i: seq<uint8> := UInt.UInt32ToSeq(COUNTER_START_VALUE);
    for iteration: BoundedInts.int32 := 1 to iterations + 1
      invariant |i| == 4
      invariant hmac.GetKey() == ikm
    {
      hmac.Update(i);
      hmac.Update(explicitInfo);
      var tmp := hmac.GetResult();
      buffer := buffer + tmp;
      i :- Increment(i);
    }
    :- Need(|buffer| >= length as int, Types.AwsCryptographicPrimitivesError(message := ""Failed to derive key of requested length""));
    return Success(buffer[..length]);
  }

  function method Increment(x: seq<uint8>): (ret: Result<seq<uint8>, Types.Error>)
    requires |x| == 4
    ensures ret.Success? ==> |ret.value| == 4
    decreases x
  {
    if x[3] < 255 then
      Success([x[0], x[1], x[2], x[3] + 1])
    else if x[2] < 255 then
      Success([x[0], x[1], x[2] + 1, 0])
    else if x[1] < 255 then
      Success([x[0], x[1] + 1, 0, 0])
    else if x[0] < 255 then
      Success([x[0] + 1, 0, 0, 0])
    else
      Failure(Types.AwsCryptographicPrimitivesError(message := ""Unable to derive key material; may have exceeded limit.""))
  }
}

module {:extern ""AESEncryption""} AESEncryption {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes
  predicate {:axiom} PlaintextDecryptedWithAAD(plaintext: seq<uint8>, aad: seq<uint8>)
    decreases plaintext, aad

  predicate {:axiom} EncryptionOutputEncryptedWithAAD(output: Types.AESEncryptOutput, aad: seq<uint8>)
    decreases output, aad

  predicate {:axiom} CiphertextGeneratedWithPlaintext(ciphertext: seq<uint8>, plaintext: seq<uint8>)
    decreases ciphertext, plaintext

  predicate {:axiom} EncryptedWithKey(ciphertext: seq<uint8>, key: seq<uint8>)
    decreases ciphertext, key

  predicate {:axiom} DecryptedWithKey(key: seq<uint8>, plaintext: seq<uint8>)
    decreases key, plaintext

  function method EncryptionOutputFromByteSeq(s: seq<uint8>, encAlg: Types.AES_GCM): (encArt: Types.AESEncryptOutput)
    requires 0 < encAlg.tagLength
    requires encAlg.tagLength as nat <= |s|
    ensures |encArt.cipherText + encArt.authTag| == |s|
    ensures |encArt.authTag| == encAlg.tagLength as int
    decreases s, encAlg
  {
    assert |s| - encAlg.tagLength as int <= |s|;
    var cipherText: seq<BoundedInts.uint8> := s[..|s| - encAlg.tagLength as int];
    var authTag: seq<BoundedInts.uint8> := s[|s| - encAlg.tagLength as int..];
    Types.AESEncryptOutput(cipherText := cipherText, authTag := authTag)
  }

  method {:extern ""AESEncryption.AES_GCM"", ""AESEncryptExtern""} AESEncryptExtern(encAlg: Types.AES_GCM, iv: seq<uint8>, key: seq<uint8>, msg: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<Types.AESEncryptOutput, Types.OpaqueError>)
    requires |iv| == encAlg.ivLength as int
    requires |key| == encAlg.keyLength as int
    ensures res.Success? ==> EncryptionOutputEncryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(res.value.cipherText, msg)
    ensures res.Success? ==> EncryptedWithKey(res.value.cipherText, key)
    decreases encAlg, iv, key, msg, aad

  method AESEncrypt(input: Types.AESEncryptInput) returns (res: Result<Types.AESEncryptOutput, Types.Error>)
    ensures res.Success? ==> |res.value.cipherText| == |input.msg| && |res.value.authTag| == input.encAlg.tagLength as int
    ensures res.Success? ==> EncryptionOutputEncryptedWithAAD(res.value, input.aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(res.value.cipherText, input.msg)
    ensures res.Success? ==> EncryptedWithKey(res.value.cipherText, input.key)
    ensures res.Success? ==> |res.value.authTag| == input.encAlg.tagLength as nat
    decreases input
  {
    :- Need(|input.iv| == input.encAlg.ivLength as int && |input.key| == input.encAlg.keyLength as int, Types.AwsCryptographicPrimitivesError(message := ""Request does not match algorithm.""));
    var AESEncryptInput(encAlg, iv, key, msg, aad) := input;
    var value :- AESEncryptExtern(encAlg, iv, key, msg, aad);
    :- Need(|value.cipherText| == |msg|, Types.AwsCryptographicPrimitivesError(message := ""AESEncrypt did not return cipherText of expected length""));
    :- Need(|value.authTag| == encAlg.tagLength as int, Types.AwsCryptographicPrimitivesError(message := ""AESEncryption did not return valid tag""));
    return Success(value);
  }

  method {:extern ""AESEncryption.AES_GCM"", ""AESDecryptExtern""} AESDecryptExtern(encAlg: Types.AES_GCM, key: seq<uint8>, cipherTxt: seq<uint8>, authTag: seq<uint8>, iv: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>, Types.OpaqueError>)
    requires |key| == encAlg.keyLength as int
    requires |iv| == encAlg.ivLength as int
    requires |authTag| == encAlg.tagLength as int
    ensures res.Success? ==> PlaintextDecryptedWithAAD(res.value, aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(cipherTxt, res.value)
    ensures res.Success? ==> DecryptedWithKey(key, res.value)
    decreases encAlg, key, cipherTxt, authTag, iv, aad

  method AESDecrypt(input: Types.AESDecryptInput) returns (res: Result<seq<uint8>, Types.Error>)
    ensures res.Success? ==> |res.value| == |input.cipherTxt|
    ensures res.Success? ==> PlaintextDecryptedWithAAD(res.value, input.aad)
    ensures res.Success? ==> CiphertextGeneratedWithPlaintext(input.cipherTxt, res.value)
    ensures res.Success? ==> DecryptedWithKey(input.key, res.value)
    decreases input
  {
    :- Need(|input.key| == input.encAlg.keyLength as int && |input.iv| == input.encAlg.ivLength as int && |input.authTag| == input.encAlg.tagLength as int, Types.AwsCryptographicPrimitivesError(message := ""Request does not match algorithm.""));
    var AESDecryptInput(encAlg, key, cipherTxt, authTag, iv, aad) := input;
    var value :- AESDecryptExtern(encAlg, key, cipherTxt, authTag, iv, aad);
    :- Need(|cipherTxt| == |value|, Types.AwsCryptographicPrimitivesError(message := ""AESDecrypt did not return plaintext of expected length""));
    return Success(value);
  }
}

module {:extern ""RSAEncryption""} RSAEncryption {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes
  method GenerateKeyPair(lengthBits: Types.RSAModulusLengthBitsToGenerate) returns (publicKey: Types.RSAPublicKey, privateKey: Types.RSAPrivateKey)
    decreases lengthBits
  {
    var pemPublic, pemPrivate := GenerateKeyPairExtern(lengthBits);
    privateKey := Types.RSAPrivateKey(pem := pemPrivate, lengthBits := lengthBits);
    publicKey := Types.RSAPublicKey(pem := pemPublic, lengthBits := lengthBits);
  }

  function method GetRSAKeyModulusLength(publicKey: seq<uint8>): (res: Result<Types.RSAModulusLengthBits, Types.Error>)
    decreases publicKey
  {
    var length: uint32 :- GetRSAKeyModulusLengthExtern(publicKey); Need(81 <= length as int < INT32_MAX_LIMIT, Types.AwsCryptographicPrimitivesError(message := ""Unsupported length for RSA modulus."")); Success(length as int32)
  }

  method Decrypt(input: Types.RSADecryptInput) returns (output: Result<seq<uint8>, Types.Error>)
    decreases input
  {
    :- Need(0 < |input.privateKey| && 0 < |input.cipherText|, Types.AwsCryptographicPrimitivesError(message := """"));
    output := DecryptExtern(input.padding, input.privateKey, input.cipherText);
  }

  method Encrypt(input: Types.RSAEncryptInput) returns (output: Result<seq<uint8>, Types.Error>)
    decreases input
  {
    :- Need(0 < |input.publicKey| && 0 < |input.plaintext|, Types.AwsCryptographicPrimitivesError(message := """"));
    output := EncryptExtern(input.padding, input.publicKey, input.plaintext);
  }

  method {:extern ""RSAEncryption.RSA"", ""GenerateKeyPairExtern""} GenerateKeyPairExtern(lengthBits: Types.RSAModulusLengthBitsToGenerate) returns (publicKey: seq<uint8>, privateKey: seq<uint8>)
    ensures |publicKey| > 0
    ensures |privateKey| > 0
    decreases lengthBits

  function method {:extern ""RSAEncryption.RSA"", ""GetRSAKeyModulusLengthExtern""} GetRSAKeyModulusLengthExtern(publicKey: seq<uint8>): (length: Result<uint32, Types.Error>)
    decreases publicKey

  method {:extern ""RSAEncryption.RSA"", ""DecryptExtern""} DecryptExtern(padding: Types.RSAPaddingMode, privateKey: seq<uint8>, cipherText: seq<uint8>)
      returns (res: Result<seq<uint8>, Types.Error>)
    requires |privateKey| > 0
    requires |cipherText| > 0
    decreases padding, privateKey, cipherText

  method {:extern ""RSAEncryption.RSA"", ""EncryptExtern""} EncryptExtern(padding: Types.RSAPaddingMode, publicKey: seq<uint8>, plaintextData: seq<uint8>)
      returns (res: Result<seq<uint8>, Types.Error>)
    requires |publicKey| > 0
    requires |plaintextData| > 0
    decreases padding, publicKey, plaintextData
}

module {:extern ""Signature""} Signature {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import Types = AwsCryptographyPrimitivesTypes
  datatype SignatureKeyPair = SignatureKeyPair(verificationKey: seq<uint8>, signingKey: seq<uint8>)

  predicate {:axiom} IsSigned(key: seq<uint8>, msg: seq<uint8>, signature: seq<uint8>)
    decreases key, msg, signature

  function method SignatureLength(signatureAlgorithm: Types.ECDSASignatureAlgorithm): uint16
    decreases signatureAlgorithm
  {
    match signatureAlgorithm
    case ECDSA_P256() =>
      71
    case ECDSA_P384() =>
      103
  }

  function method FieldSize(signatureAlgorithm: Types.ECDSASignatureAlgorithm): nat
    decreases signatureAlgorithm
  {
    match signatureAlgorithm
    case ECDSA_P256() =>
      assert 1 + (256 + 7) / 8 == 33; 33
    case ECDSA_P384() =>
      assert 1 + (384 + 7) / 8 == 49;
      49
  }

  predicate {:axiom} IsValidSignatureKeyPair(sigKeyPair: SignatureKeyPair)
    decreases sigKeyPair

  method KeyGen(input: Types.GenerateECDSASignatureKeyInput) returns (res: Result<Types.GenerateECDSASignatureKeyOutput, Types.Error>)
    ensures match res case Success(sigKeyPair) => true && |sigKeyPair.verificationKey| == FieldSize(input.signatureAlgorithm) case Failure(_ /* _v0 */) => true
    decreases input
  {
    var sigKeyPair :- ExternKeyGen(input.signatureAlgorithm);
    :- Need(|sigKeyPair.verificationKey| == FieldSize(input.signatureAlgorithm), Types.AwsCryptographicPrimitivesError(message := ""Incorrect verification-key length from ExternKeyGen.""));
    return Success(Types.GenerateECDSASignatureKeyOutput(signatureAlgorithm := input.signatureAlgorithm, verificationKey := sigKeyPair.verificationKey, signingKey := sigKeyPair.signingKey));
  }

  method {:extern ""Signature.ECDSA"", ""ExternKeyGen""} ExternKeyGen(s: Types.ECDSASignatureAlgorithm) returns (res: Result<SignatureKeyPair, Types.Error>)
    ensures res.Success? ==> IsValidSignatureKeyPair(res.value)
    decreases s

  method {:extern ""Signature.ECDSA"", ""Sign""} Sign(s: Types.ECDSASignatureAlgorithm, key: seq<uint8>, msg: seq<uint8>)
      returns (sig: Result<seq<uint8>, Types.Error>)
    ensures sig.Success? ==> IsSigned(key, msg, sig.value)
    decreases s, key, msg

  function method {:extern ""Signature.ECDSA"", ""Verify""} Verify(s: Types.ECDSASignatureAlgorithm, key: seq<uint8>, msg: seq<uint8>, sig: seq<uint8>): (res: Result<bool, Types.Error>)
    decreases s, key, msg, sig
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

module Aws {

  module Cryptography {

    module {:extern ""software.amazon.cryptography.primitives.internaldafny""} Primitives refines AbstractAwsCryptographyPrimitivesService {

      import Operations = AwsCryptographyPrimitivesOperations
      class AtomicPrimitivesClient ...  {
        predicate ValidState()
          ensures ValidState() ==> Operations.ValidInternalConfig?(config) && History !in Operations.ModifiesInternalConfig(config) && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        {
          Operations.ValidInternalConfig?(config) &&
          Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }

        constructor (config: Operations.InternalConfig)
          requires Operations.ValidInternalConfig?(config)
          ensures ValidState() && fresh(History) && this.config == config
          decreases config
        {
          this.config := config;
          History := new IAwsCryptographicPrimitivesClientCallHistory();
          Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }

        const config: Operations.InternalConfig

        predicate GenerateRandomBytesEnsuresPublicly(input: GenerateRandomBytesInput, output: Result<seq<uint8>, Error>)
          decreases input, output
        {
          Operations.GenerateRandomBytesEnsuresPublicly(input, output)
        }

        method GenerateRandomBytes(input: GenerateRandomBytesInput) returns (output: Result<seq<uint8>, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`GenerateRandomBytes
          ensures true && ValidState()
          ensures GenerateRandomBytesEnsuresPublicly(input, output)
          ensures History.GenerateRandomBytes == old(History.GenerateRandomBytes) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.GenerateRandomBytes(config, input);
          History.GenerateRandomBytes := History.GenerateRandomBytes + [DafnyCallEvent(input, output)];
        }

        predicate DigestEnsuresPublicly(input: DigestInput, output: Result<seq<uint8>, Error>)
          decreases input, output
        {
          Operations.DigestEnsuresPublicly(input, output)
        }

        method Digest(input: DigestInput) returns (output: Result<seq<uint8>, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`Digest
          ensures true && ValidState()
          ensures DigestEnsuresPublicly(input, output)
          ensures History.Digest == old(History.Digest) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.Digest(config, input);
          History.Digest := History.Digest + [DafnyCallEvent(input, output)];
        }

        function method HMac(input: HMacInput): (output: Result<seq<uint8>, Error>)
          decreases input
        {
          Operations.HMac(config, input)
        }

        predicate HkdfExtractEnsuresPublicly(input: HkdfExtractInput, output: Result<seq<uint8>, Error>)
          decreases input, output
        {
          Operations.HkdfExtractEnsuresPublicly(input, output)
        }

        method HkdfExtract(input: HkdfExtractInput) returns (output: Result<seq<uint8>, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`HkdfExtract
          ensures true && ValidState()
          ensures HkdfExtractEnsuresPublicly(input, output)
          ensures History.HkdfExtract == old(History.HkdfExtract) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.HkdfExtract(config, input);
          History.HkdfExtract := History.HkdfExtract + [DafnyCallEvent(input, output)];
        }

        predicate HkdfExpandEnsuresPublicly(input: HkdfExpandInput, output: Result<seq<uint8>, Error>)
          decreases input, output
        {
          Operations.HkdfExpandEnsuresPublicly(input, output)
        }

        method HkdfExpand(input: HkdfExpandInput) returns (output: Result<seq<uint8>, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`HkdfExpand
          ensures true && ValidState()
          ensures HkdfExpandEnsuresPublicly(input, output)
          ensures History.HkdfExpand == old(History.HkdfExpand) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.HkdfExpand(config, input);
          History.HkdfExpand := History.HkdfExpand + [DafnyCallEvent(input, output)];
        }

        predicate HkdfEnsuresPublicly(input: HkdfInput, output: Result<seq<uint8>, Error>)
          decreases input, output
        {
          Operations.HkdfEnsuresPublicly(input, output)
        }

        method Hkdf(input: HkdfInput) returns (output: Result<seq<uint8>, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`Hkdf
          ensures true && ValidState()
          ensures HkdfEnsuresPublicly(input, output)
          ensures History.Hkdf == old(History.Hkdf) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.Hkdf(config, input);
          History.Hkdf := History.Hkdf + [DafnyCallEvent(input, output)];
        }

        predicate KdfCounterModeEnsuresPublicly(input: KdfCtrInput, output: Result<seq<uint8>, Error>)
          decreases input, output
        {
          Operations.KdfCounterModeEnsuresPublicly(input, output)
        }

        method KdfCounterMode(input: KdfCtrInput) returns (output: Result<seq<uint8>, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`KdfCounterMode
          ensures true && ValidState()
          ensures KdfCounterModeEnsuresPublicly(input, output)
          ensures History.KdfCounterMode == old(History.KdfCounterMode) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.KdfCounterMode(config, input);
          History.KdfCounterMode := History.KdfCounterMode + [DafnyCallEvent(input, output)];
        }

        predicate AesKdfCounterModeEnsuresPublicly(input: AesKdfCtrInput, output: Result<seq<uint8>, Error>)
          decreases input, output
        {
          Operations.AesKdfCounterModeEnsuresPublicly(input, output)
        }

        method AesKdfCounterMode(input: AesKdfCtrInput) returns (output: Result<seq<uint8>, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`AesKdfCounterMode
          ensures true && ValidState()
          ensures AesKdfCounterModeEnsuresPublicly(input, output)
          ensures History.AesKdfCounterMode == old(History.AesKdfCounterMode) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.AesKdfCounterMode(config, input);
          History.AesKdfCounterMode := History.AesKdfCounterMode + [DafnyCallEvent(input, output)];
        }

        predicate AESEncryptEnsuresPublicly(input: AESEncryptInput, output: Result<AESEncryptOutput, Error>)
          decreases input, output
        {
          Operations.AESEncryptEnsuresPublicly(input, output)
        }

        method AESEncrypt(input: AESEncryptInput) returns (output: Result<AESEncryptOutput, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`AESEncrypt
          ensures true && ValidState()
          ensures AESEncryptEnsuresPublicly(input, output)
          ensures History.AESEncrypt == old(History.AESEncrypt) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.AESEncrypt(config, input);
          History.AESEncrypt := History.AESEncrypt + [DafnyCallEvent(input, output)];
        }

        predicate AESDecryptEnsuresPublicly(input: AESDecryptInput, output: Result<seq<uint8>, Error>)
          decreases input, output
        {
          Operations.AESDecryptEnsuresPublicly(input, output)
        }

        method AESDecrypt(input: AESDecryptInput) returns (output: Result<seq<uint8>, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`AESDecrypt
          ensures true && ValidState()
          ensures AESDecryptEnsuresPublicly(input, output)
          ensures History.AESDecrypt == old(History.AESDecrypt) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.AESDecrypt(config, input);
          History.AESDecrypt := History.AESDecrypt + [DafnyCallEvent(input, output)];
        }

        predicate GenerateRSAKeyPairEnsuresPublicly(input: GenerateRSAKeyPairInput, output: Result<GenerateRSAKeyPairOutput, Error>)
          decreases input, output
        {
          Operations.GenerateRSAKeyPairEnsuresPublicly(input, output)
        }

        method GenerateRSAKeyPair(input: GenerateRSAKeyPairInput) returns (output: Result<GenerateRSAKeyPairOutput, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`GenerateRSAKeyPair
          ensures true && ValidState()
          ensures GenerateRSAKeyPairEnsuresPublicly(input, output)
          ensures History.GenerateRSAKeyPair == old(History.GenerateRSAKeyPair) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.GenerateRSAKeyPair(config, input);
          History.GenerateRSAKeyPair := History.GenerateRSAKeyPair + [DafnyCallEvent(input, output)];
        }

        function method GetRSAKeyModulusLength(input: GetRSAKeyModulusLengthInput): (output: Result<GetRSAKeyModulusLengthOutput, Error>)
          decreases input
        {
          Operations.GetRSAKeyModulusLength(config, input)
        }

        predicate RSADecryptEnsuresPublicly(input: RSADecryptInput, output: Result<seq<uint8>, Error>)
          decreases input, output
        {
          Operations.RSADecryptEnsuresPublicly(input, output)
        }

        method RSADecrypt(input: RSADecryptInput) returns (output: Result<seq<uint8>, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`RSADecrypt
          ensures true && ValidState()
          ensures RSADecryptEnsuresPublicly(input, output)
          ensures History.RSADecrypt == old(History.RSADecrypt) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.RSADecrypt(config, input);
          History.RSADecrypt := History.RSADecrypt + [DafnyCallEvent(input, output)];
        }

        predicate RSAEncryptEnsuresPublicly(input: RSAEncryptInput, output: Result<seq<uint8>, Error>)
          decreases input, output
        {
          Operations.RSAEncryptEnsuresPublicly(input, output)
        }

        method RSAEncrypt(input: RSAEncryptInput) returns (output: Result<seq<uint8>, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`RSAEncrypt
          ensures true && ValidState()
          ensures RSAEncryptEnsuresPublicly(input, output)
          ensures History.RSAEncrypt == old(History.RSAEncrypt) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.RSAEncrypt(config, input);
          History.RSAEncrypt := History.RSAEncrypt + [DafnyCallEvent(input, output)];
        }

        predicate GenerateECDSASignatureKeyEnsuresPublicly(input: GenerateECDSASignatureKeyInput, output: Result<GenerateECDSASignatureKeyOutput, Error>)
          decreases input, output
        {
          Operations.GenerateECDSASignatureKeyEnsuresPublicly(input, output)
        }

        method GenerateECDSASignatureKey(input: GenerateECDSASignatureKeyInput) returns (output: Result<GenerateECDSASignatureKeyOutput, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`GenerateECDSASignatureKey
          ensures true && ValidState()
          ensures GenerateECDSASignatureKeyEnsuresPublicly(input, output)
          ensures History.GenerateECDSASignatureKey == old(History.GenerateECDSASignatureKey) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.GenerateECDSASignatureKey(config, input);
          History.GenerateECDSASignatureKey := History.GenerateECDSASignatureKey + [DafnyCallEvent(input, output)];
        }

        predicate ECDSASignEnsuresPublicly(input: ECDSASignInput, output: Result<seq<uint8>, Error>)
          decreases input, output
        {
          Operations.ECDSASignEnsuresPublicly(input, output)
        }

        method ECDSASign(input: ECDSASignInput) returns (output: Result<seq<uint8>, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`ECDSASign
          ensures true && ValidState()
          ensures ECDSASignEnsuresPublicly(input, output)
          ensures History.ECDSASign == old(History.ECDSASign) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.ECDSASign(config, input);
          History.ECDSASign := History.ECDSASign + [DafnyCallEvent(input, output)];
        }

        predicate ECDSAVerifyEnsuresPublicly(input: ECDSAVerifyInput, output: Result<bool, Error>)
          decreases input, output
        {
          Operations.ECDSAVerifyEnsuresPublicly(input, output)
        }

        method ECDSAVerify(input: ECDSAVerifyInput) returns (output: Result<bool, Error>)
          requires true && ValidState()
          modifies Modifies - {History}, History`ECDSAVerify
          ensures true && ValidState()
          ensures ECDSAVerifyEnsuresPublicly(input, output)
          ensures History.ECDSAVerify == old(History.ECDSAVerify) + [DafnyCallEvent(input, output)]
          decreases Modifies - {History}
        {
          output := Operations.ECDSAVerify(config, input);
          History.ECDSAVerify := History.ECDSAVerify + [DafnyCallEvent(input, output)];
        }
      }

      function method DefaultCryptoConfig(): CryptoConfig
      {
        CryptoConfig
      }

      method AtomicPrimitives(config: CryptoConfig := DefaultCryptoConfig()) returns (res: Result<AtomicPrimitivesClient, Error>)
        ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
        decreases config
      {
        var client := new AtomicPrimitivesClient(Operations.Config);
        return Success(client);
      }

      import opened Wrappers

      import opened UInt = StandardLibrary.UInt

      import opened UTF8

      import opened Types = AwsCryptographyPrimitivesTypes
    }
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
namespace software.amazon.cryptography.primitives.internaldafny.types {

  public interface _IDafnyCallEvent<I, O> {
    bool is_DafnyCallEvent { get; }
    I dtor_input { get; }
    O dtor_output { get; }
    _IDafnyCallEvent<__I, __O> DowncastClone<__I, __O>(Func<I, __I> converter0, Func<O, __O> converter1);
  }
  public class DafnyCallEvent<I, O> : _IDafnyCallEvent<I, O> {
    public readonly I _input;
    public readonly O _output;
    public DafnyCallEvent(I input, O output) {
      this._input = input;
      this._output = output;
    }
    public _IDafnyCallEvent<__I, __O> DowncastClone<__I, __O>(Func<I, __I> converter0, Func<O, __O> converter1) {
      if (this is _IDafnyCallEvent<__I, __O> dt) { return dt; }
      return new DafnyCallEvent<__I, __O>(converter0(_input), converter1(_output));
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.DafnyCallEvent<I, O>;
      return oth != null && object.Equals(this._input, oth._input) && object.Equals(this._output, oth._output);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._input));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._output));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.DafnyCallEvent.DafnyCallEvent";
      s += "(";
      s += Dafny.Helpers.ToString(this._input);
      s += ", ";
      s += Dafny.Helpers.ToString(this._output);
      s += ")";
      return s;
    }
    public static software.amazon.cryptography.primitives.internaldafny.types._IDafnyCallEvent<I, O> Default(I _default_I, O _default_O) {
      return create(_default_I, _default_O);
    }
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IDafnyCallEvent<I, O>> _TypeDescriptor(Dafny.TypeDescriptor<I> _td_I, Dafny.TypeDescriptor<O> _td_O) {
      return new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IDafnyCallEvent<I, O>>(software.amazon.cryptography.primitives.internaldafny.types.DafnyCallEvent<I, O>.Default(_td_I.Default(), _td_O.Default()));
    }
    public static _IDafnyCallEvent<I, O> create(I input, O output) {
      return new DafnyCallEvent<I, O>(input, output);
    }
    public static _IDafnyCallEvent<I, O> create_DafnyCallEvent(I input, O output) {
      return create(input, output);
    }
    public bool is_DafnyCallEvent { get { return true; } }
    public I dtor_input {
      get {
        return this._input;
      }
    }
    public O dtor_output {
      get {
        return this._output;
      }
    }
  }

  public interface _IAES__CTR {
    bool is_AES__CTR { get; }
    int dtor_keyLength { get; }
    int dtor_nonceLength { get; }
    _IAES__CTR DowncastClone();
  }
  public class AES__CTR : _IAES__CTR {
    public readonly int _keyLength;
    public readonly int _nonceLength;
    public AES__CTR(int keyLength, int nonceLength) {
      this._keyLength = keyLength;
      this._nonceLength = nonceLength;
    }
    public _IAES__CTR DowncastClone() {
      if (this is _IAES__CTR dt) { return dt; }
      return new AES__CTR(_keyLength, _nonceLength);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.AES__CTR;
      return oth != null && this._keyLength == oth._keyLength && this._nonceLength == oth._nonceLength;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._nonceLength));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.AES_CTR.AES_CTR";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this._nonceLength);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IAES__CTR theDefault = create(0, 0);
    public static software.amazon.cryptography.primitives.internaldafny.types._IAES__CTR Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAES__CTR> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAES__CTR>(software.amazon.cryptography.primitives.internaldafny.types.AES__CTR.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAES__CTR> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAES__CTR create(int keyLength, int nonceLength) {
      return new AES__CTR(keyLength, nonceLength);
    }
    public static _IAES__CTR create_AES__CTR(int keyLength, int nonceLength) {
      return create(keyLength, nonceLength);
    }
    public bool is_AES__CTR { get { return true; } }
    public int dtor_keyLength {
      get {
        return this._keyLength;
      }
    }
    public int dtor_nonceLength {
      get {
        return this._nonceLength;
      }
    }
  }

  public interface _IAES__GCM {
    bool is_AES__GCM { get; }
    int dtor_keyLength { get; }
    int dtor_tagLength { get; }
    int dtor_ivLength { get; }
    _IAES__GCM DowncastClone();
  }
  public class AES__GCM : _IAES__GCM {
    public readonly int _keyLength;
    public readonly int _tagLength;
    public readonly int _ivLength;
    public AES__GCM(int keyLength, int tagLength, int ivLength) {
      this._keyLength = keyLength;
      this._tagLength = tagLength;
      this._ivLength = ivLength;
    }
    public _IAES__GCM DowncastClone() {
      if (this is _IAES__GCM dt) { return dt; }
      return new AES__GCM(_keyLength, _tagLength, _ivLength);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.AES__GCM;
      return oth != null && this._keyLength == oth._keyLength && this._tagLength == oth._tagLength && this._ivLength == oth._ivLength;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tagLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ivLength));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.AES_GCM.AES_GCM";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tagLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ivLength);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM theDefault = create(0, 0, 0);
    public static software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM>(software.amazon.cryptography.primitives.internaldafny.types.AES__GCM.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAES__GCM create(int keyLength, int tagLength, int ivLength) {
      return new AES__GCM(keyLength, tagLength, ivLength);
    }
    public static _IAES__GCM create_AES__GCM(int keyLength, int tagLength, int ivLength) {
      return create(keyLength, tagLength, ivLength);
    }
    public bool is_AES__GCM { get { return true; } }
    public int dtor_keyLength {
      get {
        return this._keyLength;
      }
    }
    public int dtor_tagLength {
      get {
        return this._tagLength;
      }
    }
    public int dtor_ivLength {
      get {
        return this._ivLength;
      }
    }
  }

  public interface _IAESDecryptInput {
    bool is_AESDecryptInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM dtor_encAlg { get; }
    Dafny.ISequence<byte> dtor_key { get; }
    Dafny.ISequence<byte> dtor_cipherTxt { get; }
    Dafny.ISequence<byte> dtor_authTag { get; }
    Dafny.ISequence<byte> dtor_iv { get; }
    Dafny.ISequence<byte> dtor_aad { get; }
    _IAESDecryptInput DowncastClone();
  }
  public class AESDecryptInput : _IAESDecryptInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM _encAlg;
    public readonly Dafny.ISequence<byte> _key;
    public readonly Dafny.ISequence<byte> _cipherTxt;
    public readonly Dafny.ISequence<byte> _authTag;
    public readonly Dafny.ISequence<byte> _iv;
    public readonly Dafny.ISequence<byte> _aad;
    public AESDecryptInput(software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM encAlg, Dafny.ISequence<byte> key, Dafny.ISequence<byte> cipherTxt, Dafny.ISequence<byte> authTag, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> aad) {
      this._encAlg = encAlg;
      this._key = key;
      this._cipherTxt = cipherTxt;
      this._authTag = authTag;
      this._iv = iv;
      this._aad = aad;
    }
    public _IAESDecryptInput DowncastClone() {
      if (this is _IAESDecryptInput dt) { return dt; }
      return new AESDecryptInput(_encAlg, _key, _cipherTxt, _authTag, _iv, _aad);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.AESDecryptInput;
      return oth != null && object.Equals(this._encAlg, oth._encAlg) && object.Equals(this._key, oth._key) && object.Equals(this._cipherTxt, oth._cipherTxt) && object.Equals(this._authTag, oth._authTag) && object.Equals(this._iv, oth._iv) && object.Equals(this._aad, oth._aad);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encAlg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cipherTxt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._authTag));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._iv));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._aad));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.AESDecryptInput.AESDecryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._encAlg);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._cipherTxt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._authTag);
      s += ", ";
      s += Dafny.Helpers.ToString(this._iv);
      s += ", ";
      s += Dafny.Helpers.ToString(this._aad);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.AES__GCM.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput>(software.amazon.cryptography.primitives.internaldafny.types.AESDecryptInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAESDecryptInput create(software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM encAlg, Dafny.ISequence<byte> key, Dafny.ISequence<byte> cipherTxt, Dafny.ISequence<byte> authTag, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> aad) {
      return new AESDecryptInput(encAlg, key, cipherTxt, authTag, iv, aad);
    }
    public static _IAESDecryptInput create_AESDecryptInput(software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM encAlg, Dafny.ISequence<byte> key, Dafny.ISequence<byte> cipherTxt, Dafny.ISequence<byte> authTag, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> aad) {
      return create(encAlg, key, cipherTxt, authTag, iv, aad);
    }
    public bool is_AESDecryptInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM dtor_encAlg {
      get {
        return this._encAlg;
      }
    }
    public Dafny.ISequence<byte> dtor_key {
      get {
        return this._key;
      }
    }
    public Dafny.ISequence<byte> dtor_cipherTxt {
      get {
        return this._cipherTxt;
      }
    }
    public Dafny.ISequence<byte> dtor_authTag {
      get {
        return this._authTag;
      }
    }
    public Dafny.ISequence<byte> dtor_iv {
      get {
        return this._iv;
      }
    }
    public Dafny.ISequence<byte> dtor_aad {
      get {
        return this._aad;
      }
    }
  }

  public interface _IAESEncryptInput {
    bool is_AESEncryptInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM dtor_encAlg { get; }
    Dafny.ISequence<byte> dtor_iv { get; }
    Dafny.ISequence<byte> dtor_key { get; }
    Dafny.ISequence<byte> dtor_msg { get; }
    Dafny.ISequence<byte> dtor_aad { get; }
    _IAESEncryptInput DowncastClone();
  }
  public class AESEncryptInput : _IAESEncryptInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM _encAlg;
    public readonly Dafny.ISequence<byte> _iv;
    public readonly Dafny.ISequence<byte> _key;
    public readonly Dafny.ISequence<byte> _msg;
    public readonly Dafny.ISequence<byte> _aad;
    public AESEncryptInput(software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM encAlg, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> key, Dafny.ISequence<byte> msg, Dafny.ISequence<byte> aad) {
      this._encAlg = encAlg;
      this._iv = iv;
      this._key = key;
      this._msg = msg;
      this._aad = aad;
    }
    public _IAESEncryptInput DowncastClone() {
      if (this is _IAESEncryptInput dt) { return dt; }
      return new AESEncryptInput(_encAlg, _iv, _key, _msg, _aad);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.AESEncryptInput;
      return oth != null && object.Equals(this._encAlg, oth._encAlg) && object.Equals(this._iv, oth._iv) && object.Equals(this._key, oth._key) && object.Equals(this._msg, oth._msg) && object.Equals(this._aad, oth._aad);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encAlg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._iv));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._msg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._aad));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.AESEncryptInput.AESEncryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._encAlg);
      s += ", ";
      s += Dafny.Helpers.ToString(this._iv);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._msg);
      s += ", ";
      s += Dafny.Helpers.ToString(this._aad);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.AES__GCM.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput>(software.amazon.cryptography.primitives.internaldafny.types.AESEncryptInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAESEncryptInput create(software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM encAlg, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> key, Dafny.ISequence<byte> msg, Dafny.ISequence<byte> aad) {
      return new AESEncryptInput(encAlg, iv, key, msg, aad);
    }
    public static _IAESEncryptInput create_AESEncryptInput(software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM encAlg, Dafny.ISequence<byte> iv, Dafny.ISequence<byte> key, Dafny.ISequence<byte> msg, Dafny.ISequence<byte> aad) {
      return create(encAlg, iv, key, msg, aad);
    }
    public bool is_AESEncryptInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM dtor_encAlg {
      get {
        return this._encAlg;
      }
    }
    public Dafny.ISequence<byte> dtor_iv {
      get {
        return this._iv;
      }
    }
    public Dafny.ISequence<byte> dtor_key {
      get {
        return this._key;
      }
    }
    public Dafny.ISequence<byte> dtor_msg {
      get {
        return this._msg;
      }
    }
    public Dafny.ISequence<byte> dtor_aad {
      get {
        return this._aad;
      }
    }
  }

  public interface _IAESEncryptOutput {
    bool is_AESEncryptOutput { get; }
    Dafny.ISequence<byte> dtor_cipherText { get; }
    Dafny.ISequence<byte> dtor_authTag { get; }
    _IAESEncryptOutput DowncastClone();
  }
  public class AESEncryptOutput : _IAESEncryptOutput {
    public readonly Dafny.ISequence<byte> _cipherText;
    public readonly Dafny.ISequence<byte> _authTag;
    public AESEncryptOutput(Dafny.ISequence<byte> cipherText, Dafny.ISequence<byte> authTag) {
      this._cipherText = cipherText;
      this._authTag = authTag;
    }
    public _IAESEncryptOutput DowncastClone() {
      if (this is _IAESEncryptOutput dt) { return dt; }
      return new AESEncryptOutput(_cipherText, _authTag);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput;
      return oth != null && object.Equals(this._cipherText, oth._cipherText) && object.Equals(this._authTag, oth._authTag);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cipherText));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._authTag));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.AESEncryptOutput.AESEncryptOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this._cipherText);
      s += ", ";
      s += Dafny.Helpers.ToString(this._authTag);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput>(software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAESEncryptOutput create(Dafny.ISequence<byte> cipherText, Dafny.ISequence<byte> authTag) {
      return new AESEncryptOutput(cipherText, authTag);
    }
    public static _IAESEncryptOutput create_AESEncryptOutput(Dafny.ISequence<byte> cipherText, Dafny.ISequence<byte> authTag) {
      return create(cipherText, authTag);
    }
    public bool is_AESEncryptOutput { get { return true; } }
    public Dafny.ISequence<byte> dtor_cipherText {
      get {
        return this._cipherText;
      }
    }
    public Dafny.ISequence<byte> dtor_authTag {
      get {
        return this._authTag;
      }
    }
  }

  public interface _IAesKdfCtrInput {
    bool is_AesKdfCtrInput { get; }
    Dafny.ISequence<byte> dtor_ikm { get; }
    int dtor_expectedLength { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_nonce { get; }
    _IAesKdfCtrInput DowncastClone();
  }
  public class AesKdfCtrInput : _IAesKdfCtrInput {
    public readonly Dafny.ISequence<byte> _ikm;
    public readonly int _expectedLength;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _nonce;
    public AesKdfCtrInput(Dafny.ISequence<byte> ikm, int expectedLength, Wrappers_Compile._IOption<Dafny.ISequence<byte>> nonce) {
      this._ikm = ikm;
      this._expectedLength = expectedLength;
      this._nonce = nonce;
    }
    public _IAesKdfCtrInput DowncastClone() {
      if (this is _IAesKdfCtrInput dt) { return dt; }
      return new AesKdfCtrInput(_ikm, _expectedLength, _nonce);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.AesKdfCtrInput;
      return oth != null && object.Equals(this._ikm, oth._ikm) && this._expectedLength == oth._expectedLength && object.Equals(this._nonce, oth._nonce);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ikm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expectedLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._nonce));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.AesKdfCtrInput.AesKdfCtrInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._ikm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._expectedLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this._nonce);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IAesKdfCtrInput theDefault = create(Dafny.Sequence<byte>.Empty, 0, Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default());
    public static software.amazon.cryptography.primitives.internaldafny.types._IAesKdfCtrInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAesKdfCtrInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAesKdfCtrInput>(software.amazon.cryptography.primitives.internaldafny.types.AesKdfCtrInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IAesKdfCtrInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAesKdfCtrInput create(Dafny.ISequence<byte> ikm, int expectedLength, Wrappers_Compile._IOption<Dafny.ISequence<byte>> nonce) {
      return new AesKdfCtrInput(ikm, expectedLength, nonce);
    }
    public static _IAesKdfCtrInput create_AesKdfCtrInput(Dafny.ISequence<byte> ikm, int expectedLength, Wrappers_Compile._IOption<Dafny.ISequence<byte>> nonce) {
      return create(ikm, expectedLength, nonce);
    }
    public bool is_AesKdfCtrInput { get { return true; } }
    public Dafny.ISequence<byte> dtor_ikm {
      get {
        return this._ikm;
      }
    }
    public int dtor_expectedLength {
      get {
        return this._expectedLength;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_nonce {
      get {
        return this._nonce;
      }
    }
  }

  public partial class IAwsCryptographicPrimitivesClientCallHistory {
    public IAwsCryptographicPrimitivesClientCallHistory() {
    }
  }

  public interface IAwsCryptographicPrimitivesClient {
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> GenerateRandomBytes(software.amazon.cryptography.primitives.internaldafny.types._IGenerateRandomBytesInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Digest(software.amazon.cryptography.primitives.internaldafny.types._IDigestInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> HMac(software.amazon.cryptography.primitives.internaldafny.types._IHMacInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> HkdfExtract(software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> HkdfExpand(software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Hkdf(software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> KdfCounterMode(software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> AesKdfCounterMode(software.amazon.cryptography.primitives.internaldafny.types._IAesKdfCtrInput input);
    Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> AESEncrypt(software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> AESDecrypt(software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput input);
    Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> GenerateRSAKeyPair(software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairInput input);
    Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> GetRSAKeyModulusLength(software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> RSADecrypt(software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> RSAEncrypt(software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput input);
    Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> GenerateECDSASignatureKey(software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput input);
    Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> ECDSASign(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignInput input);
    Wrappers_Compile._IResult<bool, software.amazon.cryptography.primitives.internaldafny.types._IError> ECDSAVerify(software.amazon.cryptography.primitives.internaldafny.types._IECDSAVerifyInput input);
  }
  public class _Companion_IAwsCryptographicPrimitivesClient {
  }

  public interface _ICryptoConfig {
    bool is_CryptoConfig { get; }
    _ICryptoConfig DowncastClone();
  }
  public class CryptoConfig : _ICryptoConfig {
    public CryptoConfig() {
    }
    public _ICryptoConfig DowncastClone() {
      if (this is _ICryptoConfig dt) { return dt; }
      return new CryptoConfig();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.CryptoConfig;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.CryptoConfig.CryptoConfig";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._ICryptoConfig theDefault = create();
    public static software.amazon.cryptography.primitives.internaldafny.types._ICryptoConfig Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._ICryptoConfig> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._ICryptoConfig>(software.amazon.cryptography.primitives.internaldafny.types.CryptoConfig.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._ICryptoConfig> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICryptoConfig create() {
      return new CryptoConfig();
    }
    public static _ICryptoConfig create_CryptoConfig() {
      return create();
    }
    public bool is_CryptoConfig { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_ICryptoConfig> AllSingletonConstructors {
      get {
        yield return CryptoConfig.create();
      }
    }
  }

  public interface _IDigestAlgorithm {
    bool is_SHA__512 { get; }
    bool is_SHA__384 { get; }
    bool is_SHA__256 { get; }
    _IDigestAlgorithm DowncastClone();
  }
  public abstract class DigestAlgorithm : _IDigestAlgorithm {
    public DigestAlgorithm() { }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm theDefault = create_SHA__512();
    public static software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm>(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDigestAlgorithm create_SHA__512() {
      return new DigestAlgorithm_SHA__512();
    }
    public static _IDigestAlgorithm create_SHA__384() {
      return new DigestAlgorithm_SHA__384();
    }
    public static _IDigestAlgorithm create_SHA__256() {
      return new DigestAlgorithm_SHA__256();
    }
    public bool is_SHA__512 { get { return this is DigestAlgorithm_SHA__512; } }
    public bool is_SHA__384 { get { return this is DigestAlgorithm_SHA__384; } }
    public bool is_SHA__256 { get { return this is DigestAlgorithm_SHA__256; } }
    public static System.Collections.Generic.IEnumerable<_IDigestAlgorithm> AllSingletonConstructors {
      get {
        yield return DigestAlgorithm.create_SHA__512();
        yield return DigestAlgorithm.create_SHA__384();
        yield return DigestAlgorithm.create_SHA__256();
      }
    }
    public abstract _IDigestAlgorithm DowncastClone();
  }
  public class DigestAlgorithm_SHA__512 : DigestAlgorithm {
    public DigestAlgorithm_SHA__512() {
    }
    public override _IDigestAlgorithm DowncastClone() {
      if (this is _IDigestAlgorithm dt) { return dt; }
      return new DigestAlgorithm_SHA__512();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm_SHA__512;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.DigestAlgorithm.SHA_512";
      return s;
    }
  }
  public class DigestAlgorithm_SHA__384 : DigestAlgorithm {
    public DigestAlgorithm_SHA__384() {
    }
    public override _IDigestAlgorithm DowncastClone() {
      if (this is _IDigestAlgorithm dt) { return dt; }
      return new DigestAlgorithm_SHA__384();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm_SHA__384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.DigestAlgorithm.SHA_384";
      return s;
    }
  }
  public class DigestAlgorithm_SHA__256 : DigestAlgorithm {
    public DigestAlgorithm_SHA__256() {
    }
    public override _IDigestAlgorithm DowncastClone() {
      if (this is _IDigestAlgorithm dt) { return dt; }
      return new DigestAlgorithm_SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm_SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.DigestAlgorithm.SHA_256";
      return s;
    }
  }

  public interface _IDigestInput {
    bool is_DigestInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm { get; }
    Dafny.ISequence<byte> dtor_message { get; }
    _IDigestInput DowncastClone();
  }
  public class DigestInput : _IDigestInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _digestAlgorithm;
    public readonly Dafny.ISequence<byte> _message;
    public DigestInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> message) {
      this._digestAlgorithm = digestAlgorithm;
      this._message = message;
    }
    public _IDigestInput DowncastClone() {
      if (this is _IDigestInput dt) { return dt; }
      return new DigestInput(_digestAlgorithm, _message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.DigestInput;
      return oth != null && object.Equals(this._digestAlgorithm, oth._digestAlgorithm) && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._digestAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.DigestInput.DigestInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._digestAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IDigestInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.Default(), Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IDigestInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IDigestInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IDigestInput>(software.amazon.cryptography.primitives.internaldafny.types.DigestInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IDigestInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDigestInput create(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> message) {
      return new DigestInput(digestAlgorithm, message);
    }
    public static _IDigestInput create_DigestInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> message) {
      return create(digestAlgorithm, message);
    }
    public bool is_DigestInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm {
      get {
        return this._digestAlgorithm;
      }
    }
    public Dafny.ISequence<byte> dtor_message {
      get {
        return this._message;
      }
    }
  }

  public interface _IECDSASignatureAlgorithm {
    bool is_ECDSA__P384 { get; }
    bool is_ECDSA__P256 { get; }
    _IECDSASignatureAlgorithm DowncastClone();
  }
  public abstract class ECDSASignatureAlgorithm : _IECDSASignatureAlgorithm {
    public ECDSASignatureAlgorithm() { }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm theDefault = create_ECDSA__P384();
    public static software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm>(software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IECDSASignatureAlgorithm create_ECDSA__P384() {
      return new ECDSASignatureAlgorithm_ECDSA__P384();
    }
    public static _IECDSASignatureAlgorithm create_ECDSA__P256() {
      return new ECDSASignatureAlgorithm_ECDSA__P256();
    }
    public bool is_ECDSA__P384 { get { return this is ECDSASignatureAlgorithm_ECDSA__P384; } }
    public bool is_ECDSA__P256 { get { return this is ECDSASignatureAlgorithm_ECDSA__P256; } }
    public static System.Collections.Generic.IEnumerable<_IECDSASignatureAlgorithm> AllSingletonConstructors {
      get {
        yield return ECDSASignatureAlgorithm.create_ECDSA__P384();
        yield return ECDSASignatureAlgorithm.create_ECDSA__P256();
      }
    }
    public abstract _IECDSASignatureAlgorithm DowncastClone();
  }
  public class ECDSASignatureAlgorithm_ECDSA__P384 : ECDSASignatureAlgorithm {
    public ECDSASignatureAlgorithm_ECDSA__P384() {
    }
    public override _IECDSASignatureAlgorithm DowncastClone() {
      if (this is _IECDSASignatureAlgorithm dt) { return dt; }
      return new ECDSASignatureAlgorithm_ECDSA__P384();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm_ECDSA__P384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.ECDSASignatureAlgorithm.ECDSA_P384";
      return s;
    }
  }
  public class ECDSASignatureAlgorithm_ECDSA__P256 : ECDSASignatureAlgorithm {
    public ECDSASignatureAlgorithm_ECDSA__P256() {
    }
    public override _IECDSASignatureAlgorithm DowncastClone() {
      if (this is _IECDSASignatureAlgorithm dt) { return dt; }
      return new ECDSASignatureAlgorithm_ECDSA__P256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm_ECDSA__P256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.ECDSASignatureAlgorithm.ECDSA_P256";
      return s;
    }
  }

  public interface _IECDSASignInput {
    bool is_ECDSASignInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm dtor_signatureAlgorithm { get; }
    Dafny.ISequence<byte> dtor_signingKey { get; }
    Dafny.ISequence<byte> dtor_message { get; }
    _IECDSASignInput DowncastClone();
  }
  public class ECDSASignInput : _IECDSASignInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm _signatureAlgorithm;
    public readonly Dafny.ISequence<byte> _signingKey;
    public readonly Dafny.ISequence<byte> _message;
    public ECDSASignInput(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm, Dafny.ISequence<byte> signingKey, Dafny.ISequence<byte> message) {
      this._signatureAlgorithm = signatureAlgorithm;
      this._signingKey = signingKey;
      this._message = message;
    }
    public _IECDSASignInput DowncastClone() {
      if (this is _IECDSASignInput dt) { return dt; }
      return new ECDSASignInput(_signatureAlgorithm, _signingKey, _message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.ECDSASignInput;
      return oth != null && object.Equals(this._signatureAlgorithm, oth._signatureAlgorithm) && object.Equals(this._signingKey, oth._signingKey) && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._signatureAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._signingKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.ECDSASignInput.ECDSASignInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._signatureAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._signingKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IECDSASignInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IECDSASignInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IECDSASignInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IECDSASignInput>(software.amazon.cryptography.primitives.internaldafny.types.ECDSASignInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IECDSASignInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IECDSASignInput create(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm, Dafny.ISequence<byte> signingKey, Dafny.ISequence<byte> message) {
      return new ECDSASignInput(signatureAlgorithm, signingKey, message);
    }
    public static _IECDSASignInput create_ECDSASignInput(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm, Dafny.ISequence<byte> signingKey, Dafny.ISequence<byte> message) {
      return create(signatureAlgorithm, signingKey, message);
    }
    public bool is_ECDSASignInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm dtor_signatureAlgorithm {
      get {
        return this._signatureAlgorithm;
      }
    }
    public Dafny.ISequence<byte> dtor_signingKey {
      get {
        return this._signingKey;
      }
    }
    public Dafny.ISequence<byte> dtor_message {
      get {
        return this._message;
      }
    }
  }

  public interface _IECDSAVerifyInput {
    bool is_ECDSAVerifyInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm dtor_signatureAlgorithm { get; }
    Dafny.ISequence<byte> dtor_verificationKey { get; }
    Dafny.ISequence<byte> dtor_message { get; }
    Dafny.ISequence<byte> dtor_signature { get; }
    _IECDSAVerifyInput DowncastClone();
  }
  public class ECDSAVerifyInput : _IECDSAVerifyInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm _signatureAlgorithm;
    public readonly Dafny.ISequence<byte> _verificationKey;
    public readonly Dafny.ISequence<byte> _message;
    public readonly Dafny.ISequence<byte> _signature;
    public ECDSAVerifyInput(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm, Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> message, Dafny.ISequence<byte> signature) {
      this._signatureAlgorithm = signatureAlgorithm;
      this._verificationKey = verificationKey;
      this._message = message;
      this._signature = signature;
    }
    public _IECDSAVerifyInput DowncastClone() {
      if (this is _IECDSAVerifyInput dt) { return dt; }
      return new ECDSAVerifyInput(_signatureAlgorithm, _verificationKey, _message, _signature);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.ECDSAVerifyInput;
      return oth != null && object.Equals(this._signatureAlgorithm, oth._signatureAlgorithm) && object.Equals(this._verificationKey, oth._verificationKey) && object.Equals(this._message, oth._message) && object.Equals(this._signature, oth._signature);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._signatureAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._verificationKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._signature));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.ECDSAVerifyInput.ECDSAVerifyInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._signatureAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._verificationKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._message);
      s += ", ";
      s += Dafny.Helpers.ToString(this._signature);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IECDSAVerifyInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IECDSAVerifyInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IECDSAVerifyInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IECDSAVerifyInput>(software.amazon.cryptography.primitives.internaldafny.types.ECDSAVerifyInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IECDSAVerifyInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IECDSAVerifyInput create(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm, Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> message, Dafny.ISequence<byte> signature) {
      return new ECDSAVerifyInput(signatureAlgorithm, verificationKey, message, signature);
    }
    public static _IECDSAVerifyInput create_ECDSAVerifyInput(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm, Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> message, Dafny.ISequence<byte> signature) {
      return create(signatureAlgorithm, verificationKey, message, signature);
    }
    public bool is_ECDSAVerifyInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm dtor_signatureAlgorithm {
      get {
        return this._signatureAlgorithm;
      }
    }
    public Dafny.ISequence<byte> dtor_verificationKey {
      get {
        return this._verificationKey;
      }
    }
    public Dafny.ISequence<byte> dtor_message {
      get {
        return this._message;
      }
    }
    public Dafny.ISequence<byte> dtor_signature {
      get {
        return this._signature;
      }
    }
  }

  public interface _IGenerateECDSASignatureKeyInput {
    bool is_GenerateECDSASignatureKeyInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm dtor_signatureAlgorithm { get; }
    _IGenerateECDSASignatureKeyInput DowncastClone();
  }
  public class GenerateECDSASignatureKeyInput : _IGenerateECDSASignatureKeyInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm _signatureAlgorithm;
    public GenerateECDSASignatureKeyInput(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm) {
      this._signatureAlgorithm = signatureAlgorithm;
    }
    public _IGenerateECDSASignatureKeyInput DowncastClone() {
      if (this is _IGenerateECDSASignatureKeyInput dt) { return dt; }
      return new GenerateECDSASignatureKeyInput(_signatureAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyInput;
      return oth != null && object.Equals(this._signatureAlgorithm, oth._signatureAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._signatureAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.GenerateECDSASignatureKeyInput.GenerateECDSASignatureKeyInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._signatureAlgorithm);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm.Default());
    public static software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput>(software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateECDSASignatureKeyInput create(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm) {
      return new GenerateECDSASignatureKeyInput(signatureAlgorithm);
    }
    public static _IGenerateECDSASignatureKeyInput create_GenerateECDSASignatureKeyInput(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm) {
      return create(signatureAlgorithm);
    }
    public bool is_GenerateECDSASignatureKeyInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm dtor_signatureAlgorithm {
      get {
        return this._signatureAlgorithm;
      }
    }
  }

  public interface _IGenerateECDSASignatureKeyOutput {
    bool is_GenerateECDSASignatureKeyOutput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm dtor_signatureAlgorithm { get; }
    Dafny.ISequence<byte> dtor_verificationKey { get; }
    Dafny.ISequence<byte> dtor_signingKey { get; }
    _IGenerateECDSASignatureKeyOutput DowncastClone();
  }
  public class GenerateECDSASignatureKeyOutput : _IGenerateECDSASignatureKeyOutput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm _signatureAlgorithm;
    public readonly Dafny.ISequence<byte> _verificationKey;
    public readonly Dafny.ISequence<byte> _signingKey;
    public GenerateECDSASignatureKeyOutput(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm, Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> signingKey) {
      this._signatureAlgorithm = signatureAlgorithm;
      this._verificationKey = verificationKey;
      this._signingKey = signingKey;
    }
    public _IGenerateECDSASignatureKeyOutput DowncastClone() {
      if (this is _IGenerateECDSASignatureKeyOutput dt) { return dt; }
      return new GenerateECDSASignatureKeyOutput(_signatureAlgorithm, _verificationKey, _signingKey);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput;
      return oth != null && object.Equals(this._signatureAlgorithm, oth._signatureAlgorithm) && object.Equals(this._verificationKey, oth._verificationKey) && object.Equals(this._signingKey, oth._signingKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._signatureAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._verificationKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._signingKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.GenerateECDSASignatureKeyOutput.GenerateECDSASignatureKeyOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this._signatureAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._verificationKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._signingKey);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput>(software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateECDSASignatureKeyOutput create(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm, Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> signingKey) {
      return new GenerateECDSASignatureKeyOutput(signatureAlgorithm, verificationKey, signingKey);
    }
    public static _IGenerateECDSASignatureKeyOutput create_GenerateECDSASignatureKeyOutput(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm, Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> signingKey) {
      return create(signatureAlgorithm, verificationKey, signingKey);
    }
    public bool is_GenerateECDSASignatureKeyOutput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm dtor_signatureAlgorithm {
      get {
        return this._signatureAlgorithm;
      }
    }
    public Dafny.ISequence<byte> dtor_verificationKey {
      get {
        return this._verificationKey;
      }
    }
    public Dafny.ISequence<byte> dtor_signingKey {
      get {
        return this._signingKey;
      }
    }
  }

  public interface _IGenerateRandomBytesInput {
    bool is_GenerateRandomBytesInput { get; }
    int dtor_length { get; }
    _IGenerateRandomBytesInput DowncastClone();
  }
  public class GenerateRandomBytesInput : _IGenerateRandomBytesInput {
    public readonly int _length;
    public GenerateRandomBytesInput(int length) {
      this._length = length;
    }
    public _IGenerateRandomBytesInput DowncastClone() {
      if (this is _IGenerateRandomBytesInput dt) { return dt; }
      return new GenerateRandomBytesInput(_length);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.GenerateRandomBytesInput;
      return oth != null && this._length == oth._length;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._length));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.GenerateRandomBytesInput.GenerateRandomBytesInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._length);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IGenerateRandomBytesInput theDefault = create(0);
    public static software.amazon.cryptography.primitives.internaldafny.types._IGenerateRandomBytesInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRandomBytesInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRandomBytesInput>(software.amazon.cryptography.primitives.internaldafny.types.GenerateRandomBytesInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRandomBytesInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateRandomBytesInput create(int length) {
      return new GenerateRandomBytesInput(length);
    }
    public static _IGenerateRandomBytesInput create_GenerateRandomBytesInput(int length) {
      return create(length);
    }
    public bool is_GenerateRandomBytesInput { get { return true; } }
    public int dtor_length {
      get {
        return this._length;
      }
    }
  }

  public interface _IGenerateRSAKeyPairInput {
    bool is_GenerateRSAKeyPairInput { get; }
    int dtor_lengthBits { get; }
    _IGenerateRSAKeyPairInput DowncastClone();
  }
  public class GenerateRSAKeyPairInput : _IGenerateRSAKeyPairInput {
    public readonly int _lengthBits;
    public GenerateRSAKeyPairInput(int lengthBits) {
      this._lengthBits = lengthBits;
    }
    public _IGenerateRSAKeyPairInput DowncastClone() {
      if (this is _IGenerateRSAKeyPairInput dt) { return dt; }
      return new GenerateRSAKeyPairInput(_lengthBits);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairInput;
      return oth != null && this._lengthBits == oth._lengthBits;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lengthBits));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.GenerateRSAKeyPairInput.GenerateRSAKeyPairInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._lengthBits);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairInput theDefault = create(0);
    public static software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairInput>(software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateRSAKeyPairInput create(int lengthBits) {
      return new GenerateRSAKeyPairInput(lengthBits);
    }
    public static _IGenerateRSAKeyPairInput create_GenerateRSAKeyPairInput(int lengthBits) {
      return create(lengthBits);
    }
    public bool is_GenerateRSAKeyPairInput { get { return true; } }
    public int dtor_lengthBits {
      get {
        return this._lengthBits;
      }
    }
  }

  public interface _IGenerateRSAKeyPairOutput {
    bool is_GenerateRSAKeyPairOutput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey dtor_publicKey { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey dtor_privateKey { get; }
    _IGenerateRSAKeyPairOutput DowncastClone();
  }
  public class GenerateRSAKeyPairOutput : _IGenerateRSAKeyPairOutput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey _publicKey;
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey _privateKey;
    public GenerateRSAKeyPairOutput(software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey publicKey, software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey privateKey) {
      this._publicKey = publicKey;
      this._privateKey = privateKey;
    }
    public _IGenerateRSAKeyPairOutput DowncastClone() {
      if (this is _IGenerateRSAKeyPairOutput dt) { return dt; }
      return new GenerateRSAKeyPairOutput(_publicKey, _privateKey);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairOutput;
      return oth != null && object.Equals(this._publicKey, oth._publicKey) && object.Equals(this._privateKey, oth._privateKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._publicKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._privateKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.GenerateRSAKeyPairOutput.GenerateRSAKeyPairOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this._publicKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._privateKey);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.RSAPublicKey.Default(), software.amazon.cryptography.primitives.internaldafny.types.RSAPrivateKey.Default());
    public static software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput>(software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairOutput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateRSAKeyPairOutput create(software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey publicKey, software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey privateKey) {
      return new GenerateRSAKeyPairOutput(publicKey, privateKey);
    }
    public static _IGenerateRSAKeyPairOutput create_GenerateRSAKeyPairOutput(software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey publicKey, software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey privateKey) {
      return create(publicKey, privateKey);
    }
    public bool is_GenerateRSAKeyPairOutput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey dtor_publicKey {
      get {
        return this._publicKey;
      }
    }
    public software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey dtor_privateKey {
      get {
        return this._privateKey;
      }
    }
  }

  public interface _IGetRSAKeyModulusLengthInput {
    bool is_GetRSAKeyModulusLengthInput { get; }
    Dafny.ISequence<byte> dtor_publicKey { get; }
    _IGetRSAKeyModulusLengthInput DowncastClone();
  }
  public class GetRSAKeyModulusLengthInput : _IGetRSAKeyModulusLengthInput {
    public readonly Dafny.ISequence<byte> _publicKey;
    public GetRSAKeyModulusLengthInput(Dafny.ISequence<byte> publicKey) {
      this._publicKey = publicKey;
    }
    public _IGetRSAKeyModulusLengthInput DowncastClone() {
      if (this is _IGetRSAKeyModulusLengthInput dt) { return dt; }
      return new GetRSAKeyModulusLengthInput(_publicKey);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthInput;
      return oth != null && object.Equals(this._publicKey, oth._publicKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._publicKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.GetRSAKeyModulusLengthInput.GetRSAKeyModulusLengthInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._publicKey);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthInput theDefault = create(Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthInput>(software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetRSAKeyModulusLengthInput create(Dafny.ISequence<byte> publicKey) {
      return new GetRSAKeyModulusLengthInput(publicKey);
    }
    public static _IGetRSAKeyModulusLengthInput create_GetRSAKeyModulusLengthInput(Dafny.ISequence<byte> publicKey) {
      return create(publicKey);
    }
    public bool is_GetRSAKeyModulusLengthInput { get { return true; } }
    public Dafny.ISequence<byte> dtor_publicKey {
      get {
        return this._publicKey;
      }
    }
  }

  public interface _IGetRSAKeyModulusLengthOutput {
    bool is_GetRSAKeyModulusLengthOutput { get; }
    int dtor_length { get; }
    _IGetRSAKeyModulusLengthOutput DowncastClone();
  }
  public class GetRSAKeyModulusLengthOutput : _IGetRSAKeyModulusLengthOutput {
    public readonly int _length;
    public GetRSAKeyModulusLengthOutput(int length) {
      this._length = length;
    }
    public _IGetRSAKeyModulusLengthOutput DowncastClone() {
      if (this is _IGetRSAKeyModulusLengthOutput dt) { return dt; }
      return new GetRSAKeyModulusLengthOutput(_length);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthOutput;
      return oth != null && this._length == oth._length;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._length));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.GetRSAKeyModulusLengthOutput.GetRSAKeyModulusLengthOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this._length);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput theDefault = create(0);
    public static software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput>(software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthOutput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetRSAKeyModulusLengthOutput create(int length) {
      return new GetRSAKeyModulusLengthOutput(length);
    }
    public static _IGetRSAKeyModulusLengthOutput create_GetRSAKeyModulusLengthOutput(int length) {
      return create(length);
    }
    public bool is_GetRSAKeyModulusLengthOutput { get { return true; } }
    public int dtor_length {
      get {
        return this._length;
      }
    }
  }

  public interface _IHkdfExpandInput {
    bool is_HkdfExpandInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm { get; }
    Dafny.ISequence<byte> dtor_prk { get; }
    Dafny.ISequence<byte> dtor_info { get; }
    int dtor_expectedLength { get; }
    _IHkdfExpandInput DowncastClone();
  }
  public class HkdfExpandInput : _IHkdfExpandInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _digestAlgorithm;
    public readonly Dafny.ISequence<byte> _prk;
    public readonly Dafny.ISequence<byte> _info;
    public readonly int _expectedLength;
    public HkdfExpandInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> prk, Dafny.ISequence<byte> info, int expectedLength) {
      this._digestAlgorithm = digestAlgorithm;
      this._prk = prk;
      this._info = info;
      this._expectedLength = expectedLength;
    }
    public _IHkdfExpandInput DowncastClone() {
      if (this is _IHkdfExpandInput dt) { return dt; }
      return new HkdfExpandInput(_digestAlgorithm, _prk, _info, _expectedLength);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.HkdfExpandInput;
      return oth != null && object.Equals(this._digestAlgorithm, oth._digestAlgorithm) && object.Equals(this._prk, oth._prk) && object.Equals(this._info, oth._info) && this._expectedLength == oth._expectedLength;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._digestAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._prk));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._info));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expectedLength));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.HkdfExpandInput.HkdfExpandInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._digestAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._prk);
      s += ", ";
      s += Dafny.Helpers.ToString(this._info);
      s += ", ";
      s += Dafny.Helpers.ToString(this._expectedLength);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, 0);
    public static software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput>(software.amazon.cryptography.primitives.internaldafny.types.HkdfExpandInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IHkdfExpandInput create(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> prk, Dafny.ISequence<byte> info, int expectedLength) {
      return new HkdfExpandInput(digestAlgorithm, prk, info, expectedLength);
    }
    public static _IHkdfExpandInput create_HkdfExpandInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> prk, Dafny.ISequence<byte> info, int expectedLength) {
      return create(digestAlgorithm, prk, info, expectedLength);
    }
    public bool is_HkdfExpandInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm {
      get {
        return this._digestAlgorithm;
      }
    }
    public Dafny.ISequence<byte> dtor_prk {
      get {
        return this._prk;
      }
    }
    public Dafny.ISequence<byte> dtor_info {
      get {
        return this._info;
      }
    }
    public int dtor_expectedLength {
      get {
        return this._expectedLength;
      }
    }
  }

  public interface _IHkdfExtractInput {
    bool is_HkdfExtractInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_salt { get; }
    Dafny.ISequence<byte> dtor_ikm { get; }
    _IHkdfExtractInput DowncastClone();
  }
  public class HkdfExtractInput : _IHkdfExtractInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _digestAlgorithm;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _salt;
    public readonly Dafny.ISequence<byte> _ikm;
    public HkdfExtractInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm) {
      this._digestAlgorithm = digestAlgorithm;
      this._salt = salt;
      this._ikm = ikm;
    }
    public _IHkdfExtractInput DowncastClone() {
      if (this is _IHkdfExtractInput dt) { return dt; }
      return new HkdfExtractInput(_digestAlgorithm, _salt, _ikm);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.HkdfExtractInput;
      return oth != null && object.Equals(this._digestAlgorithm, oth._digestAlgorithm) && object.Equals(this._salt, oth._salt) && object.Equals(this._ikm, oth._ikm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._digestAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._salt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ikm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.HkdfExtractInput.HkdfExtractInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._digestAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._salt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ikm);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput>(software.amazon.cryptography.primitives.internaldafny.types.HkdfExtractInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IHkdfExtractInput create(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm) {
      return new HkdfExtractInput(digestAlgorithm, salt, ikm);
    }
    public static _IHkdfExtractInput create_HkdfExtractInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm) {
      return create(digestAlgorithm, salt, ikm);
    }
    public bool is_HkdfExtractInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm {
      get {
        return this._digestAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_salt {
      get {
        return this._salt;
      }
    }
    public Dafny.ISequence<byte> dtor_ikm {
      get {
        return this._ikm;
      }
    }
  }

  public interface _IHkdfInput {
    bool is_HkdfInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_salt { get; }
    Dafny.ISequence<byte> dtor_ikm { get; }
    Dafny.ISequence<byte> dtor_info { get; }
    int dtor_expectedLength { get; }
    _IHkdfInput DowncastClone();
  }
  public class HkdfInput : _IHkdfInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _digestAlgorithm;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _salt;
    public readonly Dafny.ISequence<byte> _ikm;
    public readonly Dafny.ISequence<byte> _info;
    public readonly int _expectedLength;
    public HkdfInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm, Dafny.ISequence<byte> info, int expectedLength) {
      this._digestAlgorithm = digestAlgorithm;
      this._salt = salt;
      this._ikm = ikm;
      this._info = info;
      this._expectedLength = expectedLength;
    }
    public _IHkdfInput DowncastClone() {
      if (this is _IHkdfInput dt) { return dt; }
      return new HkdfInput(_digestAlgorithm, _salt, _ikm, _info, _expectedLength);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.HkdfInput;
      return oth != null && object.Equals(this._digestAlgorithm, oth._digestAlgorithm) && object.Equals(this._salt, oth._salt) && object.Equals(this._ikm, oth._ikm) && object.Equals(this._info, oth._info) && this._expectedLength == oth._expectedLength;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._digestAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._salt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ikm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._info));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expectedLength));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.HkdfInput.HkdfInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._digestAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._salt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ikm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._info);
      s += ", ";
      s += Dafny.Helpers.ToString(this._expectedLength);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, 0);
    public static software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput>(software.amazon.cryptography.primitives.internaldafny.types.HkdfInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IHkdfInput create(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm, Dafny.ISequence<byte> info, int expectedLength) {
      return new HkdfInput(digestAlgorithm, salt, ikm, info, expectedLength);
    }
    public static _IHkdfInput create_HkdfInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm, Dafny.ISequence<byte> info, int expectedLength) {
      return create(digestAlgorithm, salt, ikm, info, expectedLength);
    }
    public bool is_HkdfInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm {
      get {
        return this._digestAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_salt {
      get {
        return this._salt;
      }
    }
    public Dafny.ISequence<byte> dtor_ikm {
      get {
        return this._ikm;
      }
    }
    public Dafny.ISequence<byte> dtor_info {
      get {
        return this._info;
      }
    }
    public int dtor_expectedLength {
      get {
        return this._expectedLength;
      }
    }
  }

  public interface _IHMacInput {
    bool is_HMacInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm { get; }
    Dafny.ISequence<byte> dtor_key { get; }
    Dafny.ISequence<byte> dtor_message { get; }
    _IHMacInput DowncastClone();
  }
  public class HMacInput : _IHMacInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _digestAlgorithm;
    public readonly Dafny.ISequence<byte> _key;
    public readonly Dafny.ISequence<byte> _message;
    public HMacInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> key, Dafny.ISequence<byte> message) {
      this._digestAlgorithm = digestAlgorithm;
      this._key = key;
      this._message = message;
    }
    public _IHMacInput DowncastClone() {
      if (this is _IHMacInput dt) { return dt; }
      return new HMacInput(_digestAlgorithm, _key, _message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.HMacInput;
      return oth != null && object.Equals(this._digestAlgorithm, oth._digestAlgorithm) && object.Equals(this._key, oth._key) && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._digestAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.HMacInput.HMacInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._digestAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IHMacInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IHMacInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHMacInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHMacInput>(software.amazon.cryptography.primitives.internaldafny.types.HMacInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IHMacInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IHMacInput create(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> key, Dafny.ISequence<byte> message) {
      return new HMacInput(digestAlgorithm, key, message);
    }
    public static _IHMacInput create_HMacInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> key, Dafny.ISequence<byte> message) {
      return create(digestAlgorithm, key, message);
    }
    public bool is_HMacInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm {
      get {
        return this._digestAlgorithm;
      }
    }
    public Dafny.ISequence<byte> dtor_key {
      get {
        return this._key;
      }
    }
    public Dafny.ISequence<byte> dtor_message {
      get {
        return this._message;
      }
    }
  }

  public interface _IKdfCtrInput {
    bool is_KdfCtrInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm { get; }
    Dafny.ISequence<byte> dtor_ikm { get; }
    int dtor_expectedLength { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_purpose { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_nonce { get; }
    _IKdfCtrInput DowncastClone();
  }
  public class KdfCtrInput : _IKdfCtrInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _digestAlgorithm;
    public readonly Dafny.ISequence<byte> _ikm;
    public readonly int _expectedLength;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _purpose;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _nonce;
    public KdfCtrInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> ikm, int expectedLength, Wrappers_Compile._IOption<Dafny.ISequence<byte>> purpose, Wrappers_Compile._IOption<Dafny.ISequence<byte>> nonce) {
      this._digestAlgorithm = digestAlgorithm;
      this._ikm = ikm;
      this._expectedLength = expectedLength;
      this._purpose = purpose;
      this._nonce = nonce;
    }
    public _IKdfCtrInput DowncastClone() {
      if (this is _IKdfCtrInput dt) { return dt; }
      return new KdfCtrInput(_digestAlgorithm, _ikm, _expectedLength, _purpose, _nonce);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.KdfCtrInput;
      return oth != null && object.Equals(this._digestAlgorithm, oth._digestAlgorithm) && object.Equals(this._ikm, oth._ikm) && this._expectedLength == oth._expectedLength && object.Equals(this._purpose, oth._purpose) && object.Equals(this._nonce, oth._nonce);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._digestAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ikm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expectedLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._purpose));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._nonce));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.KdfCtrInput.KdfCtrInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._digestAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ikm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._expectedLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this._purpose);
      s += ", ";
      s += Dafny.Helpers.ToString(this._nonce);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.Default(), Dafny.Sequence<byte>.Empty, 0, Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default());
    public static software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput>(software.amazon.cryptography.primitives.internaldafny.types.KdfCtrInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKdfCtrInput create(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> ikm, int expectedLength, Wrappers_Compile._IOption<Dafny.ISequence<byte>> purpose, Wrappers_Compile._IOption<Dafny.ISequence<byte>> nonce) {
      return new KdfCtrInput(digestAlgorithm, ikm, expectedLength, purpose, nonce);
    }
    public static _IKdfCtrInput create_KdfCtrInput(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm, Dafny.ISequence<byte> ikm, int expectedLength, Wrappers_Compile._IOption<Dafny.ISequence<byte>> purpose, Wrappers_Compile._IOption<Dafny.ISequence<byte>> nonce) {
      return create(digestAlgorithm, ikm, expectedLength, purpose, nonce);
    }
    public bool is_KdfCtrInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm dtor_digestAlgorithm {
      get {
        return this._digestAlgorithm;
      }
    }
    public Dafny.ISequence<byte> dtor_ikm {
      get {
        return this._ikm;
      }
    }
    public int dtor_expectedLength {
      get {
        return this._expectedLength;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_purpose {
      get {
        return this._purpose;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_nonce {
      get {
        return this._nonce;
      }
    }
  }

  public partial class PositiveInteger {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IRSADecryptInput {
    bool is_RSADecryptInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode dtor_padding { get; }
    Dafny.ISequence<byte> dtor_privateKey { get; }
    Dafny.ISequence<byte> dtor_cipherText { get; }
    _IRSADecryptInput DowncastClone();
  }
  public class RSADecryptInput : _IRSADecryptInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode _padding;
    public readonly Dafny.ISequence<byte> _privateKey;
    public readonly Dafny.ISequence<byte> _cipherText;
    public RSADecryptInput(software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode padding, Dafny.ISequence<byte> privateKey, Dafny.ISequence<byte> cipherText) {
      this._padding = padding;
      this._privateKey = privateKey;
      this._cipherText = cipherText;
    }
    public _IRSADecryptInput DowncastClone() {
      if (this is _IRSADecryptInput dt) { return dt; }
      return new RSADecryptInput(_padding, _privateKey, _cipherText);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.RSADecryptInput;
      return oth != null && object.Equals(this._padding, oth._padding) && object.Equals(this._privateKey, oth._privateKey) && object.Equals(this._cipherText, oth._cipherText);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._padding));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._privateKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cipherText));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.RSADecryptInput.RSADecryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._padding);
      s += ", ";
      s += Dafny.Helpers.ToString(this._privateKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._cipherText);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput>(software.amazon.cryptography.primitives.internaldafny.types.RSADecryptInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRSADecryptInput create(software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode padding, Dafny.ISequence<byte> privateKey, Dafny.ISequence<byte> cipherText) {
      return new RSADecryptInput(padding, privateKey, cipherText);
    }
    public static _IRSADecryptInput create_RSADecryptInput(software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode padding, Dafny.ISequence<byte> privateKey, Dafny.ISequence<byte> cipherText) {
      return create(padding, privateKey, cipherText);
    }
    public bool is_RSADecryptInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode dtor_padding {
      get {
        return this._padding;
      }
    }
    public Dafny.ISequence<byte> dtor_privateKey {
      get {
        return this._privateKey;
      }
    }
    public Dafny.ISequence<byte> dtor_cipherText {
      get {
        return this._cipherText;
      }
    }
  }

  public interface _IRSAEncryptInput {
    bool is_RSAEncryptInput { get; }
    software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode dtor_padding { get; }
    Dafny.ISequence<byte> dtor_publicKey { get; }
    Dafny.ISequence<byte> dtor_plaintext { get; }
    _IRSAEncryptInput DowncastClone();
  }
  public class RSAEncryptInput : _IRSAEncryptInput {
    public readonly software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode _padding;
    public readonly Dafny.ISequence<byte> _publicKey;
    public readonly Dafny.ISequence<byte> _plaintext;
    public RSAEncryptInput(software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode padding, Dafny.ISequence<byte> publicKey, Dafny.ISequence<byte> plaintext) {
      this._padding = padding;
      this._publicKey = publicKey;
      this._plaintext = plaintext;
    }
    public _IRSAEncryptInput DowncastClone() {
      if (this is _IRSAEncryptInput dt) { return dt; }
      return new RSAEncryptInput(_padding, _publicKey, _plaintext);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.RSAEncryptInput;
      return oth != null && object.Equals(this._padding, oth._padding) && object.Equals(this._publicKey, oth._publicKey) && object.Equals(this._plaintext, oth._plaintext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._padding));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._publicKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._plaintext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.RSAEncryptInput.RSAEncryptInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._padding);
      s += ", ";
      s += Dafny.Helpers.ToString(this._publicKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._plaintext);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput theDefault = create(software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.Default(), Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput>(software.amazon.cryptography.primitives.internaldafny.types.RSAEncryptInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRSAEncryptInput create(software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode padding, Dafny.ISequence<byte> publicKey, Dafny.ISequence<byte> plaintext) {
      return new RSAEncryptInput(padding, publicKey, plaintext);
    }
    public static _IRSAEncryptInput create_RSAEncryptInput(software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode padding, Dafny.ISequence<byte> publicKey, Dafny.ISequence<byte> plaintext) {
      return create(padding, publicKey, plaintext);
    }
    public bool is_RSAEncryptInput { get { return true; } }
    public software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode dtor_padding {
      get {
        return this._padding;
      }
    }
    public Dafny.ISequence<byte> dtor_publicKey {
      get {
        return this._publicKey;
      }
    }
    public Dafny.ISequence<byte> dtor_plaintext {
      get {
        return this._plaintext;
      }
    }
  }

  public partial class RSAModulusLengthBits {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class RSAModulusLengthBitsToGenerate {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IRSAPaddingMode {
    bool is_PKCS1 { get; }
    bool is_OAEP__SHA1 { get; }
    bool is_OAEP__SHA256 { get; }
    bool is_OAEP__SHA384 { get; }
    bool is_OAEP__SHA512 { get; }
    _IRSAPaddingMode DowncastClone();
  }
  public abstract class RSAPaddingMode : _IRSAPaddingMode {
    public RSAPaddingMode() { }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode theDefault = create_PKCS1();
    public static software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode>(software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAPaddingMode> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRSAPaddingMode create_PKCS1() {
      return new RSAPaddingMode_PKCS1();
    }
    public static _IRSAPaddingMode create_OAEP__SHA1() {
      return new RSAPaddingMode_OAEP__SHA1();
    }
    public static _IRSAPaddingMode create_OAEP__SHA256() {
      return new RSAPaddingMode_OAEP__SHA256();
    }
    public static _IRSAPaddingMode create_OAEP__SHA384() {
      return new RSAPaddingMode_OAEP__SHA384();
    }
    public static _IRSAPaddingMode create_OAEP__SHA512() {
      return new RSAPaddingMode_OAEP__SHA512();
    }
    public bool is_PKCS1 { get { return this is RSAPaddingMode_PKCS1; } }
    public bool is_OAEP__SHA1 { get { return this is RSAPaddingMode_OAEP__SHA1; } }
    public bool is_OAEP__SHA256 { get { return this is RSAPaddingMode_OAEP__SHA256; } }
    public bool is_OAEP__SHA384 { get { return this is RSAPaddingMode_OAEP__SHA384; } }
    public bool is_OAEP__SHA512 { get { return this is RSAPaddingMode_OAEP__SHA512; } }
    public static System.Collections.Generic.IEnumerable<_IRSAPaddingMode> AllSingletonConstructors {
      get {
        yield return RSAPaddingMode.create_PKCS1();
        yield return RSAPaddingMode.create_OAEP__SHA1();
        yield return RSAPaddingMode.create_OAEP__SHA256();
        yield return RSAPaddingMode.create_OAEP__SHA384();
        yield return RSAPaddingMode.create_OAEP__SHA512();
      }
    }
    public abstract _IRSAPaddingMode DowncastClone();
  }
  public class RSAPaddingMode_PKCS1 : RSAPaddingMode {
    public RSAPaddingMode_PKCS1() {
    }
    public override _IRSAPaddingMode DowncastClone() {
      if (this is _IRSAPaddingMode dt) { return dt; }
      return new RSAPaddingMode_PKCS1();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode_PKCS1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.RSAPaddingMode.PKCS1";
      return s;
    }
  }
  public class RSAPaddingMode_OAEP__SHA1 : RSAPaddingMode {
    public RSAPaddingMode_OAEP__SHA1() {
    }
    public override _IRSAPaddingMode DowncastClone() {
      if (this is _IRSAPaddingMode dt) { return dt; }
      return new RSAPaddingMode_OAEP__SHA1();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode_OAEP__SHA1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.RSAPaddingMode.OAEP_SHA1";
      return s;
    }
  }
  public class RSAPaddingMode_OAEP__SHA256 : RSAPaddingMode {
    public RSAPaddingMode_OAEP__SHA256() {
    }
    public override _IRSAPaddingMode DowncastClone() {
      if (this is _IRSAPaddingMode dt) { return dt; }
      return new RSAPaddingMode_OAEP__SHA256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode_OAEP__SHA256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.RSAPaddingMode.OAEP_SHA256";
      return s;
    }
  }
  public class RSAPaddingMode_OAEP__SHA384 : RSAPaddingMode {
    public RSAPaddingMode_OAEP__SHA384() {
    }
    public override _IRSAPaddingMode DowncastClone() {
      if (this is _IRSAPaddingMode dt) { return dt; }
      return new RSAPaddingMode_OAEP__SHA384();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode_OAEP__SHA384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.RSAPaddingMode.OAEP_SHA384";
      return s;
    }
  }
  public class RSAPaddingMode_OAEP__SHA512 : RSAPaddingMode {
    public RSAPaddingMode_OAEP__SHA512() {
    }
    public override _IRSAPaddingMode DowncastClone() {
      if (this is _IRSAPaddingMode dt) { return dt; }
      return new RSAPaddingMode_OAEP__SHA512();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.RSAPaddingMode_OAEP__SHA512;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.RSAPaddingMode.OAEP_SHA512";
      return s;
    }
  }

  public interface _IRSAPrivateKey {
    bool is_RSAPrivateKey { get; }
    int dtor_lengthBits { get; }
    Dafny.ISequence<byte> dtor_pem { get; }
    _IRSAPrivateKey DowncastClone();
  }
  public class RSAPrivateKey : _IRSAPrivateKey {
    public readonly int _lengthBits;
    public readonly Dafny.ISequence<byte> _pem;
    public RSAPrivateKey(int lengthBits, Dafny.ISequence<byte> pem) {
      this._lengthBits = lengthBits;
      this._pem = pem;
    }
    public _IRSAPrivateKey DowncastClone() {
      if (this is _IRSAPrivateKey dt) { return dt; }
      return new RSAPrivateKey(_lengthBits, _pem);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.RSAPrivateKey;
      return oth != null && this._lengthBits == oth._lengthBits && object.Equals(this._pem, oth._pem);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lengthBits));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pem));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.RSAPrivateKey.RSAPrivateKey";
      s += "(";
      s += Dafny.Helpers.ToString(this._lengthBits);
      s += ", ";
      s += Dafny.Helpers.ToString(this._pem);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey theDefault = create(0, Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey>(software.amazon.cryptography.primitives.internaldafny.types.RSAPrivateKey.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRSAPrivateKey create(int lengthBits, Dafny.ISequence<byte> pem) {
      return new RSAPrivateKey(lengthBits, pem);
    }
    public static _IRSAPrivateKey create_RSAPrivateKey(int lengthBits, Dafny.ISequence<byte> pem) {
      return create(lengthBits, pem);
    }
    public bool is_RSAPrivateKey { get { return true; } }
    public int dtor_lengthBits {
      get {
        return this._lengthBits;
      }
    }
    public Dafny.ISequence<byte> dtor_pem {
      get {
        return this._pem;
      }
    }
  }

  public interface _IRSAPublicKey {
    bool is_RSAPublicKey { get; }
    int dtor_lengthBits { get; }
    Dafny.ISequence<byte> dtor_pem { get; }
    _IRSAPublicKey DowncastClone();
  }
  public class RSAPublicKey : _IRSAPublicKey {
    public readonly int _lengthBits;
    public readonly Dafny.ISequence<byte> _pem;
    public RSAPublicKey(int lengthBits, Dafny.ISequence<byte> pem) {
      this._lengthBits = lengthBits;
      this._pem = pem;
    }
    public _IRSAPublicKey DowncastClone() {
      if (this is _IRSAPublicKey dt) { return dt; }
      return new RSAPublicKey(_lengthBits, _pem);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.RSAPublicKey;
      return oth != null && this._lengthBits == oth._lengthBits && object.Equals(this._pem, oth._pem);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lengthBits));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pem));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.RSAPublicKey.RSAPublicKey";
      s += "(";
      s += Dafny.Helpers.ToString(this._lengthBits);
      s += ", ";
      s += Dafny.Helpers.ToString(this._pem);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey theDefault = create(0, Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey>(software.amazon.cryptography.primitives.internaldafny.types.RSAPublicKey.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRSAPublicKey create(int lengthBits, Dafny.ISequence<byte> pem) {
      return new RSAPublicKey(lengthBits, pem);
    }
    public static _IRSAPublicKey create_RSAPublicKey(int lengthBits, Dafny.ISequence<byte> pem) {
      return create(lengthBits, pem);
    }
    public bool is_RSAPublicKey { get { return true; } }
    public int dtor_lengthBits {
      get {
        return this._lengthBits;
      }
    }
    public Dafny.ISequence<byte> dtor_pem {
      get {
        return this._pem;
      }
    }
  }

  public partial class SymmetricKeyLength {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class Uint8Bits {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class Uint8Bytes {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IError {
    bool is_AwsCryptographicPrimitivesError { get; }
    bool is_CollectionOfErrors { get; }
    bool is_Opaque { get; }
    Dafny.ISequence<char> dtor_message { get; }
    Dafny.ISequence<software.amazon.cryptography.primitives.internaldafny.types._IError> dtor_list { get; }
    object dtor_obj { get; }
    _IError DowncastClone();
  }
  public abstract class Error : _IError {
    public Error() { }
    private static readonly software.amazon.cryptography.primitives.internaldafny.types._IError theDefault = create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.primitives.internaldafny.types._IError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IError> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IError>(software.amazon.cryptography.primitives.internaldafny.types.Error.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IError create_AwsCryptographicPrimitivesError(Dafny.ISequence<char> message) {
      return new Error_AwsCryptographicPrimitivesError(message);
    }
    public static _IError create_CollectionOfErrors(Dafny.ISequence<software.amazon.cryptography.primitives.internaldafny.types._IError> list, Dafny.ISequence<char> message) {
      return new Error_CollectionOfErrors(list, message);
    }
    public static _IError create_Opaque(object obj) {
      return new Error_Opaque(obj);
    }
    public bool is_AwsCryptographicPrimitivesError { get { return this is Error_AwsCryptographicPrimitivesError; } }
    public bool is_CollectionOfErrors { get { return this is Error_CollectionOfErrors; } }
    public bool is_Opaque { get { return this is Error_Opaque; } }
    public Dafny.ISequence<char> dtor_message {
      get {
        var d = this;
        if (d is Error_AwsCryptographicPrimitivesError) { return ((Error_AwsCryptographicPrimitivesError)d)._message; }
        return ((Error_CollectionOfErrors)d)._message;
      }
    }
    public Dafny.ISequence<software.amazon.cryptography.primitives.internaldafny.types._IError> dtor_list {
      get {
        var d = this;
        return ((Error_CollectionOfErrors)d)._list;
      }
    }
    public object dtor_obj {
      get {
        var d = this;
        return ((Error_Opaque)d)._obj;
      }
    }
    public abstract _IError DowncastClone();
  }
  public class Error_AwsCryptographicPrimitivesError : Error {
    public readonly Dafny.ISequence<char> _message;
    public Error_AwsCryptographicPrimitivesError(Dafny.ISequence<char> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_AwsCryptographicPrimitivesError(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.Error_AwsCryptographicPrimitivesError;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.Error.AwsCryptographicPrimitivesError";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_CollectionOfErrors : Error {
    public readonly Dafny.ISequence<software.amazon.cryptography.primitives.internaldafny.types._IError> _list;
    public readonly Dafny.ISequence<char> _message;
    public Error_CollectionOfErrors(Dafny.ISequence<software.amazon.cryptography.primitives.internaldafny.types._IError> list, Dafny.ISequence<char> message) {
      this._list = list;
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CollectionOfErrors(_list, _message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.Error_CollectionOfErrors;
      return oth != null && object.Equals(this._list, oth._list) && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._list));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.Error.CollectionOfErrors";
      s += "(";
      s += Dafny.Helpers.ToString(this._list);
      s += ", ";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_Opaque : Error {
    public readonly object _obj;
    public Error_Opaque(object obj) {
      this._obj = obj;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_Opaque(_obj);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.primitives.internaldafny.types.Error_Opaque;
      return oth != null && this._obj == oth._obj;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.primitives.internaldafny.types_Compile.Error.Opaque";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ")";
      return s;
    }
  }

  public partial class OpaqueError {
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IError> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IError>(software.amazon.cryptography.primitives.internaldafny.types.Error.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.primitives.internaldafny.types._IError> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool IsValid__PositiveInteger(int x) {
      return (0) <= (x);
    }
    public static bool IsValid__RSAModulusLengthBits(int x) {
      return (81) <= (x);
    }
    public static bool IsValid__RSAModulusLengthBitsToGenerate(int x) {
      return ((81) <= (x)) && ((x) <= (4096));
    }
    public static bool IsValid__SymmetricKeyLength(int x) {
      return ((1) <= (x)) && ((x) <= (32));
    }
    public static bool IsValid__Uint8Bits(int x) {
      return ((0) <= (x)) && ((x) <= (255));
    }
    public static bool IsValid__Uint8Bytes(int x) {
      return ((0) <= (x)) && ((x) <= (32));
    }
  }
} // end of namespace software.amazon.cryptography.primitives.internaldafny.types
namespace ExternRandom {

} // end of namespace ExternRandom
namespace Random_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> GenerateBytes(int i)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _0_value;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _1_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out0;
      _out0 = ExternRandom.__default.GenerateBytes(i);
      _1_valueOrError0 = _out0;
      if ((_1_valueOrError0).IsFailure()) {
        res = (_1_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _0_value = (_1_valueOrError0).Extract();
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _2_valueOrError1 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _2_valueOrError1 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((new BigInteger((_0_value).Count)) == (new BigInteger(i)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Incorrect length from ExternRandom.")));
      if ((_2_valueOrError1).IsFailure()) {
        res = (_2_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      res = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(_0_value);
      return res;
      return res;
    }
  }
} // end of namespace Random_Compile
namespace AESEncryption {

  public partial class __default {
    public static software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput EncryptionOutputFromByteSeq(Dafny.ISequence<byte> s, software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM encAlg)
    {
      Dafny.ISequence<byte> _3_cipherText = (s).Take((new BigInteger((s).Count)) - (new BigInteger((encAlg).dtor_tagLength)));
      Dafny.ISequence<byte> _4_authTag = (s).Drop((new BigInteger((s).Count)) - (new BigInteger((encAlg).dtor_tagLength)));
      return software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput.create(_3_cipherText, _4_authTag);
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> AESEncrypt(software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> res = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput.Default());
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _5_valueOrError0 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _5_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>(((new BigInteger(((input).dtor_iv).Count)) == (new BigInteger(((input).dtor_encAlg).dtor_ivLength))) && ((new BigInteger(((input).dtor_key).Count)) == (new BigInteger(((input).dtor_encAlg).dtor_keyLength))), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Request does not match algorithm.")));
      if ((_5_valueOrError0).IsFailure()) {
        res = (_5_valueOrError0).PropagateFailure<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput>();
        return res;
      }
      software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput _let_tmp_rhs0 = input;
      software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM _6_encAlg = _let_tmp_rhs0.dtor_encAlg;
      Dafny.ISequence<byte> _7_iv = _let_tmp_rhs0.dtor_iv;
      Dafny.ISequence<byte> _8_key = _let_tmp_rhs0.dtor_key;
      Dafny.ISequence<byte> _9_msg = _let_tmp_rhs0.dtor_msg;
      Dafny.ISequence<byte> _10_aad = _let_tmp_rhs0.dtor_aad;
      software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput _11_value;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _12_valueOrError1 = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _out1;
      _out1 = AESEncryption.AES_GCM.AESEncryptExtern(_6_encAlg, _7_iv, _8_key, _9_msg, _10_aad);
      _12_valueOrError1 = _out1;
      if ((_12_valueOrError1).IsFailure()) {
        res = (_12_valueOrError1).PropagateFailure<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput>();
        return res;
      }
      _11_value = (_12_valueOrError1).Extract();
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _13_valueOrError2 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _13_valueOrError2 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((new BigInteger(((_11_value).dtor_cipherText).Count)) == (new BigInteger((_9_msg).Count)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("AESEncrypt did not return cipherText of expected length")));
      if ((_13_valueOrError2).IsFailure()) {
        res = (_13_valueOrError2).PropagateFailure<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput>();
        return res;
      }
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _14_valueOrError3 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _14_valueOrError3 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((new BigInteger(((_11_value).dtor_authTag).Count)) == (new BigInteger((_6_encAlg).dtor_tagLength)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("AESEncryption did not return valid tag")));
      if ((_14_valueOrError3).IsFailure()) {
        res = (_14_valueOrError3).PropagateFailure<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput>();
        return res;
      }
      res = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(_11_value);
      return res;
      return res;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> AESDecrypt(software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _15_valueOrError0 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _15_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((((new BigInteger(((input).dtor_key).Count)) == (new BigInteger(((input).dtor_encAlg).dtor_keyLength))) && ((new BigInteger(((input).dtor_iv).Count)) == (new BigInteger(((input).dtor_encAlg).dtor_ivLength)))) && ((new BigInteger(((input).dtor_authTag).Count)) == (new BigInteger(((input).dtor_encAlg).dtor_tagLength))), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Request does not match algorithm.")));
      if ((_15_valueOrError0).IsFailure()) {
        res = (_15_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput _let_tmp_rhs1 = input;
      software.amazon.cryptography.primitives.internaldafny.types._IAES__GCM _16_encAlg = _let_tmp_rhs1.dtor_encAlg;
      Dafny.ISequence<byte> _17_key = _let_tmp_rhs1.dtor_key;
      Dafny.ISequence<byte> _18_cipherTxt = _let_tmp_rhs1.dtor_cipherTxt;
      Dafny.ISequence<byte> _19_authTag = _let_tmp_rhs1.dtor_authTag;
      Dafny.ISequence<byte> _20_iv = _let_tmp_rhs1.dtor_iv;
      Dafny.ISequence<byte> _21_aad = _let_tmp_rhs1.dtor_aad;
      Dafny.ISequence<byte> _22_value;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _23_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out2;
      _out2 = AESEncryption.AES_GCM.AESDecryptExtern(_16_encAlg, _17_key, _18_cipherTxt, _19_authTag, _20_iv, _21_aad);
      _23_valueOrError1 = _out2;
      if ((_23_valueOrError1).IsFailure()) {
        res = (_23_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _22_value = (_23_valueOrError1).Extract();
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _24_valueOrError2 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _24_valueOrError2 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((new BigInteger((_18_cipherTxt).Count)) == (new BigInteger((_22_value).Count)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("AESDecrypt did not return plaintext of expected length")));
      if ((_24_valueOrError2).IsFailure()) {
        res = (_24_valueOrError2).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      res = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(_22_value);
      return res;
      return res;
    }
  }
} // end of namespace AESEncryption
namespace ExternDigest {

} // end of namespace ExternDigest
namespace Digest_Compile {

  public partial class __default {
    public static BigInteger Length(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digestAlgorithm) {
      software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _source0 = digestAlgorithm;
      if (_source0.is_SHA__512) {
        return new BigInteger(64);
      } else if (_source0.is_SHA__384) {
        return new BigInteger(48);
      } else {
        return new BigInteger(32);
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Digest(software.amazon.cryptography.primitives.internaldafny.types._IDigestInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      software.amazon.cryptography.primitives.internaldafny.types._IDigestInput _let_tmp_rhs2 = input;
      software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _25_digestAlgorithm = _let_tmp_rhs2.dtor_digestAlgorithm;
      Dafny.ISequence<byte> _26_message = _let_tmp_rhs2.dtor_message;
      Dafny.ISequence<byte> _27_value;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _28_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out3;
      _out3 = ExternDigest.__default.Digest(_25_digestAlgorithm, _26_message);
      _28_valueOrError0 = _out3;
      if ((_28_valueOrError0).IsFailure()) {
        res = (_28_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _27_value = (_28_valueOrError0).Extract();
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _29_valueOrError1 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _29_valueOrError1 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((new BigInteger((_27_value).Count)) == (Digest_Compile.__default.Length(_25_digestAlgorithm)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Incorrect length digest from ExternDigest.")));
      if ((_29_valueOrError1).IsFailure()) {
        res = (_29_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      res = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(_27_value);
      return res;
      return res;
    }
  }
} // end of namespace Digest_Compile
namespace HMAC {

  public partial class HMac {
    public HMac() {
    }
  }

} // end of namespace HMAC
namespace WrappedHMAC_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Digest(software.amazon.cryptography.primitives.internaldafny.types._IHMacInput input) {
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _30_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((new BigInteger(((input).dtor_key).Count)).Sign == 1, software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Key MUST NOT be 0 bytes.")));
      if ((_30_valueOrError0).IsFailure()) {
        return (_30_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _31_valueOrError1 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((new BigInteger(((input).dtor_message).Count)) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Message over INT32_MAX_LIMIT")));
        if ((_31_valueOrError1).IsFailure()) {
          return (_31_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        } else {
          Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _32_valueOrError2 = HMAC.__default.Digest(input);
          if ((_32_valueOrError2).IsFailure()) {
            return (_32_valueOrError2).PropagateFailure<Dafny.ISequence<byte>>();
          } else {
            Dafny.ISequence<byte> _33_value = (_32_valueOrError2).Extract();
            return Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(_33_value);
          }
        }
      }
    }
  }
} // end of namespace WrappedHMAC_Compile
namespace HKDF_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> Extract(HMAC.HMac hmac, Dafny.ISequence<byte> salt, Dafny.ISequence<byte> ikm)
    {
      Dafny.ISequence<byte> prk = Dafny.Sequence<byte>.Empty;
      (hmac).Init(salt);
      (hmac).BlockUpdate(ikm);
      Dafny.ISequence<byte> _out4;
      _out4 = (hmac).GetResult();
      prk = _out4;
      prk = prk;
      return prk;
      return prk;
    }
    public static Dafny.ISequence<byte> Expand(HMAC.HMac hmac, Dafny.ISequence<byte> prk, Dafny.ISequence<byte> info, BigInteger expectedLength, software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digest)
    {
      Dafny.ISequence<byte> okm = Dafny.Sequence<byte>.Empty;
      BigInteger _34_hashLength;
      _34_hashLength = Digest_Compile.__default.Length(digest);
      BigInteger _35_n;
      _35_n = Dafny.Helpers.EuclideanDivision(((_34_hashLength) + (expectedLength)) - (BigInteger.One), _34_hashLength);
      (hmac).Init(prk);
      Dafny.ISequence<byte> _36_t__prev;
      _36_t__prev = Dafny.Sequence<byte>.FromElements();
      Dafny.ISequence<byte> _37_t__n;
      _37_t__n = _36_t__prev;
      BigInteger _38_i;
      _38_i = BigInteger.One;
      while ((_38_i) <= (_35_n)) {
        (hmac).BlockUpdate(_36_t__prev);
        (hmac).BlockUpdate(info);
        (hmac).BlockUpdate(Dafny.Sequence<byte>.FromElements((byte)(_38_i)));
        Dafny.ISequence<byte> _out5;
        _out5 = (hmac).GetResult();
        _36_t__prev = _out5;
        _37_t__n = Dafny.Sequence<byte>.Concat(_37_t__n, _36_t__prev);
        _38_i = (_38_i) + (BigInteger.One);
      }
      okm = _37_t__n;
      if ((expectedLength) < (new BigInteger((okm).Count))) {
        okm = (okm).Take(expectedLength);
      }
      return okm;
    }
    public static Dafny.ISequence<byte> Hkdf(software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm digest, Wrappers_Compile._IOption<Dafny.ISequence<byte>> salt, Dafny.ISequence<byte> ikm, Dafny.ISequence<byte> info, BigInteger L)
    {
      Dafny.ISequence<byte> okm = Dafny.Sequence<byte>.Empty;
      if ((L).Sign == 0) {
        okm = Dafny.Sequence<byte>.FromElements();
        return okm;
      }
      HMAC.HMac _39_hmac;
      Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError> _40_valueOrError0 = default(Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError> _out6;
      _out6 = HMAC.HMac.Build(digest);
      _40_valueOrError0 = _out6;
      if (!(!((_40_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/src/HKDF/HKDF.dfy(222,13): " + _40_valueOrError0);}
      _39_hmac = (_40_valueOrError0).Extract();
      BigInteger _41_hashLength;
      _41_hashLength = Digest_Compile.__default.Length(digest);
      Dafny.ISequence<byte> _42_nonEmptySalt = Dafny.Sequence<byte>.Empty;
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _source1 = salt;
      if (_source1.is_None) {
        _42_nonEmptySalt = StandardLibrary_Compile.__default.Fill<byte>((byte)(0), _41_hashLength);
      } else {
        Dafny.ISequence<byte> _43___mcc_h0 = _source1.dtor_value;
        Dafny.ISequence<byte> _44_s = _43___mcc_h0;
        _42_nonEmptySalt = _44_s;
      }
      Dafny.ISequence<byte> _45_prk;
      Dafny.ISequence<byte> _out7;
      _out7 = HKDF_Compile.__default.Extract(_39_hmac, _42_nonEmptySalt, ikm);
      _45_prk = _out7;
      Dafny.ISequence<byte> _out8;
      _out8 = HKDF_Compile.__default.Expand(_39_hmac, _45_prk, info, L, digest);
      okm = _out8;
      return okm;
    }
  }
} // end of namespace HKDF_Compile
namespace WrappedHKDF_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Extract(software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _46_valueOrError0 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _46_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>(((((input).dtor_salt).is_None) || ((new BigInteger((((input).dtor_salt).dtor_value).Count)).Sign != 0)) && ((new BigInteger(((input).dtor_ikm).Count)) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("HKDF Extract needs a salt and reasonable ikm.")));
      if ((_46_valueOrError0).IsFailure()) {
        output = (_46_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput _let_tmp_rhs3 = input;
      software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _47_digestAlgorithm = _let_tmp_rhs3.dtor_digestAlgorithm;
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _48_salt = _let_tmp_rhs3.dtor_salt;
      Dafny.ISequence<byte> _49_ikm = _let_tmp_rhs3.dtor_ikm;
      HMAC.HMac _50_hmac;
      Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError> _51_valueOrError1 = default(Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError> _out9;
      _out9 = HMAC.HMac.Build(_47_digestAlgorithm);
      _51_valueOrError1 = _out9;
      if ((_51_valueOrError1).IsFailure()) {
        output = (_51_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      _50_hmac = (_51_valueOrError1).Extract();
      Dafny.ISequence<byte> _52_prk;
      Dafny.ISequence<byte> _out10;
      _out10 = HKDF_Compile.__default.Extract(_50_hmac, Wrappers_Compile.Option<Dafny.ISequence<byte>>.UnwrapOr(_48_salt, StandardLibrary_Compile.__default.Fill<byte>((byte)(0), Digest_Compile.__default.Length(_47_digestAlgorithm))), _49_ikm);
      _52_prk = _out10;
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(_52_prk);
      return output;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Expand(software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _53_valueOrError0 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _53_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>(((((BigInteger.One) <= (new BigInteger((input).dtor_expectedLength))) && ((new BigInteger((input).dtor_expectedLength)) <= ((new BigInteger(255)) * (Digest_Compile.__default.Length((input).dtor_digestAlgorithm))))) && ((new BigInteger(((input).dtor_info).Count)) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT))) && ((Digest_Compile.__default.Length((input).dtor_digestAlgorithm)) == (new BigInteger(((input).dtor_prk).Count))), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("HKDF Expand needs valid input.")));
      if ((_53_valueOrError0).IsFailure()) {
        output = (_53_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput _let_tmp_rhs4 = input;
      software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _54_digestAlgorithm = _let_tmp_rhs4.dtor_digestAlgorithm;
      Dafny.ISequence<byte> _55_prk = _let_tmp_rhs4.dtor_prk;
      Dafny.ISequence<byte> _56_info = _let_tmp_rhs4.dtor_info;
      int _57_expectedLength = _let_tmp_rhs4.dtor_expectedLength;
      HMAC.HMac _58_hmac;
      Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError> _59_valueOrError1 = default(Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError> _out11;
      _out11 = HMAC.HMac.Build(_54_digestAlgorithm);
      _59_valueOrError1 = _out11;
      if ((_59_valueOrError1).IsFailure()) {
        output = (_59_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      _58_hmac = (_59_valueOrError1).Extract();
      Dafny.ISequence<byte> _60_omk;
      Dafny.ISequence<byte> _out12;
      _out12 = HKDF_Compile.__default.Expand(_58_hmac, _55_prk, _56_info, new BigInteger(_57_expectedLength), _54_digestAlgorithm);
      _60_omk = _out12;
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(_60_omk);
      return output;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Hkdf(software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _61_valueOrError0 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _61_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((((((BigInteger.One) <= (new BigInteger((input).dtor_expectedLength))) && ((new BigInteger((input).dtor_expectedLength)) <= ((new BigInteger(255)) * (Digest_Compile.__default.Length((input).dtor_digestAlgorithm))))) && ((((input).dtor_salt).is_None) || ((new BigInteger((((input).dtor_salt).dtor_value).Count)).Sign != 0))) && ((new BigInteger(((input).dtor_info).Count)) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT))) && ((new BigInteger(((input).dtor_ikm).Count)) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Wrapped Hkdf input is invalid.")));
      if ((_61_valueOrError0).IsFailure()) {
        output = (_61_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput _let_tmp_rhs5 = input;
      software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _62_digest = _let_tmp_rhs5.dtor_digestAlgorithm;
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _63_salt = _let_tmp_rhs5.dtor_salt;
      Dafny.ISequence<byte> _64_ikm = _let_tmp_rhs5.dtor_ikm;
      Dafny.ISequence<byte> _65_info = _let_tmp_rhs5.dtor_info;
      int _66_expectedLength = _let_tmp_rhs5.dtor_expectedLength;
      Dafny.ISequence<byte> _67_okm;
      Dafny.ISequence<byte> _out13;
      _out13 = HKDF_Compile.__default.Hkdf(_62_digest, _63_salt, _64_ikm, _65_info, new BigInteger(_66_expectedLength));
      _67_okm = _out13;
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(_67_okm);
      return output;
      return output;
    }
  }
} // end of namespace WrappedHKDF_Compile
namespace Signature {

  public interface _ISignatureKeyPair {
    bool is_SignatureKeyPair { get; }
    Dafny.ISequence<byte> dtor_verificationKey { get; }
    Dafny.ISequence<byte> dtor_signingKey { get; }
    _ISignatureKeyPair DowncastClone();
  }
  public class SignatureKeyPair : _ISignatureKeyPair {
    public readonly Dafny.ISequence<byte> _verificationKey;
    public readonly Dafny.ISequence<byte> _signingKey;
    public SignatureKeyPair(Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> signingKey) {
      this._verificationKey = verificationKey;
      this._signingKey = signingKey;
    }
    public _ISignatureKeyPair DowncastClone() {
      if (this is _ISignatureKeyPair dt) { return dt; }
      return new SignatureKeyPair(_verificationKey, _signingKey);
    }
    public override bool Equals(object other) {
      var oth = other as Signature.SignatureKeyPair;
      return oth != null && object.Equals(this._verificationKey, oth._verificationKey) && object.Equals(this._signingKey, oth._signingKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._verificationKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._signingKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Signature_Compile.SignatureKeyPair.SignatureKeyPair";
      s += "(";
      s += Dafny.Helpers.ToString(this._verificationKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._signingKey);
      s += ")";
      return s;
    }
    private static readonly Signature._ISignatureKeyPair theDefault = create(Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
    public static Signature._ISignatureKeyPair Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Signature._ISignatureKeyPair> _TYPE = new Dafny.TypeDescriptor<Signature._ISignatureKeyPair>(Signature.SignatureKeyPair.Default());
    public static Dafny.TypeDescriptor<Signature._ISignatureKeyPair> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISignatureKeyPair create(Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> signingKey) {
      return new SignatureKeyPair(verificationKey, signingKey);
    }
    public static _ISignatureKeyPair create_SignatureKeyPair(Dafny.ISequence<byte> verificationKey, Dafny.ISequence<byte> signingKey) {
      return create(verificationKey, signingKey);
    }
    public bool is_SignatureKeyPair { get { return true; } }
    public Dafny.ISequence<byte> dtor_verificationKey {
      get {
        return this._verificationKey;
      }
    }
    public Dafny.ISequence<byte> dtor_signingKey {
      get {
        return this._signingKey;
      }
    }
  }

  public partial class __default {
    public static ushort SignatureLength(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm) {
      software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm _source2 = signatureAlgorithm;
      if (_source2.is_ECDSA__P384) {
        return (ushort)(103);
      } else {
        return (ushort)(71);
      }
    }
    public static BigInteger FieldSize(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm signatureAlgorithm) {
      software.amazon.cryptography.primitives.internaldafny.types._IECDSASignatureAlgorithm _source3 = signatureAlgorithm;
      if (_source3.is_ECDSA__P384) {
        return new BigInteger(49);
      } else {
        return new BigInteger(33);
      }
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> KeyGen(software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> res = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput.Default());
      Signature._ISignatureKeyPair _68_sigKeyPair;
      Wrappers_Compile._IResult<Signature._ISignatureKeyPair, software.amazon.cryptography.primitives.internaldafny.types._IError> _69_valueOrError0 = Wrappers_Compile.Result<Signature._ISignatureKeyPair, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Signature.SignatureKeyPair.Default());
      Wrappers_Compile._IResult<Signature._ISignatureKeyPair, software.amazon.cryptography.primitives.internaldafny.types._IError> _out14;
      _out14 = Signature.ECDSA.ExternKeyGen((input).dtor_signatureAlgorithm);
      _69_valueOrError0 = _out14;
      if ((_69_valueOrError0).IsFailure()) {
        res = (_69_valueOrError0).PropagateFailure<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput>();
        return res;
      }
      _68_sigKeyPair = (_69_valueOrError0).Extract();
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _70_valueOrError1 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _70_valueOrError1 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((new BigInteger(((_68_sigKeyPair).dtor_verificationKey).Count)) == (Signature.__default.FieldSize((input).dtor_signatureAlgorithm)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Incorrect verification-key length from ExternKeyGen.")));
      if ((_70_valueOrError1).IsFailure()) {
        res = (_70_valueOrError1).PropagateFailure<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput>();
        return res;
      }
      res = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput.create((input).dtor_signatureAlgorithm, (_68_sigKeyPair).dtor_verificationKey, (_68_sigKeyPair).dtor_signingKey));
      return res;
      return res;
    }
  }
} // end of namespace Signature
namespace KdfCtr_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> KdfCounterMode(software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _71_valueOrError0 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _71_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((((((object.Equals((input).dtor_digestAlgorithm, software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256())) && ((new BigInteger(((input).dtor_ikm).Count)) == (new BigInteger(32)))) && (((input).dtor_nonce).is_Some)) && ((new BigInteger((((input).dtor_nonce).dtor_value).Count)) == (new BigInteger(16)))) && (((input).dtor_expectedLength) == (32))) && ((((new BigInteger((input).dtor_expectedLength)) * (new BigInteger(8))).Sign == 1) && (((new BigInteger((input).dtor_expectedLength)) * (new BigInteger(8))) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT))), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Kdf in Counter Mode input is invalid.")));
      if ((_71_valueOrError0).IsFailure()) {
        output = (_71_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      Dafny.ISequence<byte> _72_ikm;
      _72_ikm = (input).dtor_ikm;
      Dafny.ISequence<byte> _73_label__;
      _73_label__ = Wrappers_Compile.Option<Dafny.ISequence<byte>>.UnwrapOr((input).dtor_purpose, Dafny.Sequence<byte>.FromElements());
      Dafny.ISequence<byte> _74_info;
      _74_info = Wrappers_Compile.Option<Dafny.ISequence<byte>>.UnwrapOr((input).dtor_nonce, Dafny.Sequence<byte>.FromElements());
      Dafny.ISequence<byte> _75_okm;
      _75_okm = Dafny.Sequence<byte>.FromElements();
      uint _76_internalLength;
      _76_internalLength = (uint)(((new BigInteger(4)) + (new BigInteger((KdfCtr_Compile.__default.SEPARATION__INDICATOR).Count))) + (new BigInteger(4)));
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _77_valueOrError1 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _77_valueOrError1 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((true) && ((((new BigInteger(_76_internalLength)) + (new BigInteger((_73_label__).Count))) + (new BigInteger((_74_info).Count))) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Input Length exceeds INT32_MAX_LIMIT")));
      if ((_77_valueOrError1).IsFailure()) {
        output = (_77_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      Dafny.ISequence<byte> _78_lengthBits;
      _78_lengthBits = StandardLibrary_mUInt_Compile.__default.UInt32ToSeq((uint)(((input).dtor_expectedLength) * (8)));
      Dafny.ISequence<byte> _79_explicitInfo;
      _79_explicitInfo = Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(_73_label__, KdfCtr_Compile.__default.SEPARATION__INDICATOR), _74_info), _78_lengthBits);
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _80_valueOrError2 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _80_valueOrError2 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>(((new BigInteger(4)) + (new BigInteger((_79_explicitInfo).Count))) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("PRF input length exceeds INT32_MAX_LIMIT.")));
      if ((_80_valueOrError2).IsFailure()) {
        output = (_80_valueOrError2).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _81_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out15;
      _out15 = KdfCtr_Compile.__default.RawDerive(_72_ikm, _79_explicitInfo, (input).dtor_expectedLength, 0);
      _81_valueOrError3 = _out15;
      if ((_81_valueOrError3).IsFailure()) {
        output = (_81_valueOrError3).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      _75_okm = (_81_valueOrError3).Extract();
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(_75_okm);
      return output;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> RawDerive(Dafny.ISequence<byte> ikm, Dafny.ISequence<byte> explicitInfo, int length, int offset)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      software.amazon.cryptography.primitives.internaldafny.types._IDigestAlgorithm _82_derivationMac;
      _82_derivationMac = software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm.create_SHA__256();
      HMAC.HMac _83_hmac;
      Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError> _84_valueOrError0 = default(Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<HMAC.HMac, software.amazon.cryptography.primitives.internaldafny.types._IError> _out16;
      _out16 = HMAC.HMac.Build(_82_derivationMac);
      _84_valueOrError0 = _out16;
      if ((_84_valueOrError0).IsFailure()) {
        output = (_84_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      _83_hmac = (_84_valueOrError0).Extract();
      (_83_hmac).Init(ikm);
      int _85_macLengthBytes;
      _85_macLengthBytes = (int)(Digest_Compile.__default.Length(_82_derivationMac));
      int _86_iterations;
      _86_iterations = Dafny.Helpers.EuclideanDivision_int(((length) + (_85_macLengthBytes)) - (1), _85_macLengthBytes);
      Dafny.ISequence<byte> _87_buffer;
      _87_buffer = Dafny.Sequence<byte>.FromElements();
      Dafny.ISequence<byte> _88_i;
      _88_i = StandardLibrary_mUInt_Compile.__default.UInt32ToSeq(KdfCtr_Compile.__default.COUNTER__START__VALUE);
      int _hi0 = (_86_iterations) + (1);
      for (int _89_iteration = 1; _89_iteration < _hi0; _89_iteration++) {
        (_83_hmac).BlockUpdate(_88_i);
        (_83_hmac).BlockUpdate(explicitInfo);
        Dafny.ISequence<byte> _90_tmp;
        Dafny.ISequence<byte> _out17;
        _out17 = (_83_hmac).GetResult();
        _90_tmp = _out17;
        _87_buffer = Dafny.Sequence<byte>.Concat(_87_buffer, _90_tmp);
        Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _91_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
        _91_valueOrError1 = KdfCtr_Compile.__default.Increment(_88_i);
        if ((_91_valueOrError1).IsFailure()) {
          output = (_91_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
          return output;
        }
        _88_i = (_91_valueOrError1).Extract();
      }
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _92_valueOrError2 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _92_valueOrError2 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>((new BigInteger((_87_buffer).Count)) >= (new BigInteger(length)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Failed to derive key of requested length")));
      if ((_92_valueOrError2).IsFailure()) {
        output = (_92_valueOrError2).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success((_87_buffer).Take(length));
      return output;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Increment(Dafny.ISequence<byte> x) {
      if (((x).Select(new BigInteger(3))) < ((byte)(255))) {
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(Dafny.Sequence<byte>.FromElements((x).Select(BigInteger.Zero), (x).Select(BigInteger.One), (x).Select(new BigInteger(2)), (byte)(((x).Select(new BigInteger(3))) + ((byte)(1)))));
      } else if (((x).Select(new BigInteger(2))) < ((byte)(255))) {
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(Dafny.Sequence<byte>.FromElements((x).Select(BigInteger.Zero), (x).Select(BigInteger.One), (byte)(((x).Select(new BigInteger(2))) + ((byte)(1))), (byte)(0)));
      } else if (((x).Select(BigInteger.One)) < ((byte)(255))) {
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(Dafny.Sequence<byte>.FromElements((x).Select(BigInteger.Zero), (byte)(((x).Select(BigInteger.One)) + ((byte)(1))), (byte)(0), (byte)(0)));
      } else if (((x).Select(BigInteger.Zero)) < ((byte)(255))) {
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(Dafny.Sequence<byte>.FromElements((byte)(((x).Select(BigInteger.Zero)) + ((byte)(1))), (byte)(0), (byte)(0), (byte)(0)));
      } else {
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Failure(software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Unable to derive key material; may have exceeded limit.")));
      }
    }
    public static Dafny.ISequence<byte> SEPARATION__INDICATOR { get {
      return Dafny.Sequence<byte>.FromElements((byte)(0));
    } }
    public static uint COUNTER__START__VALUE { get {
      return 1U;
    } }
  }
} // end of namespace KdfCtr_Compile
namespace RSAEncryption {

  public partial class __default {
    public static void GenerateKeyPair(int lengthBits, out software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey publicKey, out software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey privateKey)
    {
      publicKey = default(software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey);
      privateKey = default(software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey);
      Dafny.ISequence<byte> _93_pemPublic;
      Dafny.ISequence<byte> _94_pemPrivate;
      Dafny.ISequence<byte> _out18;
      Dafny.ISequence<byte> _out19;
      RSAEncryption.RSA.GenerateKeyPairExtern(lengthBits, out _out18, out _out19);
      _93_pemPublic = _out18;
      _94_pemPrivate = _out19;
      privateKey = software.amazon.cryptography.primitives.internaldafny.types.RSAPrivateKey.create(lengthBits, _94_pemPrivate);
      publicKey = software.amazon.cryptography.primitives.internaldafny.types.RSAPublicKey.create(lengthBits, _93_pemPublic);
    }
    public static Wrappers_Compile._IResult<int, software.amazon.cryptography.primitives.internaldafny.types._IError> GetRSAKeyModulusLength(Dafny.ISequence<byte> publicKey) {
      Wrappers_Compile._IResult<uint, software.amazon.cryptography.primitives.internaldafny.types._IError> _95_valueOrError0 = RSAEncryption.RSA.GetRSAKeyModulusLengthExtern(publicKey);
      if ((_95_valueOrError0).IsFailure()) {
        return (_95_valueOrError0).PropagateFailure<int>();
      } else {
        uint _96_length = (_95_valueOrError0).Extract();
        Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _97_valueOrError1 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>(((new BigInteger(81)) <= (new BigInteger(_96_length))) && ((new BigInteger(_96_length)) < (StandardLibrary_mUInt_Compile.__default.INT32__MAX__LIMIT)), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Unsupported length for RSA modulus.")));
        if ((_97_valueOrError1).IsFailure()) {
          return (_97_valueOrError1).PropagateFailure<int>();
        } else {
          return Wrappers_Compile.Result<int, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success((int)(_96_length));
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Decrypt(software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _98_valueOrError0 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _98_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>(((new BigInteger(((input).dtor_privateKey).Count)).Sign == 1) && ((new BigInteger(((input).dtor_cipherText).Count)).Sign == 1), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("")));
      if ((_98_valueOrError0).IsFailure()) {
        output = (_98_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out20;
      _out20 = RSAEncryption.RSA.DecryptExtern((input).dtor_padding, (input).dtor_privateKey, (input).dtor_cipherText);
      output = _out20;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Encrypt(software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IOutcome<software.amazon.cryptography.primitives.internaldafny.types._IError> _99_valueOrError0 = Wrappers_Compile.Outcome<software.amazon.cryptography.primitives.internaldafny.types._IError>.Default();
      _99_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.primitives.internaldafny.types._IError>(((new BigInteger(((input).dtor_publicKey).Count)).Sign == 1) && ((new BigInteger(((input).dtor_plaintext).Count)).Sign == 1), software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("")));
      if ((_99_valueOrError0).IsFailure()) {
        output = (_99_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return output;
      }
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out21;
      _out21 = RSAEncryption.RSA.EncryptExtern((input).dtor_padding, (input).dtor_publicKey, (input).dtor_plaintext);
      output = _out21;
      return output;
    }
  }
} // end of namespace RSAEncryption
namespace AwsCryptographyPrimitivesOperations_Compile {

  public interface _IConfig {
    bool is_Config { get; }
    _IConfig DowncastClone();
  }
  public class Config : _IConfig {
    public Config() {
    }
    public _IConfig DowncastClone() {
      if (this is _IConfig dt) { return dt; }
      return new Config();
    }
    public override bool Equals(object other) {
      var oth = other as AwsCryptographyPrimitivesOperations_Compile.Config;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "AwsCryptographyPrimitivesOperations_Compile.Config.Config";
      return s;
    }
    private static readonly AwsCryptographyPrimitivesOperations_Compile._IConfig theDefault = create();
    public static AwsCryptographyPrimitivesOperations_Compile._IConfig Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<AwsCryptographyPrimitivesOperations_Compile._IConfig> _TYPE = new Dafny.TypeDescriptor<AwsCryptographyPrimitivesOperations_Compile._IConfig>(AwsCryptographyPrimitivesOperations_Compile.Config.Default());
    public static Dafny.TypeDescriptor<AwsCryptographyPrimitivesOperations_Compile._IConfig> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConfig create() {
      return new Config();
    }
    public static _IConfig create_Config() {
      return create();
    }
    public bool is_Config { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IConfig> AllSingletonConstructors {
      get {
        yield return Config.create();
      }
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> GenerateRandomBytes(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IGenerateRandomBytesInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out22;
      _out22 = Random_Compile.__default.GenerateBytes((input).dtor_length);
      output = _out22;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Digest(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IDigestInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out23;
      _out23 = Digest_Compile.__default.Digest(input);
      output = _out23;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> HMac(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IHMacInput input)
    {
      return WrappedHMAC_Compile.__default.Digest(input);
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> HkdfExtract(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out24;
      _out24 = WrappedHKDF_Compile.__default.Extract(input);
      output = _out24;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> HkdfExpand(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out25;
      _out25 = WrappedHKDF_Compile.__default.Expand(input);
      output = _out25;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Hkdf(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out26;
      _out26 = WrappedHKDF_Compile.__default.Hkdf(input);
      output = _out26;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> KdfCounterMode(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out27;
      _out27 = KdfCtr_Compile.__default.KdfCounterMode(input);
      output = _out27;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> AesKdfCounterMode(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IAesKdfCtrInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Failure(software.amazon.cryptography.primitives.internaldafny.types.Error.create_AwsCryptographicPrimitivesError(Dafny.Sequence<char>.FromString("Implement")));
      return output;
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> AESEncrypt(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _out28;
      _out28 = AESEncryption.__default.AESEncrypt(input);
      output = _out28;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> AESDecrypt(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out29;
      _out29 = AESEncryption.__default.AESDecrypt(input);
      output = _out29;
      return output;
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> GenerateRSAKeyPair(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> output = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey _100_publicKey;
      software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey _101_privateKey;
      software.amazon.cryptography.primitives.internaldafny.types._IRSAPublicKey _out30;
      software.amazon.cryptography.primitives.internaldafny.types._IRSAPrivateKey _out31;
      RSAEncryption.__default.GenerateKeyPair((input).dtor_lengthBits, out _out30, out _out31);
      _100_publicKey = _out30;
      _101_privateKey = _out31;
      output = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairOutput.create(_100_publicKey, _101_privateKey));
      return output;
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> GetRSAKeyModulusLength(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthInput input)
    {
      Wrappers_Compile._IResult<int, software.amazon.cryptography.primitives.internaldafny.types._IError> _102_valueOrError0 = RSAEncryption.__default.GetRSAKeyModulusLength((input).dtor_publicKey);
      if ((_102_valueOrError0).IsFailure()) {
        return (_102_valueOrError0).PropagateFailure<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput>();
      } else {
        int _103_length = (_102_valueOrError0).Extract();
        return Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(software.amazon.cryptography.primitives.internaldafny.types.GetRSAKeyModulusLengthOutput.create(_103_length));
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> RSADecrypt(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out32;
      _out32 = RSAEncryption.__default.Decrypt(input);
      output = _out32;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> RSAEncrypt(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out33;
      _out33 = RSAEncryption.__default.Encrypt(input);
      output = _out33;
      return output;
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> GenerateECDSASignatureKey(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _out34;
      _out34 = Signature.__default.KeyGen(input);
      output = _out34;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> ECDSASign(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IECDSASignInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out35;
      _out35 = Signature.ECDSA.Sign((input).dtor_signatureAlgorithm, (input).dtor_signingKey, (input).dtor_message);
      output = _out35;
      return output;
    }
    public static Wrappers_Compile._IResult<bool, software.amazon.cryptography.primitives.internaldafny.types._IError> ECDSAVerify(AwsCryptographyPrimitivesOperations_Compile._IConfig config, software.amazon.cryptography.primitives.internaldafny.types._IECDSAVerifyInput input)
    {
      Wrappers_Compile._IResult<bool, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<bool, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(false);
      output = Signature.ECDSA.Verify((input).dtor_signatureAlgorithm, (input).dtor_verificationKey, (input).dtor_message, (input).dtor_signature);
      return output;
    }
  }
} // end of namespace AwsCryptographyPrimitivesOperations_Compile
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
namespace software.amazon.cryptography.primitives.internaldafny {

  public partial class AtomicPrimitivesClient : software.amazon.cryptography.primitives.internaldafny.types.IAwsCryptographicPrimitivesClient {
    public AtomicPrimitivesClient() {
      this._config = AwsCryptographyPrimitivesOperations_Compile.Config.Default();
    }
    public void __ctor(AwsCryptographyPrimitivesOperations_Compile._IConfig config)
    {
      (this)._config = config;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> GenerateRandomBytes(software.amazon.cryptography.primitives.internaldafny.types._IGenerateRandomBytesInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out36;
      _out36 = AwsCryptographyPrimitivesOperations_Compile.__default.GenerateRandomBytes((this).config, input);
      output = _out36;
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Digest(software.amazon.cryptography.primitives.internaldafny.types._IDigestInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out37;
      _out37 = AwsCryptographyPrimitivesOperations_Compile.__default.Digest((this).config, input);
      output = _out37;
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> HMac(software.amazon.cryptography.primitives.internaldafny.types._IHMacInput input) {
      return AwsCryptographyPrimitivesOperations_Compile.__default.HMac((this).config, input);
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> HkdfExtract(software.amazon.cryptography.primitives.internaldafny.types._IHkdfExtractInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out38;
      _out38 = AwsCryptographyPrimitivesOperations_Compile.__default.HkdfExtract((this).config, input);
      output = _out38;
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> HkdfExpand(software.amazon.cryptography.primitives.internaldafny.types._IHkdfExpandInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out39;
      _out39 = AwsCryptographyPrimitivesOperations_Compile.__default.HkdfExpand((this).config, input);
      output = _out39;
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> Hkdf(software.amazon.cryptography.primitives.internaldafny.types._IHkdfInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out40;
      _out40 = AwsCryptographyPrimitivesOperations_Compile.__default.Hkdf((this).config, input);
      output = _out40;
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> KdfCounterMode(software.amazon.cryptography.primitives.internaldafny.types._IKdfCtrInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out41;
      _out41 = AwsCryptographyPrimitivesOperations_Compile.__default.KdfCounterMode((this).config, input);
      output = _out41;
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> AesKdfCounterMode(software.amazon.cryptography.primitives.internaldafny.types._IAesKdfCtrInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out42;
      _out42 = AwsCryptographyPrimitivesOperations_Compile.__default.AesKdfCounterMode((this).config, input);
      output = _out42;
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> AESEncrypt(software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(software.amazon.cryptography.primitives.internaldafny.types.AESEncryptOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IAESEncryptOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _out43;
      _out43 = AwsCryptographyPrimitivesOperations_Compile.__default.AESEncrypt((this).config, input);
      output = _out43;
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> AESDecrypt(software.amazon.cryptography.primitives.internaldafny.types._IAESDecryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out44;
      _out44 = AwsCryptographyPrimitivesOperations_Compile.__default.AESDecrypt((this).config, input);
      output = _out44;
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> GenerateRSAKeyPair(software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> output = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _out45;
      _out45 = AwsCryptographyPrimitivesOperations_Compile.__default.GenerateRSAKeyPair((this).config, input);
      output = _out45;
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> GetRSAKeyModulusLength(software.amazon.cryptography.primitives.internaldafny.types._IGetRSAKeyModulusLengthInput input) {
      return AwsCryptographyPrimitivesOperations_Compile.__default.GetRSAKeyModulusLength((this).config, input);
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> RSADecrypt(software.amazon.cryptography.primitives.internaldafny.types._IRSADecryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out46;
      _out46 = AwsCryptographyPrimitivesOperations_Compile.__default.RSADecrypt((this).config, input);
      output = _out46;
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> RSAEncrypt(software.amazon.cryptography.primitives.internaldafny.types._IRSAEncryptInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out47;
      _out47 = AwsCryptographyPrimitivesOperations_Compile.__default.RSAEncrypt((this).config, input);
      output = _out47;
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> GenerateECDSASignatureKey(software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _out48;
      _out48 = AwsCryptographyPrimitivesOperations_Compile.__default.GenerateECDSASignatureKey((this).config, input);
      output = _out48;
      return output;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> ECDSASign(software.amazon.cryptography.primitives.internaldafny.types._IECDSASignInput input)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out49;
      _out49 = AwsCryptographyPrimitivesOperations_Compile.__default.ECDSASign((this).config, input);
      output = _out49;
      return output;
    }
    public Wrappers_Compile._IResult<bool, software.amazon.cryptography.primitives.internaldafny.types._IError> ECDSAVerify(software.amazon.cryptography.primitives.internaldafny.types._IECDSAVerifyInput input)
    {
      Wrappers_Compile._IResult<bool, software.amazon.cryptography.primitives.internaldafny.types._IError> output = Wrappers_Compile.Result<bool, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(false);
      Wrappers_Compile._IResult<bool, software.amazon.cryptography.primitives.internaldafny.types._IError> _out50;
      _out50 = AwsCryptographyPrimitivesOperations_Compile.__default.ECDSAVerify((this).config, input);
      output = _out50;
      return output;
    }
    public AwsCryptographyPrimitivesOperations_Compile._IConfig _config {get; set;}
    public AwsCryptographyPrimitivesOperations_Compile._IConfig config { get {
      return this._config;
    } }
  }

  public partial class __default {
    public static software.amazon.cryptography.primitives.internaldafny.types._ICryptoConfig DefaultCryptoConfig() {
      return software.amazon.cryptography.primitives.internaldafny.types.CryptoConfig.create();
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.types._ICryptoConfig config)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> res = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _104_client;
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _nw0 = new software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient();
      _nw0.__ctor(AwsCryptographyPrimitivesOperations_Compile.Config.create());
      _104_client = _nw0;
      res = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>.create_Success(_104_client);
      return res;
      return res;
    }
  }
} // end of namespace software.amazon.cryptography.primitives.internaldafny
namespace Aws_mCryptography_Compile {

} // end of namespace Aws_mCryptography_Compile
namespace Aws_Compile {

} // end of namespace Aws_Compile
namespace _module {

} // end of namespace _module
