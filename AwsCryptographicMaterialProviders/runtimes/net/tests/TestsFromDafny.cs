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
// Command Line Options: -stdin -noVerify -vcsCores:2 -compileTarget:cs -spillTargetCode:3 -runAllTests:1 -compile:0 -optimizeErasableDatatypeWrapper:0 -quantifierSyntax:3 -unicodeChar:0 -functionSyntax:3 -useRuntimeLib -out runtimes/net/tests/TestsFromDafny -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/StandardLibrary/src/Index.dfy -library:dafny/AwsCryptographicMaterialProviders/src/Index.dfy -library:dafny/AwsCryptographyKeyStore/src/Index.dfy
// the_program

method {:verify false} {:main} _Test__Main_()
















































































































module {:options ""/functionSyntax:4""} TestStormTracker {

  import opened AwsCryptographyMaterialProvidersTypes

  import opened UInt = StandardLibrary.UInt

  import opened Wrappers

  import opened StormTracker

  import opened AwsCryptographyKeyStoreTypes

  import UTF8
  function method MakeMat(data: Utf8Bytes): Materials
    decreases data
  {
    BranchKey(BranchKey := BranchKeyMaterials(branchKeyIdentifier := ""spoo"", branchKeyVersion := data, branchKey := data, encryptionContext := map[]))
  }

  function method MakeGet(data: Utf8Bytes): GetCacheEntryInput
    decreases data
  {
    GetCacheEntryInput(identifier := data, bytesUsed := Option.None)
  }

  function method MakeDel(data: Utf8Bytes): DeleteCacheEntryInput
    decreases data
  {
    DeleteCacheEntryInput(identifier := data)
  }

  function method MakePut(data: Utf8Bytes, expiryTime: PositiveLong): PutCacheEntryInput
    decreases data, expiryTime
  {
    PutCacheEntryInput(identifier := data, materials := MakeMat(data), creationTime := 123456789, expiryTime := expiryTime, messagesUsed := Option.None, bytesUsed := Option.None)
  }

  method {:test} StormTrackerBasics()
  {
    var st := new StormTracker(DefaultStorm());
    var abc := UTF8.EncodeAscii(""abc"");
    var cde := UTF8.EncodeAscii(""cde"");
    var res :- expect st.GetFromCacheWithTime(MakeGet(abc), 10000);
    expect res.EmptyFetch?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(abc), 10000);
    expect res.EmptyWait?, ""expectation violation""
    var res2 :- expect st.PutCacheEntry(MakePut(abc, 10000));
    res2 :- expect st.PutCacheEntry(MakePut(cde, 10000));
    res :- expect st.GetFromCacheWithTime(MakeGet(abc), 10001);
    expect res.EmptyFetch?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(abc), 10001);
    expect res.EmptyWait?, ""expectation violation""
    var res3 := st.GetCacheEntry(MakeGet(abc));
    res3 := st.GetCacheEntry(MakeGet(abc));
    var res4 := st.GetFromCache(MakeGet(abc));
    res4 := st.GetFromCache(MakeGet(abc));
    var res5 := st.DeleteCacheEntry(MakeDel(abc));
    res5 := st.DeleteCacheEntry(MakeDel(abc));
  }

  method {:test} StormTrackerFanOut()
  {
    var st := new StormTracker(DefaultStorm().(fanOut := 3));
    var one := UTF8.EncodeAscii(""one"");
    var two := UTF8.EncodeAscii(""two"");
    var three := UTF8.EncodeAscii(""three"");
    var four := UTF8.EncodeAscii(""four"");
    var res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.EmptyFetch?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(two), 10000);
    expect res.EmptyFetch?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(three), 10000);
    expect res.EmptyFetch?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(four), 10000);
    expect res.EmptyWait?, ""expectation violation""
  }

  method {:test} StormTrackerTTL()
  {
    var st := new StormTracker(DefaultStorm().(fanOut := 3, inFlightTTL := 5));
    var one := UTF8.EncodeAscii(""one"");
    var two := UTF8.EncodeAscii(""two"");
    var three := UTF8.EncodeAscii(""three"");
    var four := UTF8.EncodeAscii(""four"");
    var res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.EmptyFetch?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(two), 10000);
    expect res.EmptyFetch?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(three), 10000);
    expect res.EmptyFetch?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(four), 10000);
    expect res.EmptyWait?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(four), 10001);
    expect res.EmptyWait?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(four), 10003);
    expect res.EmptyWait?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(four), 10005);
    expect res.EmptyFetch?, ""expectation violation""
  }

  method {:test} StormTrackerGraceInterval()
  {
    var st := new StormTracker(DefaultStorm().(graceInterval := 3));
    var one := UTF8.EncodeAscii(""one"");
    var res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.EmptyFetch?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.EmptyWait?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10001);
    expect res.EmptyWait?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10002);
    expect res.EmptyWait?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10003);
    expect res.EmptyFetch?, ""expectation violation""
  }

  method {:test} StormTrackerGracePeriod()
  {
    var st := new StormTracker(DefaultStorm());
    var one := UTF8.EncodeAscii(""one"");
    var res2 :- expect st.PutCacheEntry(MakePut(one, 10010));
    var res :- expect st.GetFromCacheWithTime(MakeGet(one), 9999);
    expect res.Full?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.EmptyFetch?, ""expectation violation""
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.Full?, ""expectation violation""
  }
}

module TestUtils {

  import opened StandardLibrary

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import UTF8

  import MaterialProviders

  import Types = AwsCryptographyMaterialProvidersTypes

  import Materials
  datatype SmallEncryptionContextVariation = Empty | A | AB | BA

  const KMS_RSA_PUBLIC_KEY := ""-----BEGIN PUBLIC KEY-----\n"" + ""MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEA27Uc/fBaMVhxCE/SpCMQ\n"" + ""oSBRSzQJw+o2hBaA+FiPGtiJ/aPy7sn18aCkelaSj4kwoC79b/arNHlkjc7OJFsN\n"" + ""/GoFKgNvaiY4lOeJqEiWQGSSgHtsJLdbO2u4OOSxh8qIRAMKbMgQDVX4FR/PLKeK\n"" + ""fc2aCDvcNSpAM++8NlNmv7+xQBJydr5ce91eISbHkFRkK3/bAM+1iddupoRw4Wo2\n"" + ""r3avzrg5xBHmzR7u1FTab22Op3Hgb2dBLZH43wNKAceVwKqKA8UNAxashFON7xK9\n"" + ""yy4kfOL0Z/nhxRKe4jRZ/5v508qIzgzCksYy7Y3QbMejAtiYnr7s5/d5KWw0swou\n"" + ""twIDAQAB\n"" + ""-----END PUBLIC KEY-----""
  const KMS_RSA_PRIVATE_KEY_ARN := ""arn:aws:kms:us-west-2:370957321024:key/mrk-63d386cb70614ea59b32ad65c9315297""
  const SHARED_TEST_KEY_ARN := ""arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f""
  const ACCOUNT_IDS := [""658956600833""]
  const PARTITION := ""aws""

  lemma {:axiom} AssumeLongSeqIsValidUTF8(s: seq<uint8>)
    requires |s| >= 4096
    ensures UTF8.ValidUTF8Seq(s)
    decreases s

  method GenerateInvalidEncryptionContext() returns (encCtx: Types.EncryptionContext)
  {
    var validUTF8char: UTF8.ValidUTF8Bytes :- expect UTF8.Encode(""a"");
    var key: UTF8.ValidUTF8Bytes := [];
    while |key| < UINT16_LIMIT
      decreases UINT16_LIMIT - |key|
    {
      UTF8.ValidUTF8Concat(key, validUTF8char);
      key := key + validUTF8char;
    }
    encCtx := map[key := [0]];
  }

  method GenerateLargeValidEncryptionContext() returns (r: Types.EncryptionContext)
  {
    assert (65536 - 1 - 2) / (2 + 2 + 2 + 1) == (65536 - 3) / 7 == 9361;
    var numMaxPairs := 9361;
    var val :- expect UTF8.Encode(""a"");
    var encCtx: map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes> := map[];
    var i := 0;
    while |encCtx| < numMaxPairs && i < 65536
      invariant forall k: seq<uint8> {:trigger encCtx[k]} {:trigger k in encCtx} :: k in encCtx ==> |k| + |encCtx[k]| == 3
      decreases 65536 - i
    {
      var key := UInt16ToSeq(i as uint16);
      if UTF8.ValidUTF8Seq(key) {
        encCtx := encCtx[key := val];
      }
      i := i + 1;
    }
    return encCtx;
  }

  method SmallEncryptionContext(v: SmallEncryptionContextVariation) returns (encryptionContext: Types.EncryptionContext)
    ensures encryptionContext.Keys !! Materials.RESERVED_KEY_VALUES
    decreases v
  {
    var keyA :- expect UTF8.Encode(""keyA"");
    var valA :- expect UTF8.Encode(""valA"");
    var keyB :- expect UTF8.Encode(""keyB"");
    var valB :- expect UTF8.Encode(""valB"");
    match v {
      case {:split false} Empty() =>
        encryptionContext := map[];
      case {:split false} A() =>
        encryptionContext := map[keyA := valA];
      case {:split false} AB() =>
        encryptionContext := map[keyA := valA, keyB := valB];
      case {:split false} BA() =>
        encryptionContext := map[keyB := valB, keyA := valA];
    }
  }

  method GenerateMockEncryptedDataKey(keyProviderId: string, keyProviderInfo: string) returns (edk: Types.EncryptedDataKey)
    decreases keyProviderId, keyProviderInfo
  {
    var encodedkeyProviderId :- expect UTF8.Encode(keyProviderId);
    var encodedKeyProviderInfo :- expect UTF8.Encode(keyProviderInfo);
    var fakeCiphertext :- expect UTF8.Encode(""fakeCiphertext"");
    return Types.EncryptedDataKey(keyProviderId := encodedkeyProviderId, keyProviderInfo := encodedKeyProviderInfo, ciphertext := fakeCiphertext);
  }

  method NamespaceAndName(n: nat) returns (namespace: string, name: string)
    requires 0 <= n < 10
    ensures |namespace| < UINT16_LIMIT
    ensures |name| < UINT16_LIMIT
    decreases n
  {
    var s := ""child"" + [n as char + '0'];
    namespace := s + "" Namespace"";
    name := s + "" Name"";
  }
}

module {:options ""/functionSyntax:4""} TestLocalCMC {

  import opened AwsCryptographyMaterialProvidersTypes

  import opened UInt = StandardLibrary.UInt

  import opened Wrappers

  import opened LocalCMC

  import opened AwsCryptographyKeyStoreTypes

  import UTF8
  function method MakeMat(data: Utf8Bytes): Materials
    decreases data
  {
    BranchKey(BranchKey := BranchKeyMaterials(branchKeyIdentifier := ""spoo"", branchKeyVersion := data, branchKey := data, encryptionContext := map[]))
  }

  function method MakeGet(data: Utf8Bytes): GetCacheEntryInput
    decreases data
  {
    GetCacheEntryInput(identifier := data, bytesUsed := Option.None)
  }

  function method MakeDel(data: Utf8Bytes): DeleteCacheEntryInput
    decreases data
  {
    DeleteCacheEntryInput(identifier := data)
  }

  function method MakePut(data: Utf8Bytes, expiryTime: PositiveLong): PutCacheEntryInput
    decreases data, expiryTime
  {
    PutCacheEntryInput(identifier := data, materials := MakeMat(data), creationTime := 123456789, expiryTime := expiryTime, messagesUsed := Option.None, bytesUsed := Option.None)
  }

  method {:test} LocalCMCBasics()
  {
    var st := new LocalCMC(100);
    var abc := UTF8.EncodeAscii(""abc"");
    var cde := UTF8.EncodeAscii(""cde"");
    var res := st.GetCacheEntryWithTime(MakeGet(abc), 10000);
    expect res.Failure?, ""expectation violation""
    expect res.error.EntryDoesNotExist?, ""expectation violation""
    var res2 :- expect st.PutCacheEntry'(MakePut(abc, 10000));
    res2 :- expect st.PutCacheEntry'(MakePut(cde, 10000));
    var res3 :- expect st.GetCacheEntryWithTime(MakeGet(abc), 9999);
    res3 :- expect st.GetCacheEntryWithTime(MakeGet(abc), 10000);
    res := st.GetCacheEntryWithTime(MakeGet(abc), 10001);
    expect res.Failure?, ""expectation violation""
    expect res.error.EntryDoesNotExist?, ""expectation violation""
    res3 :- expect st.GetCacheEntryWithTime(MakeGet(cde), 9999);
    var res5 :- expect st.DeleteCacheEntry'(MakeDel(cde));
    res := st.GetCacheEntryWithTime(MakeGet(abc), 9999);
    expect res.Failure?, ""expectation violation""
    expect res.error.EntryDoesNotExist?, ""expectation violation""
    res5 :- expect st.DeleteCacheEntry'(MakeDel(cde));
  }
}

module TestAwsKmsEncryptedDataKeyFilter {

  import opened Wrappers

  import TestUtils

  import UTF8

  import Primitives = Aws.Cryptography.Primitives

  import AwsCryptographyPrimitivesTypes

  import MaterialProviders

  import Types = AwsCryptographyMaterialProvidersTypes

  import AwsKmsDiscoveryKeyring

  import Actions
  method {:test} TestFailsNonKeyResource()
  {
    var discoveryFilter := GetDiscoveryFilter();
    var edkFilter := new AwsKmsDiscoveryKeyring.AwsKmsEncryptedDataKeyFilter(Option.Some(discoveryFilter));
    var badEdk := GetNonKeyEncryptedDataKey();
    var filterResult := Actions.FilterWithResult(edkFilter, [badEdk]);
    expect filterResult.Failure?, ""expectation violation""
    var test: Types.Error := filterResult.error;
    expect test.AwsCryptographicMaterialProvidersException?, ""expectation violation""
    expect test.message == ""Only AWS KMS Keys supported"", ""expectation violation""
  }

  method {:test} TestMatchesKeyringsConfiguration()
  {
    var matchingEdk := TestUtils.GenerateMockEncryptedDataKey(""aws-kms"", TestUtils.SHARED_TEST_KEY_ARN);
    var mismatchEdkPartition := TestUtils.GenerateMockEncryptedDataKey(""aws-kms"", ""arn:aws-cn:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"");
    var mismatchEdkAccount := TestUtils.GenerateMockEncryptedDataKey(""aws-kms"", ""arn:aws:kms:us-west-2:827585335069:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"");
    var mismatchEdkProviderId := TestUtils.GenerateMockEncryptedDataKey(""aws"", TestUtils.SHARED_TEST_KEY_ARN);
    var discoveryFilter := GetDiscoveryFilter();
    var edkFilter := new AwsKmsDiscoveryKeyring.AwsKmsEncryptedDataKeyFilter(Option.Some(discoveryFilter));
    var filterResult := Actions.FilterWithResult(edkFilter, [matchingEdk, mismatchEdkPartition, mismatchEdkAccount, mismatchEdkProviderId]);
    expect filterResult.Success?, ""expectation violation""
    expect |filterResult.value| == 1, ""expectation violation""
    expect filterResult.value[0] == matchingEdk, ""expectation violation""
  }

  method GetDiscoveryFilter() returns (discoveryFilter: Types.DiscoveryFilter)
  {
    return Types.DiscoveryFilter(accountIds := TestUtils.ACCOUNT_IDS, partition := TestUtils.PARTITION);
  }

  method GetNonKeyEncryptedDataKey() returns (edk: Types.EncryptedDataKey)
  {
    edk := TestUtils.GenerateMockEncryptedDataKey(""aws-kms"", ""arn:aws:kms:us-west-2:658956600833:alias/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"");
  }
}

module TestAwsKmsHierarchicalKeyring {

  import Types = AwsCryptographyMaterialProvidersTypes

  import ComAmazonawsKmsTypes

  import KMS = Com.Amazonaws.Kms

  import DDB = Com.Amazonaws.Dynamodb

  import DDBTypes = ComAmazonawsDynamodbTypes

  import KeyStore

  import KeyStoreTypes = AwsCryptographyKeyStoreTypes

  import Crypto = AwsCryptographyPrimitivesTypes

  import Primitives = Aws.Cryptography.Primitives

  import MaterialProviders

  import StormTracker

  import StormTrackingCMC

  import opened TestUtils

  import opened AlgorithmSuites

  import opened Materials

  import opened UInt = StandardLibrary.UInt

  import opened Wrappers

  import Fixtures
  class DummyBranchKeyIdSupplier extends Types.IBranchKeyIdSupplier {
    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      History in Modifies
    }

    constructor ()
      ensures ValidState() && fresh(this) && fresh(History) && fresh(Modifies)
    {
      History := new Types.IBranchKeyIdSupplierCallHistory();
      Modifies := {History};
    }

    predicate GetBranchKeyIdEnsuresPublicly(input: Types.GetBranchKeyIdInput, output: Result<Types.GetBranchKeyIdOutput, Types.Error>)
      decreases input, output
    {
      true
    }

    method GetBranchKeyId'(input: Types.GetBranchKeyIdInput) returns (output: Result<Types.GetBranchKeyIdOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      ensures ValidState()
      ensures GetBranchKeyIdEnsuresPublicly(input, output)
      ensures unchanged(History)
      decreases Modifies - {History}
    {
      var context := input.encryptionContext;
      if BRANCH_KEY in context.Keys && context[BRANCH_KEY] == CASE_A {
        return Success(Types.GetBranchKeyIdOutput(branchKeyId := BRANCH_KEY_ID_A));
      } else if BRANCH_KEY in context.Keys && context[BRANCH_KEY] == CASE_B {
        return Success(Types.GetBranchKeyIdOutput(branchKeyId := BRANCH_KEY_ID_B));
      } else {
        return Failure(Types.AwsCryptographicMaterialProvidersException(message := ""Can't determine branchKeyId from context""));
      }
    }
  }

  const TEST_ESDK_ALG_SUITE_ID := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF)
  const TEST_DBE_ALG_SUITE_ID := Types.AlgorithmSuiteId.DBE(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384)
  const keyArn := Fixtures.keyArn
  const branchKeyStoreName: DDBTypes.TableName := Fixtures.branchKeyStoreName
  const logicalKeyStoreName := branchKeyStoreName
  const BRANCH_KEY_ID := Fixtures.branchKeyId
  const BRANCH_KEY := UTF8.EncodeAscii(""branchKey"")
  const CASE_A := UTF8.EncodeAscii(""caseA"")
  const CASE_B := UTF8.EncodeAscii(""caseB"")
  const BRANCH_KEY_ID_A := BRANCH_KEY_ID
  const BRANCH_KEY_ID_B := Fixtures.branchKeyIdWithEC

  method GetTestMaterials(suiteId: Types.AlgorithmSuiteId) returns (out: Types.EncryptionMaterials)
    decreases suiteId
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var suite := AlgorithmSuites.GetSuite(suiteId);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := suiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := [], signingKey := None, verificationKey := None));
    return encryptionMaterialsIn;
  }

  method {:test} TestHierarchyClientESDKSuite()
  {
    var branchKeyId := BRANCH_KEY_ID;
    var ttl: Types.PositiveLong := 1 * 60000 * 10;
    var mpl :- expect MaterialProviders.MaterialProviders();
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := KeyStoreTypes.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := KeyStoreTypes.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var hierarchyKeyring :- expect mpl.CreateAwsKmsHierarchicalKeyring(Types.CreateAwsKmsHierarchicalKeyringInput(branchKeyId := Some(branchKeyId), branchKeyIdSupplier := None, keyStore := keyStore, ttlSeconds := ttl, cache := None));
    var materials := GetTestMaterials(TEST_ESDK_ALG_SUITE_ID);
    TestRoundtrip(hierarchyKeyring, materials, TEST_ESDK_ALG_SUITE_ID, branchKeyId);
    var suite := AlgorithmSuites.GetSuite(TEST_ESDK_ALG_SUITE_ID);
    var zeroedKey := seq(AlgorithmSuites.GetEncryptKeyLength(suite) as nat, (_ /* _v0 */: int) => 0);
    materials := materials.(plaintextDataKey := Some(zeroedKey));
    TestRoundtrip(hierarchyKeyring, materials, TEST_ESDK_ALG_SUITE_ID, branchKeyId);
  }

  method {:test} TestHierarchyClientDBESuite()
  {
    var branchKeyId := BRANCH_KEY_ID;
    var ttl: Types.PositiveLong := 1 * 60000 * 10;
    var mpl :- expect MaterialProviders.MaterialProviders();
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := KeyStoreTypes.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := KeyStoreTypes.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var hierarchyKeyring :- expect mpl.CreateAwsKmsHierarchicalKeyring(Types.CreateAwsKmsHierarchicalKeyringInput(branchKeyId := Some(branchKeyId), branchKeyIdSupplier := None, keyStore := keyStore, ttlSeconds := ttl, cache := None));
    var materials := GetTestMaterials(TEST_DBE_ALG_SUITE_ID);
    TestRoundtrip(hierarchyKeyring, materials, TEST_DBE_ALG_SUITE_ID, branchKeyId);
    var suite := AlgorithmSuites.GetSuite(TEST_DBE_ALG_SUITE_ID);
    var zeroedKey := seq(AlgorithmSuites.GetEncryptKeyLength(suite) as nat, (_ /* _v1 */: int) => 0);
    materials := materials.(plaintextDataKey := Some(zeroedKey));
    TestRoundtrip(hierarchyKeyring, materials, TEST_DBE_ALG_SUITE_ID, branchKeyId);
  }

  method {:test} TestBranchKeyIdSupplier()
  {
    var branchKeyIdSupplier: Types.IBranchKeyIdSupplier := new DummyBranchKeyIdSupplier();
    var ttl: int64 := 1 * 60000 * 10;
    var mpl :- expect MaterialProviders.MaterialProviders();
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := KeyStoreTypes.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := KeyStoreTypes.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var hierarchyKeyring :- expect mpl.CreateAwsKmsHierarchicalKeyring(Types.CreateAwsKmsHierarchicalKeyringInput(branchKeyId := None, branchKeyIdSupplier := Some(branchKeyIdSupplier), keyStore := keyStore, ttlSeconds := ttl, cache := None));
    var materials := GetTestMaterials(TEST_DBE_ALG_SUITE_ID);
    var contextCaseA := materials.encryptionContext[BRANCH_KEY := CASE_A];
    materials := materials.(encryptionContext := contextCaseA);
    TestRoundtrip(hierarchyKeyring, materials, TEST_DBE_ALG_SUITE_ID, BRANCH_KEY_ID_A);
    var contextCaseB := materials.encryptionContext[BRANCH_KEY := CASE_B];
    materials := materials.(encryptionContext := contextCaseB);
    TestRoundtrip(hierarchyKeyring, materials, TEST_DBE_ALG_SUITE_ID, BRANCH_KEY_ID_B);
  }

  method TestRoundtrip(hierarchyKeyring: Types.IKeyring, encryptionMaterialsIn: Types.EncryptionMaterials, algorithmSuiteId: Types.AlgorithmSuiteId, expectedBranchKeyId: string)
    requires hierarchyKeyring.ValidState()
    modifies hierarchyKeyring.Modifies
    ensures hierarchyKeyring.ValidState()
    decreases hierarchyKeyring, encryptionMaterialsIn, algorithmSuiteId, expectedBranchKeyId
  {
    var encryptionMaterialsOut :- expect hierarchyKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    var mpl :- expect MaterialProviders.MaterialProviders();
    var _ /* _v2 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1, ""expectation violation""
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var expectedBranchKeyIdUTF8 :- expect UTF8.Encode(expectedBranchKeyId);
    expect edk.keyProviderInfo == expectedBranchKeyIdUTF8, ""expectation violation""
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionMaterialsIn.encryptionContext, requiredEncryptionContextKeys := []));
    var decryptionMaterialsOut :- expect hierarchyKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := [edk]));
    expect encryptionMaterialsOut.materials.plaintextDataKey == decryptionMaterialsOut.materials.plaintextDataKey, ""expectation violation""
  }
}

module Fixtures {

  import opened UInt = StandardLibrary.UInt
  const branchKeyStoreName := ""KeyStoreDdbTable""
  const logicalKeyStoreName := branchKeyStoreName
  const branchKeyId := ""75789115-1deb-4fe3-a2ec-be9e885d1945""
  const branchKeyIdActiveVersion := ""fed7ad33-0774-4f97-aa5e-6c766fc8af9f""
  const branchKeyIdWithEC := ""4bb57643-07c1-419e-92ad-0df0df149d7c""
  const branchKeyIdActiveVersionUtf8Bytes: seq<uint8> := [102, 101, 100, 55, 97, 100, 51, 51, 45, 48, 55, 55, 52, 45, 52, 102, 57, 55, 45, 97, 97, 53, 101, 45, 54, 99, 55, 54, 54, 102, 99, 56, 97, 102, 57, 102]
  const keyArn := ""arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126""
  const mkrKeyArn := ""arn:aws:kms:us-west-2:370957321024:key/mrk-63d386cb70614ea59b32ad65c9315297""
  const keyId := ""9d989aa2-2f9c-438c-a745-cc57d3ad0126""
}

module TestAwsKmsRsaKeyring {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import MaterialProviders

  import Types = AwsCryptographyMaterialProvidersTypes

  import AwsKmsRsaKeyring

  import TestUtils

  import ComAmazonawsKmsTypes

  import AlgorithmSuites

  import UTF8
  method {:test} TestKmsRsaRoundtrip()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var publicKey :- expect UTF8.Encode(TestUtils.KMS_RSA_PUBLIC_KEY);
    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput());
    var kmsClient :- expect clientSupplier.GetClient(Types.GetClientInput(region := ""us-west-2""));
    var kmsRsaKeyring :- expect mpl.CreateAwsKmsRsaKeyring(Types.CreateAwsKmsRsaKeyringInput(publicKey := Some(publicKey), kmsKeyId := TestUtils.KMS_RSA_PRIVATE_KEY_ARN, encryptionAlgorithm := ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1, kmsClient := Some(kmsClient), grantTokens := None()));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var suite := AlgorithmSuites.GetSuite(algorithmSuiteId);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := [], signingKey := None, verificationKey := None));
    var encryptionMaterialsOut :- expect kmsRsaKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    var _ /* _v0 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1, ""expectation violation""
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    var decryptionMaterialsOut :- expect kmsRsaKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := [edk]));
    expect encryptionMaterialsOut.materials.plaintextDataKey == decryptionMaterialsOut.materials.plaintextDataKey, ""expectation violation""
  }

  method {:test} TestKmsRsaWithAsymmetricSignatureFails()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var publicKey :- expect UTF8.Encode(TestUtils.KMS_RSA_PUBLIC_KEY);
    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput());
    var kmsClient :- expect clientSupplier.GetClient(Types.GetClientInput(region := ""us-west-2""));
    var kmsRsaKeyring :- expect mpl.CreateAwsKmsRsaKeyring(Types.CreateAwsKmsRsaKeyringInput(publicKey := Some(publicKey), kmsKeyId := TestUtils.KMS_RSA_PRIVATE_KEY_ARN, encryptionAlgorithm := ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1, kmsClient := Some(kmsClient), grantTokens := None()));
    var algorithmSuiteId := Types.AlgorithmSuiteId.DBE(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384);
    var suite := AlgorithmSuites.GetSuite(algorithmSuiteId);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := map[], requiredEncryptionContextKeys := [], signingKey := Some([0, 0, 0, 0, 0]), verificationKey := Some([0, 0, 0, 0, 0])));
    var encryptionMaterialsOutRes := kmsRsaKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    expect encryptionMaterialsOutRes.Failure?, ""expectation violation""
    expect encryptionMaterialsOutRes.error.AwsCryptographicMaterialProvidersException?, ""expectation violation""
    expect encryptionMaterialsOutRes.error.message == ""AwsKmsRsaKeyring cannot be used with"" + "" an Algorithm Suite with asymmetric signing. Please specify an algorithm suite without asymmetric signing."", ""expectation violation""
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionMaterialsIn.encryptionContext, requiredEncryptionContextKeys := []));
    var decryptionMaterialsOutRes := kmsRsaKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := []));
    expect decryptionMaterialsOutRes.Failure?, ""expectation violation""
    expect decryptionMaterialsOutRes.error.AwsCryptographicMaterialProvidersException?, ""expectation violation""
    expect decryptionMaterialsOutRes.error.message == ""AwsKmsRsaKeyring cannot be used with"" + "" an Algorithm Suite with asymmetric signing. Please specify an algorithm suite without asymmetric signing."", ""expectation violation""
  }
}

module TestRawRSAKeying {

  import opened Wrappers

  import TestUtils

  import Primitives = Aws.Cryptography.Primitives

  import AwsCryptographyPrimitivesTypes

  import MaterialProviders

  import Types = AwsCryptographyMaterialProvidersTypes
  method {:test} TestOnEncryptOnDecryptSuppliedDataKey()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var keys := GenerateKeyPair(2048 as AwsCryptographyPrimitivesTypes.RSAModulusLengthBits);
    var rawRSAKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(keyNamespace := namespace, keyName := name, paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1, publicKey := Option.Some(keys.publicKey.pem), privateKey := Option.Some(keys.privateKey.pem)));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, signingKey := None, verificationKey := None, requiredEncryptionContextKeys := []));
    var encryptionMaterialsOut :- expect rawRSAKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    var _ /* _v0 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    var decryptionMaterialsOut :- expect rawRSAKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := [edk]));
    expect decryptionMaterialsOut.materials.plaintextDataKey == encryptionMaterialsOut.materials.plaintextDataKey, ""expectation violation""
  }

  method {:test} TestOnDecryptKeyNameMismatch()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var keys := GenerateKeyPair(2048 as AwsCryptographyPrimitivesTypes.RSAModulusLengthBits);
    var rawRSAKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(keyNamespace := namespace, keyName := name, paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1, publicKey := Option.Some(keys.publicKey.pem), privateKey := Option.Some(keys.privateKey.pem)));
    var mismatchedRSAKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(keyNamespace := namespace, keyName := ""mismatched"", paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1, publicKey := Option.Some(keys.publicKey.pem), privateKey := Option.Some(keys.privateKey.pem)));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, signingKey := None, verificationKey := None, requiredEncryptionContextKeys := []));
    var encryptionMaterialsOut :- expect rawRSAKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    var _ /* _v1 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    var decryptionMaterialsOut := mismatchedRSAKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := [edk]));
    expect decryptionMaterialsOut.IsFailure(), ""expectation violation""
  }

  method {:test} TestOnDecryptFailure()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var encryptKeys := GenerateKeyPair(2048 as AwsCryptographyPrimitivesTypes.RSAModulusLengthBits);
    var decryptKeys := GenerateKeyPair(2048 as AwsCryptographyPrimitivesTypes.RSAModulusLengthBits);
    var encryptKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(keyNamespace := namespace, keyName := name, paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1, publicKey := Option.Some(encryptKeys.publicKey.pem), privateKey := Option.Some(encryptKeys.privateKey.pem)));
    var decryptKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(keyNamespace := namespace, keyName := name, paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1, publicKey := Option.Some(decryptKeys.publicKey.pem), privateKey := Option.Some(decryptKeys.privateKey.pem)));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, signingKey := None, verificationKey := None, requiredEncryptionContextKeys := []));
    var encryptionMaterialsOut :- expect encryptKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    var _ /* _v2 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    var decryptionMaterialsOut := decryptKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := [edk]));
    expect decryptionMaterialsOut.IsFailure(), ""expectation violation""
  }

  method {:test} TestOnDecryptBadAndGoodEdkSucceeds()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var keys := GenerateKeyPair(2048 as AwsCryptographyPrimitivesTypes.RSAModulusLengthBits);
    var rawRSAKeyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(keyNamespace := namespace, keyName := name, paddingScheme := Types.PaddingScheme.OAEP_SHA1_MGF1, publicKey := Option.Some(keys.publicKey.pem), privateKey := Option.Some(keys.privateKey.pem)));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, signingKey := None, verificationKey := None, requiredEncryptionContextKeys := []));
    var encryptionMaterialsOut :- expect rawRSAKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    var _ /* _v3 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    var fakeEdk := Types.EncryptedDataKey(keyProviderId := edk.keyProviderId, keyProviderInfo := edk.keyProviderInfo, ciphertext := seq(|edk.ciphertext|, (i: int) => 0));
    var decryptionMaterialsOut :- expect rawRSAKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := [fakeEdk, edk]));
    expect decryptionMaterialsOut.materials.plaintextDataKey == encryptionMaterialsOut.materials.plaintextDataKey, ""expectation violation""
  }

  method GenerateKeyPair(keyModulusLength: AwsCryptographyPrimitivesTypes.RSAModulusLengthBitsToGenerate) returns (keys: AwsCryptographyPrimitivesTypes.GenerateRSAKeyPairOutput)
    decreases keyModulusLength
  {
    var crypto :- expect Primitives.AtomicPrimitives();
    keys :- expect crypto.GenerateRSAKeyPair(AwsCryptographyPrimitivesTypes.GenerateRSAKeyPairInput(lengthBits := keyModulusLength));
  }
}

module TestMultiKeyring {

  import opened Wrappers

  import TestUtils

  import UTF8

  import Primitives = Aws.Cryptography.Primitives

  import AwsCryptographyPrimitivesTypes

  import MaterialProviders

  import Types = AwsCryptographyMaterialProvidersTypes
  class StaticKeyring extends Types.IKeyring {
    const encryptionMaterials: Option<Types.EncryptionMaterials>
    const decryptionMaterials: Option<Types.DecryptionMaterials>

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      true &&
      History in Modifies
    }

    predicate OnEncryptEnsuresPublicly(input: Types.OnEncryptInput, output: Result<Types.OnEncryptOutput, Types.Error>)
      decreases input, output
    {
      true
    }

    predicate OnDecryptEnsuresPublicly(input: Types.OnDecryptInput, output: Result<Types.OnDecryptOutput, Types.Error>)
      decreases input, output
    {
      true
    }

    constructor (encryptionMaterials: Option<Types.EncryptionMaterials>, decryptionMaterials: Option<Types.DecryptionMaterials>)
      ensures ValidState() && fresh(History) && fresh(Modifies)
      decreases encryptionMaterials, decryptionMaterials
    {
      this.encryptionMaterials := encryptionMaterials;
      this.decryptionMaterials := decryptionMaterials;
      History := new Types.IKeyringCallHistory();
      Modifies := {History};
    }

    method OnEncrypt'(input: Types.OnEncryptInput) returns (res: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, res)
      ensures unchanged(History)
      decreases Modifies - {History}
    {
      if this.encryptionMaterials.Some? {
        return Success(Types.OnEncryptOutput(materials := encryptionMaterials.value));
      } else {
        var exception := Types.AwsCryptographicMaterialProvidersException(message := ""Failure"");
        return Failure(exception);
      }
    }

    method OnDecrypt'(input: Types.OnDecryptInput) returns (res: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, res)
      decreases Modifies - {History}
    {
      if this.decryptionMaterials.Some? {
        return Success(Types.OnDecryptOutput(materials := decryptionMaterials.value));
      } else {
        var exception := Types.AwsCryptographicMaterialProvidersException(message := ""Failure"");
        return Failure(exception);
      }
    }
  }

  class FailingKeyring extends Types.IKeyring {
    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      true &&
      History in Modifies
    }

    predicate OnEncryptEnsuresPublicly(input: Types.OnEncryptInput, output: Result<Types.OnEncryptOutput, Types.Error>)
      decreases input, output
    {
      true
    }

    predicate OnDecryptEnsuresPublicly(input: Types.OnDecryptInput, output: Result<Types.OnDecryptOutput, Types.Error>)
      decreases input, output
    {
      true
    }

    constructor ()
      ensures ValidState() && fresh(History) && fresh(Modifies)
    {
      History := new Types.IKeyringCallHistory();
      Modifies := {History};
    }

    method OnEncrypt'(input: Types.OnEncryptInput) returns (res: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, res)
      ensures unchanged(History)
      decreases Modifies - {History}
    {
      var exception := Types.AwsCryptographicMaterialProvidersException(message := ""Failure"");
      return Failure(exception);
    }

    method OnDecrypt'(input: Types.OnDecryptInput) returns (res: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, res)
      ensures unchanged(History)
      decreases Modifies - {History}
    {
      var exception := Types.AwsCryptographicMaterialProvidersException(message := ""Failure"");
      return Failure(exception);
    }
  }

  method getInputEncryptionMaterials(encryptionContext: Types.EncryptionContext) returns (res: Types.EncryptionMaterials)
    decreases encryptionContext
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, signingKey := None, verificationKey := None, requiredEncryptionContextKeys := []));
    return encryptionMaterialsIn;
  }

  method getInputDecryptionMaterials(encryptionContext: Types.EncryptionContext) returns (res: Types.DecryptionMaterials)
    decreases encryptionContext
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    return decryptionMaterialsIn;
  }

  method {:test} TestHappyCase()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var encryptionMaterials := getInputEncryptionMaterials(encryptionContext);
    var decryptionMaterials := getInputDecryptionMaterials(encryptionContext);
    var rawAESKeyring := setupRawAesKeyring(encryptionContext);
    var expectedEncryptionMaterials := rawAESKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterials));
    expect expectedEncryptionMaterials.Success?, ""expectation violation""
    var expectedPlaintextDataKey := expectedEncryptionMaterials.value.materials.plaintextDataKey;
    expect expectedPlaintextDataKey.Some?, ""expectation violation""
    var staticKeyring := SetupStaticKeyring(Some(expectedEncryptionMaterials.value.materials), None());
    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(generator := Some(staticKeyring), childKeyrings := [rawAESKeyring]));
    var encryptionMaterialsOut :- expect multiKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterials));
    var _ /* _v0 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    expect encryptionMaterialsOut.materials.plaintextDataKey.value == expectedPlaintextDataKey.value, ""expectation violation""
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 2, ""expectation violation""
  }

  method {:test} TestChildKeyringFailureEncrypt()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var rawAESKeyring := setupRawAesKeyring(encryptionContext);
    var failingKeyring := SetupFailingKeyring();
    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(generator := Some(rawAESKeyring), childKeyrings := [failingKeyring]));
    var encryptionMaterials := getInputEncryptionMaterials(encryptionContext);
    var result := multiKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterials));
    expect result.IsFailure(), ""expectation violation""
  }

  method {:test} TestGeneratorKeyringFails()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var failingKeyring := SetupFailingKeyring();
    var rawAESKeyring := setupRawAesKeyring(encryptionContext);
    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(generator := Some(failingKeyring), childKeyrings := [rawAESKeyring]));
    var encryptionMaterials := getInputEncryptionMaterials(encryptionContext);
    var result := multiKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterials));
    expect result.IsFailure(), ""expectation violation""
  }

  method {:test} TestGeneratorKeyringDoesNotReturnPlaintextDataKey()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var encryptionMaterials := getInputEncryptionMaterials(encryptionContext);
    var failingKeyring := SetupStaticKeyring(Some(encryptionMaterials), None());
    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(generator := Some(failingKeyring), childKeyrings := []));
    var result := multiKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterials));
    expect result.IsFailure(), ""expectation violation""
  }

  method {:test} TestGeneratorAbleToDecrypt()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var rawAESKeyring := setupRawAesKeyring(encryptionContext);
    var inputEncryptionMaterials := getInputEncryptionMaterials(encryptionContext);
    var encryptionMaterials := rawAESKeyring.OnEncrypt(Types.OnEncryptInput(materials := inputEncryptionMaterials));
    expect encryptionMaterials.Success?, ""expectation violation""
    var inputDecryptionMaterials := getInputDecryptionMaterials(encryptionContext);
    var failingKeyring := SetupFailingKeyring();
    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(generator := Some(rawAESKeyring), childKeyrings := [failingKeyring]));
    var onDecryptInput := Types.OnDecryptInput(materials := inputDecryptionMaterials, encryptedDataKeys := encryptionMaterials.value.materials.encryptedDataKeys);
    var decryptionMaterials := multiKeyring.OnDecrypt(input := onDecryptInput);
    expect decryptionMaterials.Success?, ""expectation violation""
    expect decryptionMaterials.value.materials.plaintextDataKey == encryptionMaterials.value.materials.plaintextDataKey, ""expectation violation""
  }

  method {:test} TestGeneratorUnableToDecrypt()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var rawAESKeyring := setupRawAesKeyring(encryptionContext);
    var inputEncryptionMaterials := getInputEncryptionMaterials(encryptionContext);
    var encryptionMaterials := rawAESKeyring.OnEncrypt(Types.OnEncryptInput(materials := inputEncryptionMaterials));
    expect encryptionMaterials.Success?, ""expectation violation""
    var inputDecryptionMaterials := getInputDecryptionMaterials(encryptionContext);
    var failingKeyring := SetupFailingKeyring();
    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(generator := Some(failingKeyring), childKeyrings := [failingKeyring, rawAESKeyring, failingKeyring]));
    var onDecryptInput := Types.OnDecryptInput(materials := inputDecryptionMaterials, encryptedDataKeys := encryptionMaterials.value.materials.encryptedDataKeys);
    var decryptionMaterials := multiKeyring.OnDecrypt(input := onDecryptInput);
    expect decryptionMaterials.Success?, ""expectation violation""
    expect decryptionMaterials.value.materials.plaintextDataKey == encryptionMaterials.value.materials.plaintextDataKey, ""expectation violation""
  }

  method {:test} TestCollectFailuresDecrypt()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var failingKeyring := SetupFailingKeyring();
    var multiKeyring :- expect mpl.CreateMultiKeyring(Types.CreateMultiKeyringInput(generator := None(), childKeyrings := [failingKeyring, failingKeyring]));
    var materials :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF), encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    var result := multiKeyring.OnDecrypt(Types.OnDecryptInput(materials := materials, encryptedDataKeys := []));
    expect result.IsFailure(), ""expectation violation""
  }

  method setupRawAesKeyring(encryptionContext: Types.EncryptionContext) returns (res: Types.IKeyring)
    ensures res.ValidState() && fresh(res) && fresh(res.History) && fresh(res.Modifies)
    decreases encryptionContext
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(keyNamespace := namespace, keyName := name, wrappingKey := seq(32, (i: int) => 0), wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16));
    return rawAESKeyring;
  }

  method SetupStaticKeyring(encryptionMaterials: Option<Types.EncryptionMaterials>, decryptionMaterials: Option<Types.DecryptionMaterials>) returns (res: Types.IKeyring)
    ensures res.ValidState() && fresh(res) && fresh(res.History) && fresh(res.Modifies)
    decreases encryptionMaterials, decryptionMaterials
  {
    return new StaticKeyring(encryptionMaterials, decryptionMaterials);
  }

  method SetupFailingKeyring() returns (res: Types.IKeyring)
    ensures res.ValidState() && fresh(res) && fresh(res.History) && fresh(res.Modifies)
  {
    return new FailingKeyring();
  }
}

module TestRawAESKeyring {

  import opened Wrappers

  import TestUtils

  import UTF8

  import Primitives = Aws.Cryptography.Primitives

  import AwsCryptographyPrimitivesTypes

  import MaterialProviders

  import Types = AwsCryptographyMaterialProvidersTypes
  method {:test} TestOnEncryptOnDecryptGenerateDataKey()
  {
    ghost var asdf := ""asdf"";
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(keyNamespace := namespace, keyName := name, wrappingKey := seq(32, (i: int) => 0), wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, signingKey := None, verificationKey := None, requiredEncryptionContextKeys := []));
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    var _ /* _v0 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1, ""expectation violation""
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := [edk]));
    expect encryptionMaterialsOut.materials.plaintextDataKey == encryptionMaterialsOut.materials.plaintextDataKey, ""expectation violation""
  }

  method {:test} TestOnEncryptOnDecryptSuppliedDataKey()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(keyNamespace := namespace, keyName := name, wrappingKey := seq(32, (i: int) => 0), wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, signingKey := None, verificationKey := None, requiredEncryptionContextKeys := []));
    var pdk := seq(32, (i: int) => 0);
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn.(plaintextDataKey := Some(pdk))));
    var _ /* _v1 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := [edk]));
    expect decryptionMaterialsOut.materials.plaintextDataKey == Some(pdk), ""expectation violation""
  }

  method {:test} TestOnDecryptKeyNameMismatch()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(keyNamespace := namespace, keyName := name, wrappingKey := seq(32, (i: int) => 0), wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16));
    var mismatchedAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(keyNamespace := namespace, keyName := ""mismatched"", wrappingKey := seq(32, (i: int) => 1), wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, signingKey := None, verificationKey := None, requiredEncryptionContextKeys := []));
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    var _ /* _v2 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    var decryptionMaterialsOut := mismatchedAESKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := [edk]));
    expect decryptionMaterialsOut.IsFailure(), ""expectation violation""
  }

  method {:test} TestOnDecryptBadAndGoodEdkSucceeds()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(keyNamespace := namespace, keyName := name, wrappingKey := seq(32, (i: int) => 0), wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, signingKey := None, verificationKey := None, requiredEncryptionContextKeys := []));
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    var _ /* _v3 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    var fakeEdk: Types.EncryptedDataKey := Types.EncryptedDataKey(keyProviderId := edk.keyProviderId, keyProviderInfo := edk.keyProviderInfo, ciphertext := seq(|edk.ciphertext|, (i: int) => 0));
    var decryptionMaterialsOut :- expect rawAESKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := [fakeEdk, edk]));
    expect decryptionMaterialsOut.materials.plaintextDataKey == encryptionMaterialsOut.materials.plaintextDataKey, ""expectation violation""
  }

  method {:test} TestOnDecryptNoEDKs()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(keyNamespace := namespace, keyName := name, wrappingKey := seq(32, (i: int) => 0), wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := []));
    var decryptionMaterialsOut := rawAESKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := []));
    expect decryptionMaterialsOut.IsFailure(), ""expectation violation""
  }

  method {:test} TestOnEncryptUnserializableEC()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(keyNamespace := namespace, keyName := name, wrappingKey := seq(32, (i: int) => 0), wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16));
    var unserializableEncryptionContext := generateUnserializableEncryptionContext();
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := unserializableEncryptionContext, signingKey := None, verificationKey := None, requiredEncryptionContextKeys := []));
    var encryptionMaterialsOut := rawAESKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    expect encryptionMaterialsOut.Failure?, ""expectation violation""
  }

  method {:test} TestOnDecryptUnserializableEC()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var namespace, name := TestUtils.NamespaceAndName(0);
    var rawAESKeyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(keyNamespace := namespace, keyName := name, wrappingKey := seq(32, (i: int) => 0), wrappingAlg := Types.ALG_AES256_GCM_IV12_TAG16));
    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);
    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, signingKey := None, verificationKey := None, requiredEncryptionContextKeys := []));
    var encryptionMaterialsOut :- expect rawAESKeyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    var _ /* _v4 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);
    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];
    var unserializableEncryptionContext := generateUnserializableEncryptionContext();
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := unserializableEncryptionContext, requiredEncryptionContextKeys := []));
    var decryptionMaterialsOut := rawAESKeyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := [edk]));
    expect decryptionMaterialsOut.Failure?, ""expectation violation""
  }

  method generateUnserializableEncryptionContext() returns (encCtx: Types.EncryptionContext)
  {
    var keyA :- expect UTF8.Encode(""keyA"");
    var invalidVal := seq(65536, (_ /* _v5 */: int) => 0);
    TestUtils.AssumeLongSeqIsValidUTF8(invalidVal);
    return map[keyA := invalidVal];
  }
}

module TestDefaultClientProvider {

  import Types = AwsCryptographyMaterialProvidersTypes

  import ComAmazonawsKmsTypes

  import KMS = Com.Amazonaws.Kms

  import MaterialProviders

  import opened TestUtils

  import opened UInt = StandardLibrary.UInt

  import opened Wrappers
  method {:test} GetUsWestTwo()
  {
    var mpl :- expect MaterialProviders.MaterialProviders();
    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput());
    var client :- expect clientSupplier.GetClient(Types.GetClientInput(region := ""us-west-2""));
    var kmsRequest := ComAmazonawsKmsTypes.GenerateDataKeyRequest(KeyId := TestUtils.SHARED_TEST_KEY_ARN, EncryptionContext := Option.None, GrantTokens := Option.None, NumberOfBytes := Option.Some(24 as int32), KeySpec := Option.None);
    var kmsReply :- expect client.GenerateDataKey(kmsRequest);
  }
}

module TestIntermediateKeyWrapping {

  import Types = AwsCryptographyMaterialProvidersTypes

  import MaterialProviders

  import opened TestUtils

  import opened UInt = StandardLibrary.UInt

  import opened Wrappers

  import opened Actions

  import opened IntermediateKeyWrapping

  import MaterialWrapping

  import AlgorithmSuites
  datatype TestInfo = TestInfo

  class TestGenerateAndWrapKeyMaterial extends MaterialWrapping.GenerateAndWrapMaterial<TestInfo> {
    constructor ()
      ensures Invariant()
    {
      Modifies := {};
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      Modifies == {}
    }

    predicate Ensures(input: MaterialWrapping.GenerateAndWrapInput, res: Result<MaterialWrapping.GenerateAndWrapOutput<TestInfo>, Types.Error>, attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<TestInfo>, Types.Error>>>)
      reads Modifies
      decreases Modifies
    {
      true
    }

    method Invoke(input: MaterialWrapping.GenerateAndWrapInput, ghost attemptsState: seq<ActionInvoke<MaterialWrapping.GenerateAndWrapInput, Result<MaterialWrapping.GenerateAndWrapOutput<TestInfo>, Types.Error>>>) returns (res: Result<MaterialWrapping.GenerateAndWrapOutput<TestInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      ensures res.Success? ==> |res.value.plaintextMaterial| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat
      decreases Modifies
    {
      :- Need(input.algorithmSuite == TEST_ALG_SUITE, Types.AwsCryptographicMaterialProvidersException(message := ""Unexpected input on TestGenerateAndWrapMaterial""));
      return Success(MaterialWrapping.GenerateAndWrapOutput(plaintextMaterial := PLAINTEXT_MAT, wrappedMaterial := WRAPPED_MAT, wrapInfo := TestInfo()));
    }
  }

  class TestUnwrapKeyMaterial extends MaterialWrapping.UnwrapMaterial<TestInfo> {
    constructor ()
      ensures Invariant()
    {
      Modifies := {};
    }

    predicate Invariant()
      reads Modifies
      decreases Modifies
    {
      Modifies == {}
    }

    predicate Ensures(input: MaterialWrapping.UnwrapInput, res: Result<MaterialWrapping.UnwrapOutput<TestInfo>, Types.Error>, attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<TestInfo>, Types.Error>>>)
      reads Modifies
      decreases Modifies
    {
      true
    }

    method Invoke(input: MaterialWrapping.UnwrapInput, ghost attemptsState: seq<ActionInvoke<MaterialWrapping.UnwrapInput, Result<MaterialWrapping.UnwrapOutput<TestInfo>, Types.Error>>>) returns (res: Result<MaterialWrapping.UnwrapOutput<TestInfo>, Types.Error>)
      requires Invariant()
      modifies Modifies
      ensures Invariant()
      ensures Ensures(input, res, attemptsState)
      ensures res.Success? ==> |res.value.unwrappedMaterial| == AlgorithmSuites.GetEncryptKeyLength(input.algorithmSuite) as nat
      decreases Modifies
    {
      :- Need(input.wrappedMaterial == WRAPPED_MAT, Types.AwsCryptographicMaterialProvidersException(message := ""Unexpected input on TestUnwrapMaterial""));
      :- Need(input.algorithmSuite == TEST_ALG_SUITE, Types.AwsCryptographicMaterialProvidersException(message := ""Unexpected input on TestUnwrapMaterial""));
      return Success(MaterialWrapping.UnwrapOutput(unwrappedMaterial := PLAINTEXT_MAT, unwrapInfo := TestInfo()));
    }
  }

  const TEST_ALG_SUITE := AlgorithmSuites.DBE_ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384
  const PLAINTEXT_MAT: seq<uint8> := seq(TEST_ALG_SUITE.encrypt.AES_GCM.keyLength as int, (_ /* _v0 */: int) => 1)
  const WRAPPED_MAT: seq<uint8> := seq(TEST_ALG_SUITE.encrypt.AES_GCM.keyLength as int, (_ /* _v1 */: int) => 2)

  method {:test} IntermediateWrapUnwrapTest()
  {
    var encCtx := map[];
    var keyLen := TEST_ALG_SUITE.encrypt.AES_GCM.keyLength as int;
    var tagLen := TEST_ALG_SUITE.encrypt.AES_GCM.tagLength as int;
    var pdk: seq<uint8> := seq(keyLen, (_ /* _v2 */: int) => 0);
    var testGenerateAndWrap := new TestGenerateAndWrapKeyMaterial();
    var intermediateWrapOutput := IntermediateWrap(testGenerateAndWrap, pdk, TEST_ALG_SUITE, encCtx);
    expect intermediateWrapOutput.Success?, ""expectation violation""
    expect |intermediateWrapOutput.value.wrappedMaterial| == keyLen + tagLen + |WRAPPED_MAT|, ""expectation violation""
    expect intermediateWrapOutput.value.wrappedMaterial[keyLen + tagLen..] == WRAPPED_MAT, ""expectation violation""
    var testUnwrap := new TestUnwrapKeyMaterial();
    var intermediateUnwrapOutput := IntermediateUnwrap(testUnwrap, intermediateWrapOutput.value.wrappedMaterial, TEST_ALG_SUITE, encCtx);
    expect intermediateUnwrapOutput.Success?, ""expectation violation""
    expect intermediateUnwrapOutput.value.plaintextDataKey == pdk, ""expectation violation""
    expect intermediateWrapOutput.value.symmetricSigningKey == intermediateUnwrapOutput.value.symmetricSigningKey, ""expectation violation""
  }

  method {:test} IntermediateGenerateAndWrapUnwrapTest()
  {
    var encCtx := map[];
    var keyLen := TEST_ALG_SUITE.encrypt.AES_GCM.keyLength as int;
    var tagLen := TEST_ALG_SUITE.encrypt.AES_GCM.tagLength as int;
    var testGenerateAndWrap := new TestGenerateAndWrapKeyMaterial();
    var intermediateWrapOutput := IntermediateGenerateAndWrap(testGenerateAndWrap, TEST_ALG_SUITE, encCtx);
    expect intermediateWrapOutput.Success?, ""expectation violation""
    expect |intermediateWrapOutput.value.wrappedMaterial| == keyLen + tagLen + |WRAPPED_MAT|, ""expectation violation""
    expect intermediateWrapOutput.value.wrappedMaterial[keyLen + tagLen..] == WRAPPED_MAT, ""expectation violation""
    var testUnwrap := new TestUnwrapKeyMaterial();
    var intermediateUnwrapOutput := IntermediateUnwrap(testUnwrap, intermediateWrapOutput.value.wrappedMaterial, TEST_ALG_SUITE, encCtx);
    expect intermediateUnwrapOutput.Success?, ""expectation violation""
    expect intermediateWrapOutput.value.plaintextDataKey == intermediateUnwrapOutput.value.plaintextDataKey, ""expectation violation""
    expect intermediateWrapOutput.value.symmetricSigningKey == intermediateUnwrapOutput.value.symmetricSigningKey, ""expectation violation""
  }
}

module TestVersionKey {

  import Types = AwsCryptographyKeyStoreTypes

  import ComAmazonawsKmsTypes

  import KMS = Com.Amazonaws.Kms

  import DDB = Com.Amazonaws.Dynamodb

  import KeyStore

  import UUID

  import opened StandardLibrary

  import opened Wrappers

  import opened AwsKmsUtils

  import opened Fixtures

  import CleanupItems

  import Structure

  import DDBKeystoreOperations
  method {:test} TestVersionKey()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var branchKeyId :- expect keyStore.CreateKey(Types.CreateKeyInput(branchKeyIdentifier := None, encryptionContext := None));
    var oldActiveResult :- expect keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(branchKeyIdentifier := branchKeyId.branchKeyIdentifier));
    var oldActiveVersion :- expect UTF8.Decode(oldActiveResult.branchKeyMaterials.branchKeyVersion);
    var versionKeyResult :- expect keyStore.VersionKey(Types.VersionKeyInput(branchKeyIdentifier := branchKeyId.branchKeyIdentifier));
    var getBranchKeyVersionResult :- expect keyStore.GetBranchKeyVersion(Types.GetBranchKeyVersionInput(branchKeyIdentifier := branchKeyId.branchKeyIdentifier, branchKeyVersion := oldActiveVersion));
    var newActiveResult :- expect keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(branchKeyIdentifier := branchKeyId.branchKeyIdentifier));
    var newActiveVersion :- expect UTF8.Decode(newActiveResult.branchKeyMaterials.branchKeyVersion);
    CleanupItems.DeleteVersion(branchKeyId.branchKeyIdentifier, newActiveVersion, ddbClient);
    CleanupItems.DeleteVersion(branchKeyId.branchKeyIdentifier, oldActiveVersion, ddbClient);
    CleanupItems.DeleteActive(branchKeyId.branchKeyIdentifier, ddbClient);
    expect getBranchKeyVersionResult.branchKeyMaterials.branchKeyVersion == oldActiveResult.branchKeyMaterials.branchKeyVersion, ""expectation violation""
    expect getBranchKeyVersionResult.branchKeyMaterials.branchKey == oldActiveResult.branchKeyMaterials.branchKey, ""expectation violation""
    expect getBranchKeyVersionResult.branchKeyMaterials.branchKeyVersion != newActiveResult.branchKeyMaterials.branchKeyVersion, ""expectation violation""
    expect getBranchKeyVersionResult.branchKeyMaterials.branchKey != newActiveResult.branchKeyMaterials.branchKey, ""expectation violation""
  }

  method {:test} InsertingADuplicateVersionWillFail()
  {
    var ddbClient :- expect DDB.DynamoDBClient();
    var encryptionContext := Structure.DecryptOnlyBranchKeyEncryptionContext(branchKeyId, branchKeyIdActiveVersion, """", """", keyArn, map[]);
    var output := DDBKeystoreOperations.WriteNewBranchKeyVersionToKeystore(Structure.ToAttributeMap(encryptionContext, [1]), Structure.ToAttributeMap(Structure.ActiveBranchKeyEncryptionContext(encryptionContext), [2]), branchKeyStoreName, ddbClient);
    expect output.Failure?, ""expectation violation""
  }

  method {:test} VersioningANonexistentBranchKeyWillFail()
  {
    var ddbClient :- expect DDB.DynamoDBClient();
    var encryptionContext := Structure.DecryptOnlyBranchKeyEncryptionContext(""!= branchKeyId"", branchKeyIdActiveVersion, """", """", keyArn, map[]);
    var output := DDBKeystoreOperations.WriteNewBranchKeyVersionToKeystore(Structure.ToAttributeMap(encryptionContext, [1]), Structure.ToAttributeMap(Structure.ActiveBranchKeyEncryptionContext(encryptionContext), [2]), branchKeyStoreName, ddbClient);
    expect output.Failure?, ""expectation violation""
  }
}

module CleanupItems {

  import DDB = Com.Amazonaws.Dynamodb

  import opened Wrappers

  import opened Fixtures

  import Structure
  method DeleteVersion(branchKeyIdentifier: string, branchKeyVersion: string, ddbClient: DDB.Types.IDynamoDBClient)
    requires ddbClient.ValidState()
    modifies ddbClient.Modifies
    ensures ddbClient.ValidState()
    decreases branchKeyIdentifier, branchKeyVersion, ddbClient
  {
    var _ /* _v0 */ := ddbClient.DeleteItem(DDB.Types.DeleteItemInput(TableName := branchKeyStoreName, Key := map[Structure.BRANCH_KEY_IDENTIFIER_FIELD := DDB.Types.AttributeValue.S(branchKeyIdentifier), Structure.TYPE_FIELD := DDB.Types.AttributeValue.S(Structure.BRANCH_KEY_TYPE_PREFIX + branchKeyVersion)], Expected := None, ConditionalOperator := None, ReturnValues := None, ReturnConsumedCapacity := None, ReturnItemCollectionMetrics := None, ConditionExpression := None, ExpressionAttributeNames := None, ExpressionAttributeValues := None));
  }

  method DeleteActive(branchKeyIdentifier: string, ddbClient: DDB.Types.IDynamoDBClient)
    requires ddbClient.ValidState()
    modifies ddbClient.Modifies
    ensures ddbClient.ValidState()
    decreases branchKeyIdentifier, ddbClient
  {
    var _ /* _v1 */ := ddbClient.DeleteItem(DDB.Types.DeleteItemInput(TableName := branchKeyStoreName, Key := map[Structure.BRANCH_KEY_IDENTIFIER_FIELD := DDB.Types.AttributeValue.S(branchKeyIdentifier), Structure.TYPE_FIELD := DDB.Types.AttributeValue.S(Structure.BRANCH_KEY_ACTIVE_TYPE)], Expected := None, ConditionalOperator := None, ReturnValues := None, ReturnConsumedCapacity := None, ReturnItemCollectionMetrics := None, ConditionExpression := None, ExpressionAttributeNames := None, ExpressionAttributeValues := None));
    var _ /* _v2 */ := ddbClient.DeleteItem(DDB.Types.DeleteItemInput(TableName := branchKeyStoreName, Key := map[Structure.BRANCH_KEY_IDENTIFIER_FIELD := DDB.Types.AttributeValue.S(branchKeyIdentifier), Structure.TYPE_FIELD := DDB.Types.AttributeValue.S(Structure.BEACON_KEY_TYPE_VALUE)], Expected := None, ConditionalOperator := None, ReturnValues := None, ReturnConsumedCapacity := None, ReturnItemCollectionMetrics := None, ConditionExpression := None, ExpressionAttributeNames := None, ExpressionAttributeValues := None));
  }
}

module TestCreateKeys {

  import Types = AwsCryptographyKeyStoreTypes

  import ComAmazonawsKmsTypes

  import KMS = Com.Amazonaws.Kms

  import DDB = Com.Amazonaws.Dynamodb

  import KeyStore

  import opened Wrappers

  import opened Fixtures

  import Structure

  import UTF8

  import CleanupItems

  import DDBKeystoreOperations

  import UUID
  method {:test} TestCreateBranchAndBeaconKeys()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var branchKeyId :- expect keyStore.CreateKey(Types.CreateKeyInput(branchKeyIdentifier := None, encryptionContext := None));
    var beaconKeyResult :- expect keyStore.GetBeaconKey(Types.GetBeaconKeyInput(branchKeyIdentifier := branchKeyId.branchKeyIdentifier));
    var activeResult :- expect keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(branchKeyIdentifier := branchKeyId.branchKeyIdentifier));
    var branchKeyVersion :- expect UTF8.Decode(activeResult.branchKeyMaterials.branchKeyVersion);
    var versionResult :- expect keyStore.GetBranchKeyVersion(Types.GetBranchKeyVersionInput(branchKeyIdentifier := branchKeyId.branchKeyIdentifier, branchKeyVersion := branchKeyVersion));
    CleanupItems.DeleteVersion(branchKeyId.branchKeyIdentifier, branchKeyVersion, ddbClient);
    CleanupItems.DeleteActive(branchKeyId.branchKeyIdentifier, ddbClient);
    expect beaconKeyResult.beaconKeyMaterials.beaconKey.Some?, ""expectation violation""
    expect |beaconKeyResult.beaconKeyMaterials.beaconKey.value| == 32, ""expectation violation""
    expect |activeResult.branchKeyMaterials.branchKey| == 32, ""expectation violation""
    expect versionResult.branchKeyMaterials.branchKey == activeResult.branchKeyMaterials.branchKey, ""expectation violation""
    expect versionResult.branchKeyMaterials.branchKeyIdentifier == activeResult.branchKeyMaterials.branchKeyIdentifier == beaconKeyResult.beaconKeyMaterials.beaconKeyIdentifier, ""expectation violation""
    expect versionResult.branchKeyMaterials.branchKeyVersion == activeResult.branchKeyMaterials.branchKeyVersion, ""expectation violation""
    var idByteUUID :- expect UUID.ToByteArray(activeResult.branchKeyMaterials.branchKeyIdentifier);
    var idRoundTrip :- expect UUID.FromByteArray(idByteUUID);
    expect idRoundTrip == activeResult.branchKeyMaterials.branchKeyIdentifier, ""expectation violation""
    var versionString :- expect UTF8.Decode(activeResult.branchKeyMaterials.branchKeyVersion);
    var versionByteUUID :- expect UUID.ToByteArray(versionString);
    var versionRoundTrip :- expect UUID.FromByteArray(versionByteUUID);
    expect versionRoundTrip == versionString, ""expectation violation""
  }

  method {:test} TestCreateOptions()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var id :- expect UUID.GenerateUUID();
    var encryptionContext :- expect EncodeEncryptionContext(map[""some"" := ""encryption"", ""context"" := ""values""]);
    var branchKeyId :- expect keyStore.CreateKey(Types.CreateKeyInput(branchKeyIdentifier := Some(id), encryptionContext := Some(encryptionContext)));
    var beaconKeyResult :- expect keyStore.GetBeaconKey(Types.GetBeaconKeyInput(branchKeyIdentifier := branchKeyId.branchKeyIdentifier));
    var activeResult :- expect keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(branchKeyIdentifier := branchKeyId.branchKeyIdentifier));
    var branchKeyVersion :- expect UTF8.Decode(activeResult.branchKeyMaterials.branchKeyVersion);
    var versionResult :- expect keyStore.GetBranchKeyVersion(Types.GetBranchKeyVersionInput(branchKeyIdentifier := branchKeyId.branchKeyIdentifier, branchKeyVersion := branchKeyVersion));
    CleanupItems.DeleteVersion(branchKeyId.branchKeyIdentifier, branchKeyVersion, ddbClient);
    CleanupItems.DeleteActive(branchKeyId.branchKeyIdentifier, ddbClient);
    expect id == versionResult.branchKeyMaterials.branchKeyIdentifier == activeResult.branchKeyMaterials.branchKeyIdentifier == beaconKeyResult.beaconKeyMaterials.beaconKeyIdentifier, ""expectation violation""
    expect encryptionContext == versionResult.branchKeyMaterials.encryptionContext == activeResult.branchKeyMaterials.encryptionContext == beaconKeyResult.beaconKeyMaterials.encryptionContext, ""expectation violation""
  }

  method {:test} TestCreateDuplicate()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var attempt := keyStore.CreateKey(Types.CreateKeyInput(branchKeyIdentifier := Some(branchKeyId), encryptionContext := None));
    expect attempt.Failure?, ""expectation violation""
  }

  method {:test} InsertingADuplicateWillFail()
  {
    var ddbClient :- expect DDB.DynamoDBClient();
    var encryptionContext := Structure.DecryptOnlyBranchKeyEncryptionContext(branchKeyId, branchKeyIdActiveVersion, """", """", keyArn, map[]);
    var output := DDBKeystoreOperations.WriteNewKeyToStore(Structure.ToAttributeMap(encryptionContext, [1]), Structure.ToAttributeMap(Structure.ActiveBranchKeyEncryptionContext(encryptionContext), [2]), Structure.ToAttributeMap(Structure.BeaconKeyEncryptionContext(encryptionContext), [3]), branchKeyStoreName, ddbClient);
    expect output.Failure?, ""expectation violation""
  }

  method {:test} InsertingADuplicateWillWithADifferentVersionFail()
  {
    var ddbClient :- expect DDB.DynamoDBClient();
    var encryptionContext := Structure.DecryptOnlyBranchKeyEncryptionContext(branchKeyId, ""!= branchKeyIdActiveVersion"", """", """", keyArn, map[]);
    var output := DDBKeystoreOperations.WriteNewKeyToStore(Structure.ToAttributeMap(encryptionContext, [1]), Structure.ToAttributeMap(Structure.ActiveBranchKeyEncryptionContext(encryptionContext), [2]), Structure.ToAttributeMap(Structure.BeaconKeyEncryptionContext(encryptionContext), [3]), branchKeyStoreName, ddbClient);
    expect output.Failure?, ""expectation violation""
  }

  method EncodeEncryptionContext(input: map<string, string>) returns (output: Result<Types.EncryptionContext, string>)
    decreases input
  {
    var encodedEncryptionContext := set k: seq<char> {:trigger input[k]} {:trigger k in input} | k in input :: (UTF8.Encode(k), UTF8.Encode(input[k]), k);
    :- Need(forall i: (Result<ValidUTF8Bytes, seq<char>>, Result<ValidUTF8Bytes, seq<char>>, seq<char>) {:trigger i.2} {:trigger i.1} {:trigger i.0} {:trigger i in encodedEncryptionContext} | i in encodedEncryptionContext :: i.0.Success? && i.1.Success? && var encoded: Result<string, string> := UTF8.Decode(i.0.value); encoded.Success? && i.2 == encoded.value, ""Unable to encode string"");
    output := Success(map i: (Result<ValidUTF8Bytes, seq<char>>, Result<ValidUTF8Bytes, seq<char>>, seq<char>) {:trigger i.1} {:trigger i.0} {:trigger i in encodedEncryptionContext} | i in encodedEncryptionContext :: i.0.value := i.1.value);
  }
}

module TestGetKeys {

  import Types = AwsCryptographyKeyStoreTypes

  import ComAmazonawsKmsTypes

  import KMS = Com.Amazonaws.Kms

  import DDB = Com.Amazonaws.Dynamodb

  import KeyStore

  import opened Wrappers

  import opened Fixtures

  import UTF8
  const incorrectLogicalName := ""MySuperAwesomeTableName""

  method {:test} TestGetBeaconKey()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var beaconKeyResult :- expect keyStore.GetBeaconKey(Types.GetBeaconKeyInput(branchKeyIdentifier := branchKeyId));
    expect beaconKeyResult.beaconKeyMaterials.beaconKeyIdentifier == branchKeyId, ""expectation violation""
    expect beaconKeyResult.beaconKeyMaterials.beaconKey.Some?, ""expectation violation""
    expect |beaconKeyResult.beaconKeyMaterials.beaconKey.value| == 32, ""expectation violation""
  }

  method {:test} TestGetActiveKey()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var activeResult :- expect keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(branchKeyIdentifier := branchKeyId));
    expect activeResult.branchKeyMaterials.branchKeyIdentifier == branchKeyId, ""expectation violation""
    expect activeResult.branchKeyMaterials.branchKeyVersion == branchKeyIdActiveVersionUtf8Bytes, ""expectation violation""
    expect |activeResult.branchKeyMaterials.branchKey| == 32, ""expectation violation""
  }

  method {:test} TestGetBranchKeyVersion()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var versionResult :- expect keyStore.GetBranchKeyVersion(Types.GetBranchKeyVersionInput(branchKeyIdentifier := branchKeyId, branchKeyVersion := branchKeyIdActiveVersion));
    var testBytes :- expect UTF8.Encode(branchKeyIdActiveVersion);
    expect versionResult.branchKeyMaterials.branchKeyIdentifier == branchKeyId, ""expectation violation""
    expect versionResult.branchKeyMaterials.branchKeyVersion == branchKeyIdActiveVersionUtf8Bytes == testBytes, ""expectation violation""
    expect |versionResult.branchKeyMaterials.branchKey| == 32, ""expectation violation""
  }

  method {:test} TestGetActiveKeyWithIncorrectKmsKeyArn()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(mkrKeyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var activeResult := keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(branchKeyIdentifier := branchKeyId));
    expect activeResult.Failure?, ""expectation violation""
  }

  method {:test} TestGetActiveKeyWrongLogicalKeyStoreName()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := incorrectLogicalName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var activeResult := keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(branchKeyIdentifier := branchKeyId));
    expect activeResult.Failure?, ""expectation violation""
  }

  method {:test} TestGetActiveKeyWithNoClients()
  {
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := None, kmsClient := None);
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var activeResult :- expect keyStore.GetActiveBranchKey(Types.GetActiveBranchKeyInput(branchKeyIdentifier := branchKeyId));
    expect |activeResult.branchKeyMaterials.branchKey| == 32, ""expectation violation""
  }
}

module TestConfig {

  import Types = AwsCryptographyKeyStoreTypes

  import ComAmazonawsKmsTypes

  import KMS = Com.Amazonaws.Kms

  import DDB = Com.Amazonaws.Dynamodb

  import KeyStore

  import opened Wrappers

  import opened Fixtures

  import UUID
  method {:test} TestInvalidKmsKeyArnConfig()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyId);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Failure?, ""expectation violation""
    expect keyStore.error == Types.KeyStoreException(message := ""Invalid AWS KMS Key Arn""), ""expectation violation""
  }

  method {:test} TestValidConfig()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?, ""expectation violation""
    var conf :- expect keyStore.value.GetKeyStoreInfo();
    var idByteUUID :- expect UUID.ToByteArray(conf.keyStoreId);
    var idRoundTrip :- expect UUID.FromByteArray(idByteUUID);
    expect idRoundTrip == conf.keyStoreId, ""expectation violation""
    expect conf.keyStoreName == branchKeyStoreName, ""expectation violation""
    expect conf.logicalKeyStoreName == logicalKeyStoreName, ""expectation violation""
    expect conf.kmsConfiguration == kmsConfig, ""expectation violation""
  }

  method {:test} TestValidConfigNoClients()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := None);
    var keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?, ""expectation violation""
    keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := None, kmsClient := Some(kmsClient));
    keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?, ""expectation violation""
    keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := None, kmsClient := None);
    keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?, ""expectation violation""
  }
}

module TestCreateKeyStore {

  import Types = AwsCryptographyKeyStoreTypes

  import KMS = Com.Amazonaws.Kms

  import DDB = Com.Amazonaws.Dynamodb

  import KeyStore

  import opened Wrappers

  import opened AwsArnParsing

  import opened Fixtures
  method {:test} TestCreateKeyStore()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);
    var keyStoreConfig := Types.KeyStoreConfig(id := None, kmsConfiguration := kmsConfig, logicalKeyStoreName := logicalKeyStoreName, grantTokens := None, ddbTableName := branchKeyStoreName, ddbClient := Some(ddbClient), kmsClient := Some(kmsClient));
    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    var keyStoreArn :- expect keyStore.CreateKeyStore(Types.CreateKeyStoreInput());
    expect AwsArnParsing.ParseAmazonDynamodbTableName(keyStoreArn.tableArn).Success?, ""expectation violation""
    expect AwsArnParsing.ParseAmazonDynamodbTableName(keyStoreArn.tableArn).value == branchKeyStoreName, ""expectation violation""
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

module Aws {

  module Cryptography {

      }
}

module Com {

  module Amazonaws {

    
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
  public static Func<U1, U2, U3, U4, U5, U6, U7, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, TResult, U1, U2, U3, U4, U5, U6, U7, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
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
namespace Com_mAmazonaws_Compile {

} // end of namespace Com_mAmazonaws_Compile
namespace Com_Compile {

} // end of namespace Com_Compile
namespace TestStormTracker_Compile {

  public partial class __default {
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IMaterials MakeMat(Dafny.ISequence<byte> data) {
      return software.amazon.cryptography.materialproviders.internaldafny.types.Materials.create_BranchKey(software.amazon.cryptography.keystore.internaldafny.types.BranchKeyMaterials.create(Dafny.Sequence<char>.FromString("spoo"), data, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(), data));
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryInput MakeGet(Dafny.ISequence<byte> data) {
      return software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryInput.create(data, Wrappers_Compile.Option<long>.create_None());
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IDeleteCacheEntryInput MakeDel(Dafny.ISequence<byte> data) {
      return software.amazon.cryptography.materialproviders.internaldafny.types.DeleteCacheEntryInput.create(data);
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IPutCacheEntryInput MakePut(Dafny.ISequence<byte> data, long expiryTime)
    {
      return software.amazon.cryptography.materialproviders.internaldafny.types.PutCacheEntryInput.create(data, TestStormTracker_Compile.__default.MakeMat(data), 123456789L, expiryTime, Wrappers_Compile.Option<int>.create_None(), Wrappers_Compile.Option<int>.create_None());
    }
    public static void StormTrackerBasics()
    {
      StormTracker_Compile.StormTracker _0_st;
      StormTracker_Compile.StormTracker _nw0 = new StormTracker_Compile.StormTracker();
      _nw0.__ctor(StormTracker_Compile.__default.DefaultStorm());
      _0_st = _nw0;
      Dafny.ISequence<byte> _1_abc;
      _1_abc = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("abc"));
      Dafny.ISequence<byte> _2_cde;
      _2_cde = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("cde"));
      StormTracker_Compile._ICacheState _3_res;
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _4_valueOrError0 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out0;
      _out0 = (_0_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_1_abc), 10000L);
      _4_valueOrError0 = _out0;
      if (!(!((_4_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(55,12): " + _4_valueOrError0);}
      _3_res = (_4_valueOrError0).Extract();
      if (!((_3_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(56,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _5_valueOrError1 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out1;
      _out1 = (_0_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_1_abc), 10000L);
      _5_valueOrError1 = _out1;
      if (!(!((_5_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(57,8): " + _5_valueOrError1);}
      _3_res = (_5_valueOrError1).Extract();
      if (!((_3_res).is_EmptyWait)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(58,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _System._ITuple0 _6_res2;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _7_valueOrError2 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out2;
      _out2 = (_0_st).PutCacheEntry(TestStormTracker_Compile.__default.MakePut(_1_abc, 10000L));
      _7_valueOrError2 = _out2;
      if (!(!((_7_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(59,13): " + _7_valueOrError2);}
      _6_res2 = (_7_valueOrError2).Extract();
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _8_valueOrError3 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out3;
      _out3 = (_0_st).PutCacheEntry(TestStormTracker_Compile.__default.MakePut(_2_cde, 10000L));
      _8_valueOrError3 = _out3;
      if (!(!((_8_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(60,9): " + _8_valueOrError3);}
      _6_res2 = (_8_valueOrError3).Extract();
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _9_valueOrError4 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out4;
      _out4 = (_0_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_1_abc), 10001L);
      _9_valueOrError4 = _out4;
      if (!(!((_9_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(61,8): " + _9_valueOrError4);}
      _3_res = (_9_valueOrError4).Extract();
      if (!((_3_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(62,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _10_valueOrError5 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out5;
      _out5 = (_0_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_1_abc), 10001L);
      _10_valueOrError5 = _out5;
      if (!(!((_10_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(63,8): " + _10_valueOrError5);}
      _3_res = (_10_valueOrError5).Extract();
      if (!((_3_res).is_EmptyWait)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(64,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _11_res3;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out6;
      _out6 = (_0_st).GetCacheEntry(TestStormTracker_Compile.__default.MakeGet(_1_abc));
      _11_res3 = _out6;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out7;
      _out7 = (_0_st).GetCacheEntry(TestStormTracker_Compile.__default.MakeGet(_1_abc));
      _11_res3 = _out7;
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _12_res4;
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out8;
      _out8 = (_0_st).GetFromCache(TestStormTracker_Compile.__default.MakeGet(_1_abc));
      _12_res4 = _out8;
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out9;
      _out9 = (_0_st).GetFromCache(TestStormTracker_Compile.__default.MakeGet(_1_abc));
      _12_res4 = _out9;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _13_res5;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out10;
      _out10 = (_0_st).DeleteCacheEntry(TestStormTracker_Compile.__default.MakeDel(_1_abc));
      _13_res5 = _out10;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out11;
      _out11 = (_0_st).DeleteCacheEntry(TestStormTracker_Compile.__default.MakeDel(_1_abc));
      _13_res5 = _out11;
    }
    public static void StormTrackerFanOut()
    {
      StormTracker_Compile.StormTracker _14_st;
      StormTracker_Compile.StormTracker _nw1 = new StormTracker_Compile.StormTracker();
      _nw1.__ctor(Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(StormTracker_Compile.__default.DefaultStorm(), _pat_let0_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(_pat_let0_0, _15_dt__update__tmp_h0 => Dafny.Helpers.Let<int, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(3, _pat_let1_0 => Dafny.Helpers.Let<int, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(_pat_let1_0, _16_dt__update_hfanOut_h0 => software.amazon.cryptography.materialproviders.internaldafny.types.StormTrackingCache.create((_15_dt__update__tmp_h0).dtor_entryCapacity, (_15_dt__update__tmp_h0).dtor_entryPruningTailSize, (_15_dt__update__tmp_h0).dtor_gracePeriod, (_15_dt__update__tmp_h0).dtor_graceInterval, _16_dt__update_hfanOut_h0, (_15_dt__update__tmp_h0).dtor_inFlightTTL, (_15_dt__update__tmp_h0).dtor_sleepMilli))))));
      _14_st = _nw1;
      Dafny.ISequence<byte> _17_one;
      _17_one = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("one"));
      Dafny.ISequence<byte> _18_two;
      _18_two = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("two"));
      Dafny.ISequence<byte> _19_three;
      _19_three = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("three"));
      Dafny.ISequence<byte> _20_four;
      _20_four = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("four"));
      StormTracker_Compile._ICacheState _21_res;
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _22_valueOrError0 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out12;
      _out12 = (_14_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_17_one), 10000L);
      _22_valueOrError0 = _out12;
      if (!(!((_22_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(84,12): " + _22_valueOrError0);}
      _21_res = (_22_valueOrError0).Extract();
      if (!((_21_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(85,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _23_valueOrError1 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out13;
      _out13 = (_14_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_18_two), 10000L);
      _23_valueOrError1 = _out13;
      if (!(!((_23_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(86,8): " + _23_valueOrError1);}
      _21_res = (_23_valueOrError1).Extract();
      if (!((_21_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(87,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _24_valueOrError2 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out14;
      _out14 = (_14_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_19_three), 10000L);
      _24_valueOrError2 = _out14;
      if (!(!((_24_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(88,8): " + _24_valueOrError2);}
      _21_res = (_24_valueOrError2).Extract();
      if (!((_21_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(89,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _25_valueOrError3 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out15;
      _out15 = (_14_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_20_four), 10000L);
      _25_valueOrError3 = _out15;
      if (!(!((_25_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(90,8): " + _25_valueOrError3);}
      _21_res = (_25_valueOrError3).Extract();
      if (!((_21_res).is_EmptyWait)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(91,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void StormTrackerTTL()
    {
      StormTracker_Compile.StormTracker _26_st;
      StormTracker_Compile.StormTracker _nw2 = new StormTracker_Compile.StormTracker();
      _nw2.__ctor(Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(StormTracker_Compile.__default.DefaultStorm(), _pat_let2_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(_pat_let2_0, _27_dt__update__tmp_h0 => Dafny.Helpers.Let<int, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(5, _pat_let3_0 => Dafny.Helpers.Let<int, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(_pat_let3_0, _28_dt__update_hinFlightTTL_h0 => Dafny.Helpers.Let<int, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(3, _pat_let4_0 => Dafny.Helpers.Let<int, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(_pat_let4_0, _29_dt__update_hfanOut_h0 => software.amazon.cryptography.materialproviders.internaldafny.types.StormTrackingCache.create((_27_dt__update__tmp_h0).dtor_entryCapacity, (_27_dt__update__tmp_h0).dtor_entryPruningTailSize, (_27_dt__update__tmp_h0).dtor_gracePeriod, (_27_dt__update__tmp_h0).dtor_graceInterval, _29_dt__update_hfanOut_h0, _28_dt__update_hinFlightTTL_h0, (_27_dt__update__tmp_h0).dtor_sleepMilli))))))));
      _26_st = _nw2;
      Dafny.ISequence<byte> _30_one;
      _30_one = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("one"));
      Dafny.ISequence<byte> _31_two;
      _31_two = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("two"));
      Dafny.ISequence<byte> _32_three;
      _32_three = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("three"));
      Dafny.ISequence<byte> _33_four;
      _33_four = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("four"));
      StormTracker_Compile._ICacheState _34_res;
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _35_valueOrError0 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out16;
      _out16 = (_26_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_30_one), 10000L);
      _35_valueOrError0 = _out16;
      if (!(!((_35_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(103,12): " + _35_valueOrError0);}
      _34_res = (_35_valueOrError0).Extract();
      if (!((_34_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(104,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _36_valueOrError1 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out17;
      _out17 = (_26_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_31_two), 10000L);
      _36_valueOrError1 = _out17;
      if (!(!((_36_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(105,8): " + _36_valueOrError1);}
      _34_res = (_36_valueOrError1).Extract();
      if (!((_34_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(106,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _37_valueOrError2 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out18;
      _out18 = (_26_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_32_three), 10000L);
      _37_valueOrError2 = _out18;
      if (!(!((_37_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(107,8): " + _37_valueOrError2);}
      _34_res = (_37_valueOrError2).Extract();
      if (!((_34_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(108,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _38_valueOrError3 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out19;
      _out19 = (_26_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_33_four), 10000L);
      _38_valueOrError3 = _out19;
      if (!(!((_38_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(109,8): " + _38_valueOrError3);}
      _34_res = (_38_valueOrError3).Extract();
      if (!((_34_res).is_EmptyWait)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(110,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _39_valueOrError4 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out20;
      _out20 = (_26_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_33_four), 10001L);
      _39_valueOrError4 = _out20;
      if (!(!((_39_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(111,8): " + _39_valueOrError4);}
      _34_res = (_39_valueOrError4).Extract();
      if (!((_34_res).is_EmptyWait)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(112,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _40_valueOrError5 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out21;
      _out21 = (_26_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_33_four), 10003L);
      _40_valueOrError5 = _out21;
      if (!(!((_40_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(113,8): " + _40_valueOrError5);}
      _34_res = (_40_valueOrError5).Extract();
      if (!((_34_res).is_EmptyWait)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(114,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _41_valueOrError6 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out22;
      _out22 = (_26_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_33_four), 10005L);
      _41_valueOrError6 = _out22;
      if (!(!((_41_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(115,8): " + _41_valueOrError6);}
      _34_res = (_41_valueOrError6).Extract();
      if (!((_34_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(116,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void StormTrackerGraceInterval()
    {
      StormTracker_Compile.StormTracker _42_st;
      StormTracker_Compile.StormTracker _nw3 = new StormTracker_Compile.StormTracker();
      _nw3.__ctor(Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(StormTracker_Compile.__default.DefaultStorm(), _pat_let5_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(_pat_let5_0, _43_dt__update__tmp_h0 => Dafny.Helpers.Let<int, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(3, _pat_let6_0 => Dafny.Helpers.Let<int, software.amazon.cryptography.materialproviders.internaldafny.types._IStormTrackingCache>(_pat_let6_0, _44_dt__update_hgraceInterval_h0 => software.amazon.cryptography.materialproviders.internaldafny.types.StormTrackingCache.create((_43_dt__update__tmp_h0).dtor_entryCapacity, (_43_dt__update__tmp_h0).dtor_entryPruningTailSize, (_43_dt__update__tmp_h0).dtor_gracePeriod, _44_dt__update_hgraceInterval_h0, (_43_dt__update__tmp_h0).dtor_fanOut, (_43_dt__update__tmp_h0).dtor_inFlightTTL, (_43_dt__update__tmp_h0).dtor_sleepMilli))))));
      _42_st = _nw3;
      Dafny.ISequence<byte> _45_one;
      _45_one = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("one"));
      StormTracker_Compile._ICacheState _46_res;
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _47_valueOrError0 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out23;
      _out23 = (_42_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_45_one), 10000L);
      _47_valueOrError0 = _out23;
      if (!(!((_47_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(125,12): " + _47_valueOrError0);}
      _46_res = (_47_valueOrError0).Extract();
      if (!((_46_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(126,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _48_valueOrError1 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out24;
      _out24 = (_42_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_45_one), 10000L);
      _48_valueOrError1 = _out24;
      if (!(!((_48_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(127,8): " + _48_valueOrError1);}
      _46_res = (_48_valueOrError1).Extract();
      if (!((_46_res).is_EmptyWait)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(128,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _49_valueOrError2 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out25;
      _out25 = (_42_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_45_one), 10001L);
      _49_valueOrError2 = _out25;
      if (!(!((_49_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(129,8): " + _49_valueOrError2);}
      _46_res = (_49_valueOrError2).Extract();
      if (!((_46_res).is_EmptyWait)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(130,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _50_valueOrError3 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out26;
      _out26 = (_42_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_45_one), 10002L);
      _50_valueOrError3 = _out26;
      if (!(!((_50_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(131,8): " + _50_valueOrError3);}
      _46_res = (_50_valueOrError3).Extract();
      if (!((_46_res).is_EmptyWait)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(132,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _51_valueOrError4 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out27;
      _out27 = (_42_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_45_one), 10003L);
      _51_valueOrError4 = _out27;
      if (!(!((_51_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(133,8): " + _51_valueOrError4);}
      _46_res = (_51_valueOrError4).Extract();
      if (!((_46_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(134,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void StormTrackerGracePeriod()
    {
      StormTracker_Compile.StormTracker _52_st;
      StormTracker_Compile.StormTracker _nw4 = new StormTracker_Compile.StormTracker();
      _nw4.__ctor(StormTracker_Compile.__default.DefaultStorm());
      _52_st = _nw4;
      Dafny.ISequence<byte> _53_one;
      _53_one = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("one"));
      _System._ITuple0 _54_res2;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _55_valueOrError0 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out28;
      _out28 = (_52_st).PutCacheEntry(TestStormTracker_Compile.__default.MakePut(_53_one, 10010L));
      _55_valueOrError0 = _out28;
      if (!(!((_55_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(143,13): " + _55_valueOrError0);}
      _54_res2 = (_55_valueOrError0).Extract();
      StormTracker_Compile._ICacheState _56_res;
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _57_valueOrError1 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out29;
      _out29 = (_52_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_53_one), 9999L);
      _57_valueOrError1 = _out29;
      if (!(!((_57_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(145,12): " + _57_valueOrError1);}
      _56_res = (_57_valueOrError1).Extract();
      if (!((_56_res).is_Full)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(146,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _58_valueOrError2 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out30;
      _out30 = (_52_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_53_one), 10000L);
      _58_valueOrError2 = _out30;
      if (!(!((_58_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(147,8): " + _58_valueOrError2);}
      _56_res = (_58_valueOrError2).Extract();
      if (!((_56_res).is_EmptyFetch)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(148,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _59_valueOrError3 = Wrappers_Compile.Result<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(StormTracker_Compile.CacheState.Default());
      Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out31;
      _out31 = (_52_st).GetFromCacheWithTime(TestStormTracker_Compile.__default.MakeGet(_53_one), 10000L);
      _59_valueOrError3 = _out31;
      if (!(!((_59_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(149,8): " + _59_valueOrError3);}
      _56_res = (_59_valueOrError3).Extract();
      if (!((_56_res).is_Full)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/StormTracker.dfy(150,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestStormTracker_Compile
namespace TestUtils_Compile {

  public interface _ISmallEncryptionContextVariation {
    bool is_Empty { get; }
    bool is_A { get; }
    bool is_AB { get; }
    bool is_BA { get; }
    _ISmallEncryptionContextVariation DowncastClone();
  }
  public abstract class SmallEncryptionContextVariation : _ISmallEncryptionContextVariation {
    public SmallEncryptionContextVariation() { }
    private static readonly TestUtils_Compile._ISmallEncryptionContextVariation theDefault = create_Empty();
    public static TestUtils_Compile._ISmallEncryptionContextVariation Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestUtils_Compile._ISmallEncryptionContextVariation> _TYPE = new Dafny.TypeDescriptor<TestUtils_Compile._ISmallEncryptionContextVariation>(TestUtils_Compile.SmallEncryptionContextVariation.Default());
    public static Dafny.TypeDescriptor<TestUtils_Compile._ISmallEncryptionContextVariation> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISmallEncryptionContextVariation create_Empty() {
      return new SmallEncryptionContextVariation_Empty();
    }
    public static _ISmallEncryptionContextVariation create_A() {
      return new SmallEncryptionContextVariation_A();
    }
    public static _ISmallEncryptionContextVariation create_AB() {
      return new SmallEncryptionContextVariation_AB();
    }
    public static _ISmallEncryptionContextVariation create_BA() {
      return new SmallEncryptionContextVariation_BA();
    }
    public bool is_Empty { get { return this is SmallEncryptionContextVariation_Empty; } }
    public bool is_A { get { return this is SmallEncryptionContextVariation_A; } }
    public bool is_AB { get { return this is SmallEncryptionContextVariation_AB; } }
    public bool is_BA { get { return this is SmallEncryptionContextVariation_BA; } }
    public static System.Collections.Generic.IEnumerable<_ISmallEncryptionContextVariation> AllSingletonConstructors {
      get {
        yield return SmallEncryptionContextVariation.create_Empty();
        yield return SmallEncryptionContextVariation.create_A();
        yield return SmallEncryptionContextVariation.create_AB();
        yield return SmallEncryptionContextVariation.create_BA();
      }
    }
    public abstract _ISmallEncryptionContextVariation DowncastClone();
  }
  public class SmallEncryptionContextVariation_Empty : SmallEncryptionContextVariation {
    public SmallEncryptionContextVariation_Empty() {
    }
    public override _ISmallEncryptionContextVariation DowncastClone() {
      if (this is _ISmallEncryptionContextVariation dt) { return dt; }
      return new SmallEncryptionContextVariation_Empty();
    }
    public override bool Equals(object other) {
      var oth = other as TestUtils_Compile.SmallEncryptionContextVariation_Empty;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestUtils_Compile.SmallEncryptionContextVariation.Empty";
      return s;
    }
  }
  public class SmallEncryptionContextVariation_A : SmallEncryptionContextVariation {
    public SmallEncryptionContextVariation_A() {
    }
    public override _ISmallEncryptionContextVariation DowncastClone() {
      if (this is _ISmallEncryptionContextVariation dt) { return dt; }
      return new SmallEncryptionContextVariation_A();
    }
    public override bool Equals(object other) {
      var oth = other as TestUtils_Compile.SmallEncryptionContextVariation_A;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestUtils_Compile.SmallEncryptionContextVariation.A";
      return s;
    }
  }
  public class SmallEncryptionContextVariation_AB : SmallEncryptionContextVariation {
    public SmallEncryptionContextVariation_AB() {
    }
    public override _ISmallEncryptionContextVariation DowncastClone() {
      if (this is _ISmallEncryptionContextVariation dt) { return dt; }
      return new SmallEncryptionContextVariation_AB();
    }
    public override bool Equals(object other) {
      var oth = other as TestUtils_Compile.SmallEncryptionContextVariation_AB;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestUtils_Compile.SmallEncryptionContextVariation.AB";
      return s;
    }
  }
  public class SmallEncryptionContextVariation_BA : SmallEncryptionContextVariation {
    public SmallEncryptionContextVariation_BA() {
    }
    public override _ISmallEncryptionContextVariation DowncastClone() {
      if (this is _ISmallEncryptionContextVariation dt) { return dt; }
      return new SmallEncryptionContextVariation_BA();
    }
    public override bool Equals(object other) {
      var oth = other as TestUtils_Compile.SmallEncryptionContextVariation_BA;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestUtils_Compile.SmallEncryptionContextVariation.BA";
      return s;
    }
  }

  public partial class __default {
    public static Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> GenerateInvalidEncryptionContext()
    {
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty;
      Dafny.ISequence<byte> _60_validUTF8char;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _61_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _61_valueOrError0 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("a"));
      if (!(!((_61_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestUtils.dfy(42,43): " + _61_valueOrError0);}
      _60_validUTF8char = (_61_valueOrError0).Extract();
      Dafny.ISequence<byte> _62_key;
      _62_key = Dafny.Sequence<byte>.FromElements();
      while ((new BigInteger((_62_key).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT)) {
        _62_key = Dafny.Sequence<byte>.Concat(_62_key, _60_validUTF8char);
      }
      encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_62_key, Dafny.Sequence<byte>.FromElements((byte)(0))));
      return encCtx;
    }
    public static Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> GenerateLargeValidEncryptionContext()
    {
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> r = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty;
      BigInteger _63_numMaxPairs;
      _63_numMaxPairs = new BigInteger(9361);
      Dafny.ISequence<byte> _64_val;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _65_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _65_valueOrError0 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("a"));
      if (!(!((_65_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestUtils.dfy(62,12): " + _65_valueOrError0);}
      _64_val = (_65_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _66_encCtx;
      _66_encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements();
      BigInteger _67_i;
      _67_i = BigInteger.Zero;
      while (((new BigInteger((_66_encCtx).Count)) < (_63_numMaxPairs)) && ((_67_i) < (new BigInteger(65536)))) {
        Dafny.ISequence<byte> _68_key;
        _68_key = StandardLibrary_mUInt_Compile.__default.UInt16ToSeq((ushort)(_67_i));
        if (UTF8.__default.ValidUTF8Seq(_68_key)) {
          _66_encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Update(_66_encCtx, _68_key, _64_val);
        }
        _67_i = (_67_i) + (BigInteger.One);
      }
      r = _66_encCtx;
      return r;
      return r;
    }
    public static Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> SmallEncryptionContext(TestUtils_Compile._ISmallEncryptionContextVariation v)
    {
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty;
      Dafny.ISequence<byte> _69_keyA;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _70_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _70_valueOrError0 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("keyA"));
      if (!(!((_70_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestUtils.dfy(90,13): " + _70_valueOrError0);}
      _69_keyA = (_70_valueOrError0).Extract();
      Dafny.ISequence<byte> _71_valA;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _72_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _72_valueOrError1 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("valA"));
      if (!(!((_72_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestUtils.dfy(91,13): " + _72_valueOrError1);}
      _71_valA = (_72_valueOrError1).Extract();
      Dafny.ISequence<byte> _73_keyB;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _74_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _74_valueOrError2 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("keyB"));
      if (!(!((_74_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestUtils.dfy(92,13): " + _74_valueOrError2);}
      _73_keyB = (_74_valueOrError2).Extract();
      Dafny.ISequence<byte> _75_valB;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _76_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _76_valueOrError3 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("valB"));
      if (!(!((_76_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestUtils.dfy(93,13): " + _76_valueOrError3);}
      _75_valB = (_76_valueOrError3).Extract();
      TestUtils_Compile._ISmallEncryptionContextVariation _source0 = v;
      if (_source0.is_Empty) {
        encryptionContext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements();
      } else if (_source0.is_A) {
        encryptionContext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_69_keyA, _71_valA));
      } else if (_source0.is_AB) {
        encryptionContext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_69_keyA, _71_valA), new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_73_keyB, _75_valB));
      } else {
        encryptionContext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_73_keyB, _75_valB), new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_69_keyA, _71_valA));
      }
      return encryptionContext;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey GenerateMockEncryptedDataKey(Dafny.ISequence<char> keyProviderId, Dafny.ISequence<char> keyProviderInfo)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey edk = software.amazon.cryptography.materialproviders.internaldafny.types.EncryptedDataKey.Default();
      Dafny.ISequence<byte> _77_encodedkeyProviderId;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _78_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _78_valueOrError0 = UTF8.__default.Encode(keyProviderId);
      if (!(!((_78_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestUtils.dfy(113,29): " + _78_valueOrError0);}
      _77_encodedkeyProviderId = (_78_valueOrError0).Extract();
      Dafny.ISequence<byte> _79_encodedKeyProviderInfo;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _80_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _80_valueOrError1 = UTF8.__default.Encode(keyProviderInfo);
      if (!(!((_80_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestUtils.dfy(114,31): " + _80_valueOrError1);}
      _79_encodedKeyProviderInfo = (_80_valueOrError1).Extract();
      Dafny.ISequence<byte> _81_fakeCiphertext;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _82_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _82_valueOrError2 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("fakeCiphertext"));
      if (!(!((_82_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestUtils.dfy(115,23): " + _82_valueOrError2);}
      _81_fakeCiphertext = (_82_valueOrError2).Extract();
      edk = software.amazon.cryptography.materialproviders.internaldafny.types.EncryptedDataKey.create(_77_encodedkeyProviderId, _79_encodedKeyProviderInfo, _81_fakeCiphertext);
      return edk;
      return edk;
    }
    public static void NamespaceAndName(BigInteger n, out Dafny.ISequence<char> @namespace, out Dafny.ISequence<char> name)
    {
      @namespace = Dafny.Sequence<char>.Empty;
      name = Dafny.Sequence<char>.Empty;
      Dafny.ISequence<char> _83_s;
      _83_s = Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("child"), Dafny.Sequence<char>.FromElements((char)(((char)(n)) + ('0'))));
      @namespace = Dafny.Sequence<char>.Concat(_83_s, Dafny.Sequence<char>.FromString(" Namespace"));
      name = Dafny.Sequence<char>.Concat(_83_s, Dafny.Sequence<char>.FromString(" Name"));
    }
    public static Dafny.ISequence<char> KMS__RSA__PUBLIC__KEY { get {
      return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("-----BEGIN PUBLIC KEY-----\n"), Dafny.Sequence<char>.FromString("MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEA27Uc/fBaMVhxCE/SpCMQ\n")), Dafny.Sequence<char>.FromString("oSBRSzQJw+o2hBaA+FiPGtiJ/aPy7sn18aCkelaSj4kwoC79b/arNHlkjc7OJFsN\n")), Dafny.Sequence<char>.FromString("/GoFKgNvaiY4lOeJqEiWQGSSgHtsJLdbO2u4OOSxh8qIRAMKbMgQDVX4FR/PLKeK\n")), Dafny.Sequence<char>.FromString("fc2aCDvcNSpAM++8NlNmv7+xQBJydr5ce91eISbHkFRkK3/bAM+1iddupoRw4Wo2\n")), Dafny.Sequence<char>.FromString("r3avzrg5xBHmzR7u1FTab22Op3Hgb2dBLZH43wNKAceVwKqKA8UNAxashFON7xK9\n")), Dafny.Sequence<char>.FromString("yy4kfOL0Z/nhxRKe4jRZ/5v508qIzgzCksYy7Y3QbMejAtiYnr7s5/d5KWw0swou\n")), Dafny.Sequence<char>.FromString("twIDAQAB\n")), Dafny.Sequence<char>.FromString("-----END PUBLIC KEY-----"));
    } }
    public static Dafny.ISequence<char> KMS__RSA__PRIVATE__KEY__ARN { get {
      return Dafny.Sequence<char>.FromString("arn:aws:kms:us-west-2:370957321024:key/mrk-63d386cb70614ea59b32ad65c9315297");
    } }
    public static Dafny.ISequence<char> SHARED__TEST__KEY__ARN { get {
      return Dafny.Sequence<char>.FromString("arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f");
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> ACCOUNT__IDS { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("658956600833"));
    } }
    public static Dafny.ISequence<char> PARTITION { get {
      return Dafny.Sequence<char>.FromString("aws");
    } }
  }
} // end of namespace TestUtils_Compile
namespace TestLocalCMC_Compile {

  public partial class __default {
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IMaterials MakeMat(Dafny.ISequence<byte> data) {
      return software.amazon.cryptography.materialproviders.internaldafny.types.Materials.create_BranchKey(software.amazon.cryptography.keystore.internaldafny.types.BranchKeyMaterials.create(Dafny.Sequence<char>.FromString("spoo"), data, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(), data));
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryInput MakeGet(Dafny.ISequence<byte> data) {
      return software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryInput.create(data, Wrappers_Compile.Option<long>.create_None());
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IDeleteCacheEntryInput MakeDel(Dafny.ISequence<byte> data) {
      return software.amazon.cryptography.materialproviders.internaldafny.types.DeleteCacheEntryInput.create(data);
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IPutCacheEntryInput MakePut(Dafny.ISequence<byte> data, long expiryTime)
    {
      return software.amazon.cryptography.materialproviders.internaldafny.types.PutCacheEntryInput.create(data, TestLocalCMC_Compile.__default.MakeMat(data), 123456789L, expiryTime, Wrappers_Compile.Option<int>.create_None(), Wrappers_Compile.Option<int>.create_None());
    }
    public static void LocalCMCBasics()
    {
      LocalCMC_Compile.LocalCMC _84_st;
      LocalCMC_Compile.LocalCMC _nw5 = new LocalCMC_Compile.LocalCMC();
      _nw5.__ctor(new BigInteger(100), BigInteger.One);
      _84_st = _nw5;
      Dafny.ISequence<byte> _85_abc;
      _85_abc = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("abc"));
      Dafny.ISequence<byte> _86_cde;
      _86_cde = UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("cde"));
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _87_res;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out32;
      _out32 = (_84_st).GetCacheEntryWithTime(TestLocalCMC_Compile.__default.MakeGet(_85_abc), 10000L);
      _87_res = _out32;
      if (!((_87_res).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(56,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((_87_res).dtor_error).is_EntryDoesNotExist)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(57,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _System._ITuple0 _88_res2;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _89_valueOrError0 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out33;
      _out33 = (_84_st).PutCacheEntry_k(TestLocalCMC_Compile.__default.MakePut(_85_abc, 10000L));
      _89_valueOrError0 = _out33;
      if (!(!((_89_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(59,13): " + _89_valueOrError0);}
      _88_res2 = (_89_valueOrError0).Extract();
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _90_valueOrError1 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out34;
      _out34 = (_84_st).PutCacheEntry_k(TestLocalCMC_Compile.__default.MakePut(_86_cde, 10000L));
      _90_valueOrError1 = _out34;
      if (!(!((_90_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(60,9): " + _90_valueOrError1);}
      _88_res2 = (_90_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput _91_res3;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _92_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out35;
      _out35 = (_84_st).GetCacheEntryWithTime(TestLocalCMC_Compile.__default.MakeGet(_85_abc), 9999L);
      _92_valueOrError2 = _out35;
      if (!(!((_92_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(62,13): " + _92_valueOrError2);}
      _91_res3 = (_92_valueOrError2).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _93_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out36;
      _out36 = (_84_st).GetCacheEntryWithTime(TestLocalCMC_Compile.__default.MakeGet(_85_abc), 10000L);
      _93_valueOrError3 = _out36;
      if (!(!((_93_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(63,9): " + _93_valueOrError3);}
      _91_res3 = (_93_valueOrError3).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out37;
      _out37 = (_84_st).GetCacheEntryWithTime(TestLocalCMC_Compile.__default.MakeGet(_85_abc), 10001L);
      _87_res = _out37;
      if (!((_87_res).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(65,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((_87_res).dtor_error).is_EntryDoesNotExist)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(66,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _94_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out38;
      _out38 = (_84_st).GetCacheEntryWithTime(TestLocalCMC_Compile.__default.MakeGet(_86_cde), 9999L);
      _94_valueOrError4 = _out38;
      if (!(!((_94_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(68,9): " + _94_valueOrError4);}
      _91_res3 = (_94_valueOrError4).Extract();
      _System._ITuple0 _95_res5;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _96_valueOrError5 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out39;
      _out39 = (_84_st).DeleteCacheEntry_k(TestLocalCMC_Compile.__default.MakeDel(_86_cde));
      _96_valueOrError5 = _out39;
      if (!(!((_96_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(69,13): " + _96_valueOrError5);}
      _95_res5 = (_96_valueOrError5).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out40;
      _out40 = (_84_st).GetCacheEntryWithTime(TestLocalCMC_Compile.__default.MakeGet(_85_abc), 9999L);
      _87_res = _out40;
      if (!((_87_res).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(71,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((_87_res).dtor_error).is_EntryDoesNotExist)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(72,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _97_valueOrError6 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out41;
      _out41 = (_84_st).DeleteCacheEntry_k(TestLocalCMC_Compile.__default.MakeDel(_86_cde));
      _97_valueOrError6 = _out41;
      if (!(!((_97_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/CMCs/LocalCMC.dfy(73,9): " + _97_valueOrError6);}
      _95_res5 = (_97_valueOrError6).Extract();
    }
  }
} // end of namespace TestLocalCMC_Compile
namespace TestAwsKmsEncryptedDataKeyFilter_Compile {

  public partial class __default {
    public static void TestFailsNonKeyResource()
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter _98_discoveryFilter;
      software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter _out42;
      _out42 = TestAwsKmsEncryptedDataKeyFilter_Compile.__default.GetDiscoveryFilter();
      _98_discoveryFilter = _out42;
      AwsKmsDiscoveryKeyring_Compile.AwsKmsEncryptedDataKeyFilter _99_edkFilter;
      AwsKmsDiscoveryKeyring_Compile.AwsKmsEncryptedDataKeyFilter _nw6 = new AwsKmsDiscoveryKeyring_Compile.AwsKmsEncryptedDataKeyFilter();
      _nw6.__ctor(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>.create_Some(_98_discoveryFilter));
      _99_edkFilter = _nw6;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _100_badEdk;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _out43;
      _out43 = TestAwsKmsEncryptedDataKeyFilter_Compile.__default.GetNonKeyEncryptedDataKey();
      _100_badEdk = _out43;
      Wrappers_Compile._IResult<Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _101_filterResult;
      Wrappers_Compile._IResult<Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out44;
      _out44 = Actions_Compile.__default.FilterWithResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey, software.amazon.cryptography.materialproviders.internaldafny.types._IError>(_99_edkFilter, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_100_badEdk));
      _101_filterResult = _out44;
      if (!((_101_filterResult).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsDiscoveryKeryring/TestAwsKmsEncryptedDataKeyFilter.dfy(32,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.materialproviders.internaldafny.types._IError _102_test;
      _102_test = (_101_filterResult).dtor_error;
      if (!((_102_test).is_AwsCryptographicMaterialProvidersException)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsDiscoveryKeryring/TestAwsKmsEncryptedDataKeyFilter.dfy(34,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((_102_test).dtor_message).Equals(Dafny.Sequence<char>.FromString("Only AWS KMS Keys supported")))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsDiscoveryKeryring/TestAwsKmsEncryptedDataKeyFilter.dfy(35,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestMatchesKeyringsConfiguration()
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _103_matchingEdk;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _out45;
      _out45 = TestUtils_Compile.__default.GenerateMockEncryptedDataKey(Dafny.Sequence<char>.FromString("aws-kms"), TestUtils_Compile.__default.SHARED__TEST__KEY__ARN);
      _103_matchingEdk = _out45;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _104_mismatchEdkPartition;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _out46;
      _out46 = TestUtils_Compile.__default.GenerateMockEncryptedDataKey(Dafny.Sequence<char>.FromString("aws-kms"), Dafny.Sequence<char>.FromString("arn:aws-cn:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"));
      _104_mismatchEdkPartition = _out46;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _105_mismatchEdkAccount;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _out47;
      _out47 = TestUtils_Compile.__default.GenerateMockEncryptedDataKey(Dafny.Sequence<char>.FromString("aws-kms"), Dafny.Sequence<char>.FromString("arn:aws:kms:us-west-2:827585335069:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"));
      _105_mismatchEdkAccount = _out47;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _106_mismatchEdkProviderId;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _out48;
      _out48 = TestUtils_Compile.__default.GenerateMockEncryptedDataKey(Dafny.Sequence<char>.FromString("aws"), TestUtils_Compile.__default.SHARED__TEST__KEY__ARN);
      _106_mismatchEdkProviderId = _out48;
      software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter _107_discoveryFilter;
      software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter _out49;
      _out49 = TestAwsKmsEncryptedDataKeyFilter_Compile.__default.GetDiscoveryFilter();
      _107_discoveryFilter = _out49;
      AwsKmsDiscoveryKeyring_Compile.AwsKmsEncryptedDataKeyFilter _108_edkFilter;
      AwsKmsDiscoveryKeyring_Compile.AwsKmsEncryptedDataKeyFilter _nw7 = new AwsKmsDiscoveryKeyring_Compile.AwsKmsEncryptedDataKeyFilter();
      _nw7.__ctor(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>.create_Some(_107_discoveryFilter));
      _108_edkFilter = _nw7;
      Wrappers_Compile._IResult<Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _109_filterResult;
      Wrappers_Compile._IResult<Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out50;
      _out50 = Actions_Compile.__default.FilterWithResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey, software.amazon.cryptography.materialproviders.internaldafny.types._IError>(_108_edkFilter, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_103_matchingEdk, _104_mismatchEdkPartition, _105_mismatchEdkAccount, _106_mismatchEdkProviderId));
      _109_filterResult = _out50;
      if (!((_109_filterResult).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsDiscoveryKeryring/TestAwsKmsEncryptedDataKeyFilter.dfy(65,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((new BigInteger(((_109_filterResult).dtor_value).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsDiscoveryKeryring/TestAwsKmsEncryptedDataKeyFilter.dfy(66,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(object.Equals(((_109_filterResult).dtor_value).Select(BigInteger.Zero), _103_matchingEdk))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsDiscoveryKeryring/TestAwsKmsEncryptedDataKeyFilter.dfy(67,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter GetDiscoveryFilter()
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter discoveryFilter = software.amazon.cryptography.materialproviders.internaldafny.types.DiscoveryFilter.Default();
      discoveryFilter = software.amazon.cryptography.materialproviders.internaldafny.types.DiscoveryFilter.create(TestUtils_Compile.__default.ACCOUNT__IDS, TestUtils_Compile.__default.PARTITION);
      return discoveryFilter;
      return discoveryFilter;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey GetNonKeyEncryptedDataKey()
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey edk = software.amazon.cryptography.materialproviders.internaldafny.types.EncryptedDataKey.Default();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _out51;
      _out51 = TestUtils_Compile.__default.GenerateMockEncryptedDataKey(Dafny.Sequence<char>.FromString("aws-kms"), Dafny.Sequence<char>.FromString("arn:aws:kms:us-west-2:658956600833:alias/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"));
      edk = _out51;
      return edk;
    }
  }
} // end of namespace TestAwsKmsEncryptedDataKeyFilter_Compile
namespace Fixtures_Compile {

  public partial class __default {
    public static Dafny.ISequence<char> branchKeyStoreName { get {
      return Dafny.Sequence<char>.FromString("KeyStoreDdbTable");
    } }
    public static Dafny.ISequence<char> logicalKeyStoreName { get {
      return Fixtures_Compile.__default.branchKeyStoreName;
    } }
    public static Dafny.ISequence<char> branchKeyId { get {
      return Dafny.Sequence<char>.FromString("75789115-1deb-4fe3-a2ec-be9e885d1945");
    } }
    public static Dafny.ISequence<char> branchKeyIdActiveVersion { get {
      return Dafny.Sequence<char>.FromString("fed7ad33-0774-4f97-aa5e-6c766fc8af9f");
    } }
    public static Dafny.ISequence<char> branchKeyIdWithEC { get {
      return Dafny.Sequence<char>.FromString("4bb57643-07c1-419e-92ad-0df0df149d7c");
    } }
    public static Dafny.ISequence<byte> branchKeyIdActiveVersionUtf8Bytes { get {
      return Dafny.Sequence<byte>.FromElements((byte)(102), (byte)(101), (byte)(100), (byte)(55), (byte)(97), (byte)(100), (byte)(51), (byte)(51), (byte)(45), (byte)(48), (byte)(55), (byte)(55), (byte)(52), (byte)(45), (byte)(52), (byte)(102), (byte)(57), (byte)(55), (byte)(45), (byte)(97), (byte)(97), (byte)(53), (byte)(101), (byte)(45), (byte)(54), (byte)(99), (byte)(55), (byte)(54), (byte)(54), (byte)(102), (byte)(99), (byte)(56), (byte)(97), (byte)(102), (byte)(57), (byte)(102));
    } }
    public static Dafny.ISequence<char> keyArn { get {
      return Dafny.Sequence<char>.FromString("arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126");
    } }
    public static Dafny.ISequence<char> mkrKeyArn { get {
      return Dafny.Sequence<char>.FromString("arn:aws:kms:us-west-2:370957321024:key/mrk-63d386cb70614ea59b32ad65c9315297");
    } }
    public static Dafny.ISequence<char> keyId { get {
      return Dafny.Sequence<char>.FromString("9d989aa2-2f9c-438c-a745-cc57d3ad0126");
    } }
  }
} // end of namespace Fixtures_Compile
namespace TestAwsKmsHierarchicalKeyring_Compile {

  public partial class DummyBranchKeyIdSupplier : software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier {
    public DummyBranchKeyIdSupplier() {
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetBranchKeyId(software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out52;
      _out52 = software.amazon.cryptography.materialproviders.internaldafny.types._Companion_IBranchKeyIdSupplier.GetBranchKeyId(this, input);
      return _out52;
    }
    public void __ctor()
    {
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetBranchKeyId_k(software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdOutput.Default());
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _110_context;
      _110_context = (input).dtor_encryptionContext;
      if ((((_110_context).Keys).Contains(TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY)) && ((Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Select(_110_context,TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY)).Equals(TestAwsKmsHierarchicalKeyring_Compile.__default.CASE__A))) {
        output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdOutput.create(TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY__ID__A));
        return output;
      } else if ((((_110_context).Keys).Contains(TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY)) && ((Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Select(_110_context,TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY)).Equals(TestAwsKmsHierarchicalKeyring_Compile.__default.CASE__B))) {
        output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(software.amazon.cryptography.materialproviders.internaldafny.types.GetBranchKeyIdOutput.create(TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY__ID__B));
        return output;
      } else {
        output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetBranchKeyIdOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(software.amazon.cryptography.materialproviders.internaldafny.types.Error.create_AwsCryptographicMaterialProvidersException(Dafny.Sequence<char>.FromString("Can't determine branchKeyId from context")));
        return output;
      }
      return output;
    }
  }

  public partial class __default {
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials GetTestMaterials(software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId suiteId)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials @out = default(software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials);
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _111_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _112_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out53;
      _out53 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _112_valueOrError0 = _out53;
      if (!(!((_112_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(52,12): " + _112_valueOrError0);}
      _111_mpl = (_112_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _113_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out54;
      _out54 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _113_encryptionContext = _out54;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _114_suite;
      _114_suite = AlgorithmSuites_Compile.__default.GetSuite(suiteId);
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _115_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _116_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _116_valueOrError1 = (_111_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(suiteId, _113_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_116_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(57,30): " + _116_valueOrError1);}
      _115_encryptionMaterialsIn = (_116_valueOrError1).Extract();
      @out = _115_encryptionMaterialsIn;
      return @out;
      return @out;
    }
    public static void TestHierarchyClientESDKSuite()
    {
      Dafny.ISequence<char> _117_branchKeyId;
      _117_branchKeyId = TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY__ID;
      long _118_ttl;
      _118_ttl = ((1L) * (60000L)) * (10L);
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _119_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _120_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out55;
      _out55 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _120_valueOrError0 = _out55;
      if (!(!((_120_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(74,12): " + _120_valueOrError0);}
      _119_mpl = (_120_valueOrError0).Extract();
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _121_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _122_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out56;
      _out56 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _122_valueOrError1 = _out56;
      if (!(!((_122_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(76,18): " + _122_valueOrError1);}
      _121_kmsClient = (_122_valueOrError1).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _123_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _124_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out57;
      _out57 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _124_valueOrError2 = _out57;
      if (!(!((_124_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(77,18): " + _124_valueOrError2);}
      _123_ddbClient = (_124_valueOrError2).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _125_kmsConfig;
      _125_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(TestAwsKmsHierarchicalKeyring_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _126_keyStoreConfig;
      _126_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(TestAwsKmsHierarchicalKeyring_Compile.__default.branchKeyStoreName, _125_kmsConfig, TestAwsKmsHierarchicalKeyring_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_123_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_121_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _127_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _128_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out58;
      _out58 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_126_keyStoreConfig);
      _128_valueOrError3 = _out58;
      if (!(!((_128_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(90,17): " + _128_valueOrError3);}
      _127_keyStore = (_128_valueOrError3).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _129_hierarchyKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _130_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out59;
      _out59 = (_119_mpl).CreateAwsKmsHierarchicalKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsHierarchicalKeyringInput.create(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(_117_branchKeyId), Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier>.create_None(), _127_keyStore, _118_ttl, Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._ICacheType>.create_None()));
      _130_valueOrError4 = _out59;
      if (!(!((_130_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(92,25): " + _130_valueOrError4);}
      _129_hierarchyKeyring = (_130_valueOrError4).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _131_materials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _out60;
      _out60 = TestAwsKmsHierarchicalKeyring_Compile.__default.GetTestMaterials(TestAwsKmsHierarchicalKeyring_Compile.__default.TEST__ESDK__ALG__SUITE__ID);
      _131_materials = _out60;
      TestAwsKmsHierarchicalKeyring_Compile.__default.TestRoundtrip(_129_hierarchyKeyring, _131_materials, TestAwsKmsHierarchicalKeyring_Compile.__default.TEST__ESDK__ALG__SUITE__ID, _117_branchKeyId);
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _132_suite;
      _132_suite = AlgorithmSuites_Compile.__default.GetSuite(TestAwsKmsHierarchicalKeyring_Compile.__default.TEST__ESDK__ALG__SUITE__ID);
      Dafny.ISequence<byte> _133_zeroedKey;
      _133_zeroedKey = ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim0 = new BigInteger(AlgorithmSuites_Compile.__default.GetEncryptKeyLength(_132_suite));
        var arr0 = new byte[Dafny.Helpers.ToIntChecked(dim0, "array size exceeds memory limit")];
        for (int i0 = 0; i0 < dim0; i0++) {
          var _134___v0 = (BigInteger) i0;
          arr0[(int)(_134___v0)] = (byte)(0);
        }
        return Dafny.Sequence<byte>.FromArray(arr0);
      }))();
      var _pat_let_tv0 = _133_zeroedKey;
      _131_materials = Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_131_materials, _pat_let7_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let7_0, _135_dt__update__tmp_h0 => Dafny.Helpers.Let<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_pat_let_tv0), _pat_let8_0 => Dafny.Helpers.Let<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let8_0, _136_dt__update_hplaintextDataKey_h0 => software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials.create((_135_dt__update__tmp_h0).dtor_algorithmSuite, (_135_dt__update__tmp_h0).dtor_encryptionContext, (_135_dt__update__tmp_h0).dtor_encryptedDataKeys, (_135_dt__update__tmp_h0).dtor_requiredEncryptionContextKeys, _136_dt__update_hplaintextDataKey_h0, (_135_dt__update__tmp_h0).dtor_signingKey, (_135_dt__update__tmp_h0).dtor_symmetricSigningKeys)))));
      TestAwsKmsHierarchicalKeyring_Compile.__default.TestRoundtrip(_129_hierarchyKeyring, _131_materials, TestAwsKmsHierarchicalKeyring_Compile.__default.TEST__ESDK__ALG__SUITE__ID, _117_branchKeyId);
    }
    public static void TestHierarchyClientDBESuite()
    {
      Dafny.ISequence<char> _137_branchKeyId;
      _137_branchKeyId = TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY__ID;
      long _138_ttl;
      _138_ttl = ((1L) * (60000L)) * (10L);
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _139_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _140_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out61;
      _out61 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _140_valueOrError0 = _out61;
      if (!(!((_140_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(115,12): " + _140_valueOrError0);}
      _139_mpl = (_140_valueOrError0).Extract();
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _141_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _142_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out62;
      _out62 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _142_valueOrError1 = _out62;
      if (!(!((_142_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(117,18): " + _142_valueOrError1);}
      _141_kmsClient = (_142_valueOrError1).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _143_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _144_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out63;
      _out63 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _144_valueOrError2 = _out63;
      if (!(!((_144_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(118,18): " + _144_valueOrError2);}
      _143_ddbClient = (_144_valueOrError2).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _145_kmsConfig;
      _145_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(TestAwsKmsHierarchicalKeyring_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _146_keyStoreConfig;
      _146_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(TestAwsKmsHierarchicalKeyring_Compile.__default.branchKeyStoreName, _145_kmsConfig, TestAwsKmsHierarchicalKeyring_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_143_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_141_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _147_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _148_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out64;
      _out64 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_146_keyStoreConfig);
      _148_valueOrError3 = _out64;
      if (!(!((_148_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(131,17): " + _148_valueOrError3);}
      _147_keyStore = (_148_valueOrError3).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _149_hierarchyKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _150_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out65;
      _out65 = (_139_mpl).CreateAwsKmsHierarchicalKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsHierarchicalKeyringInput.create(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(_137_branchKeyId), Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier>.create_None(), _147_keyStore, _138_ttl, Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._ICacheType>.create_None()));
      _150_valueOrError4 = _out65;
      if (!(!((_150_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(133,25): " + _150_valueOrError4);}
      _149_hierarchyKeyring = (_150_valueOrError4).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _151_materials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _out66;
      _out66 = TestAwsKmsHierarchicalKeyring_Compile.__default.GetTestMaterials(TestAwsKmsHierarchicalKeyring_Compile.__default.TEST__DBE__ALG__SUITE__ID);
      _151_materials = _out66;
      TestAwsKmsHierarchicalKeyring_Compile.__default.TestRoundtrip(_149_hierarchyKeyring, _151_materials, TestAwsKmsHierarchicalKeyring_Compile.__default.TEST__DBE__ALG__SUITE__ID, _137_branchKeyId);
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _152_suite;
      _152_suite = AlgorithmSuites_Compile.__default.GetSuite(TestAwsKmsHierarchicalKeyring_Compile.__default.TEST__DBE__ALG__SUITE__ID);
      Dafny.ISequence<byte> _153_zeroedKey;
      _153_zeroedKey = ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim1 = new BigInteger(AlgorithmSuites_Compile.__default.GetEncryptKeyLength(_152_suite));
        var arr1 = new byte[Dafny.Helpers.ToIntChecked(dim1, "array size exceeds memory limit")];
        for (int i1 = 0; i1 < dim1; i1++) {
          var _154___v1 = (BigInteger) i1;
          arr1[(int)(_154___v1)] = (byte)(0);
        }
        return Dafny.Sequence<byte>.FromArray(arr1);
      }))();
      var _pat_let_tv1 = _153_zeroedKey;
      _151_materials = Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_151_materials, _pat_let9_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let9_0, _155_dt__update__tmp_h0 => Dafny.Helpers.Let<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_pat_let_tv1), _pat_let10_0 => Dafny.Helpers.Let<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let10_0, _156_dt__update_hplaintextDataKey_h0 => software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials.create((_155_dt__update__tmp_h0).dtor_algorithmSuite, (_155_dt__update__tmp_h0).dtor_encryptionContext, (_155_dt__update__tmp_h0).dtor_encryptedDataKeys, (_155_dt__update__tmp_h0).dtor_requiredEncryptionContextKeys, _156_dt__update_hplaintextDataKey_h0, (_155_dt__update__tmp_h0).dtor_signingKey, (_155_dt__update__tmp_h0).dtor_symmetricSigningKeys)))));
      TestAwsKmsHierarchicalKeyring_Compile.__default.TestRoundtrip(_149_hierarchyKeyring, _151_materials, TestAwsKmsHierarchicalKeyring_Compile.__default.TEST__DBE__ALG__SUITE__ID, _137_branchKeyId);
    }
    public static void TestBranchKeyIdSupplier()
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier _157_branchKeyIdSupplier;
      TestAwsKmsHierarchicalKeyring_Compile.DummyBranchKeyIdSupplier _nw8 = new TestAwsKmsHierarchicalKeyring_Compile.DummyBranchKeyIdSupplier();
      _nw8.__ctor();
      _157_branchKeyIdSupplier = _nw8;
      long _158_ttl;
      _158_ttl = ((1L) * (60000L)) * (10L);
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _159_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _160_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out67;
      _out67 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _160_valueOrError0 = _out67;
      if (!(!((_160_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(157,12): " + _160_valueOrError0);}
      _159_mpl = (_160_valueOrError0).Extract();
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _161_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _162_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out68;
      _out68 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _162_valueOrError1 = _out68;
      if (!(!((_162_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(159,18): " + _162_valueOrError1);}
      _161_kmsClient = (_162_valueOrError1).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _163_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _164_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out69;
      _out69 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _164_valueOrError2 = _out69;
      if (!(!((_164_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(160,18): " + _164_valueOrError2);}
      _163_ddbClient = (_164_valueOrError2).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _165_kmsConfig;
      _165_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(TestAwsKmsHierarchicalKeyring_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _166_keyStoreConfig;
      _166_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(TestAwsKmsHierarchicalKeyring_Compile.__default.branchKeyStoreName, _165_kmsConfig, TestAwsKmsHierarchicalKeyring_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_163_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_161_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _167_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _168_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out70;
      _out70 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_166_keyStoreConfig);
      _168_valueOrError3 = _out70;
      if (!(!((_168_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(173,17): " + _168_valueOrError3);}
      _167_keyStore = (_168_valueOrError3).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _169_hierarchyKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _170_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out71;
      _out71 = (_159_mpl).CreateAwsKmsHierarchicalKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsHierarchicalKeyringInput.create(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier>.create_Some(_157_branchKeyIdSupplier), _167_keyStore, _158_ttl, Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._ICacheType>.create_None()));
      _170_valueOrError4 = _out71;
      if (!(!((_170_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(175,25): " + _170_valueOrError4);}
      _169_hierarchyKeyring = (_170_valueOrError4).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _171_materials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _out72;
      _out72 = TestAwsKmsHierarchicalKeyring_Compile.__default.GetTestMaterials(TestAwsKmsHierarchicalKeyring_Compile.__default.TEST__DBE__ALG__SUITE__ID);
      _171_materials = _out72;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _172_contextCaseA;
      _172_contextCaseA = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Update((_171_materials).dtor_encryptionContext, TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY, TestAwsKmsHierarchicalKeyring_Compile.__default.CASE__A);
      var _pat_let_tv2 = _172_contextCaseA;
      _171_materials = Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_171_materials, _pat_let11_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let11_0, _173_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let_tv2, _pat_let12_0 => Dafny.Helpers.Let<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let12_0, _174_dt__update_hencryptionContext_h0 => software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials.create((_173_dt__update__tmp_h0).dtor_algorithmSuite, _174_dt__update_hencryptionContext_h0, (_173_dt__update__tmp_h0).dtor_encryptedDataKeys, (_173_dt__update__tmp_h0).dtor_requiredEncryptionContextKeys, (_173_dt__update__tmp_h0).dtor_plaintextDataKey, (_173_dt__update__tmp_h0).dtor_signingKey, (_173_dt__update__tmp_h0).dtor_symmetricSigningKeys)))));
      TestAwsKmsHierarchicalKeyring_Compile.__default.TestRoundtrip(_169_hierarchyKeyring, _171_materials, TestAwsKmsHierarchicalKeyring_Compile.__default.TEST__DBE__ALG__SUITE__ID, TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY__ID__A);
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _175_contextCaseB;
      _175_contextCaseB = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Update((_171_materials).dtor_encryptionContext, TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY, TestAwsKmsHierarchicalKeyring_Compile.__default.CASE__B);
      var _pat_let_tv3 = _175_contextCaseB;
      _171_materials = Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_171_materials, _pat_let13_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let13_0, _176_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let_tv3, _pat_let14_0 => Dafny.Helpers.Let<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let14_0, _177_dt__update_hencryptionContext_h1 => software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials.create((_176_dt__update__tmp_h1).dtor_algorithmSuite, _177_dt__update_hencryptionContext_h1, (_176_dt__update__tmp_h1).dtor_encryptedDataKeys, (_176_dt__update__tmp_h1).dtor_requiredEncryptionContextKeys, (_176_dt__update__tmp_h1).dtor_plaintextDataKey, (_176_dt__update__tmp_h1).dtor_signingKey, (_176_dt__update__tmp_h1).dtor_symmetricSigningKeys)))));
      TestAwsKmsHierarchicalKeyring_Compile.__default.TestRoundtrip(_169_hierarchyKeyring, _171_materials, TestAwsKmsHierarchicalKeyring_Compile.__default.TEST__DBE__ALG__SUITE__ID, TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY__ID__B);
    }
    public static void TestRoundtrip(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring hierarchyKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials encryptionMaterialsIn, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId algorithmSuiteId, Dafny.ISequence<char> expectedBranchKeyId)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _178_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _179_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out73;
      _out73 = (hierarchyKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(encryptionMaterialsIn));
      _179_valueOrError0 = _out73;
      if (!(!((_179_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(207,31): " + _179_valueOrError0);}
      _178_encryptionMaterialsOut = (_179_valueOrError0).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _180_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _181_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out74;
      _out74 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _181_valueOrError1 = _out74;
      if (!(!((_181_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(211,12): " + _181_valueOrError1);}
      _180_mpl = (_181_valueOrError1).Extract();
      _System._ITuple0 _182___v2;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _183_valueOrError2 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _183_valueOrError2 = (_180_mpl).EncryptionMaterialsHasPlaintextDataKey((_178_encryptionMaterialsOut).dtor_materials);
      if (!(!((_183_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(212,10): " + _183_valueOrError2);}
      _182___v2 = (_183_valueOrError2).Extract();
      if (!((new BigInteger((((_178_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(214,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _184_edk;
      _184_edk = (((_178_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Select(BigInteger.Zero);
      Dafny.ISequence<byte> _185_expectedBranchKeyIdUTF8;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _186_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _186_valueOrError3 = UTF8.__default.Encode(expectedBranchKeyId);
      if (!(!((_186_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(219,32): " + _186_valueOrError3);}
      _185_expectedBranchKeyIdUTF8 = (_186_valueOrError3).Extract();
      if (!(((_184_edk).dtor_keyProviderInfo).Equals(_185_expectedBranchKeyIdUTF8))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(220,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _187_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _188_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _188_valueOrError4 = (_180_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(algorithmSuiteId, (encryptionMaterialsIn).dtor_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_188_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(222,30): " + _188_valueOrError4);}
      _187_decryptionMaterialsIn = (_188_valueOrError4).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput _189_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _190_valueOrError5 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out75;
      _out75 = (hierarchyKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_187_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_184_edk)));
      _190_valueOrError5 = _out75;
      if (!(!((_190_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(229,31): " + _190_valueOrError5);}
      _189_decryptionMaterialsOut = (_190_valueOrError5).Extract();
      if (!(object.Equals(((_178_encryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey, ((_189_decryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/AwsKmsHierarchicalKeyring/TestAwsKmsHierarchicalKeyring.dfy(241,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static Dafny.ISequence<byte> BRANCH__KEY { get {
      return UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("branchKey"));
    } }
    public static Dafny.ISequence<byte> CASE__A { get {
      return UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("caseA"));
    } }
    public static Dafny.ISequence<char> BRANCH__KEY__ID { get {
      return Fixtures_Compile.__default.branchKeyId;
    } }
    public static Dafny.ISequence<char> BRANCH__KEY__ID__A { get {
      return TestAwsKmsHierarchicalKeyring_Compile.__default.BRANCH__KEY__ID;
    } }
    public static Dafny.ISequence<byte> CASE__B { get {
      return UTF8.__default.EncodeAscii(Dafny.Sequence<char>.FromString("caseB"));
    } }
    public static Dafny.ISequence<char> BRANCH__KEY__ID__B { get {
      return Fixtures_Compile.__default.branchKeyIdWithEC;
    } }
    public static Dafny.ISequence<char> branchKeyStoreName { get {
      return Fixtures_Compile.__default.branchKeyStoreName;
    } }
    public static Dafny.ISequence<char> logicalKeyStoreName { get {
      return TestAwsKmsHierarchicalKeyring_Compile.__default.branchKeyStoreName;
    } }
    public static Dafny.ISequence<char> keyArn { get {
      return Fixtures_Compile.__default.keyArn;
    } }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId TEST__ESDK__ALG__SUITE__ID { get {
      return software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
    } }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId TEST__DBE__ALG__SUITE__ID { get {
      return software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_DBE(software.amazon.cryptography.materialproviders.internaldafny.types.DBEAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__SYMSIG__HMAC__SHA384());
    } }
  }
} // end of namespace TestAwsKmsHierarchicalKeyring_Compile
namespace TestAwsKmsRsaKeyring_Compile {

  public partial class __default {
    public static void TestKmsRsaRoundtrip()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _191_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _192_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out76;
      _out76 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _192_valueOrError0 = _out76;
      if (!(!((_192_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(21,12): " + _192_valueOrError0);}
      _191_mpl = (_192_valueOrError0).Extract();
      Dafny.ISequence<byte> _193_publicKey;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _194_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _194_valueOrError1 = UTF8.__default.Encode(TestUtils_Compile.__default.KMS__RSA__PUBLIC__KEY);
      if (!(!((_194_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(23,18): " + _194_valueOrError1);}
      _193_publicKey = (_194_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier _195_clientSupplier;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _196_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out77;
      _out77 = (_191_mpl).CreateDefaultClientSupplier(software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultClientSupplierInput.create());
      _196_valueOrError2 = _out77;
      if (!(!((_196_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(25,23): " + _196_valueOrError2);}
      _195_clientSupplier = (_196_valueOrError2).Extract();
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _197_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _198_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out78;
      _out78 = (_195_clientSupplier).GetClient(software.amazon.cryptography.materialproviders.internaldafny.types.GetClientInput.create(Dafny.Sequence<char>.FromString("us-west-2")));
      _198_valueOrError3 = _out78;
      if (!(!((_198_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(26,18): " + _198_valueOrError3);}
      _197_kmsClient = (_198_valueOrError3).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _199_kmsRsaKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _200_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out79;
      _out79 = (_191_mpl).CreateAwsKmsRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsRsaKeyringInput.create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_193_publicKey), TestUtils_Compile.__default.KMS__RSA__PRIVATE__KEY__ARN, software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__1(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_197_kmsClient), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()));
      _200_valueOrError4 = _out79;
      if (!(!((_200_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(28,22): " + _200_valueOrError4);}
      _199_kmsRsaKeyring = (_200_valueOrError4).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _201_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out80;
      _out80 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _201_encryptionContext = _out80;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _202_algorithmSuiteId;
      _202_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _203_suite;
      _203_suite = AlgorithmSuites_Compile.__default.GetSuite(_202_algorithmSuiteId);
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _204_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _205_valueOrError5 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _205_valueOrError5 = (_191_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_202_algorithmSuiteId, _201_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_205_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(40,30): " + _205_valueOrError5);}
      _204_encryptionMaterialsIn = (_205_valueOrError5).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _206_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _207_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out81;
      _out81 = (_199_kmsRsaKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_204_encryptionMaterialsIn));
      _207_valueOrError6 = _out81;
      if (!(!((_207_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(50,31): " + _207_valueOrError6);}
      _206_encryptionMaterialsOut = (_207_valueOrError6).Extract();
      _System._ITuple0 _208___v0;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _209_valueOrError7 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _209_valueOrError7 = (_191_mpl).EncryptionMaterialsHasPlaintextDataKey((_206_encryptionMaterialsOut).dtor_materials);
      if (!(!((_209_valueOrError7).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(54,10): " + _209_valueOrError7);}
      _208___v0 = (_209_valueOrError7).Extract();
      if (!((new BigInteger((((_206_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(56,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _210_edk;
      _210_edk = (((_206_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Select(BigInteger.Zero);
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _211_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _212_valueOrError8 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _212_valueOrError8 = (_191_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_202_algorithmSuiteId, _201_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_212_valueOrError8).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(60,30): " + _212_valueOrError8);}
      _211_decryptionMaterialsIn = (_212_valueOrError8).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput _213_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _214_valueOrError9 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out82;
      _out82 = (_199_kmsRsaKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_211_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_210_edk)));
      _214_valueOrError9 = _out82;
      if (!(!((_214_valueOrError9).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(67,31): " + _214_valueOrError9);}
      _213_decryptionMaterialsOut = (_214_valueOrError9).Extract();
      if (!(object.Equals(((_206_encryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey, ((_213_decryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(74,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestKmsRsaWithAsymmetricSignatureFails()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _215_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _216_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out83;
      _out83 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _216_valueOrError0 = _out83;
      if (!(!((_216_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(79,12): " + _216_valueOrError0);}
      _215_mpl = (_216_valueOrError0).Extract();
      Dafny.ISequence<byte> _217_publicKey;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _218_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _218_valueOrError1 = UTF8.__default.Encode(TestUtils_Compile.__default.KMS__RSA__PUBLIC__KEY);
      if (!(!((_218_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(81,18): " + _218_valueOrError1);}
      _217_publicKey = (_218_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier _219_clientSupplier;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _220_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out84;
      _out84 = (_215_mpl).CreateDefaultClientSupplier(software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultClientSupplierInput.create());
      _220_valueOrError2 = _out84;
      if (!(!((_220_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(83,23): " + _220_valueOrError2);}
      _219_clientSupplier = (_220_valueOrError2).Extract();
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _221_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _222_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out85;
      _out85 = (_219_clientSupplier).GetClient(software.amazon.cryptography.materialproviders.internaldafny.types.GetClientInput.create(Dafny.Sequence<char>.FromString("us-west-2")));
      _222_valueOrError3 = _out85;
      if (!(!((_222_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(84,18): " + _222_valueOrError3);}
      _221_kmsClient = (_222_valueOrError3).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _223_kmsRsaKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _224_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out86;
      _out86 = (_215_mpl).CreateAwsKmsRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsRsaKeyringInput.create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_217_publicKey), TestUtils_Compile.__default.KMS__RSA__PRIVATE__KEY__ARN, software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__1(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_221_kmsClient), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()));
      _224_valueOrError4 = _out86;
      if (!(!((_224_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(86,22): " + _224_valueOrError4);}
      _223_kmsRsaKeyring = (_224_valueOrError4).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _225_algorithmSuiteId;
      _225_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_DBE(software.amazon.cryptography.materialproviders.internaldafny.types.DBEAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384__SYMSIG__HMAC__SHA384());
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _226_suite;
      _226_suite = AlgorithmSuites_Compile.__default.GetSuite(_225_algorithmSuiteId);
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _227_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _228_valueOrError5 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _228_valueOrError5 = (_215_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_225_algorithmSuiteId, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(), Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(0), (byte)(0), (byte)(0), (byte)(0))), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(0), (byte)(0), (byte)(0), (byte)(0)))));
      if (!(!((_228_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(96,30): " + _228_valueOrError5);}
      _227_encryptionMaterialsIn = (_228_valueOrError5).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _229_encryptionMaterialsOutRes;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out87;
      _out87 = (_223_kmsRsaKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_227_encryptionMaterialsIn));
      _229_encryptionMaterialsOutRes = _out87;
      if (!((_229_encryptionMaterialsOutRes).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(110,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((_229_encryptionMaterialsOutRes).dtor_error).is_AwsCryptographicMaterialProvidersException)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(111,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_229_encryptionMaterialsOutRes).dtor_error).dtor_message).Equals(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("AwsKmsRsaKeyring cannot be used with"), Dafny.Sequence<char>.FromString(" an Algorithm Suite with asymmetric signing. Please specify an algorithm suite without asymmetric signing."))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(112,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _230_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _231_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _231_valueOrError6 = (_215_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_225_algorithmSuiteId, (_227_encryptionMaterialsIn).dtor_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_231_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(115,30): " + _231_valueOrError6);}
      _230_decryptionMaterialsIn = (_231_valueOrError6).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _232_decryptionMaterialsOutRes;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out88;
      _out88 = (_223_kmsRsaKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_230_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements()));
      _232_decryptionMaterialsOutRes = _out88;
      if (!((_232_decryptionMaterialsOutRes).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(129,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((_232_decryptionMaterialsOutRes).dtor_error).is_AwsCryptographicMaterialProvidersException)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(130,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_232_decryptionMaterialsOutRes).dtor_error).dtor_message).Equals(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("AwsKmsRsaKeyring cannot be used with"), Dafny.Sequence<char>.FromString(" an Algorithm Suite with asymmetric signing. Please specify an algorithm suite without asymmetric signing."))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/AwsKms/TestAwsKmsRsaKeyring.dfy(131,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestAwsKmsRsaKeyring_Compile
namespace TestRawRSAKeying_Compile {

  public partial class __default {
    public static void TestOnEncryptOnDecryptSuppliedDataKey()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _233_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _234_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out89;
      _out89 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _234_valueOrError0 = _out89;
      if (!(!((_234_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(18,12): " + _234_valueOrError0);}
      _233_mpl = (_234_valueOrError0).Extract();
      Dafny.ISequence<char> _235_namespace;
      Dafny.ISequence<char> _236_name;
      Dafny.ISequence<char> _out90;
      Dafny.ISequence<char> _out91;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out90, out _out91);
      _235_namespace = _out90;
      _236_name = _out91;
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _237_keys;
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _out92;
      _out92 = TestRawRSAKeying_Compile.__default.GenerateKeyPair((int)(2048));
      _237_keys = _out92;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _238_rawRSAKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _239_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out93;
      _out93 = (_233_mpl).CreateRawRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput.create(_235_namespace, _236_name, software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.create_OAEP__SHA1__MGF1(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_237_keys).dtor_publicKey).dtor_pem), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_237_keys).dtor_privateKey).dtor_pem)));
      _239_valueOrError1 = _out93;
      if (!(!((_239_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(22,22): " + _239_valueOrError1);}
      _238_rawRSAKeyring = (_239_valueOrError1).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _240_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out94;
      _out94 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _240_encryptionContext = _out94;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _241_algorithmSuiteId;
      _241_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _242_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _243_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _243_valueOrError2 = (_233_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_241_algorithmSuiteId, _240_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_243_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(35,30): " + _243_valueOrError2);}
      _242_encryptionMaterialsIn = (_243_valueOrError2).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _244_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _245_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out95;
      _out95 = (_238_rawRSAKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_242_encryptionMaterialsIn));
      _245_valueOrError3 = _out95;
      if (!(!((_245_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(45,31): " + _245_valueOrError3);}
      _244_encryptionMaterialsOut = (_245_valueOrError3).Extract();
      _System._ITuple0 _246___v0;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _247_valueOrError4 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _247_valueOrError4 = (_233_mpl).EncryptionMaterialsHasPlaintextDataKey((_244_encryptionMaterialsOut).dtor_materials);
      if (!(!((_247_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(48,10): " + _247_valueOrError4);}
      _246___v0 = (_247_valueOrError4).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _248_edk;
      _248_edk = (((_244_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Select(BigInteger.Zero);
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _249_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _250_valueOrError5 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _250_valueOrError5 = (_233_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_241_algorithmSuiteId, _240_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_250_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(52,30): " + _250_valueOrError5);}
      _249_decryptionMaterialsIn = (_250_valueOrError5).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput _251_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _252_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out96;
      _out96 = (_238_rawRSAKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_249_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_248_edk)));
      _252_valueOrError6 = _out96;
      if (!(!((_252_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(60,31): " + _252_valueOrError6);}
      _251_decryptionMaterialsOut = (_252_valueOrError6).Extract();
      if (!(object.Equals(((_251_decryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey, ((_244_encryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(72,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestOnDecryptKeyNameMismatch()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _253_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _254_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out97;
      _out97 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _254_valueOrError0 = _out97;
      if (!(!((_254_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(78,12): " + _254_valueOrError0);}
      _253_mpl = (_254_valueOrError0).Extract();
      Dafny.ISequence<char> _255_namespace;
      Dafny.ISequence<char> _256_name;
      Dafny.ISequence<char> _out98;
      Dafny.ISequence<char> _out99;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out98, out _out99);
      _255_namespace = _out98;
      _256_name = _out99;
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _257_keys;
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _out100;
      _out100 = TestRawRSAKeying_Compile.__default.GenerateKeyPair((int)(2048));
      _257_keys = _out100;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _258_rawRSAKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _259_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out101;
      _out101 = (_253_mpl).CreateRawRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput.create(_255_namespace, _256_name, software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.create_OAEP__SHA1__MGF1(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_257_keys).dtor_publicKey).dtor_pem), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_257_keys).dtor_privateKey).dtor_pem)));
      _259_valueOrError1 = _out101;
      if (!(!((_259_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(82,22): " + _259_valueOrError1);}
      _258_rawRSAKeyring = (_259_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _260_mismatchedRSAKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _261_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out102;
      _out102 = (_253_mpl).CreateRawRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput.create(_255_namespace, Dafny.Sequence<char>.FromString("mismatched"), software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.create_OAEP__SHA1__MGF1(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_257_keys).dtor_publicKey).dtor_pem), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_257_keys).dtor_privateKey).dtor_pem)));
      _261_valueOrError2 = _out102;
      if (!(!((_261_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(90,29): " + _261_valueOrError2);}
      _260_mismatchedRSAKeyring = (_261_valueOrError2).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _262_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out103;
      _out103 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _262_encryptionContext = _out103;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _263_algorithmSuiteId;
      _263_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _264_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _265_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _265_valueOrError3 = (_253_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_263_algorithmSuiteId, _262_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_265_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(103,30): " + _265_valueOrError3);}
      _264_encryptionMaterialsIn = (_265_valueOrError3).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _266_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _267_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out104;
      _out104 = (_258_rawRSAKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_264_encryptionMaterialsIn));
      _267_valueOrError4 = _out104;
      if (!(!((_267_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(112,31): " + _267_valueOrError4);}
      _266_encryptionMaterialsOut = (_267_valueOrError4).Extract();
      _System._ITuple0 _268___v1;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _269_valueOrError5 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _269_valueOrError5 = (_253_mpl).EncryptionMaterialsHasPlaintextDataKey((_266_encryptionMaterialsOut).dtor_materials);
      if (!(!((_269_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(115,10): " + _269_valueOrError5);}
      _268___v1 = (_269_valueOrError5).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _270_edk;
      _270_edk = (((_266_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Select(BigInteger.Zero);
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _271_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _272_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _272_valueOrError6 = (_253_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_263_algorithmSuiteId, _262_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_272_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(119,30): " + _272_valueOrError6);}
      _271_decryptionMaterialsIn = (_272_valueOrError6).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _273_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out105;
      _out105 = (_260_mismatchedRSAKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_271_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_270_edk)));
      _273_decryptionMaterialsOut = _out105;
      if (!((_273_decryptionMaterialsOut).IsFailure())) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(133,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestOnDecryptFailure()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _274_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _275_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out106;
      _out106 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _275_valueOrError0 = _out106;
      if (!(!((_275_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(139,12): " + _275_valueOrError0);}
      _274_mpl = (_275_valueOrError0).Extract();
      Dafny.ISequence<char> _276_namespace;
      Dafny.ISequence<char> _277_name;
      Dafny.ISequence<char> _out107;
      Dafny.ISequence<char> _out108;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out107, out _out108);
      _276_namespace = _out107;
      _277_name = _out108;
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _278_encryptKeys;
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _out109;
      _out109 = TestRawRSAKeying_Compile.__default.GenerateKeyPair((int)(2048));
      _278_encryptKeys = _out109;
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _279_decryptKeys;
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _out110;
      _out110 = TestRawRSAKeying_Compile.__default.GenerateKeyPair((int)(2048));
      _279_decryptKeys = _out110;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _280_encryptKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _281_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out111;
      _out111 = (_274_mpl).CreateRawRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput.create(_276_namespace, _277_name, software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.create_OAEP__SHA1__MGF1(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_278_encryptKeys).dtor_publicKey).dtor_pem), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_278_encryptKeys).dtor_privateKey).dtor_pem)));
      _281_valueOrError1 = _out111;
      if (!(!((_281_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(147,23): " + _281_valueOrError1);}
      _280_encryptKeyring = (_281_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _282_decryptKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _283_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out112;
      _out112 = (_274_mpl).CreateRawRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput.create(_276_namespace, _277_name, software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.create_OAEP__SHA1__MGF1(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_279_decryptKeys).dtor_publicKey).dtor_pem), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_279_decryptKeys).dtor_privateKey).dtor_pem)));
      _283_valueOrError2 = _out112;
      if (!(!((_283_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(155,23): " + _283_valueOrError2);}
      _282_decryptKeyring = (_283_valueOrError2).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _284_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out113;
      _out113 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _284_encryptionContext = _out113;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _285_algorithmSuiteId;
      _285_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _286_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _287_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _287_valueOrError3 = (_274_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_285_algorithmSuiteId, _284_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_287_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(166,30): " + _287_valueOrError3);}
      _286_encryptionMaterialsIn = (_287_valueOrError3).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _288_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _289_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out114;
      _out114 = (_280_encryptKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_286_encryptionMaterialsIn));
      _289_valueOrError4 = _out114;
      if (!(!((_289_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(175,31): " + _289_valueOrError4);}
      _288_encryptionMaterialsOut = (_289_valueOrError4).Extract();
      _System._ITuple0 _290___v2;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _291_valueOrError5 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _291_valueOrError5 = (_274_mpl).EncryptionMaterialsHasPlaintextDataKey((_288_encryptionMaterialsOut).dtor_materials);
      if (!(!((_291_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(178,10): " + _291_valueOrError5);}
      _290___v2 = (_291_valueOrError5).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _292_edk;
      _292_edk = (((_288_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Select(BigInteger.Zero);
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _293_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _294_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _294_valueOrError6 = (_274_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_285_algorithmSuiteId, _284_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_294_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(182,30): " + _294_valueOrError6);}
      _293_decryptionMaterialsIn = (_294_valueOrError6).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _295_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out115;
      _out115 = (_282_decryptKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_293_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_292_edk)));
      _295_decryptionMaterialsOut = _out115;
      if (!((_295_decryptionMaterialsOut).IsFailure())) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(200,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestOnDecryptBadAndGoodEdkSucceeds()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _296_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _297_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out116;
      _out116 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _297_valueOrError0 = _out116;
      if (!(!((_297_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(212,12): " + _297_valueOrError0);}
      _296_mpl = (_297_valueOrError0).Extract();
      Dafny.ISequence<char> _298_namespace;
      Dafny.ISequence<char> _299_name;
      Dafny.ISequence<char> _out117;
      Dafny.ISequence<char> _out118;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out117, out _out118);
      _298_namespace = _out117;
      _299_name = _out118;
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _300_keys;
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _out119;
      _out119 = TestRawRSAKeying_Compile.__default.GenerateKeyPair((int)(2048));
      _300_keys = _out119;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _301_rawRSAKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _302_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out120;
      _out120 = (_296_mpl).CreateRawRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput.create(_298_namespace, _299_name, software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.create_OAEP__SHA1__MGF1(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_300_keys).dtor_publicKey).dtor_pem), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_300_keys).dtor_privateKey).dtor_pem)));
      _302_valueOrError1 = _out120;
      if (!(!((_302_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(216,22): " + _302_valueOrError1);}
      _301_rawRSAKeyring = (_302_valueOrError1).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _303_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out121;
      _out121 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _303_encryptionContext = _out121;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _304_algorithmSuiteId;
      _304_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _305_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _306_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _306_valueOrError2 = (_296_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_304_algorithmSuiteId, _303_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_306_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(229,30): " + _306_valueOrError2);}
      _305_encryptionMaterialsIn = (_306_valueOrError2).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _307_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _308_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out122;
      _out122 = (_301_rawRSAKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_305_encryptionMaterialsIn));
      _308_valueOrError3 = _out122;
      if (!(!((_308_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(238,31): " + _308_valueOrError3);}
      _307_encryptionMaterialsOut = (_308_valueOrError3).Extract();
      _System._ITuple0 _309___v3;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _310_valueOrError4 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _310_valueOrError4 = (_296_mpl).EncryptionMaterialsHasPlaintextDataKey((_307_encryptionMaterialsOut).dtor_materials);
      if (!(!((_310_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(241,10): " + _310_valueOrError4);}
      _309___v3 = (_310_valueOrError4).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _311_edk;
      _311_edk = (((_307_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Select(BigInteger.Zero);
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _312_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _313_valueOrError5 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _313_valueOrError5 = (_296_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_304_algorithmSuiteId, _303_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_313_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(245,30): " + _313_valueOrError5);}
      _312_decryptionMaterialsIn = (_313_valueOrError5).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _314_fakeEdk;
      _314_fakeEdk = software.amazon.cryptography.materialproviders.internaldafny.types.EncryptedDataKey.create((_311_edk).dtor_keyProviderId, (_311_edk).dtor_keyProviderInfo, ((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim2 = new BigInteger(((_311_edk).dtor_ciphertext).Count);
  var arr2 = new byte[Dafny.Helpers.ToIntChecked(dim2, "array size exceeds memory limit")];
  for (int i2 = 0; i2 < dim2; i2++) {
    var _315_i = (BigInteger) i2;
    arr2[(int)(_315_i)] = (byte)(0);
  }
  return Dafny.Sequence<byte>.FromArray(arr2);
}))());
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput _316_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _317_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out123;
      _out123 = (_301_rawRSAKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_312_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_314_fakeEdk, _311_edk)));
      _317_valueOrError6 = _out123;
      if (!(!((_317_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(262,31): " + _317_valueOrError6);}
      _316_decryptionMaterialsOut = (_317_valueOrError6).Extract();
      if (!(object.Equals(((_316_decryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey, ((_307_encryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(273,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput GenerateKeyPair(int keyModulusLength)
    {
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput keys = default(software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput);
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _318_crypto;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _319_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out124;
      _out124 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _319_valueOrError0 = _out124;
      if (!(!((_319_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(280,15): " + _319_valueOrError0);}
      _318_crypto = (_319_valueOrError0).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _320_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _out125;
      _out125 = (_318_crypto).GenerateRSAKeyPair(software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairInput.create(keyModulusLength));
      _320_valueOrError1 = _out125;
      if (!(!((_320_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawRSAKeyring.dfy(282,9): " + _320_valueOrError1);}
      keys = (_320_valueOrError1).Extract();
      return keys;
    }
  }
} // end of namespace TestRawRSAKeying_Compile
namespace TestMultiKeyring_Compile {

  public partial class StaticKeyring : software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring {
    public StaticKeyring() {
      this._encryptionMaterials = Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>.Default();
      this._decryptionMaterials = Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials>.Default();
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out126;
      _out126 = software.amazon.cryptography.materialproviders.internaldafny.types._Companion_IKeyring.OnEncrypt(this, input);
      return _out126;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out127;
      _out127 = software.amazon.cryptography.materialproviders.internaldafny.types._Companion_IKeyring.OnDecrypt(this, input);
      return _out127;
    }
    public void __ctor(Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials> encryptionMaterials, Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials> decryptionMaterials)
    {
      (this)._encryptionMaterials = encryptionMaterials;
      (this)._decryptionMaterials = decryptionMaterials;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnEncrypt_k(software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> res = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      if (((this).encryptionMaterials).is_Some) {
        res = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptOutput.create(((this).encryptionMaterials).dtor_value));
        return res;
      } else {
        software.amazon.cryptography.materialproviders.internaldafny.types._IError _321_exception;
        _321_exception = software.amazon.cryptography.materialproviders.internaldafny.types.Error.create_AwsCryptographicMaterialProvidersException(Dafny.Sequence<char>.FromString("Failure"));
        res = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(_321_exception);
        return res;
      }
      return res;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnDecrypt_k(software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> res = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      if (((this).decryptionMaterials).is_Some) {
        res = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptOutput.create(((this).decryptionMaterials).dtor_value));
        return res;
      } else {
        software.amazon.cryptography.materialproviders.internaldafny.types._IError _322_exception;
        _322_exception = software.amazon.cryptography.materialproviders.internaldafny.types.Error.create_AwsCryptographicMaterialProvidersException(Dafny.Sequence<char>.FromString("Failure"));
        res = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(_322_exception);
        return res;
      }
      return res;
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials> _encryptionMaterials {get; set;}
    public Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials> encryptionMaterials { get {
      return this._encryptionMaterials;
    } }
    public Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials> _decryptionMaterials {get; set;}
    public Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials> decryptionMaterials { get {
      return this._decryptionMaterials;
    } }
  }

  public partial class FailingKeyring : software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring {
    public FailingKeyring() {
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out128;
      _out128 = software.amazon.cryptography.materialproviders.internaldafny.types._Companion_IKeyring.OnEncrypt(this, input);
      return _out128;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out129;
      _out129 = software.amazon.cryptography.materialproviders.internaldafny.types._Companion_IKeyring.OnDecrypt(this, input);
      return _out129;
    }
    public void __ctor()
    {
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnEncrypt_k(software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> res = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      software.amazon.cryptography.materialproviders.internaldafny.types._IError _323_exception;
      _323_exception = software.amazon.cryptography.materialproviders.internaldafny.types.Error.create_AwsCryptographicMaterialProvidersException(Dafny.Sequence<char>.FromString("Failure"));
      res = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(_323_exception);
      return res;
      return res;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnDecrypt_k(software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> res = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      software.amazon.cryptography.materialproviders.internaldafny.types._IError _324_exception;
      _324_exception = software.amazon.cryptography.materialproviders.internaldafny.types.Error.create_AwsCryptographicMaterialProvidersException(Dafny.Sequence<char>.FromString("Failure"));
      res = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Failure(_324_exception);
      return res;
      return res;
    }
  }

  public partial class __default {
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials getInputEncryptionMaterials(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials res = default(software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials);
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _325_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _326_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out130;
      _out130 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _326_valueOrError0 = _out130;
      if (!(!((_326_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(18,12): " + _326_valueOrError0);}
      _325_mpl = (_326_valueOrError0).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _327_algorithmSuiteId;
      _327_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _328_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _329_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _329_valueOrError1 = (_325_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_327_algorithmSuiteId, encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_329_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(21,30): " + _329_valueOrError1);}
      _328_encryptionMaterialsIn = (_329_valueOrError1).Extract();
      res = _328_encryptionMaterialsIn;
      return res;
      return res;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials getInputDecryptionMaterials(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials res = default(software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials);
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _330_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _331_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out131;
      _out131 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _331_valueOrError0 = _out131;
      if (!(!((_331_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(35,12): " + _331_valueOrError0);}
      _330_mpl = (_331_valueOrError0).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _332_algorithmSuiteId;
      _332_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _333_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _334_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _334_valueOrError1 = (_330_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_332_algorithmSuiteId, encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_334_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(38,30): " + _334_valueOrError1);}
      _333_decryptionMaterialsIn = (_334_valueOrError1).Extract();
      res = _333_decryptionMaterialsIn;
      return res;
      return res;
    }
    public static void TestHappyCase()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _335_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _336_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out132;
      _out132 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _336_valueOrError0 = _out132;
      if (!(!((_336_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(51,12): " + _336_valueOrError0);}
      _335_mpl = (_336_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _337_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out133;
      _out133 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _337_encryptionContext = _out133;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _338_encryptionMaterials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _out134;
      _out134 = TestMultiKeyring_Compile.__default.getInputEncryptionMaterials(_337_encryptionContext);
      _338_encryptionMaterials = _out134;
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _339_decryptionMaterials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _out135;
      _out135 = TestMultiKeyring_Compile.__default.getInputDecryptionMaterials(_337_encryptionContext);
      _339_decryptionMaterials = _out135;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _340_rawAESKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out136;
      _out136 = TestMultiKeyring_Compile.__default.setupRawAesKeyring(_337_encryptionContext);
      _340_rawAESKeyring = _out136;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _341_expectedEncryptionMaterials;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out137;
      _out137 = (_340_rawAESKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_338_encryptionMaterials));
      _341_expectedEncryptionMaterials = _out137;
      if (!((_341_expectedEncryptionMaterials).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(63,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _342_expectedPlaintextDataKey;
      _342_expectedPlaintextDataKey = (((_341_expectedEncryptionMaterials).dtor_value).dtor_materials).dtor_plaintextDataKey;
      if (!((_342_expectedPlaintextDataKey).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(65,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _343_staticKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out138;
      _out138 = TestMultiKeyring_Compile.__default.SetupStaticKeyring(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>.create_Some(((_341_expectedEncryptionMaterials).dtor_value).dtor_materials), Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials>.create_None());
      _343_staticKeyring = _out138;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _344_multiKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _345_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out139;
      _out139 = (_335_mpl).CreateMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateMultiKeyringInput.create(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.create_Some(_343_staticKeyring), Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_340_rawAESKeyring)));
      _345_valueOrError1 = _out139;
      if (!(!((_345_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(69,21): " + _345_valueOrError1);}
      _344_multiKeyring = (_345_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _346_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _347_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out140;
      _out140 = (_344_multiKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_338_encryptionMaterials));
      _347_valueOrError2 = _out140;
      if (!(!((_347_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(74,31): " + _347_valueOrError2);}
      _346_encryptionMaterialsOut = (_347_valueOrError2).Extract();
      _System._ITuple0 _348___v0;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _349_valueOrError3 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _349_valueOrError3 = (_335_mpl).EncryptionMaterialsHasPlaintextDataKey((_346_encryptionMaterialsOut).dtor_materials);
      if (!(!((_349_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(76,10): " + _349_valueOrError3);}
      _348___v0 = (_349_valueOrError3).Extract();
      if (!(((((_346_encryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey).dtor_value).Equals((_342_expectedPlaintextDataKey).dtor_value))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(87,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((new BigInteger((((_346_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Count)) == (new BigInteger(2)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(101,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestChildKeyringFailureEncrypt()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _350_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _351_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out141;
      _out141 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _351_valueOrError0 = _out141;
      if (!(!((_351_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(106,12): " + _351_valueOrError0);}
      _350_mpl = (_351_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _352_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out142;
      _out142 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _352_encryptionContext = _out142;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _353_rawAESKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out143;
      _out143 = TestMultiKeyring_Compile.__default.setupRawAesKeyring(_352_encryptionContext);
      _353_rawAESKeyring = _out143;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _354_failingKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out144;
      _out144 = TestMultiKeyring_Compile.__default.SetupFailingKeyring();
      _354_failingKeyring = _out144;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _355_multiKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _356_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out145;
      _out145 = (_350_mpl).CreateMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateMultiKeyringInput.create(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.create_Some(_353_rawAESKeyring), Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_354_failingKeyring)));
      _356_valueOrError1 = _out145;
      if (!(!((_356_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(116,21): " + _356_valueOrError1);}
      _355_multiKeyring = (_356_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _357_encryptionMaterials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _out146;
      _out146 = TestMultiKeyring_Compile.__default.getInputEncryptionMaterials(_352_encryptionContext);
      _357_encryptionMaterials = _out146;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _358_result;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out147;
      _out147 = (_355_multiKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_357_encryptionMaterials));
      _358_result = _out147;
      if (!((_358_result).IsFailure())) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(124,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestGeneratorKeyringFails()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _359_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _360_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out148;
      _out148 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _360_valueOrError0 = _out148;
      if (!(!((_360_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(129,12): " + _360_valueOrError0);}
      _359_mpl = (_360_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _361_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out149;
      _out149 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _361_encryptionContext = _out149;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _362_failingKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out150;
      _out150 = TestMultiKeyring_Compile.__default.SetupFailingKeyring();
      _362_failingKeyring = _out150;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _363_rawAESKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out151;
      _out151 = TestMultiKeyring_Compile.__default.setupRawAesKeyring(_361_encryptionContext);
      _363_rawAESKeyring = _out151;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _364_multiKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _365_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out152;
      _out152 = (_359_mpl).CreateMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateMultiKeyringInput.create(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.create_Some(_362_failingKeyring), Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_363_rawAESKeyring)));
      _365_valueOrError1 = _out152;
      if (!(!((_365_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(142,21): " + _365_valueOrError1);}
      _364_multiKeyring = (_365_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _366_encryptionMaterials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _out153;
      _out153 = TestMultiKeyring_Compile.__default.getInputEncryptionMaterials(_361_encryptionContext);
      _366_encryptionMaterials = _out153;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _367_result;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out154;
      _out154 = (_364_multiKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_366_encryptionMaterials));
      _367_result = _out154;
      if (!((_367_result).IsFailure())) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(150,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestGeneratorKeyringDoesNotReturnPlaintextDataKey()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _368_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _369_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out155;
      _out155 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _369_valueOrError0 = _out155;
      if (!(!((_369_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(155,12): " + _369_valueOrError0);}
      _368_mpl = (_369_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _370_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out156;
      _out156 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _370_encryptionContext = _out156;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _371_encryptionMaterials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _out157;
      _out157 = TestMultiKeyring_Compile.__default.getInputEncryptionMaterials(_370_encryptionContext);
      _371_encryptionMaterials = _out157;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _372_failingKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out158;
      _out158 = TestMultiKeyring_Compile.__default.SetupStaticKeyring(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>.create_Some(_371_encryptionMaterials), Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials>.create_None());
      _372_failingKeyring = _out158;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _373_multiKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _374_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out159;
      _out159 = (_368_mpl).CreateMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateMultiKeyringInput.create(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.create_Some(_372_failingKeyring), Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements()));
      _374_valueOrError1 = _out159;
      if (!(!((_374_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(165,21): " + _374_valueOrError1);}
      _373_multiKeyring = (_374_valueOrError1).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _375_result;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out160;
      _out160 = (_373_multiKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_371_encryptionMaterials));
      _375_result = _out160;
      if (!((_375_result).IsFailure())) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(171,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestGeneratorAbleToDecrypt()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _376_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _377_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out161;
      _out161 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _377_valueOrError0 = _out161;
      if (!(!((_377_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(176,12): " + _377_valueOrError0);}
      _376_mpl = (_377_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _378_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out162;
      _out162 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _378_encryptionContext = _out162;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _379_rawAESKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out163;
      _out163 = TestMultiKeyring_Compile.__default.setupRawAesKeyring(_378_encryptionContext);
      _379_rawAESKeyring = _out163;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _380_inputEncryptionMaterials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _out164;
      _out164 = TestMultiKeyring_Compile.__default.getInputEncryptionMaterials(_378_encryptionContext);
      _380_inputEncryptionMaterials = _out164;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _381_encryptionMaterials;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out165;
      _out165 = (_379_rawAESKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_380_inputEncryptionMaterials));
      _381_encryptionMaterials = _out165;
      if (!((_381_encryptionMaterials).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(190,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _382_inputDecryptionMaterials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _out166;
      _out166 = TestMultiKeyring_Compile.__default.getInputDecryptionMaterials(_378_encryptionContext);
      _382_inputDecryptionMaterials = _out166;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _383_failingKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out167;
      _out167 = TestMultiKeyring_Compile.__default.SetupFailingKeyring();
      _383_failingKeyring = _out167;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _384_multiKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _385_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out168;
      _out168 = (_376_mpl).CreateMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateMultiKeyringInput.create(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.create_Some(_379_rawAESKeyring), Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_383_failingKeyring)));
      _385_valueOrError1 = _out168;
      if (!(!((_385_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(196,21): " + _385_valueOrError1);}
      _384_multiKeyring = (_385_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptInput _386_onDecryptInput;
      _386_onDecryptInput = software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_382_inputDecryptionMaterials, (((_381_encryptionMaterials).dtor_value).dtor_materials).dtor_encryptedDataKeys);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _387_decryptionMaterials;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out169;
      _out169 = (_384_multiKeyring).OnDecrypt(_386_onDecryptInput);
      _387_decryptionMaterials = _out169;
      if (!((_387_decryptionMaterials).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(206,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(object.Equals((((_387_decryptionMaterials).dtor_value).dtor_materials).dtor_plaintextDataKey, (((_381_encryptionMaterials).dtor_value).dtor_materials).dtor_plaintextDataKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(207,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestGeneratorUnableToDecrypt()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _388_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _389_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out170;
      _out170 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _389_valueOrError0 = _out170;
      if (!(!((_389_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(212,12): " + _389_valueOrError0);}
      _388_mpl = (_389_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _390_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out171;
      _out171 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _390_encryptionContext = _out171;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _391_rawAESKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out172;
      _out172 = TestMultiKeyring_Compile.__default.setupRawAesKeyring(_390_encryptionContext);
      _391_rawAESKeyring = _out172;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _392_inputEncryptionMaterials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _out173;
      _out173 = TestMultiKeyring_Compile.__default.getInputEncryptionMaterials(_390_encryptionContext);
      _392_inputEncryptionMaterials = _out173;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _393_encryptionMaterials;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out174;
      _out174 = (_391_rawAESKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_392_inputEncryptionMaterials));
      _393_encryptionMaterials = _out174;
      if (!((_393_encryptionMaterials).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(237,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _394_inputDecryptionMaterials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _out175;
      _out175 = TestMultiKeyring_Compile.__default.getInputDecryptionMaterials(_390_encryptionContext);
      _394_inputDecryptionMaterials = _out175;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _395_failingKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out176;
      _out176 = TestMultiKeyring_Compile.__default.SetupFailingKeyring();
      _395_failingKeyring = _out176;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _396_multiKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _397_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out177;
      _out177 = (_388_mpl).CreateMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateMultiKeyringInput.create(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.create_Some(_395_failingKeyring), Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_395_failingKeyring, _391_rawAESKeyring, _395_failingKeyring)));
      _397_valueOrError1 = _out177;
      if (!(!((_397_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(245,21): " + _397_valueOrError1);}
      _396_multiKeyring = (_397_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptInput _398_onDecryptInput;
      _398_onDecryptInput = software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_394_inputDecryptionMaterials, (((_393_encryptionMaterials).dtor_value).dtor_materials).dtor_encryptedDataKeys);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _399_decryptionMaterials;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out178;
      _out178 = (_396_multiKeyring).OnDecrypt(_398_onDecryptInput);
      _399_decryptionMaterials = _out178;
      if (!((_399_decryptionMaterials).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(265,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(object.Equals((((_399_decryptionMaterials).dtor_value).dtor_materials).dtor_plaintextDataKey, (((_393_encryptionMaterials).dtor_value).dtor_materials).dtor_plaintextDataKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(266,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestCollectFailuresDecrypt()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _400_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _401_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out179;
      _out179 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _401_valueOrError0 = _out179;
      if (!(!((_401_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(272,12): " + _401_valueOrError0);}
      _400_mpl = (_401_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _402_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out180;
      _out180 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _402_encryptionContext = _out180;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _403_failingKeyring;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out181;
      _out181 = TestMultiKeyring_Compile.__default.SetupFailingKeyring();
      _403_failingKeyring = _out181;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _404_multiKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _405_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out182;
      _out182 = (_400_mpl).CreateMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateMultiKeyringInput.create(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.create_None(), Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_403_failingKeyring, _403_failingKeyring)));
      _405_valueOrError1 = _out182;
      if (!(!((_405_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(291,21): " + _405_valueOrError1);}
      _404_multiKeyring = (_405_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _406_materials;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _407_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _407_valueOrError2 = (_400_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF()), _402_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_407_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(296,18): " + _407_valueOrError2);}
      _406_materials = (_407_valueOrError2).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _408_result;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out183;
      _out183 = (_404_multiKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_406_materials, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements()));
      _408_result = _out183;
      if (!((_408_result).IsFailure())) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(305,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring setupRawAesKeyring(Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring res = default(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring);
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _409_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _410_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out184;
      _out184 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _410_valueOrError0 = _out184;
      if (!(!((_410_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(313,12): " + _410_valueOrError0);}
      _409_mpl = (_410_valueOrError0).Extract();
      Dafny.ISequence<char> _411_namespace;
      Dafny.ISequence<char> _412_name;
      Dafny.ISequence<char> _out185;
      Dafny.ISequence<char> _out186;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out185, out _out186);
      _411_namespace = _out185;
      _412_name = _out186;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _413_rawAESKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _414_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out187;
      _out187 = (_409_mpl).CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput.create(_411_namespace, _412_name, ((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim3 = new BigInteger(32);
  var arr3 = new byte[Dafny.Helpers.ToIntChecked(dim3, "array size exceeds memory limit")];
  for (int i3 = 0; i3 < dim3; i3++) {
    var _415_i = (BigInteger) i3;
    arr3[(int)(_415_i)] = (byte)(0);
  }
  return Dafny.Sequence<byte>.FromArray(arr3);
}))(), software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16()));
      _414_valueOrError1 = _out187;
      if (!(!((_414_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestMultiKeyring.dfy(316,22): " + _414_valueOrError1);}
      _413_rawAESKeyring = (_414_valueOrError1).Extract();
      res = _413_rawAESKeyring;
      return res;
      return res;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring SetupStaticKeyring(Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials> encryptionMaterials, Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials> decryptionMaterials)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring res = default(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring);
      TestMultiKeyring_Compile.StaticKeyring _nw9 = new TestMultiKeyring_Compile.StaticKeyring();
      _nw9.__ctor(encryptionMaterials, decryptionMaterials);
      res = _nw9;
      return res;
      return res;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring SetupFailingKeyring()
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring res = default(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring);
      TestMultiKeyring_Compile.FailingKeyring _nw10 = new TestMultiKeyring_Compile.FailingKeyring();
      _nw10.__ctor();
      res = _nw10;
      return res;
      return res;
    }
  }
} // end of namespace TestMultiKeyring_Compile
namespace TestRawAESKeyring_Compile {

  public partial class __default {
    public static void TestOnEncryptOnDecryptGenerateDataKey()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _416_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _417_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out188;
      _out188 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _417_valueOrError0 = _out188;
      if (!(!((_417_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(21,12): " + _417_valueOrError0);}
      _416_mpl = (_417_valueOrError0).Extract();
      Dafny.ISequence<char> _418_namespace;
      Dafny.ISequence<char> _419_name;
      Dafny.ISequence<char> _out189;
      Dafny.ISequence<char> _out190;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out189, out _out190);
      _418_namespace = _out189;
      _419_name = _out190;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _420_rawAESKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _421_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out191;
      _out191 = (_416_mpl).CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput.create(_418_namespace, _419_name, ((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim4 = new BigInteger(32);
  var arr4 = new byte[Dafny.Helpers.ToIntChecked(dim4, "array size exceeds memory limit")];
  for (int i4 = 0; i4 < dim4; i4++) {
    var _422_i = (BigInteger) i4;
    arr4[(int)(_422_i)] = (byte)(0);
  }
  return Dafny.Sequence<byte>.FromArray(arr4);
}))(), software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16()));
      _421_valueOrError1 = _out191;
      if (!(!((_421_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(24,22): " + _421_valueOrError1);}
      _420_rawAESKeyring = (_421_valueOrError1).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _423_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out192;
      _out192 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _423_encryptionContext = _out192;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _424_algorithmSuiteId;
      _424_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _425_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _426_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _426_valueOrError2 = (_416_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_424_algorithmSuiteId, _423_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_426_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(33,30): " + _426_valueOrError2);}
      _425_encryptionMaterialsIn = (_426_valueOrError2).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _427_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _428_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out193;
      _out193 = (_420_rawAESKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_425_encryptionMaterialsIn));
      _428_valueOrError3 = _out193;
      if (!(!((_428_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(43,31): " + _428_valueOrError3);}
      _427_encryptionMaterialsOut = (_428_valueOrError3).Extract();
      _System._ITuple0 _429___v0;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _430_valueOrError4 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _430_valueOrError4 = (_416_mpl).EncryptionMaterialsHasPlaintextDataKey((_427_encryptionMaterialsOut).dtor_materials);
      if (!(!((_430_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(58,10): " + _430_valueOrError4);}
      _429___v0 = (_430_valueOrError4).Extract();
      if (!((new BigInteger((((_427_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(65,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _431_edk;
      _431_edk = (((_427_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Select(BigInteger.Zero);
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _432_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _433_valueOrError5 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _433_valueOrError5 = (_416_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_424_algorithmSuiteId, _423_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_433_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(69,30): " + _433_valueOrError5);}
      _432_decryptionMaterialsIn = (_433_valueOrError5).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput _434_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _435_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out194;
      _out194 = (_420_rawAESKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_432_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_431_edk)));
      _435_valueOrError6 = _out194;
      if (!(!((_435_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(76,31): " + _435_valueOrError6);}
      _434_decryptionMaterialsOut = (_435_valueOrError6).Extract();
      if (!(object.Equals(((_427_encryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey, ((_427_encryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(88,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestOnEncryptOnDecryptSuppliedDataKey()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _436_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _437_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out195;
      _out195 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _437_valueOrError0 = _out195;
      if (!(!((_437_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(95,12): " + _437_valueOrError0);}
      _436_mpl = (_437_valueOrError0).Extract();
      Dafny.ISequence<char> _438_namespace;
      Dafny.ISequence<char> _439_name;
      Dafny.ISequence<char> _out196;
      Dafny.ISequence<char> _out197;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out196, out _out197);
      _438_namespace = _out196;
      _439_name = _out197;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _440_rawAESKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _441_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out198;
      _out198 = (_436_mpl).CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput.create(_438_namespace, _439_name, ((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim5 = new BigInteger(32);
  var arr5 = new byte[Dafny.Helpers.ToIntChecked(dim5, "array size exceeds memory limit")];
  for (int i5 = 0; i5 < dim5; i5++) {
    var _442_i = (BigInteger) i5;
    arr5[(int)(_442_i)] = (byte)(0);
  }
  return Dafny.Sequence<byte>.FromArray(arr5);
}))(), software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16()));
      _441_valueOrError1 = _out198;
      if (!(!((_441_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(98,22): " + _441_valueOrError1);}
      _440_rawAESKeyring = (_441_valueOrError1).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _443_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out199;
      _out199 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _443_encryptionContext = _out199;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _444_algorithmSuiteId;
      _444_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _445_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _446_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _446_valueOrError2 = (_436_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_444_algorithmSuiteId, _443_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_446_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(107,30): " + _446_valueOrError2);}
      _445_encryptionMaterialsIn = (_446_valueOrError2).Extract();
      Dafny.ISequence<byte> _447_pdk;
      _447_pdk = ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim6 = new BigInteger(32);
        var arr6 = new byte[Dafny.Helpers.ToIntChecked(dim6, "array size exceeds memory limit")];
        for (int i6 = 0; i6 < dim6; i6++) {
          var _448_i = (BigInteger) i6;
          arr6[(int)(_448_i)] = (byte)(0);
        }
        return Dafny.Sequence<byte>.FromArray(arr6);
      }))();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _449_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _450_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      var _pat_let_tv4 = _447_pdk;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out200;
      _out200 = (_440_rawAESKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_445_encryptionMaterialsIn, _pat_let15_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let15_0, _451_dt__update__tmp_h0 => Dafny.Helpers.Let<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_pat_let_tv4), _pat_let16_0 => Dafny.Helpers.Let<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>(_pat_let16_0, _452_dt__update_hplaintextDataKey_h0 => software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials.create((_451_dt__update__tmp_h0).dtor_algorithmSuite, (_451_dt__update__tmp_h0).dtor_encryptionContext, (_451_dt__update__tmp_h0).dtor_encryptedDataKeys, (_451_dt__update__tmp_h0).dtor_requiredEncryptionContextKeys, _452_dt__update_hplaintextDataKey_h0, (_451_dt__update__tmp_h0).dtor_signingKey, (_451_dt__update__tmp_h0).dtor_symmetricSigningKeys)))))));
      _450_valueOrError3 = _out200;
      if (!(!((_450_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(122,31): " + _450_valueOrError3);}
      _449_encryptionMaterialsOut = (_450_valueOrError3).Extract();
      _System._ITuple0 _453___v1;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _454_valueOrError4 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _454_valueOrError4 = (_436_mpl).EncryptionMaterialsHasPlaintextDataKey((_449_encryptionMaterialsOut).dtor_materials);
      if (!(!((_454_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(126,10): " + _454_valueOrError4);}
      _453___v1 = (_454_valueOrError4).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _455_edk;
      _455_edk = (((_449_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Select(BigInteger.Zero);
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _456_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _457_valueOrError5 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _457_valueOrError5 = (_436_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_444_algorithmSuiteId, _443_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_457_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(130,30): " + _457_valueOrError5);}
      _456_decryptionMaterialsIn = (_457_valueOrError5).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput _458_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _459_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out201;
      _out201 = (_440_rawAESKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_456_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_455_edk)));
      _459_valueOrError6 = _out201;
      if (!(!((_459_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(138,31): " + _459_valueOrError6);}
      _458_decryptionMaterialsOut = (_459_valueOrError6).Extract();
      if (!(object.Equals(((_458_decryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey, Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_447_pdk)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(150,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestOnDecryptKeyNameMismatch()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _460_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _461_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out202;
      _out202 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _461_valueOrError0 = _out202;
      if (!(!((_461_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(156,12): " + _461_valueOrError0);}
      _460_mpl = (_461_valueOrError0).Extract();
      Dafny.ISequence<char> _462_namespace;
      Dafny.ISequence<char> _463_name;
      Dafny.ISequence<char> _out203;
      Dafny.ISequence<char> _out204;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out203, out _out204);
      _462_namespace = _out203;
      _463_name = _out204;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _464_rawAESKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _465_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out205;
      _out205 = (_460_mpl).CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput.create(_462_namespace, _463_name, ((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim7 = new BigInteger(32);
  var arr7 = new byte[Dafny.Helpers.ToIntChecked(dim7, "array size exceeds memory limit")];
  for (int i7 = 0; i7 < dim7; i7++) {
    var _466_i = (BigInteger) i7;
    arr7[(int)(_466_i)] = (byte)(0);
  }
  return Dafny.Sequence<byte>.FromArray(arr7);
}))(), software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16()));
      _465_valueOrError1 = _out205;
      if (!(!((_465_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(159,22): " + _465_valueOrError1);}
      _464_rawAESKeyring = (_465_valueOrError1).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _467_mismatchedAESKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _468_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out206;
      _out206 = (_460_mpl).CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput.create(_462_namespace, Dafny.Sequence<char>.FromString("mismatched"), ((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim8 = new BigInteger(32);
  var arr8 = new byte[Dafny.Helpers.ToIntChecked(dim8, "array size exceeds memory limit")];
  for (int i8 = 0; i8 < dim8; i8++) {
    var _469_i = (BigInteger) i8;
    arr8[(int)(_469_i)] = (byte)(1);
  }
  return Dafny.Sequence<byte>.FromArray(arr8);
}))(), software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16()));
      _468_valueOrError2 = _out206;
      if (!(!((_468_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(166,29): " + _468_valueOrError2);}
      _467_mismatchedAESKeyring = (_468_valueOrError2).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _470_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out207;
      _out207 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _470_encryptionContext = _out207;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _471_algorithmSuiteId;
      _471_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _472_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _473_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _473_valueOrError3 = (_460_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_471_algorithmSuiteId, _470_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_473_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(176,30): " + _473_valueOrError3);}
      _472_encryptionMaterialsIn = (_473_valueOrError3).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _474_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _475_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out208;
      _out208 = (_464_rawAESKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_472_encryptionMaterialsIn));
      _475_valueOrError4 = _out208;
      if (!(!((_475_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(186,31): " + _475_valueOrError4);}
      _474_encryptionMaterialsOut = (_475_valueOrError4).Extract();
      _System._ITuple0 _476___v2;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _477_valueOrError5 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _477_valueOrError5 = (_460_mpl).EncryptionMaterialsHasPlaintextDataKey((_474_encryptionMaterialsOut).dtor_materials);
      if (!(!((_477_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(190,10): " + _477_valueOrError5);}
      _476___v2 = (_477_valueOrError5).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _478_edk;
      _478_edk = (((_474_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Select(BigInteger.Zero);
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _479_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _480_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _480_valueOrError6 = (_460_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_471_algorithmSuiteId, _470_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_480_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(194,30): " + _480_valueOrError6);}
      _479_decryptionMaterialsIn = (_480_valueOrError6).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _481_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out209;
      _out209 = (_467_mismatchedAESKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_479_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_478_edk)));
      _481_decryptionMaterialsOut = _out209;
      if (!((_481_decryptionMaterialsOut).IsFailure())) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(207,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestOnDecryptBadAndGoodEdkSucceeds()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _482_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _483_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out210;
      _out210 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _483_valueOrError0 = _out210;
      if (!(!((_483_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(213,12): " + _483_valueOrError0);}
      _482_mpl = (_483_valueOrError0).Extract();
      Dafny.ISequence<char> _484_namespace;
      Dafny.ISequence<char> _485_name;
      Dafny.ISequence<char> _out211;
      Dafny.ISequence<char> _out212;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out211, out _out212);
      _484_namespace = _out211;
      _485_name = _out212;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _486_rawAESKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _487_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out213;
      _out213 = (_482_mpl).CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput.create(_484_namespace, _485_name, ((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim9 = new BigInteger(32);
  var arr9 = new byte[Dafny.Helpers.ToIntChecked(dim9, "array size exceeds memory limit")];
  for (int i9 = 0; i9 < dim9; i9++) {
    var _488_i = (BigInteger) i9;
    arr9[(int)(_488_i)] = (byte)(0);
  }
  return Dafny.Sequence<byte>.FromArray(arr9);
}))(), software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16()));
      _487_valueOrError1 = _out213;
      if (!(!((_487_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(216,22): " + _487_valueOrError1);}
      _486_rawAESKeyring = (_487_valueOrError1).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _489_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out214;
      _out214 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _489_encryptionContext = _out214;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _490_algorithmSuiteId;
      _490_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _491_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _492_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _492_valueOrError2 = (_482_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_490_algorithmSuiteId, _489_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_492_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(225,30): " + _492_valueOrError2);}
      _491_encryptionMaterialsIn = (_492_valueOrError2).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _493_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _494_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out215;
      _out215 = (_486_rawAESKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_491_encryptionMaterialsIn));
      _494_valueOrError3 = _out215;
      if (!(!((_494_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(235,31): " + _494_valueOrError3);}
      _493_encryptionMaterialsOut = (_494_valueOrError3).Extract();
      _System._ITuple0 _495___v3;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _496_valueOrError4 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _496_valueOrError4 = (_482_mpl).EncryptionMaterialsHasPlaintextDataKey((_493_encryptionMaterialsOut).dtor_materials);
      if (!(!((_496_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(239,10): " + _496_valueOrError4);}
      _495___v3 = (_496_valueOrError4).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _497_edk;
      _497_edk = (((_493_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Select(BigInteger.Zero);
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _498_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _499_valueOrError5 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _499_valueOrError5 = (_482_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_490_algorithmSuiteId, _489_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_499_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(243,30): " + _499_valueOrError5);}
      _498_decryptionMaterialsIn = (_499_valueOrError5).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _500_fakeEdk;
      _500_fakeEdk = software.amazon.cryptography.materialproviders.internaldafny.types.EncryptedDataKey.create((_497_edk).dtor_keyProviderId, (_497_edk).dtor_keyProviderInfo, ((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim10 = new BigInteger(((_497_edk).dtor_ciphertext).Count);
  var arr10 = new byte[Dafny.Helpers.ToIntChecked(dim10, "array size exceeds memory limit")];
  for (int i10 = 0; i10 < dim10; i10++) {
    var _501_i = (BigInteger) i10;
    arr10[(int)(_501_i)] = (byte)(0);
  }
  return Dafny.Sequence<byte>.FromArray(arr10);
}))());
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput _502_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _503_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out216;
      _out216 = (_486_rawAESKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_498_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_500_fakeEdk, _497_edk)));
      _503_valueOrError6 = _out216;
      if (!(!((_503_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(256,31): " + _503_valueOrError6);}
      _502_decryptionMaterialsOut = (_503_valueOrError6).Extract();
      if (!(object.Equals(((_502_decryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey, ((_493_encryptionMaterialsOut).dtor_materials).dtor_plaintextDataKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(263,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestOnDecryptNoEDKs()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _504_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _505_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out217;
      _out217 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _505_valueOrError0 = _out217;
      if (!(!((_505_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(269,12): " + _505_valueOrError0);}
      _504_mpl = (_505_valueOrError0).Extract();
      Dafny.ISequence<char> _506_namespace;
      Dafny.ISequence<char> _507_name;
      Dafny.ISequence<char> _out218;
      Dafny.ISequence<char> _out219;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out218, out _out219);
      _506_namespace = _out218;
      _507_name = _out219;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _508_rawAESKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _509_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out220;
      _out220 = (_504_mpl).CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput.create(_506_namespace, _507_name, ((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim11 = new BigInteger(32);
  var arr11 = new byte[Dafny.Helpers.ToIntChecked(dim11, "array size exceeds memory limit")];
  for (int i11 = 0; i11 < dim11; i11++) {
    var _510_i = (BigInteger) i11;
    arr11[(int)(_510_i)] = (byte)(0);
  }
  return Dafny.Sequence<byte>.FromArray(arr11);
}))(), software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16()));
      _509_valueOrError1 = _out220;
      if (!(!((_509_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(272,22): " + _509_valueOrError1);}
      _508_rawAESKeyring = (_509_valueOrError1).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _511_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out221;
      _out221 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _511_encryptionContext = _out221;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _512_algorithmSuiteId;
      _512_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _513_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _514_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _514_valueOrError2 = (_504_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_512_algorithmSuiteId, _511_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_514_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(281,30): " + _514_valueOrError2);}
      _513_decryptionMaterialsIn = (_514_valueOrError2).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _515_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out222;
      _out222 = (_508_rawAESKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_513_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements()));
      _515_decryptionMaterialsOut = _out222;
      if (!((_515_decryptionMaterialsOut).IsFailure())) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(294,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestOnEncryptUnserializableEC()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _516_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _517_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out223;
      _out223 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _517_valueOrError0 = _out223;
      if (!(!((_517_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(303,12): " + _517_valueOrError0);}
      _516_mpl = (_517_valueOrError0).Extract();
      Dafny.ISequence<char> _518_namespace;
      Dafny.ISequence<char> _519_name;
      Dafny.ISequence<char> _out224;
      Dafny.ISequence<char> _out225;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out224, out _out225);
      _518_namespace = _out224;
      _519_name = _out225;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _520_rawAESKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _521_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out226;
      _out226 = (_516_mpl).CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput.create(_518_namespace, _519_name, ((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim12 = new BigInteger(32);
  var arr12 = new byte[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
  for (int i12 = 0; i12 < dim12; i12++) {
    var _522_i = (BigInteger) i12;
    arr12[(int)(_522_i)] = (byte)(0);
  }
  return Dafny.Sequence<byte>.FromArray(arr12);
}))(), software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16()));
      _521_valueOrError1 = _out226;
      if (!(!((_521_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(306,22): " + _521_valueOrError1);}
      _520_rawAESKeyring = (_521_valueOrError1).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _523_unserializableEncryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out227;
      _out227 = TestRawAESKeyring_Compile.__default.generateUnserializableEncryptionContext();
      _523_unserializableEncryptionContext = _out227;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _524_algorithmSuiteId;
      _524_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _525_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _526_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _526_valueOrError2 = (_516_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_524_algorithmSuiteId, _523_unserializableEncryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_526_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(315,30): " + _526_valueOrError2);}
      _525_encryptionMaterialsIn = (_526_valueOrError2).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _527_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out228;
      _out228 = (_520_rawAESKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_525_encryptionMaterialsIn));
      _527_encryptionMaterialsOut = _out228;
      if (!((_527_encryptionMaterialsOut).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(327,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestOnDecryptUnserializableEC()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _528_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _529_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out229;
      _out229 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _529_valueOrError0 = _out229;
      if (!(!((_529_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(337,12): " + _529_valueOrError0);}
      _528_mpl = (_529_valueOrError0).Extract();
      Dafny.ISequence<char> _530_namespace;
      Dafny.ISequence<char> _531_name;
      Dafny.ISequence<char> _out230;
      Dafny.ISequence<char> _out231;
      TestUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out230, out _out231);
      _530_namespace = _out230;
      _531_name = _out231;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _532_rawAESKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _533_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out232;
      _out232 = (_528_mpl).CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput.create(_530_namespace, _531_name, ((System.Func<Dafny.ISequence<byte>>) (() => {
  BigInteger dim13 = new BigInteger(32);
  var arr13 = new byte[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _534_i = (BigInteger) i13;
    arr13[(int)(_534_i)] = (byte)(0);
  }
  return Dafny.Sequence<byte>.FromArray(arr13);
}))(), software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16()));
      _533_valueOrError1 = _out232;
      if (!(!((_533_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(340,22): " + _533_valueOrError1);}
      _532_rawAESKeyring = (_533_valueOrError1).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _535_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out233;
      _out233 = TestUtils_Compile.__default.SmallEncryptionContext(TestUtils_Compile.SmallEncryptionContextVariation.create_A());
      _535_encryptionContext = _out233;
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _536_algorithmSuiteId;
      _536_algorithmSuiteId = software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF());
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _537_encryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _538_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _538_valueOrError2 = (_528_mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(_536_algorithmSuiteId, _535_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None()));
      if (!(!((_538_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(349,30): " + _538_valueOrError2);}
      _537_encryptionMaterialsIn = (_538_valueOrError2).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _539_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _540_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out234;
      _out234 = (_532_rawAESKeyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(_537_encryptionMaterialsIn));
      _540_valueOrError3 = _out234;
      if (!(!((_540_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(359,31): " + _540_valueOrError3);}
      _539_encryptionMaterialsOut = (_540_valueOrError3).Extract();
      _System._ITuple0 _541___v4;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _542_valueOrError4 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _542_valueOrError4 = (_528_mpl).EncryptionMaterialsHasPlaintextDataKey((_539_encryptionMaterialsOut).dtor_materials);
      if (!(!((_542_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(362,10): " + _542_valueOrError4);}
      _541___v4 = (_542_valueOrError4).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey _543_edk;
      _543_edk = (((_539_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Select(BigInteger.Zero);
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _544_unserializableEncryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out235;
      _out235 = TestRawAESKeyring_Compile.__default.generateUnserializableEncryptionContext();
      _544_unserializableEncryptionContext = _out235;
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _545_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _546_valueOrError5 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _546_valueOrError5 = (_528_mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(_536_algorithmSuiteId, _544_unserializableEncryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_546_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(367,30): " + _546_valueOrError5);}
      _545_decryptionMaterialsIn = (_546_valueOrError5).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _547_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out236;
      _out236 = (_532_rawAESKeyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(_545_decryptionMaterialsIn, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.FromElements(_543_edk)));
      _547_decryptionMaterialsOut = _out236;
      if (!((_547_decryptionMaterialsOut).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(380,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> generateUnserializableEncryptionContext()
    {
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty;
      Dafny.ISequence<byte> _548_keyA;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _549_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _549_valueOrError0 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("keyA"));
      if (!(!((_549_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/Keyrings/TestRawAESKeyring.dfy(385,13): " + _549_valueOrError0);}
      _548_keyA = (_549_valueOrError0).Extract();
      Dafny.ISequence<byte> _550_invalidVal;
      _550_invalidVal = ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim14 = new BigInteger(65536);
        var arr14 = new byte[Dafny.Helpers.ToIntChecked(dim14, "array size exceeds memory limit")];
        for (int i14 = 0; i14 < dim14; i14++) {
          var _551___v5 = (BigInteger) i14;
          arr14[(int)(_551___v5)] = (byte)(0);
        }
        return Dafny.Sequence<byte>.FromArray(arr14);
      }))();
      encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_548_keyA, _550_invalidVal));
      return encCtx;
      return encCtx;
    }
  }
} // end of namespace TestRawAESKeyring_Compile
namespace TestDefaultClientProvider_Compile {

  public partial class __default {
    public static void GetUsWestTwo()
    {
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _552_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _553_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out237;
      _out237 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _553_valueOrError0 = _out237;
      if (!(!((_553_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestDefaultClientProvider.dfy(18,12): " + _553_valueOrError0);}
      _552_mpl = (_553_valueOrError0).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier _554_clientSupplier;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _555_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out238;
      _out238 = (_552_mpl).CreateDefaultClientSupplier(software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultClientSupplierInput.create());
      _555_valueOrError1 = _out238;
      if (!(!((_555_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestDefaultClientProvider.dfy(20,23): " + _555_valueOrError1);}
      _554_clientSupplier = (_555_valueOrError1).Extract();
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _556_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _557_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out239;
      _out239 = (_554_clientSupplier).GetClient(software.amazon.cryptography.materialproviders.internaldafny.types.GetClientInput.create(Dafny.Sequence<char>.FromString("us-west-2")));
      _557_valueOrError2 = _out239;
      if (!(!((_557_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestDefaultClientProvider.dfy(22,15): " + _557_valueOrError2);}
      _556_client = (_557_valueOrError2).Extract();
      software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyRequest _558_kmsRequest;
      _558_kmsRequest = software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyRequest.create(TestUtils_Compile.__default.SHARED__TEST__KEY__ARN, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<int>.create_Some((int)(24)), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None());
      software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse _559_kmsReply;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> _560_valueOrError3 = Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError>.Default(software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyResponse.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out240;
      _out240 = (_556_client).GenerateDataKey(_558_kmsRequest);
      _560_valueOrError3 = _out240;
      if (!(!((_560_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestDefaultClientProvider.dfy(36,17): " + _560_valueOrError3);}
      _559_kmsReply = (_560_valueOrError3).Extract();
    }
  }
} // end of namespace TestDefaultClientProvider_Compile
namespace TestIntermediateKeyWrapping_Compile {

  public interface _ITestInfo {
    bool is_TestInfo { get; }
    _ITestInfo DowncastClone();
  }
  public class TestInfo : _ITestInfo {
    public TestInfo() {
    }
    public _ITestInfo DowncastClone() {
      if (this is _ITestInfo dt) { return dt; }
      return new TestInfo();
    }
    public override bool Equals(object other) {
      var oth = other as TestIntermediateKeyWrapping_Compile.TestInfo;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestIntermediateKeyWrapping_Compile.TestInfo.TestInfo";
      return s;
    }
    private static readonly TestIntermediateKeyWrapping_Compile._ITestInfo theDefault = create();
    public static TestIntermediateKeyWrapping_Compile._ITestInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestIntermediateKeyWrapping_Compile._ITestInfo> _TYPE = new Dafny.TypeDescriptor<TestIntermediateKeyWrapping_Compile._ITestInfo>(TestIntermediateKeyWrapping_Compile.TestInfo.Default());
    public static Dafny.TypeDescriptor<TestIntermediateKeyWrapping_Compile._ITestInfo> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITestInfo create() {
      return new TestInfo();
    }
    public static _ITestInfo create_TestInfo() {
      return create();
    }
    public bool is_TestInfo { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_ITestInfo> AllSingletonConstructors {
      get {
        yield return TestInfo.create();
      }
    }
  }

  public partial class TestGenerateAndWrapKeyMaterial : MaterialWrapping_Compile.GenerateAndWrapMaterial<TestIntermediateKeyWrapping_Compile._ITestInfo>, Actions_Compile.ActionWithResult<MaterialWrapping_Compile._IGenerateAndWrapInput, MaterialWrapping_Compile._IGenerateAndWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError>, Actions_Compile.Action<MaterialWrapping_Compile._IGenerateAndWrapInput, Wrappers_Compile._IResult<MaterialWrapping_Compile._IGenerateAndWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError>> {
    public TestGenerateAndWrapKeyMaterial() {
    }
    public void __ctor()
    {
    }
    public Wrappers_Compile._IResult<MaterialWrapping_Compile._IGenerateAndWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> Invoke(MaterialWrapping_Compile._IGenerateAndWrapInput input)
    {
      Wrappers_Compile._IResult<MaterialWrapping_Compile._IGenerateAndWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> res = Wrappers_Compile.Result<MaterialWrapping_Compile._IGenerateAndWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(MaterialWrapping_Compile.GenerateAndWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>.Default(TestIntermediateKeyWrapping_Compile.TestInfo.Default()));
      Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviders.internaldafny.types._IError> _561_valueOrError0 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default();
      _561_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviders.internaldafny.types._IError>(object.Equals((input).dtor_algorithmSuite, TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE), software.amazon.cryptography.materialproviders.internaldafny.types.Error.create_AwsCryptographicMaterialProvidersException(Dafny.Sequence<char>.FromString("Unexpected input on TestGenerateAndWrapMaterial")));
      if ((_561_valueOrError0).IsFailure()) {
        res = (_561_valueOrError0).PropagateFailure<MaterialWrapping_Compile._IGenerateAndWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>>();
        return res;
      }
      res = Wrappers_Compile.Result<MaterialWrapping_Compile._IGenerateAndWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(MaterialWrapping_Compile.GenerateAndWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>.create(TestIntermediateKeyWrapping_Compile.__default.PLAINTEXT__MAT, TestIntermediateKeyWrapping_Compile.__default.WRAPPED__MAT, TestIntermediateKeyWrapping_Compile.TestInfo.create()));
      return res;
      return res;
    }
  }

  public partial class TestUnwrapKeyMaterial : MaterialWrapping_Compile.UnwrapMaterial<TestIntermediateKeyWrapping_Compile._ITestInfo>, Actions_Compile.ActionWithResult<MaterialWrapping_Compile._IUnwrapInput, MaterialWrapping_Compile._IUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError>, Actions_Compile.Action<MaterialWrapping_Compile._IUnwrapInput, Wrappers_Compile._IResult<MaterialWrapping_Compile._IUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError>> {
    public TestUnwrapKeyMaterial() {
    }
    public void __ctor()
    {
    }
    public Wrappers_Compile._IResult<MaterialWrapping_Compile._IUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> Invoke(MaterialWrapping_Compile._IUnwrapInput input)
    {
      Wrappers_Compile._IResult<MaterialWrapping_Compile._IUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> res = Wrappers_Compile.Result<MaterialWrapping_Compile._IUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(MaterialWrapping_Compile.UnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>.Default(TestIntermediateKeyWrapping_Compile.TestInfo.Default()));
      Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviders.internaldafny.types._IError> _562_valueOrError0 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default();
      _562_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviders.internaldafny.types._IError>(((input).dtor_wrappedMaterial).Equals(TestIntermediateKeyWrapping_Compile.__default.WRAPPED__MAT), software.amazon.cryptography.materialproviders.internaldafny.types.Error.create_AwsCryptographicMaterialProvidersException(Dafny.Sequence<char>.FromString("Unexpected input on TestUnwrapMaterial")));
      if ((_562_valueOrError0).IsFailure()) {
        res = (_562_valueOrError0).PropagateFailure<MaterialWrapping_Compile._IUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>>();
        return res;
      }
      Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviders.internaldafny.types._IError> _563_valueOrError1 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default();
      _563_valueOrError1 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviders.internaldafny.types._IError>(object.Equals((input).dtor_algorithmSuite, TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE), software.amazon.cryptography.materialproviders.internaldafny.types.Error.create_AwsCryptographicMaterialProvidersException(Dafny.Sequence<char>.FromString("Unexpected input on TestUnwrapMaterial")));
      if ((_563_valueOrError1).IsFailure()) {
        res = (_563_valueOrError1).PropagateFailure<MaterialWrapping_Compile._IUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>>();
        return res;
      }
      res = Wrappers_Compile.Result<MaterialWrapping_Compile._IUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(MaterialWrapping_Compile.UnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>.create(TestIntermediateKeyWrapping_Compile.__default.PLAINTEXT__MAT, TestIntermediateKeyWrapping_Compile.TestInfo.create()));
      return res;
      return res;
    }
  }

  public partial class __default {
    public static void IntermediateWrapUnwrapTest()
    {
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _564_encCtx;
      _564_encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements();
      BigInteger _565_keyLen;
      _565_keyLen = new BigInteger((((TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE).dtor_encrypt).dtor_AES__GCM).dtor_keyLength);
      BigInteger _566_tagLen;
      _566_tagLen = new BigInteger((((TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE).dtor_encrypt).dtor_AES__GCM).dtor_tagLength);
      Dafny.ISequence<byte> _567_pdk;
      _567_pdk = ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim15 = _565_keyLen;
        var arr15 = new byte[Dafny.Helpers.ToIntChecked(dim15, "array size exceeds memory limit")];
        for (int i15 = 0; i15 < dim15; i15++) {
          var _568___v2 = (BigInteger) i15;
          arr15[(int)(_568___v2)] = (byte)(0);
        }
        return Dafny.Sequence<byte>.FromArray(arr15);
      }))();
      TestIntermediateKeyWrapping_Compile.TestGenerateAndWrapKeyMaterial _569_testGenerateAndWrap;
      TestIntermediateKeyWrapping_Compile.TestGenerateAndWrapKeyMaterial _nw11 = new TestIntermediateKeyWrapping_Compile.TestGenerateAndWrapKeyMaterial();
      _nw11.__ctor();
      _569_testGenerateAndWrap = _nw11;
      Wrappers_Compile._IResult<IntermediateKeyWrapping_Compile._IIntermediateWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _570_intermediateWrapOutput;
      Wrappers_Compile._IResult<IntermediateKeyWrapping_Compile._IIntermediateWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out241;
      _out241 = IntermediateKeyWrapping_Compile.__default.IntermediateWrap<TestIntermediateKeyWrapping_Compile._ITestInfo>(_569_testGenerateAndWrap, _567_pdk, TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE, _564_encCtx);
      _570_intermediateWrapOutput = _out241;
      if (!((_570_intermediateWrapOutput).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(36,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((new BigInteger((((_570_intermediateWrapOutput).dtor_value).dtor_wrappedMaterial).Count)) == (((_565_keyLen) + (_566_tagLen)) + (new BigInteger((TestIntermediateKeyWrapping_Compile.__default.WRAPPED__MAT).Count))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(37,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((((_570_intermediateWrapOutput).dtor_value).dtor_wrappedMaterial).Drop((_565_keyLen) + (_566_tagLen))).Equals(TestIntermediateKeyWrapping_Compile.__default.WRAPPED__MAT))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(38,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      TestIntermediateKeyWrapping_Compile.TestUnwrapKeyMaterial _571_testUnwrap;
      TestIntermediateKeyWrapping_Compile.TestUnwrapKeyMaterial _nw12 = new TestIntermediateKeyWrapping_Compile.TestUnwrapKeyMaterial();
      _nw12.__ctor();
      _571_testUnwrap = _nw12;
      Wrappers_Compile._IResult<IntermediateKeyWrapping_Compile._IIntermediateUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _572_intermediateUnwrapOutput;
      Wrappers_Compile._IResult<IntermediateKeyWrapping_Compile._IIntermediateUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out242;
      _out242 = IntermediateKeyWrapping_Compile.__default.IntermediateUnwrap<TestIntermediateKeyWrapping_Compile._ITestInfo>(_571_testUnwrap, ((_570_intermediateWrapOutput).dtor_value).dtor_wrappedMaterial, TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE, _564_encCtx);
      _572_intermediateUnwrapOutput = _out242;
      if (!((_572_intermediateUnwrapOutput).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(47,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_572_intermediateUnwrapOutput).dtor_value).dtor_plaintextDataKey).Equals(_567_pdk))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(48,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_570_intermediateWrapOutput).dtor_value).dtor_symmetricSigningKey).Equals(((_572_intermediateUnwrapOutput).dtor_value).dtor_symmetricSigningKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(49,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void IntermediateGenerateAndWrapUnwrapTest()
    {
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _573_encCtx;
      _573_encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements();
      BigInteger _574_keyLen;
      _574_keyLen = new BigInteger((((TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE).dtor_encrypt).dtor_AES__GCM).dtor_keyLength);
      BigInteger _575_tagLen;
      _575_tagLen = new BigInteger((((TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE).dtor_encrypt).dtor_AES__GCM).dtor_tagLength);
      TestIntermediateKeyWrapping_Compile.TestGenerateAndWrapKeyMaterial _576_testGenerateAndWrap;
      TestIntermediateKeyWrapping_Compile.TestGenerateAndWrapKeyMaterial _nw13 = new TestIntermediateKeyWrapping_Compile.TestGenerateAndWrapKeyMaterial();
      _nw13.__ctor();
      _576_testGenerateAndWrap = _nw13;
      Wrappers_Compile._IResult<IntermediateKeyWrapping_Compile._IIntermediateGenerateAndWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _577_intermediateWrapOutput;
      Wrappers_Compile._IResult<IntermediateKeyWrapping_Compile._IIntermediateGenerateAndWrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out243;
      _out243 = IntermediateKeyWrapping_Compile.__default.IntermediateGenerateAndWrap<TestIntermediateKeyWrapping_Compile._ITestInfo>(_576_testGenerateAndWrap, TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE, _573_encCtx);
      _577_intermediateWrapOutput = _out243;
      if (!((_577_intermediateWrapOutput).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(63,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((new BigInteger((((_577_intermediateWrapOutput).dtor_value).dtor_wrappedMaterial).Count)) == (((_574_keyLen) + (_575_tagLen)) + (new BigInteger((TestIntermediateKeyWrapping_Compile.__default.WRAPPED__MAT).Count))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(64,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((((_577_intermediateWrapOutput).dtor_value).dtor_wrappedMaterial).Drop((_574_keyLen) + (_575_tagLen))).Equals(TestIntermediateKeyWrapping_Compile.__default.WRAPPED__MAT))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(65,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      TestIntermediateKeyWrapping_Compile.TestUnwrapKeyMaterial _578_testUnwrap;
      TestIntermediateKeyWrapping_Compile.TestUnwrapKeyMaterial _nw14 = new TestIntermediateKeyWrapping_Compile.TestUnwrapKeyMaterial();
      _nw14.__ctor();
      _578_testUnwrap = _nw14;
      Wrappers_Compile._IResult<IntermediateKeyWrapping_Compile._IIntermediateUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _579_intermediateUnwrapOutput;
      Wrappers_Compile._IResult<IntermediateKeyWrapping_Compile._IIntermediateUnwrapOutput<TestIntermediateKeyWrapping_Compile._ITestInfo>, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out244;
      _out244 = IntermediateKeyWrapping_Compile.__default.IntermediateUnwrap<TestIntermediateKeyWrapping_Compile._ITestInfo>(_578_testUnwrap, ((_577_intermediateWrapOutput).dtor_value).dtor_wrappedMaterial, TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE, _573_encCtx);
      _579_intermediateUnwrapOutput = _out244;
      if (!((_579_intermediateUnwrapOutput).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(74,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_577_intermediateWrapOutput).dtor_value).dtor_plaintextDataKey).Equals(((_579_intermediateUnwrapOutput).dtor_value).dtor_plaintextDataKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(75,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_577_intermediateWrapOutput).dtor_value).dtor_symmetricSigningKey).Equals(((_579_intermediateUnwrapOutput).dtor_value).dtor_symmetricSigningKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/test/TestIntermediateKeyWrapping.dfy(76,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo TEST__ALG__SUITE { get {
      return AlgorithmSuites_Compile.__default.DBE__ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384__SYMSIG__HMAC__SHA384;
    } }
    public static Dafny.ISequence<byte> PLAINTEXT__MAT { get {
      return ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim16 = new BigInteger((((TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE).dtor_encrypt).dtor_AES__GCM).dtor_keyLength);
        var arr16 = new byte[Dafny.Helpers.ToIntChecked(dim16, "array size exceeds memory limit")];
        for (int i16 = 0; i16 < dim16; i16++) {
          var _580___v0 = (BigInteger) i16;
          arr16[(int)(_580___v0)] = (byte)(1);
        }
        return Dafny.Sequence<byte>.FromArray(arr16);
      }))();
    } }
    public static Dafny.ISequence<byte> WRAPPED__MAT { get {
      return ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim17 = new BigInteger((((TestIntermediateKeyWrapping_Compile.__default.TEST__ALG__SUITE).dtor_encrypt).dtor_AES__GCM).dtor_keyLength);
        var arr17 = new byte[Dafny.Helpers.ToIntChecked(dim17, "array size exceeds memory limit")];
        for (int i17 = 0; i17 < dim17; i17++) {
          var _581___v1 = (BigInteger) i17;
          arr17[(int)(_581___v1)] = (byte)(2);
        }
        return Dafny.Sequence<byte>.FromArray(arr17);
      }))();
    } }
  }
} // end of namespace TestIntermediateKeyWrapping_Compile
namespace CleanupItems_Compile {

  public partial class __default {
    public static void DeleteVersion(Dafny.ISequence<char> branchKeyIdentifier, Dafny.ISequence<char> branchKeyVersion, software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient ddbClient)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _582___v0;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out245;
      _out245 = (ddbClient).DeleteItem(software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteItemInput.create(Fixtures_Compile.__default.branchKeyStoreName, Dafny.Map<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>.FromElements(new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Structure_Compile.__default.BRANCH__KEY__IDENTIFIER__FIELD, software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(branchKeyIdentifier)), new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Structure_Compile.__default.TYPE__FIELD, software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(Dafny.Sequence<char>.Concat(Structure_Compile.__default.BRANCH__KEY__TYPE__PREFIX, branchKeyVersion)))), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IExpectedAttributeValue>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IConditionalOperator>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnValue>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnConsumedCapacity>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnItemCollectionMetrics>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>>.create_None()));
      _582___v0 = _out245;
    }
    public static void DeleteActive(Dafny.ISequence<char> branchKeyIdentifier, software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient ddbClient)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _583___v1;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out246;
      _out246 = (ddbClient).DeleteItem(software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteItemInput.create(Fixtures_Compile.__default.branchKeyStoreName, Dafny.Map<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>.FromElements(new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Structure_Compile.__default.BRANCH__KEY__IDENTIFIER__FIELD, software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(branchKeyIdentifier)), new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Structure_Compile.__default.TYPE__FIELD, software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(Structure_Compile.__default.BRANCH__KEY__ACTIVE__TYPE))), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IExpectedAttributeValue>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IConditionalOperator>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnValue>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnConsumedCapacity>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnItemCollectionMetrics>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>>.create_None()));
      _583___v1 = _out246;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _584___v2;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IDeleteItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out247;
      _out247 = (ddbClient).DeleteItem(software.amazon.cryptography.services.dynamodb.internaldafny.types.DeleteItemInput.create(Fixtures_Compile.__default.branchKeyStoreName, Dafny.Map<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>.FromElements(new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Structure_Compile.__default.BRANCH__KEY__IDENTIFIER__FIELD, software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(branchKeyIdentifier)), new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Structure_Compile.__default.TYPE__FIELD, software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(Structure_Compile.__default.BEACON__KEY__TYPE__VALUE))), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IExpectedAttributeValue>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IConditionalOperator>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnValue>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnConsumedCapacity>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnItemCollectionMetrics>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>>.create_None()));
      _584___v2 = _out247;
    }
  }
} // end of namespace CleanupItems_Compile
namespace TestVersionKey_Compile {

  public partial class __default {
    public static void TestVersionKey()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _585_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _586_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out248;
      _out248 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _586_valueOrError0 = _out248;
      if (!(!((_586_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(25,18): " + _586_valueOrError0);}
      _585_kmsClient = (_586_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _587_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _588_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out249;
      _out249 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _588_valueOrError1 = _out249;
      if (!(!((_588_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(26,18): " + _588_valueOrError1);}
      _587_ddbClient = (_588_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _589_kmsConfig;
      _589_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _590_keyStoreConfig;
      _590_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _589_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_587_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_585_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _591_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _592_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out250;
      _out250 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_590_keyStoreConfig);
      _592_valueOrError2 = _out250;
      if (!(!((_592_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(39,17): " + _592_valueOrError2);}
      _591_keyStore = (_592_valueOrError2).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput _593_branchKeyId;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _594_valueOrError3 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.CreateKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out251;
      _out251 = (_591_keyStore).CreateKey(software.amazon.cryptography.keystore.internaldafny.types.CreateKeyInput.create(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>.create_None()));
      _594_valueOrError3 = _out251;
      if (!(!((_594_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(44,20): " + _594_valueOrError3);}
      _593_branchKeyId = (_594_valueOrError3).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput _595_oldActiveResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _596_valueOrError4 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out252;
      _out252 = (_591_keyStore).GetActiveBranchKey(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput.create((_593_branchKeyId).dtor_branchKeyIdentifier));
      _596_valueOrError4 = _out252;
      if (!(!((_596_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(49,24): " + _596_valueOrError4);}
      _595_oldActiveResult = (_596_valueOrError4).Extract();
      Dafny.ISequence<char> _597_oldActiveVersion;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _598_valueOrError5 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _598_valueOrError5 = UTF8.__default.Decode(((_595_oldActiveResult).dtor_branchKeyMaterials).dtor_branchKeyVersion);
      if (!(!((_598_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(54,25): " + _598_valueOrError5);}
      _597_oldActiveVersion = (_598_valueOrError5).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyOutput _599_versionKeyResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _600_valueOrError6 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.VersionKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out253;
      _out253 = (_591_keyStore).VersionKey(software.amazon.cryptography.keystore.internaldafny.types.VersionKeyInput.create((_593_branchKeyId).dtor_branchKeyIdentifier));
      _600_valueOrError6 = _out253;
      if (!(!((_600_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(56,25): " + _600_valueOrError6);}
      _599_versionKeyResult = (_600_valueOrError6).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput _601_getBranchKeyVersionResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _602_valueOrError7 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out254;
      _out254 = (_591_keyStore).GetBranchKeyVersion(software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionInput.create((_593_branchKeyId).dtor_branchKeyIdentifier, _597_oldActiveVersion));
      _602_valueOrError7 = _out254;
      if (!(!((_602_valueOrError7).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(61,34): " + _602_valueOrError7);}
      _601_getBranchKeyVersionResult = (_602_valueOrError7).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput _603_newActiveResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _604_valueOrError8 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out255;
      _out255 = (_591_keyStore).GetActiveBranchKey(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput.create((_593_branchKeyId).dtor_branchKeyIdentifier));
      _604_valueOrError8 = _out255;
      if (!(!((_604_valueOrError8).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(69,24): " + _604_valueOrError8);}
      _603_newActiveResult = (_604_valueOrError8).Extract();
      Dafny.ISequence<char> _605_newActiveVersion;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _606_valueOrError9 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _606_valueOrError9 = UTF8.__default.Decode(((_603_newActiveResult).dtor_branchKeyMaterials).dtor_branchKeyVersion);
      if (!(!((_606_valueOrError9).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(74,25): " + _606_valueOrError9);}
      _605_newActiveVersion = (_606_valueOrError9).Extract();
      CleanupItems_Compile.__default.DeleteVersion((_593_branchKeyId).dtor_branchKeyIdentifier, _605_newActiveVersion, _587_ddbClient);
      CleanupItems_Compile.__default.DeleteVersion((_593_branchKeyId).dtor_branchKeyIdentifier, _597_oldActiveVersion, _587_ddbClient);
      CleanupItems_Compile.__default.DeleteActive((_593_branchKeyId).dtor_branchKeyIdentifier, _587_ddbClient);
      if (!((((_601_getBranchKeyVersionResult).dtor_branchKeyMaterials).dtor_branchKeyVersion).Equals(((_595_oldActiveResult).dtor_branchKeyMaterials).dtor_branchKeyVersion))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(84,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_601_getBranchKeyVersionResult).dtor_branchKeyMaterials).dtor_branchKey).Equals(((_595_oldActiveResult).dtor_branchKeyMaterials).dtor_branchKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(85,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(!(((_601_getBranchKeyVersionResult).dtor_branchKeyMaterials).dtor_branchKeyVersion).Equals(((_603_newActiveResult).dtor_branchKeyMaterials).dtor_branchKeyVersion))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(87,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(!(((_601_getBranchKeyVersionResult).dtor_branchKeyMaterials).dtor_branchKey).Equals(((_603_newActiveResult).dtor_branchKeyMaterials).dtor_branchKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(88,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void InsertingADuplicateVersionWillFail()
    {
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _607_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _608_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out256;
      _out256 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _608_valueOrError0 = _out256;
      if (!(!((_608_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(93,18): " + _608_valueOrError0);}
      _607_ddbClient = (_608_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> _609_encryptionContext;
      _609_encryptionContext = Structure_Compile.__default.DecryptOnlyBranchKeyEncryptionContext(Fixtures_Compile.__default.branchKeyId, Fixtures_Compile.__default.branchKeyIdActiveVersion, Dafny.Sequence<char>.FromString(""), Dafny.Sequence<char>.FromString(""), Fixtures_Compile.__default.keyArn, Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.FromElements());
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _610_output;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out257;
      _out257 = DDBKeystoreOperations_Compile.__default.WriteNewBranchKeyVersionToKeystore(Structure_Compile.__default.ToAttributeMap(_609_encryptionContext, Dafny.Sequence<byte>.FromElements((byte)(1))), Structure_Compile.__default.ToAttributeMap(Structure_Compile.__default.ActiveBranchKeyEncryptionContext(_609_encryptionContext), Dafny.Sequence<byte>.FromElements((byte)(2))), Fixtures_Compile.__default.branchKeyStoreName, _607_ddbClient);
      _610_output = _out257;
      if (!((_610_output).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(111,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void VersioningANonexistentBranchKeyWillFail()
    {
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _611_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _612_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out258;
      _out258 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _612_valueOrError0 = _out258;
      if (!(!((_612_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(116,18): " + _612_valueOrError0);}
      _611_ddbClient = (_612_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> _613_encryptionContext;
      _613_encryptionContext = Structure_Compile.__default.DecryptOnlyBranchKeyEncryptionContext(Dafny.Sequence<char>.FromString("!= branchKeyId"), Fixtures_Compile.__default.branchKeyIdActiveVersion, Dafny.Sequence<char>.FromString(""), Dafny.Sequence<char>.FromString(""), Fixtures_Compile.__default.keyArn, Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.FromElements());
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _614_output;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out259;
      _out259 = DDBKeystoreOperations_Compile.__default.WriteNewBranchKeyVersionToKeystore(Structure_Compile.__default.ToAttributeMap(_613_encryptionContext, Dafny.Sequence<byte>.FromElements((byte)(1))), Structure_Compile.__default.ToAttributeMap(Structure_Compile.__default.ActiveBranchKeyEncryptionContext(_613_encryptionContext), Dafny.Sequence<byte>.FromElements((byte)(2))), Fixtures_Compile.__default.branchKeyStoreName, _611_ddbClient);
      _614_output = _out259;
      if (!((_614_output).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestVersionKey.dfy(134,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestVersionKey_Compile
namespace TestCreateKeys_Compile {

  public partial class __default {
    public static void TestCreateBranchAndBeaconKeys()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _615_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _616_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out260;
      _out260 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _616_valueOrError0 = _out260;
      if (!(!((_616_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(25,18): " + _616_valueOrError0);}
      _615_kmsClient = (_616_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _617_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _618_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out261;
      _out261 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _618_valueOrError1 = _out261;
      if (!(!((_618_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(26,18): " + _618_valueOrError1);}
      _617_ddbClient = (_618_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _619_kmsConfig;
      _619_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _620_keyStoreConfig;
      _620_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _619_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_617_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_615_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _621_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _622_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out262;
      _out262 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_620_keyStoreConfig);
      _622_valueOrError2 = _out262;
      if (!(!((_622_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(39,17): " + _622_valueOrError2);}
      _621_keyStore = (_622_valueOrError2).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput _623_branchKeyId;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _624_valueOrError3 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.CreateKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out263;
      _out263 = (_621_keyStore).CreateKey(software.amazon.cryptography.keystore.internaldafny.types.CreateKeyInput.create(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>.create_None()));
      _624_valueOrError3 = _out263;
      if (!(!((_624_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(41,20): " + _624_valueOrError3);}
      _623_branchKeyId = (_624_valueOrError3).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput _625_beaconKeyResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _626_valueOrError4 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out264;
      _out264 = (_621_keyStore).GetBeaconKey(software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyInput.create((_623_branchKeyId).dtor_branchKeyIdentifier));
      _626_valueOrError4 = _out264;
      if (!(!((_626_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(46,24): " + _626_valueOrError4);}
      _625_beaconKeyResult = (_626_valueOrError4).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput _627_activeResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _628_valueOrError5 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out265;
      _out265 = (_621_keyStore).GetActiveBranchKey(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput.create((_623_branchKeyId).dtor_branchKeyIdentifier));
      _628_valueOrError5 = _out265;
      if (!(!((_628_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(51,21): " + _628_valueOrError5);}
      _627_activeResult = (_628_valueOrError5).Extract();
      Dafny.ISequence<char> _629_branchKeyVersion;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _630_valueOrError6 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _630_valueOrError6 = UTF8.__default.Decode(((_627_activeResult).dtor_branchKeyMaterials).dtor_branchKeyVersion);
      if (!(!((_630_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(56,25): " + _630_valueOrError6);}
      _629_branchKeyVersion = (_630_valueOrError6).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput _631_versionResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _632_valueOrError7 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out266;
      _out266 = (_621_keyStore).GetBranchKeyVersion(software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionInput.create((_623_branchKeyId).dtor_branchKeyIdentifier, _629_branchKeyVersion));
      _632_valueOrError7 = _out266;
      if (!(!((_632_valueOrError7).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(57,22): " + _632_valueOrError7);}
      _631_versionResult = (_632_valueOrError7).Extract();
      CleanupItems_Compile.__default.DeleteVersion((_623_branchKeyId).dtor_branchKeyIdentifier, _629_branchKeyVersion, _617_ddbClient);
      CleanupItems_Compile.__default.DeleteActive((_623_branchKeyId).dtor_branchKeyIdentifier, _617_ddbClient);
      if (!((((_625_beaconKeyResult).dtor_beaconKeyMaterials).dtor_beaconKey).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(69,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((new BigInteger(((((_625_beaconKeyResult).dtor_beaconKeyMaterials).dtor_beaconKey).dtor_value).Count)) == (new BigInteger(32)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(70,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((new BigInteger((((_627_activeResult).dtor_branchKeyMaterials).dtor_branchKey).Count)) == (new BigInteger(32)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(71,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_631_versionResult).dtor_branchKeyMaterials).dtor_branchKey).Equals(((_627_activeResult).dtor_branchKeyMaterials).dtor_branchKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(72,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((((_631_versionResult).dtor_branchKeyMaterials).dtor_branchKeyIdentifier).Equals(((_627_activeResult).dtor_branchKeyMaterials).dtor_branchKeyIdentifier)) && ((((_627_activeResult).dtor_branchKeyMaterials).dtor_branchKeyIdentifier).Equals(((_625_beaconKeyResult).dtor_beaconKeyMaterials).dtor_beaconKeyIdentifier)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(73,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_631_versionResult).dtor_branchKeyMaterials).dtor_branchKeyVersion).Equals(((_627_activeResult).dtor_branchKeyMaterials).dtor_branchKeyVersion))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(76,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<byte> _633_idByteUUID;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _634_valueOrError8 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      _634_valueOrError8 = UUID.__default.ToByteArray(((_627_activeResult).dtor_branchKeyMaterials).dtor_branchKeyIdentifier);
      if (!(!((_634_valueOrError8).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(83,19): " + _634_valueOrError8);}
      _633_idByteUUID = (_634_valueOrError8).Extract();
      Dafny.ISequence<char> _635_idRoundTrip;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _636_valueOrError9 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _636_valueOrError9 = UUID.__default.FromByteArray(_633_idByteUUID);
      if (!(!((_636_valueOrError9).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(84,20): " + _636_valueOrError9);}
      _635_idRoundTrip = (_636_valueOrError9).Extract();
      if (!((_635_idRoundTrip).Equals(((_627_activeResult).dtor_branchKeyMaterials).dtor_branchKeyIdentifier))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(85,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<char> _637_versionString;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _638_valueOrError10 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _638_valueOrError10 = UTF8.__default.Decode(((_627_activeResult).dtor_branchKeyMaterials).dtor_branchKeyVersion);
      if (!(!((_638_valueOrError10).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(91,22): " + _638_valueOrError10);}
      _637_versionString = (_638_valueOrError10).Extract();
      Dafny.ISequence<byte> _639_versionByteUUID;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _640_valueOrError11 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      _640_valueOrError11 = UUID.__default.ToByteArray(_637_versionString);
      if (!(!((_640_valueOrError11).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(92,24): " + _640_valueOrError11);}
      _639_versionByteUUID = (_640_valueOrError11).Extract();
      Dafny.ISequence<char> _641_versionRoundTrip;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _642_valueOrError12 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _642_valueOrError12 = UUID.__default.FromByteArray(_639_versionByteUUID);
      if (!(!((_642_valueOrError12).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(93,25): " + _642_valueOrError12);}
      _641_versionRoundTrip = (_642_valueOrError12).Extract();
      if (!((_641_versionRoundTrip).Equals(_637_versionString))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(94,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestCreateOptions()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _643_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _644_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out267;
      _out267 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _644_valueOrError0 = _out267;
      if (!(!((_644_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(100,18): " + _644_valueOrError0);}
      _643_kmsClient = (_644_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _645_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _646_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out268;
      _out268 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _646_valueOrError1 = _out268;
      if (!(!((_646_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(101,18): " + _646_valueOrError1);}
      _645_ddbClient = (_646_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _647_kmsConfig;
      _647_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _648_keyStoreConfig;
      _648_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _647_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_645_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_643_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _649_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _650_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out269;
      _out269 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_648_keyStoreConfig);
      _650_valueOrError2 = _out269;
      if (!(!((_650_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(114,17): " + _650_valueOrError2);}
      _649_keyStore = (_650_valueOrError2).Extract();
      Dafny.ISequence<char> _651_id;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _652_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _out270;
      _out270 = UUID.__default.GenerateUUID();
      _652_valueOrError3 = _out270;
      if (!(!((_652_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(117,11): " + _652_valueOrError3);}
      _651_id = (_652_valueOrError3).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _653_encryptionContext;
      Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>> _654_valueOrError4 = Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.Default(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty);
      Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>> _out271;
      _out271 = TestCreateKeys_Compile.__default.EncodeEncryptionContext(Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.FromElements(new Dafny.Pair<Dafny.ISequence<char>, Dafny.ISequence<char>>(Dafny.Sequence<char>.FromString("some"), Dafny.Sequence<char>.FromString("encryption")), new Dafny.Pair<Dafny.ISequence<char>, Dafny.ISequence<char>>(Dafny.Sequence<char>.FromString("context"), Dafny.Sequence<char>.FromString("values"))));
      _654_valueOrError4 = _out271;
      if (!(!((_654_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(119,26): " + _654_valueOrError4);}
      _653_encryptionContext = (_654_valueOrError4).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput _655_branchKeyId;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _656_valueOrError5 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.CreateKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out272;
      _out272 = (_649_keyStore).CreateKey(software.amazon.cryptography.keystore.internaldafny.types.CreateKeyInput.create(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(_651_id), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>.create_Some(_653_encryptionContext)));
      _656_valueOrError5 = _out272;
      if (!(!((_656_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(124,20): " + _656_valueOrError5);}
      _655_branchKeyId = (_656_valueOrError5).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput _657_beaconKeyResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _658_valueOrError6 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out273;
      _out273 = (_649_keyStore).GetBeaconKey(software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyInput.create((_655_branchKeyId).dtor_branchKeyIdentifier));
      _658_valueOrError6 = _out273;
      if (!(!((_658_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(129,24): " + _658_valueOrError6);}
      _657_beaconKeyResult = (_658_valueOrError6).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput _659_activeResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _660_valueOrError7 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out274;
      _out274 = (_649_keyStore).GetActiveBranchKey(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput.create((_655_branchKeyId).dtor_branchKeyIdentifier));
      _660_valueOrError7 = _out274;
      if (!(!((_660_valueOrError7).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(134,21): " + _660_valueOrError7);}
      _659_activeResult = (_660_valueOrError7).Extract();
      Dafny.ISequence<char> _661_branchKeyVersion;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _662_valueOrError8 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _662_valueOrError8 = UTF8.__default.Decode(((_659_activeResult).dtor_branchKeyMaterials).dtor_branchKeyVersion);
      if (!(!((_662_valueOrError8).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(139,25): " + _662_valueOrError8);}
      _661_branchKeyVersion = (_662_valueOrError8).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput _663_versionResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _664_valueOrError9 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out275;
      _out275 = (_649_keyStore).GetBranchKeyVersion(software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionInput.create((_655_branchKeyId).dtor_branchKeyIdentifier, _661_branchKeyVersion));
      _664_valueOrError9 = _out275;
      if (!(!((_664_valueOrError9).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(140,22): " + _664_valueOrError9);}
      _663_versionResult = (_664_valueOrError9).Extract();
      CleanupItems_Compile.__default.DeleteVersion((_655_branchKeyId).dtor_branchKeyIdentifier, _661_branchKeyVersion, _645_ddbClient);
      CleanupItems_Compile.__default.DeleteActive((_655_branchKeyId).dtor_branchKeyIdentifier, _645_ddbClient);
      if (!((((_651_id).Equals(((_663_versionResult).dtor_branchKeyMaterials).dtor_branchKeyIdentifier)) && ((((_663_versionResult).dtor_branchKeyMaterials).dtor_branchKeyIdentifier).Equals(((_659_activeResult).dtor_branchKeyMaterials).dtor_branchKeyIdentifier))) && ((((_659_activeResult).dtor_branchKeyMaterials).dtor_branchKeyIdentifier).Equals(((_657_beaconKeyResult).dtor_beaconKeyMaterials).dtor_beaconKeyIdentifier)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(153,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_653_encryptionContext).Equals(((_663_versionResult).dtor_branchKeyMaterials).dtor_encryptionContext)) && ((((_663_versionResult).dtor_branchKeyMaterials).dtor_encryptionContext).Equals(((_659_activeResult).dtor_branchKeyMaterials).dtor_encryptionContext))) && ((((_659_activeResult).dtor_branchKeyMaterials).dtor_encryptionContext).Equals(((_657_beaconKeyResult).dtor_beaconKeyMaterials).dtor_encryptionContext)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(158,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestCreateDuplicate()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _665_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _666_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out276;
      _out276 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _666_valueOrError0 = _out276;
      if (!(!((_666_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(167,18): " + _666_valueOrError0);}
      _665_kmsClient = (_666_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _667_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _668_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out277;
      _out277 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _668_valueOrError1 = _out277;
      if (!(!((_668_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(168,18): " + _668_valueOrError1);}
      _667_ddbClient = (_668_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _669_kmsConfig;
      _669_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _670_keyStoreConfig;
      _670_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _669_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_667_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_665_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _671_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _672_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out278;
      _out278 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_670_keyStoreConfig);
      _672_valueOrError2 = _out278;
      if (!(!((_672_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(181,17): " + _672_valueOrError2);}
      _671_keyStore = (_672_valueOrError2).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _673_attempt;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out279;
      _out279 = (_671_keyStore).CreateKey(software.amazon.cryptography.keystore.internaldafny.types.CreateKeyInput.create(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(Fixtures_Compile.__default.branchKeyId), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>.create_None()));
      _673_attempt = _out279;
      if (!((_673_attempt).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(188,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void InsertingADuplicateWillFail()
    {
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _674_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _675_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out280;
      _out280 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _675_valueOrError0 = _out280;
      if (!(!((_675_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(193,18): " + _675_valueOrError0);}
      _674_ddbClient = (_675_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> _676_encryptionContext;
      _676_encryptionContext = Structure_Compile.__default.DecryptOnlyBranchKeyEncryptionContext(Fixtures_Compile.__default.branchKeyId, Fixtures_Compile.__default.branchKeyIdActiveVersion, Dafny.Sequence<char>.FromString(""), Dafny.Sequence<char>.FromString(""), Fixtures_Compile.__default.keyArn, Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.FromElements());
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _677_output;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out281;
      _out281 = DDBKeystoreOperations_Compile.__default.WriteNewKeyToStore(Structure_Compile.__default.ToAttributeMap(_676_encryptionContext, Dafny.Sequence<byte>.FromElements((byte)(1))), Structure_Compile.__default.ToAttributeMap(Structure_Compile.__default.ActiveBranchKeyEncryptionContext(_676_encryptionContext), Dafny.Sequence<byte>.FromElements((byte)(2))), Structure_Compile.__default.ToAttributeMap(Structure_Compile.__default.BeaconKeyEncryptionContext(_676_encryptionContext), Dafny.Sequence<byte>.FromElements((byte)(3))), Fixtures_Compile.__default.branchKeyStoreName, _674_ddbClient);
      _677_output = _out281;
      if (!((_677_output).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(212,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void InsertingADuplicateWillWithADifferentVersionFail()
    {
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _678_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _679_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out282;
      _out282 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _679_valueOrError0 = _out282;
      if (!(!((_679_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(217,18): " + _679_valueOrError0);}
      _678_ddbClient = (_679_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> _680_encryptionContext;
      _680_encryptionContext = Structure_Compile.__default.DecryptOnlyBranchKeyEncryptionContext(Fixtures_Compile.__default.branchKeyId, Dafny.Sequence<char>.FromString("!= branchKeyIdActiveVersion"), Dafny.Sequence<char>.FromString(""), Dafny.Sequence<char>.FromString(""), Fixtures_Compile.__default.keyArn, Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.FromElements());
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _681_output;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._ITransactWriteItemsOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out283;
      _out283 = DDBKeystoreOperations_Compile.__default.WriteNewKeyToStore(Structure_Compile.__default.ToAttributeMap(_680_encryptionContext, Dafny.Sequence<byte>.FromElements((byte)(1))), Structure_Compile.__default.ToAttributeMap(Structure_Compile.__default.ActiveBranchKeyEncryptionContext(_680_encryptionContext), Dafny.Sequence<byte>.FromElements((byte)(2))), Structure_Compile.__default.ToAttributeMap(Structure_Compile.__default.BeaconKeyEncryptionContext(_680_encryptionContext), Dafny.Sequence<byte>.FromElements((byte)(3))), Fixtures_Compile.__default.branchKeyStoreName, _678_ddbClient);
      _681_output = _out283;
      if (!((_681_output).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeys.dfy(236,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>> EncodeEncryptionContext(Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> input)
    {
      Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>> output = Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.Default(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty);
      Dafny.ISet<_System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>>> _682_encodedEncryptionContext;
      _682_encodedEncryptionContext = Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>, Dafny.ISet<_System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>>>>>((_683_input) => ((System.Func<Dafny.ISet<_System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>>>>)(() => {
        var _coll0 = new System.Collections.Generic.List<_System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>>>();
        foreach (Dafny.ISequence<char> _compr_0 in (_683_input).Keys.Elements) {
          Dafny.ISequence<char> _684_k = (Dafny.ISequence<char>)_compr_0;
          if ((_683_input).Contains(_684_k)) {
            _coll0.Add(_System.Tuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>>.create(UTF8.__default.Encode(_684_k), UTF8.__default.Encode(Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.Select(_683_input,_684_k)), _684_k));
          }
        }
        return Dafny.Set<_System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>>>.FromCollection(_coll0);
      }))())(input);
      Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _685_valueOrError0 = Wrappers_Compile.Outcome<Dafny.ISequence<char>>.Default();
      _685_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(Dafny.Helpers.Id<Func<Dafny.ISet<_System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>>>, bool>>((_686_encodedEncryptionContext) => Dafny.Helpers.Quantifier<_System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>>>((_686_encodedEncryptionContext).Elements, true, (((_forall_var_0) => {
        _System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>> _687_i = (_System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>>)_forall_var_0;
        return !((_686_encodedEncryptionContext).Contains(_687_i)) || (((((_687_i).dtor__0).is_Success) && (((_687_i).dtor__1).is_Success)) && (Dafny.Helpers.Let<Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>>, bool>(UTF8.__default.Decode(((_687_i).dtor__0).dtor_value), _pat_let17_0 => Dafny.Helpers.Let<Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>>, bool>(_pat_let17_0, _688_encoded => ((_688_encoded).is_Success) && (((_687_i).dtor__2).Equals((_688_encoded).dtor_value))))));
      }))))(_682_encodedEncryptionContext), Dafny.Sequence<char>.FromString("Unable to encode string"));
      if ((_685_valueOrError0).IsFailure()) {
        output = (_685_valueOrError0).PropagateFailure<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>();
        return output;
      }
      output = Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Success(Dafny.Helpers.Id<Func<Dafny.ISet<_System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>>>, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>>((_689_encodedEncryptionContext) => ((System.Func<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>)(() => {
  var _coll1 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>();
  foreach (_System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>> _compr_1 in (_689_encodedEncryptionContext).Elements) {
    _System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>> _690_i = (_System._ITuple3<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Dafny.ISequence<char>>)_compr_1;
    if ((_689_encodedEncryptionContext).Contains(_690_i)) {
      _coll1.Add(new Dafny.Pair<Dafny.ISequence<byte>,Dafny.ISequence<byte>>(((_690_i).dtor__0).dtor_value, ((_690_i).dtor__1).dtor_value));
    }
  }
  return Dafny.Map<Dafny.ISequence<byte>,Dafny.ISequence<byte>>.FromCollection(_coll1);
}))())(_682_encodedEncryptionContext));
      return output;
    }
  }
} // end of namespace TestCreateKeys_Compile
namespace TestGetKeys_Compile {

  public partial class __default {
    public static void TestGetBeaconKey()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _691_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _692_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out284;
      _out284 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _692_valueOrError0 = _out284;
      if (!(!((_692_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(21,18): " + _692_valueOrError0);}
      _691_kmsClient = (_692_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _693_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _694_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out285;
      _out285 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _694_valueOrError1 = _out285;
      if (!(!((_694_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(22,18): " + _694_valueOrError1);}
      _693_ddbClient = (_694_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _695_kmsConfig;
      _695_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _696_keyStoreConfig;
      _696_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _695_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_693_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_691_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _697_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _698_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out286;
      _out286 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_696_keyStoreConfig);
      _698_valueOrError2 = _out286;
      if (!(!((_698_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(35,17): " + _698_valueOrError2);}
      _697_keyStore = (_698_valueOrError2).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput _699_beaconKeyResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _700_valueOrError3 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out287;
      _out287 = (_697_keyStore).GetBeaconKey(software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyInput.create(Fixtures_Compile.__default.branchKeyId));
      _700_valueOrError3 = _out287;
      if (!(!((_700_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(37,24): " + _700_valueOrError3);}
      _699_beaconKeyResult = (_700_valueOrError3).Extract();
      if (!((((_699_beaconKeyResult).dtor_beaconKeyMaterials).dtor_beaconKeyIdentifier).Equals(Fixtures_Compile.__default.branchKeyId))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(41,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_699_beaconKeyResult).dtor_beaconKeyMaterials).dtor_beaconKey).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(42,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((new BigInteger(((((_699_beaconKeyResult).dtor_beaconKeyMaterials).dtor_beaconKey).dtor_value).Count)) == (new BigInteger(32)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(43,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestGetActiveKey()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _701_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _702_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out288;
      _out288 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _702_valueOrError0 = _out288;
      if (!(!((_702_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(48,18): " + _702_valueOrError0);}
      _701_kmsClient = (_702_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _703_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _704_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out289;
      _out289 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _704_valueOrError1 = _out289;
      if (!(!((_704_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(49,18): " + _704_valueOrError1);}
      _703_ddbClient = (_704_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _705_kmsConfig;
      _705_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _706_keyStoreConfig;
      _706_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _705_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_703_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_701_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _707_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _708_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out290;
      _out290 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_706_keyStoreConfig);
      _708_valueOrError2 = _out290;
      if (!(!((_708_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(62,17): " + _708_valueOrError2);}
      _707_keyStore = (_708_valueOrError2).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput _709_activeResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _710_valueOrError3 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out291;
      _out291 = (_707_keyStore).GetActiveBranchKey(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput.create(Fixtures_Compile.__default.branchKeyId));
      _710_valueOrError3 = _out291;
      if (!(!((_710_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(64,21): " + _710_valueOrError3);}
      _709_activeResult = (_710_valueOrError3).Extract();
      if (!((((_709_activeResult).dtor_branchKeyMaterials).dtor_branchKeyIdentifier).Equals(Fixtures_Compile.__default.branchKeyId))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(69,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((((_709_activeResult).dtor_branchKeyMaterials).dtor_branchKeyVersion).Equals(Fixtures_Compile.__default.branchKeyIdActiveVersionUtf8Bytes))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(70,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((new BigInteger((((_709_activeResult).dtor_branchKeyMaterials).dtor_branchKey).Count)) == (new BigInteger(32)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(71,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestGetBranchKeyVersion()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _711_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _712_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out292;
      _out292 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _712_valueOrError0 = _out292;
      if (!(!((_712_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(76,18): " + _712_valueOrError0);}
      _711_kmsClient = (_712_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _713_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _714_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out293;
      _out293 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _714_valueOrError1 = _out293;
      if (!(!((_714_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(77,18): " + _714_valueOrError1);}
      _713_ddbClient = (_714_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _715_kmsConfig;
      _715_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _716_keyStoreConfig;
      _716_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _715_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_713_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_711_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _717_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _718_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out294;
      _out294 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_716_keyStoreConfig);
      _718_valueOrError2 = _out294;
      if (!(!((_718_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(90,17): " + _718_valueOrError2);}
      _717_keyStore = (_718_valueOrError2).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput _719_versionResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _720_valueOrError3 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out295;
      _out295 = (_717_keyStore).GetBranchKeyVersion(software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionInput.create(Fixtures_Compile.__default.branchKeyId, Fixtures_Compile.__default.branchKeyIdActiveVersion));
      _720_valueOrError3 = _out295;
      if (!(!((_720_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(92,22): " + _720_valueOrError3);}
      _719_versionResult = (_720_valueOrError3).Extract();
      Dafny.ISequence<byte> _721_testBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _722_valueOrError4 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _722_valueOrError4 = UTF8.__default.Encode(Fixtures_Compile.__default.branchKeyIdActiveVersion);
      if (!(!((_722_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(98,18): " + _722_valueOrError4);}
      _721_testBytes = (_722_valueOrError4).Extract();
      if (!((((_719_versionResult).dtor_branchKeyMaterials).dtor_branchKeyIdentifier).Equals(Fixtures_Compile.__default.branchKeyId))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(100,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((((_719_versionResult).dtor_branchKeyMaterials).dtor_branchKeyVersion).Equals(Fixtures_Compile.__default.branchKeyIdActiveVersionUtf8Bytes)) && ((Fixtures_Compile.__default.branchKeyIdActiveVersionUtf8Bytes).Equals(_721_testBytes)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(101,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((new BigInteger((((_719_versionResult).dtor_branchKeyMaterials).dtor_branchKey).Count)) == (new BigInteger(32)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(102,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestGetActiveKeyWithIncorrectKmsKeyArn()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _723_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _724_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out296;
      _out296 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _724_valueOrError0 = _out296;
      if (!(!((_724_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(107,18): " + _724_valueOrError0);}
      _723_kmsClient = (_724_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _725_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _726_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out297;
      _out297 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _726_valueOrError1 = _out297;
      if (!(!((_726_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(108,18): " + _726_valueOrError1);}
      _725_ddbClient = (_726_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _727_kmsConfig;
      _727_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.mkrKeyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _728_keyStoreConfig;
      _728_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _727_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_725_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_723_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _729_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _730_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out298;
      _out298 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_728_keyStoreConfig);
      _730_valueOrError2 = _out298;
      if (!(!((_730_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(121,17): " + _730_valueOrError2);}
      _729_keyStore = (_730_valueOrError2).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _731_activeResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out299;
      _out299 = (_729_keyStore).GetActiveBranchKey(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput.create(Fixtures_Compile.__default.branchKeyId));
      _731_activeResult = _out299;
      if (!((_731_activeResult).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(128,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestGetActiveKeyWrongLogicalKeyStoreName()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _732_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _733_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out300;
      _out300 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _733_valueOrError0 = _out300;
      if (!(!((_733_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(132,18): " + _733_valueOrError0);}
      _732_kmsClient = (_733_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _734_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _735_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out301;
      _out301 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _735_valueOrError1 = _out301;
      if (!(!((_735_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(133,18): " + _735_valueOrError1);}
      _734_ddbClient = (_735_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _736_kmsConfig;
      _736_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _737_keyStoreConfig;
      _737_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _736_kmsConfig, TestGetKeys_Compile.__default.incorrectLogicalName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_734_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_732_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _738_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _739_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out302;
      _out302 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_737_keyStoreConfig);
      _739_valueOrError2 = _out302;
      if (!(!((_739_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(146,17): " + _739_valueOrError2);}
      _738_keyStore = (_739_valueOrError2).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _740_activeResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out303;
      _out303 = (_738_keyStore).GetActiveBranchKey(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput.create(Fixtures_Compile.__default.branchKeyId));
      _740_activeResult = _out303;
      if (!((_740_activeResult).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(153,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestGetActiveKeyWithNoClients()
    {
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _741_kmsConfig;
      _741_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _742_keyStoreConfig;
      _742_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _741_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_None());
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _743_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _744_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out304;
      _out304 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_742_keyStoreConfig);
      _744_valueOrError0 = _out304;
      if (!(!((_744_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(169,17): " + _744_valueOrError0);}
      _743_keyStore = (_744_valueOrError0).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput _745_activeResult;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _746_valueOrError1 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out305;
      _out305 = (_743_keyStore).GetActiveBranchKey(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput.create(Fixtures_Compile.__default.branchKeyId));
      _746_valueOrError1 = _out305;
      if (!(!((_746_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(171,21): " + _746_valueOrError1);}
      _745_activeResult = (_746_valueOrError1).Extract();
      if (!((new BigInteger((((_745_activeResult).dtor_branchKeyMaterials).dtor_branchKey).Count)) == (new BigInteger(32)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestGetKeys.dfy(176,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static Dafny.ISequence<char> incorrectLogicalName { get {
      return Dafny.Sequence<char>.FromString("MySuperAwesomeTableName");
    } }
  }
} // end of namespace TestGetKeys_Compile
namespace TestConfig_Compile {

  public partial class __default {
    public static void TestInvalidKmsKeyArnConfig()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _747_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _748_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out306;
      _out306 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _748_valueOrError0 = _out306;
      if (!(!((_748_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(18,18): " + _748_valueOrError0);}
      _747_kmsClient = (_748_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _749_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _750_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out307;
      _out307 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _750_valueOrError1 = _out307;
      if (!(!((_750_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(19,18): " + _750_valueOrError1);}
      _749_ddbClient = (_750_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _751_kmsConfig;
      _751_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyId);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _752_keyStoreConfig;
      _752_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _751_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_749_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_747_kmsClient));
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _753_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out308;
      _out308 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_752_keyStoreConfig);
      _753_keyStore = _out308;
      if (!((_753_keyStore).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(33,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(object.Equals((_753_keyStore).dtor_error, software.amazon.cryptography.keystore.internaldafny.types.Error.create_KeyStoreException(Dafny.Sequence<char>.FromString("Invalid AWS KMS Key Arn"))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(34,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestValidConfig()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _754_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _755_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out309;
      _out309 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _755_valueOrError0 = _out309;
      if (!(!((_755_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(38,18): " + _755_valueOrError0);}
      _754_kmsClient = (_755_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _756_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _757_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out310;
      _out310 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _757_valueOrError1 = _out310;
      if (!(!((_757_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(39,18): " + _757_valueOrError1);}
      _756_ddbClient = (_757_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _758_kmsConfig;
      _758_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _759_keyStoreConfig;
      _759_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _758_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_756_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_754_kmsClient));
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _760_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out311;
      _out311 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_759_keyStoreConfig);
      _760_keyStore = _out311;
      if (!((_760_keyStore).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(53,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.keystore.internaldafny.types._IGetKeyStoreInfoOutput _761_conf;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetKeyStoreInfoOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _762_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetKeyStoreInfoOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetKeyStoreInfoOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out312;
      _out312 = ((_760_keyStore).dtor_value).GetKeyStoreInfo();
      _762_valueOrError2 = _out312;
      if (!(!((_762_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(55,13): " + _762_valueOrError2);}
      _761_conf = (_762_valueOrError2).Extract();
      Dafny.ISequence<byte> _763_idByteUUID;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _764_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      _764_valueOrError3 = UUID.__default.ToByteArray((_761_conf).dtor_keyStoreId);
      if (!(!((_764_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(60,19): " + _764_valueOrError3);}
      _763_idByteUUID = (_764_valueOrError3).Extract();
      Dafny.ISequence<char> _765_idRoundTrip;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _766_valueOrError4 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _766_valueOrError4 = UUID.__default.FromByteArray(_763_idByteUUID);
      if (!(!((_766_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(61,20): " + _766_valueOrError4);}
      _765_idRoundTrip = (_766_valueOrError4).Extract();
      if (!((_765_idRoundTrip).Equals((_761_conf).dtor_keyStoreId))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(62,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((_761_conf).dtor_keyStoreName).Equals(Fixtures_Compile.__default.branchKeyStoreName))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(64,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((_761_conf).dtor_logicalKeyStoreName).Equals(Fixtures_Compile.__default.logicalKeyStoreName))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(65,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(object.Equals((_761_conf).dtor_kmsConfiguration, _758_kmsConfig))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(66,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestValidConfigNoClients()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _767_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _768_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out313;
      _out313 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _768_valueOrError0 = _out313;
      if (!(!((_768_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(71,18): " + _768_valueOrError0);}
      _767_kmsClient = (_768_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _769_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _770_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out314;
      _out314 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _770_valueOrError1 = _out314;
      if (!(!((_770_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(72,18): " + _770_valueOrError1);}
      _769_ddbClient = (_770_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _771_kmsConfig;
      _771_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _772_keyStoreConfig;
      _772_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _771_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_769_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_None());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _773_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out315;
      _out315 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_772_keyStoreConfig);
      _773_keyStore = _out315;
      if (!((_773_keyStore).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(86,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _772_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _771_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_767_kmsClient));
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out316;
      _out316 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_772_keyStoreConfig);
      _773_keyStore = _out316;
      if (!((_773_keyStore).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(99,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _772_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _771_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_None());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out317;
      _out317 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_772_keyStoreConfig);
      _773_keyStore = _out317;
      if (!((_773_keyStore).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestConfig.dfy(112,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestConfig_Compile
namespace TestCreateKeyStore_Compile {

  public partial class __default {
    public static void TestCreateKeyStore()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _774_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _775_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out318;
      _out318 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _775_valueOrError0 = _out318;
      if (!(!((_775_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeyStore.dfy(19,18): " + _775_valueOrError0);}
      _774_kmsClient = (_775_valueOrError0).Extract();
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _776_ddbClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _777_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out319;
      _out319 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _777_valueOrError1 = _out319;
      if (!(!((_777_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeyStore.dfy(20,18): " + _777_valueOrError1);}
      _776_ddbClient = (_777_valueOrError1).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._IKMSConfiguration _778_kmsConfig;
      _778_kmsConfig = software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration.create(Fixtures_Compile.__default.keyArn);
      software.amazon.cryptography.keystore.internaldafny.types._IKeyStoreConfig _779_keyStoreConfig;
      _779_keyStoreConfig = software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig.create(Fixtures_Compile.__default.branchKeyStoreName, _778_kmsConfig, Fixtures_Compile.__default.logicalKeyStoreName, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient>.create_Some(_776_ddbClient), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_774_kmsClient));
      software.amazon.cryptography.keystore.internaldafny.KeyStoreClient _780_keyStore;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _781_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.KeyStoreClient, software.amazon.cryptography.keystore.internaldafny.types._IError> _out320;
      _out320 = software.amazon.cryptography.keystore.internaldafny.__default.KeyStore(_779_keyStoreConfig);
      _781_valueOrError2 = _out320;
      if (!(!((_781_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeyStore.dfy(33,17): " + _781_valueOrError2);}
      _780_keyStore = (_781_valueOrError2).Extract();
      software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreOutput _782_keyStoreArn;
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _783_valueOrError3 = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreOutput.Default());
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> _out321;
      _out321 = (_780_keyStore).CreateKeyStore(software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreInput.create());
      _783_valueOrError3 = _out321;
      if (!(!((_783_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeyStore.dfy(36,20): " + _783_valueOrError3);}
      _782_keyStoreArn = (_783_valueOrError3).Extract();
      if (!((AwsArnParsing_Compile.__default.ParseAmazonDynamodbTableName((_782_keyStoreArn).dtor_tableArn)).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeyStore.dfy(38,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((AwsArnParsing_Compile.__default.ParseAmazonDynamodbTableName((_782_keyStoreArn).dtor_tableArn)).dtor_value).Equals(Fixtures_Compile.__default.branchKeyStoreName))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/test/TestCreateKeyStore.dfy(39,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestCreateKeyStore_Compile
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
      bool _784_success;
      _784_success = true;
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestStormTracker.StormTrackerBasics: ")));
      try {
        {
          TestStormTracker_Compile.__default.StormTrackerBasics();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _785_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_785_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestStormTracker.StormTrackerFanOut: ")));
      try {
        {
          TestStormTracker_Compile.__default.StormTrackerFanOut();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _786_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_786_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestStormTracker.StormTrackerTTL: ")));
      try {
        {
          TestStormTracker_Compile.__default.StormTrackerTTL();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _787_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_787_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestStormTracker.StormTrackerGraceInterval: ")));
      try {
        {
          TestStormTracker_Compile.__default.StormTrackerGraceInterval();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _788_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_788_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestStormTracker.StormTrackerGracePeriod: ")));
      try {
        {
          TestStormTracker_Compile.__default.StormTrackerGracePeriod();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _789_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_789_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestLocalCMC.LocalCMCBasics: ")));
      try {
        {
          TestLocalCMC_Compile.__default.LocalCMCBasics();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _790_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_790_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsKmsEncryptedDataKeyFilter.TestFailsNonKeyResource: ")));
      try {
        {
          TestAwsKmsEncryptedDataKeyFilter_Compile.__default.TestFailsNonKeyResource();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _791_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_791_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsKmsEncryptedDataKeyFilter.TestMatchesKeyringsConfiguration: ")));
      try {
        {
          TestAwsKmsEncryptedDataKeyFilter_Compile.__default.TestMatchesKeyringsConfiguration();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _792_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_792_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsKmsHierarchicalKeyring.TestHierarchyClientESDKSuite: ")));
      try {
        {
          TestAwsKmsHierarchicalKeyring_Compile.__default.TestHierarchyClientESDKSuite();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _793_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_793_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsKmsHierarchicalKeyring.TestHierarchyClientDBESuite: ")));
      try {
        {
          TestAwsKmsHierarchicalKeyring_Compile.__default.TestHierarchyClientDBESuite();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _794_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_794_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsKmsHierarchicalKeyring.TestBranchKeyIdSupplier: ")));
      try {
        {
          TestAwsKmsHierarchicalKeyring_Compile.__default.TestBranchKeyIdSupplier();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _795_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_795_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsKmsRsaKeyring.TestKmsRsaRoundtrip: ")));
      try {
        {
          TestAwsKmsRsaKeyring_Compile.__default.TestKmsRsaRoundtrip();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _796_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_796_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestAwsKmsRsaKeyring.TestKmsRsaWithAsymmetricSignatureFails: ")));
      try {
        {
          TestAwsKmsRsaKeyring_Compile.__default.TestKmsRsaWithAsymmetricSignatureFails();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _797_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_797_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestRawRSAKeying.TestOnEncryptOnDecryptSuppliedDataKey: ")));
      try {
        {
          TestRawRSAKeying_Compile.__default.TestOnEncryptOnDecryptSuppliedDataKey();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _798_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_798_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestRawRSAKeying.TestOnDecryptKeyNameMismatch: ")));
      try {
        {
          TestRawRSAKeying_Compile.__default.TestOnDecryptKeyNameMismatch();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _799_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_799_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestRawRSAKeying.TestOnDecryptFailure: ")));
      try {
        {
          TestRawRSAKeying_Compile.__default.TestOnDecryptFailure();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _800_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_800_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestRawRSAKeying.TestOnDecryptBadAndGoodEdkSucceeds: ")));
      try {
        {
          TestRawRSAKeying_Compile.__default.TestOnDecryptBadAndGoodEdkSucceeds();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _801_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_801_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestMultiKeyring.TestHappyCase: ")));
      try {
        {
          TestMultiKeyring_Compile.__default.TestHappyCase();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _802_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_802_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestMultiKeyring.TestChildKeyringFailureEncrypt: ")));
      try {
        {
          TestMultiKeyring_Compile.__default.TestChildKeyringFailureEncrypt();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _803_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_803_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestMultiKeyring.TestGeneratorKeyringFails: ")));
      try {
        {
          TestMultiKeyring_Compile.__default.TestGeneratorKeyringFails();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _804_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_804_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestMultiKeyring.TestGeneratorKeyringDoesNotReturnPlaintextDataKey: ")));
      try {
        {
          TestMultiKeyring_Compile.__default.TestGeneratorKeyringDoesNotReturnPlaintextDataKey();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _805_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_805_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestMultiKeyring.TestGeneratorAbleToDecrypt: ")));
      try {
        {
          TestMultiKeyring_Compile.__default.TestGeneratorAbleToDecrypt();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _806_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_806_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestMultiKeyring.TestGeneratorUnableToDecrypt: ")));
      try {
        {
          TestMultiKeyring_Compile.__default.TestGeneratorUnableToDecrypt();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _807_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_807_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestMultiKeyring.TestCollectFailuresDecrypt: ")));
      try {
        {
          TestMultiKeyring_Compile.__default.TestCollectFailuresDecrypt();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _808_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_808_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestRawAESKeyring.TestOnEncryptOnDecryptGenerateDataKey: ")));
      try {
        {
          TestRawAESKeyring_Compile.__default.TestOnEncryptOnDecryptGenerateDataKey();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _809_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_809_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestRawAESKeyring.TestOnEncryptOnDecryptSuppliedDataKey: ")));
      try {
        {
          TestRawAESKeyring_Compile.__default.TestOnEncryptOnDecryptSuppliedDataKey();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _810_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_810_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestRawAESKeyring.TestOnDecryptKeyNameMismatch: ")));
      try {
        {
          TestRawAESKeyring_Compile.__default.TestOnDecryptKeyNameMismatch();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _811_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_811_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestRawAESKeyring.TestOnDecryptBadAndGoodEdkSucceeds: ")));
      try {
        {
          TestRawAESKeyring_Compile.__default.TestOnDecryptBadAndGoodEdkSucceeds();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _812_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_812_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestRawAESKeyring.TestOnDecryptNoEDKs: ")));
      try {
        {
          TestRawAESKeyring_Compile.__default.TestOnDecryptNoEDKs();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _813_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_813_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestRawAESKeyring.TestOnEncryptUnserializableEC: ")));
      try {
        {
          TestRawAESKeyring_Compile.__default.TestOnEncryptUnserializableEC();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _814_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_814_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestRawAESKeyring.TestOnDecryptUnserializableEC: ")));
      try {
        {
          TestRawAESKeyring_Compile.__default.TestOnDecryptUnserializableEC();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _815_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_815_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestDefaultClientProvider.GetUsWestTwo: ")));
      try {
        {
          TestDefaultClientProvider_Compile.__default.GetUsWestTwo();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _816_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_816_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestIntermediateKeyWrapping.IntermediateWrapUnwrapTest: ")));
      try {
        {
          TestIntermediateKeyWrapping_Compile.__default.IntermediateWrapUnwrapTest();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _817_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_817_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestIntermediateKeyWrapping.IntermediateGenerateAndWrapUnwrapTest: ")));
      try {
        {
          TestIntermediateKeyWrapping_Compile.__default.IntermediateGenerateAndWrapUnwrapTest();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _818_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_818_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestVersionKey.TestVersionKey: ")));
      try {
        {
          TestVersionKey_Compile.__default.TestVersionKey();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _819_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_819_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestVersionKey.InsertingADuplicateVersionWillFail: ")));
      try {
        {
          TestVersionKey_Compile.__default.InsertingADuplicateVersionWillFail();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _820_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_820_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestVersionKey.VersioningANonexistentBranchKeyWillFail: ")));
      try {
        {
          TestVersionKey_Compile.__default.VersioningANonexistentBranchKeyWillFail();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _821_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_821_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestCreateKeys.TestCreateBranchAndBeaconKeys: ")));
      try {
        {
          TestCreateKeys_Compile.__default.TestCreateBranchAndBeaconKeys();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _822_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_822_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestCreateKeys.TestCreateOptions: ")));
      try {
        {
          TestCreateKeys_Compile.__default.TestCreateOptions();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _823_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_823_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestCreateKeys.TestCreateDuplicate: ")));
      try {
        {
          TestCreateKeys_Compile.__default.TestCreateDuplicate();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _824_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_824_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestCreateKeys.InsertingADuplicateWillFail: ")));
      try {
        {
          TestCreateKeys_Compile.__default.InsertingADuplicateWillFail();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _825_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_825_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestCreateKeys.InsertingADuplicateWillWithADifferentVersionFail: ")));
      try {
        {
          TestCreateKeys_Compile.__default.InsertingADuplicateWillWithADifferentVersionFail();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _826_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_826_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestGetKeys.TestGetBeaconKey: ")));
      try {
        {
          TestGetKeys_Compile.__default.TestGetBeaconKey();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _827_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_827_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestGetKeys.TestGetActiveKey: ")));
      try {
        {
          TestGetKeys_Compile.__default.TestGetActiveKey();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _828_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_828_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestGetKeys.TestGetBranchKeyVersion: ")));
      try {
        {
          TestGetKeys_Compile.__default.TestGetBranchKeyVersion();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _829_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_829_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestGetKeys.TestGetActiveKeyWithIncorrectKmsKeyArn: ")));
      try {
        {
          TestGetKeys_Compile.__default.TestGetActiveKeyWithIncorrectKmsKeyArn();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _830_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_830_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestGetKeys.TestGetActiveKeyWrongLogicalKeyStoreName: ")));
      try {
        {
          TestGetKeys_Compile.__default.TestGetActiveKeyWrongLogicalKeyStoreName();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _831_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_831_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestGetKeys.TestGetActiveKeyWithNoClients: ")));
      try {
        {
          TestGetKeys_Compile.__default.TestGetActiveKeyWithNoClients();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _832_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_832_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestConfig.TestInvalidKmsKeyArnConfig: ")));
      try {
        {
          TestConfig_Compile.__default.TestInvalidKmsKeyArnConfig();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _833_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_833_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestConfig.TestValidConfig: ")));
      try {
        {
          TestConfig_Compile.__default.TestValidConfig();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _834_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_834_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestConfig.TestValidConfigNoClients: ")));
      try {
        {
          TestConfig_Compile.__default.TestValidConfigNoClients();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _835_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_835_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestCreateKeyStore.TestCreateKeyStore: ")));
      try {
        {
          TestCreateKeyStore_Compile.__default.TestCreateKeyStore();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _836_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_836_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _784_success = false;
        }
      }
      if (!(_784_success)) {
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
