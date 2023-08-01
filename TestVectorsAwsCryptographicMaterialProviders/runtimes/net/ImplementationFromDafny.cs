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
// Command Line Options: -stdin -noVerify -vcsCores:2 -compileTarget:cs -spillTargetCode:3 -compile:0 -optimizeErasableDatatypeWrapper:0 -quantifierSyntax:3 -unicodeChar:0 -functionSyntax:3 -useRuntimeLib -out runtimes/net/ImplementationFromDafny -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/StandardLibrary/src/Index.dfy -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographyPrimitives/src/Index.dfy -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/ComAmazonawsKms/src/Index.dfy -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/ComAmazonawsDynamodb/src/Index.dfy -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/src/Index.dfy -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/AwsCryptographicMaterialProviders/dafny/AwsCryptographyKeyStore/src/Index.dfy
// the_program

















































































































module {:extern ""software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny""} KeyVectors refines AbstractAwsCryptographyMaterialProvidersTestVectorKeysService {

  import Operations = KeysVectorOperations

  import API = JSON.API

  import Errors = JSON.Errors

  import FileIO

  import opened JSONHelpers

  import KeyMaterial

  import MaterialProviders
  class KeyVectorsClient ...  {
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
      History := new IKeyVectorsClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }

    const config: Operations.InternalConfig

    predicate CreateTestVectorKeyringEnsuresPublicly(input: TestVectorKeyringInput, output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      decreases input, output
    {
      Operations.CreateTestVectorKeyringEnsuresPublicly(input, output)
    }

    method CreateTestVectorKeyring(input: TestVectorKeyringInput) returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateTestVectorKeyring
      ensures ValidState() && (output.Success? ==> output.value.ValidState() && output.value.Modifies !! {History} && fresh(output.value) && fresh(output.value.Modifies - Modifies - {History}))
      ensures CreateTestVectorKeyringEnsuresPublicly(input, output)
      ensures History.CreateTestVectorKeyring == old(History.CreateTestVectorKeyring) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.CreateTestVectorKeyring(config, input);
      History.CreateTestVectorKeyring := History.CreateTestVectorKeyring + [DafnyCallEvent(input, output)];
    }

    predicate CreateWappedTestVectorKeyringEnsuresPublicly(input: TestVectorKeyringInput, output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      decreases input, output
    {
      Operations.CreateWappedTestVectorKeyringEnsuresPublicly(input, output)
    }

    method CreateWappedTestVectorKeyring(input: TestVectorKeyringInput) returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateWappedTestVectorKeyring
      ensures ValidState() && (output.Success? ==> output.value.ValidState() && output.value.Modifies !! {History} && fresh(output.value) && fresh(output.value.Modifies - Modifies - {History}))
      ensures CreateWappedTestVectorKeyringEnsuresPublicly(input, output)
      ensures History.CreateWappedTestVectorKeyring == old(History.CreateWappedTestVectorKeyring) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.CreateWappedTestVectorKeyring(config, input);
      History.CreateWappedTestVectorKeyring := History.CreateWappedTestVectorKeyring + [DafnyCallEvent(input, output)];
    }

    function method GetKeyDescription(input: GetKeyDescriptionInput): (output: Result<GetKeyDescriptionOutput, Error>)
      decreases input
    {
      Operations.GetKeyDescription(config, input)
    }

    function method SerializeKeyDescription(input: SerializeKeyDescriptionInput): (output: Result<SerializeKeyDescriptionOutput, Error>)
      decreases input
    {
      Operations.SerializeKeyDescription(config, input)
    }
  }

  function method DefaultKeyVectorsConfig(): KeyVectorsConfig
  {
    KeyVectorsConfig(keyManifiestPath := """")
  }

  method KeyVectors(config: KeyVectorsConfig := DefaultKeyVectorsConfig()) returns (res: Result<KeyVectorsClient, Error>)
    ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
    decreases config
  {
    var keysManifestBv :- expect FileIO.ReadBytesFromFile(config.keyManifiestPath);
    var keysManifestBytes := BvToBytes(keysManifestBv);
    var keysManifestJSON :- API.Deserialize(keysManifestBytes).MapFailure((e: Errors.DeserializationError) => KeyVectorException(message := e.ToString()));
    expect keysManifestJSON.Object?, ""expectation violation""
    var keysObject :- expect Get(""keys"", keysManifestJSON.obj);
    expect keysObject.Object?, ""expectation violation""
    var maybeMpl := MaterialProviders.MaterialProviders();
    var mpl :- maybeMpl.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
    var keys :- KeyMaterial.BuildKeyMaterials(mpl, keysObject.obj).MapFailure((e: string) => KeyVectorException(message := e));
    var config := Operations.Config(keys := keys);
    var client := new KeyVectorsClient(config);
    res := Success(client);
  }

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = AwsCryptographyMaterialProvidersTestVectorKeysTypes
}

module {:options ""-functionSyntax:4""} KeysVectorOperations refines AbstractAwsCryptographyMaterialProvidersTestVectorKeysOperations {

  import API = JSON.API

  import Errors = JSON.Errors

  import Values = JSON.Values

  import KeyDescription

  import MPL = AwsCryptographyMaterialProvidersTypes

  import KeyMaterial

  import KeyringFromKeyDescription

  import WrappedMaterialProviders

  import MaterialProviders
  datatype Config = Config(keys: map<string, KeyMaterial.KeyMaterial>)

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

  predicate method CreateTestVectorKeyringEnsuresPublicly(input: TestVectorKeyringInput, output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
    decreases input, output
  {
    true
  }

  method CreateTestVectorKeyring(config: InternalConfig, input: TestVectorKeyringInput) returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures ValidInternalConfig?(config) && (output.Success? ==> output.value.ValidState() && fresh(output.value) && fresh(output.value.Modifies - ModifiesInternalConfig(config)))
    ensures CreateTestVectorKeyringEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    var keyDescription := input.keyDescription;
    var keyId := GetKeyId(keyDescription);
    var info := KeyringFromKeyDescription.KeyringInfo(keyDescription, if keyId in config.keys then Some(config.keys[keyId]) else None);
    var maybeMpl := MaterialProviders.MaterialProviders();
    var mpl :- maybeMpl.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
    output := KeyringFromKeyDescription.ToKeyring(mpl, info);
  }

  predicate method CreateWappedTestVectorKeyringEnsuresPublicly(input: TestVectorKeyringInput, output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
    decreases input, output
  {
    true
  }

  method CreateWappedTestVectorKeyring(config: InternalConfig, input: TestVectorKeyringInput) returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures ValidInternalConfig?(config) && (output.Success? ==> output.value.ValidState() && fresh(output.value) && fresh(output.value.Modifies - ModifiesInternalConfig(config)))
    ensures CreateWappedTestVectorKeyringEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    var keyDescription := input.keyDescription;
    var keyId := GetKeyId(keyDescription);
    var info := KeyringFromKeyDescription.KeyringInfo(keyDescription, if keyId in config.keys then Some(config.keys[keyId]) else None);
    var maybeMpl := WrappedMaterialProviders.WrappedMaterialProviders();
    var wrappedMPL :- maybeMpl.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
    output := KeyringFromKeyDescription.ToKeyring(wrappedMPL, info);
  }

  function method GetKeyDescription(config: InternalConfig, input: GetKeyDescriptionInput): (output: Result<GetKeyDescriptionOutput, Error>)
    decreases config, input
  {
    var keyDescriptionJSON: Values.JSON :- API.Deserialize(input.json).MapFailure((e: Errors.DeserializationError) => AwsCryptographyMaterialProviders(AwsCryptographyMaterialProvidersTypes.AwsCryptographicMaterialProvidersException(message := e.ToString()))); var keyDescription: KeyDescription :- KeyDescription.ToKeyDescription(keyDescriptionJSON).MapFailure((e: string) => AwsCryptographyMaterialProviders(AwsCryptographyMaterialProvidersTypes.AwsCryptographicMaterialProvidersException(message := e))); Success(GetKeyDescriptionOutput(keyDescription := keyDescription))
  }

  function method SerializeKeyDescription(config: InternalConfig, input: SerializeKeyDescriptionInput): (output: Result<SerializeKeyDescriptionOutput, Error>)
    decreases config, input
  {
    Failure(KeyVectorException(message := ""Not Supported""))
  }

  function method GetKeyId(input: Types.KeyDescription): string
    decreases input
  {
    match input
    case Kms(i) =>
      i.keyId
    case KmsMrk(i) =>
      i.keyId
    case KmsMrkDiscovery(i) =>
      i.keyId
    case RSA(i) =>
      i.keyId
    case AES(i) =>
      i.keyId
    case Static(i) =>
      i.keyId
    case Hierarchy(i) =>
      i.keyId
    case KmsRsa(i) =>
      i.keyId
  }

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = AwsCryptographyMaterialProvidersTestVectorKeysTypes
}

module {:extern ""software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types""} AwsCryptographyMaterialProvidersTestVectorKeysTypes {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import AwsCryptographyMaterialProvidersTypes

  import ComAmazonawsKmsTypes
  datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)

  datatype GetKeyDescriptionInput = GetKeyDescriptionInput(nameonly json: seq<uint8>)

  datatype GetKeyDescriptionOutput = GetKeyDescriptionOutput(nameonly keyDescription: KeyDescription)

  datatype HierarchyKeyring = HierarchyKeyring(nameonly keyId: string)

  datatype KeyDescription = Kms(Kms: KMSInfo) | KmsMrk(KmsMrk: KmsMrkAware) | KmsMrkDiscovery(KmsMrkDiscovery: KmsMrkAwareDiscovery) | RSA(RSA: RawRSA) | AES(AES: RawAES) | Static(Static: StaticKeyring) | KmsRsa(KmsRsa: KmsRsaKeyring) | Hierarchy(Hierarchy: HierarchyKeyring)

  class IKeyVectorsClientCallHistory {
    ghost constructor ()
    {
      CreateTestVectorKeyring := [];
      CreateWappedTestVectorKeyring := [];
      GetKeyDescription := [];
      SerializeKeyDescription := [];
    }

    ghost var CreateTestVectorKeyring: seq<DafnyCallEvent<TestVectorKeyringInput, Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>>>
    ghost var CreateWappedTestVectorKeyring: seq<DafnyCallEvent<TestVectorKeyringInput, Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>>>
    ghost var GetKeyDescription: seq<DafnyCallEvent<GetKeyDescriptionInput, Result<GetKeyDescriptionOutput, Error>>>
    ghost var SerializeKeyDescription: seq<DafnyCallEvent<SerializeKeyDescriptionInput, Result<SerializeKeyDescriptionOutput, Error>>>
  }

  trait {:termination false} IKeyVectorsClient {
    ghost const Modifies: set<object>

    predicate ValidState()
      ensures ValidState() ==> History in Modifies

    ghost const History: IKeyVectorsClientCallHistory

    predicate CreateTestVectorKeyringEnsuresPublicly(input: TestVectorKeyringInput, output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      decreases input, output

    method CreateTestVectorKeyring(input: TestVectorKeyringInput) returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateTestVectorKeyring
      ensures ValidState() && (output.Success? ==> output.value.ValidState() && output.value.Modifies !! {History} && fresh(output.value) && fresh(output.value.Modifies - Modifies - {History}))
      ensures CreateTestVectorKeyringEnsuresPublicly(input, output)
      ensures History.CreateTestVectorKeyring == old(History.CreateTestVectorKeyring) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate CreateWappedTestVectorKeyringEnsuresPublicly(input: TestVectorKeyringInput, output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      decreases input, output

    method CreateWappedTestVectorKeyring(input: TestVectorKeyringInput) returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateWappedTestVectorKeyring
      ensures ValidState() && (output.Success? ==> output.value.ValidState() && output.value.Modifies !! {History} && fresh(output.value) && fresh(output.value.Modifies - Modifies - {History}))
      ensures CreateWappedTestVectorKeyringEnsuresPublicly(input, output)
      ensures History.CreateWappedTestVectorKeyring == old(History.CreateWappedTestVectorKeyring) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    function method GetKeyDescription(input: GetKeyDescriptionInput): (output: Result<GetKeyDescriptionOutput, Error>)
      decreases input

    function method SerializeKeyDescription(input: SerializeKeyDescriptionInput): (output: Result<SerializeKeyDescriptionOutput, Error>)
      decreases input
  }

  datatype KeyVectorsConfig = KeyVectorsConfig(nameonly keyManifiestPath: string)

  datatype KMSInfo = KMSInfo(nameonly keyId: string)

  datatype KmsMrkAware = KmsMrkAware(nameonly keyId: string)

  datatype KmsMrkAwareDiscovery = KmsMrkAwareDiscovery(nameonly keyId: string, nameonly defaultMrkRegion: string, nameonly awsKmsDiscoveryFilter: Option<AwsCryptographyMaterialProvidersTypes.DiscoveryFilter>)

  datatype KmsRsaKeyring = KmsRsaKeyring(nameonly keyId: string, nameonly encryptionAlgorithm: ComAmazonawsKmsTypes.EncryptionAlgorithmSpec)

  datatype RawAES = RawAES(nameonly keyId: string, nameonly providerId: string)

  datatype RawRSA = RawRSA(nameonly keyId: string, nameonly providerId: string, nameonly padding: AwsCryptographyMaterialProvidersTypes.PaddingScheme)

  datatype SerializeKeyDescriptionInput = SerializeKeyDescriptionInput(nameonly keyDescription: KeyDescription)

  datatype SerializeKeyDescriptionOutput = SerializeKeyDescriptionOutput(nameonly json: seq<uint8>)

  datatype StaticKeyring = StaticKeyring(nameonly keyId: string)

  datatype TestVectorKeyringInput = TestVectorKeyringInput(nameonly keyDescription: KeyDescription)

  datatype Error = KeyVectorException(nameonly message: string) | AwsCryptographyMaterialProviders(AwsCryptographyMaterialProviders: AwsCryptographyMaterialProvidersTypes.Error) | ComAmazonawsKms(ComAmazonawsKms: ComAmazonawsKmsTypes.Error) | CollectionOfErrors(list: seq<Error>, nameonly message: string) | Opaque(obj: object)

  type OpaqueError = e: Error
    | e.Opaque?
    witness *
}

abstract module AbstractAwsCryptographyMaterialProvidersTestVectorKeysService {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = AwsCryptographyMaterialProvidersTestVectorKeysTypes

  import Operations : AbstractAwsCryptographyMaterialProvidersTestVectorKeysOperations
  class KeyVectorsClient extends IKeyVectorsClient {
    constructor (config: Operations.InternalConfig)
      requires Operations.ValidInternalConfig?(config)
      ensures ValidState() && fresh(History) && this.config == config

    const config: Operations.InternalConfig

    predicate ValidState()
      ensures ValidState() ==> Operations.ValidInternalConfig?(config) && History !in Operations.ModifiesInternalConfig(config) && Modifies == Operations.ModifiesInternalConfig(config) + {History}

    predicate CreateTestVectorKeyringEnsuresPublicly(input: TestVectorKeyringInput, output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      decreases input, output
    {
      Operations.CreateTestVectorKeyringEnsuresPublicly(input, output)
    }

    method CreateTestVectorKeyring(input: TestVectorKeyringInput) returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateTestVectorKeyring
      ensures ValidState() && (output.Success? ==> output.value.ValidState() && output.value.Modifies !! {History} && fresh(output.value) && fresh(output.value.Modifies - Modifies - {History}))
      ensures CreateTestVectorKeyringEnsuresPublicly(input, output)
      ensures History.CreateTestVectorKeyring == old(History.CreateTestVectorKeyring) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.CreateTestVectorKeyring(config, input);
      History.CreateTestVectorKeyring := History.CreateTestVectorKeyring + [DafnyCallEvent(input, output)];
    }

    predicate CreateWappedTestVectorKeyringEnsuresPublicly(input: TestVectorKeyringInput, output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      decreases input, output
    {
      Operations.CreateWappedTestVectorKeyringEnsuresPublicly(input, output)
    }

    method CreateWappedTestVectorKeyring(input: TestVectorKeyringInput) returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateWappedTestVectorKeyring
      ensures ValidState() && (output.Success? ==> output.value.ValidState() && output.value.Modifies !! {History} && fresh(output.value) && fresh(output.value.Modifies - Modifies - {History}))
      ensures CreateWappedTestVectorKeyringEnsuresPublicly(input, output)
      ensures History.CreateWappedTestVectorKeyring == old(History.CreateWappedTestVectorKeyring) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.CreateWappedTestVectorKeyring(config, input);
      History.CreateWappedTestVectorKeyring := History.CreateWappedTestVectorKeyring + [DafnyCallEvent(input, output)];
    }

    function method GetKeyDescription(input: GetKeyDescriptionInput): (output: Result<GetKeyDescriptionOutput, Error>)
      decreases input
    {
      Operations.GetKeyDescription(config, input)
    }

    function method SerializeKeyDescription(input: SerializeKeyDescriptionInput): (output: Result<SerializeKeyDescriptionOutput, Error>)
      decreases input
    {
      Operations.SerializeKeyDescription(config, input)
    }
  }

  function method DefaultKeyVectorsConfig(): KeyVectorsConfig

  method KeyVectors(config: KeyVectorsConfig := DefaultKeyVectorsConfig()) returns (res: Result<KeyVectorsClient, Error>)
    ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
    decreases config
}

abstract module AbstractAwsCryptographyMaterialProvidersTestVectorKeysOperations {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  type InternalConfig

  predicate ValidInternalConfig?(config: InternalConfig)

  function ModifiesInternalConfig(config: InternalConfig): set<object>

  predicate CreateTestVectorKeyringEnsuresPublicly(input: TestVectorKeyringInput, output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
    decreases input, output

  method CreateTestVectorKeyring(config: InternalConfig, input: TestVectorKeyringInput) returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures ValidInternalConfig?(config) && (output.Success? ==> output.value.ValidState() && fresh(output.value) && fresh(output.value.Modifies - ModifiesInternalConfig(config)))
    ensures CreateTestVectorKeyringEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate CreateWappedTestVectorKeyringEnsuresPublicly(input: TestVectorKeyringInput, output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
    decreases input, output

  method CreateWappedTestVectorKeyring(config: InternalConfig, input: TestVectorKeyringInput) returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures ValidInternalConfig?(config) && (output.Success? ==> output.value.ValidState() && fresh(output.value) && fresh(output.value.Modifies - ModifiesInternalConfig(config)))
    ensures CreateWappedTestVectorKeyringEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  function method GetKeyDescription(config: InternalConfig, input: GetKeyDescriptionInput): (output: Result<GetKeyDescriptionOutput, Error>)
    decreases input

  function method SerializeKeyDescription(config: InternalConfig, input: SerializeKeyDescriptionInput): (output: Result<SerializeKeyDescriptionOutput, Error>)
    decreases input
}

module {:extern ""software.amazon.cryptography.materialproviders.internaldafny.wrapped""} WrappedMaterialProviders refines WrappedAbstractAwsCryptographyMaterialProvidersService {

  import WrappedService = MaterialProviders
  function method WrappedDefaultMaterialProvidersConfig(): MaterialProvidersConfig
  {
    MaterialProvidersConfig
  }

  method {:extern} WrappedMaterialProviders(config: MaterialProvidersConfig := WrappedDefaultMaterialProvidersConfig()) returns (res: Result<IAwsCryptographicMaterialProvidersClient, Error>)
    ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
    decreases config

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = AwsCryptographyMaterialProvidersTypes
}

abstract module WrappedAbstractAwsCryptographyMaterialProvidersService {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = AwsCryptographyMaterialProvidersTypes

  import WrappedService : AbstractAwsCryptographyMaterialProvidersService
  function method WrappedDefaultMaterialProvidersConfig(): MaterialProvidersConfig

  method {:extern} WrappedMaterialProviders(config: MaterialProvidersConfig := WrappedDefaultMaterialProvidersConfig()) returns (res: Result<IAwsCryptographicMaterialProvidersClient, Error>)
    ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
    decreases config
}

module WrappedMaterialProvidersMain {

  import WrappedMaterialProviders

  import KeyringExpectations

  import CreateKeyrings

  import TestManifests
  method CheckKeyrings()
  {
    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    var all := CreateKeyrings.CreateAllEncryptDecryptKeyrings();
    for i: int := 0 to |all| {
      var keyring := all[i];
      KeyringExpectations.ExpectAlgorithmSuiteKeyringSuccess(mpl, keyring);
    }
  }

  method EncryptTestVectors()
  {
  }
}

module KeyringExpectations {

  import opened Wrappers

  import WrappedMaterialProviders

  import Types = AwsCryptographyMaterialProvidersTypes

  import opened TestVectorConstants

  import TestVectorsUtils
  datatype Materials = Materials(encryptionMaterials: Types.EncryptionMaterials, decryptionMaterials: Types.DecryptionMaterials)

  method ExpectAlgorithmSuiteKeyringSuccess(mpl: Types.IAwsCryptographicMaterialProvidersClient, keyring: Types.IKeyring)
    requires keyring.ValidState() && mpl.ValidState()
    modifies keyring.Modifies
    ensures keyring.ValidState() && mpl.ValidState()
    decreases mpl, keyring
  {
    var encryptionContext := TestVectorsUtils.SmallEncryptionContext(TestVectorsUtils.SmallEncryptionContextVariation.A);
    for i: int := 0 to |AllAlgorithmSuiteIds| {
      var algorithmSuiteId := AllAlgorithmSuiteIds[i];
      var encryptionMaterials := TestVectorsUtils.GetEncryptionMaterials(mpl, algorithmSuiteId, encryptionContext);
      var _ /* _v0 */ := ExpectKeyringSuccess(mpl, keyring, encryptionMaterials);
    }
  }

  method ExpectKeyringSuccess(mpl: Types.IAwsCryptographicMaterialProvidersClient, keyring: Types.IKeyring, encryptionMaterialsIn: Types.EncryptionMaterials)
      returns (results: Materials)
    requires keyring.ValidState()
    modifies keyring.Modifies
    ensures keyring.ValidState()
    ensures results.encryptionMaterials.plaintextDataKey == results.decryptionMaterials.plaintextDataKey
    decreases mpl, keyring, encryptionMaterialsIn
  {
    print ""\n ExpectKeyringSuccess:\n"", encryptionMaterialsIn.algorithmSuite.id;
    var encryptionMaterials := ExpectOnEncryptSuccess(mpl, keyring, encryptionMaterialsIn);
    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(Types.InitializeDecryptionMaterialsInput(algorithmSuiteId := encryptionMaterials.algorithmSuite.id, requiredEncryptionContextKeys := [], encryptionContext := encryptionMaterials.encryptionContext));
    var decryptionMaterials := ExpectOnDecryptSuccess(mpl, keyring, decryptionMaterialsIn, encryptionMaterials.encryptedDataKeys);
    expect encryptionMaterials.plaintextDataKey == decryptionMaterials.plaintextDataKey, ""expectation violation""
    results := Materials(encryptionMaterials, decryptionMaterials);
  }

  method ExpectOnEncryptSuccess(mpl: Types.IAwsCryptographicMaterialProvidersClient, keyring: Types.IKeyring, encryptionMaterialsIn: Types.EncryptionMaterials)
      returns (encryptionMaterials: Types.EncryptionMaterials)
    requires keyring.ValidState()
    modifies keyring.Modifies
    ensures keyring.ValidState()
    ensures mpl.ValidEncryptionMaterialsTransition(Types.ValidEncryptionMaterialsTransitionInput(start := encryptionMaterialsIn, stop := encryptionMaterials)).Success?
    ensures mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterials).Success?
    decreases mpl, keyring, encryptionMaterialsIn
  {
    var encryptionMaterialsOut :- expect keyring.OnEncrypt(Types.OnEncryptInput(materials := encryptionMaterialsIn));
    encryptionMaterials := encryptionMaterialsOut.materials;
    var _ /* _v1 */ :- expect mpl.ValidEncryptionMaterialsTransition(Types.ValidEncryptionMaterialsTransitionInput(start := encryptionMaterialsIn, stop := encryptionMaterials));
    var _ /* _v2 */ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterials);
    expect 1 <= |encryptionMaterialsOut.materials.encryptedDataKeys|, ""expectation violation""
  }

  method ExpectOnDecryptSuccess(mpl: Types.IAwsCryptographicMaterialProvidersClient, keyring: Types.IKeyring, decryptionMaterialsIn: Types.DecryptionMaterials, encryptedDataKeys: Types.EncryptedDataKeyList)
      returns (decryptionMaterials: Types.DecryptionMaterials)
    requires keyring.ValidState()
    modifies keyring.Modifies
    ensures keyring.ValidState()
    ensures mpl.ValidDecryptionMaterialsTransition(Types.ValidDecryptionMaterialsTransitionInput(start := decryptionMaterialsIn, stop := decryptionMaterials)).Success?
    ensures mpl.DecryptionMaterialsWithPlaintextDataKey(decryptionMaterials).Success?
    decreases mpl, keyring, decryptionMaterialsIn, encryptedDataKeys
  {
    var decryptionMaterialsOut :- expect keyring.OnDecrypt(Types.OnDecryptInput(materials := decryptionMaterialsIn, encryptedDataKeys := encryptedDataKeys));
    decryptionMaterials := decryptionMaterialsOut.materials;
    var _ /* _v3 */ :- expect mpl.ValidDecryptionMaterialsTransition(Types.ValidDecryptionMaterialsTransitionInput(start := decryptionMaterialsIn, stop := decryptionMaterials));
    var _ /* _v4 */ :- expect mpl.DecryptionMaterialsWithPlaintextDataKey(decryptionMaterials);
  }
}

module TestVectorsUtils {

  import opened StandardLibrary

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import UTF8

  import Types = AwsCryptographyMaterialProvidersTypes

  import WrappedMaterialProviders

  import Primitives = Aws.Cryptography.Primitives

  import Crypto = AwsCryptographyPrimitivesTypes

  import AlgorithmSuites
  datatype SmallEncryptionContextVariation = Empty | A | AB | BA

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

  method GetEncryptionMaterials(mpl: Types.IAwsCryptographicMaterialProvidersClient, algorithmSuiteId: Types.AlgorithmSuiteId, encryptionContext: Types.EncryptionContext)
      returns (encryptionMaterials: Types.EncryptionMaterials)
    decreases mpl, algorithmSuiteId, encryptionContext
  {
    var crypto :- expect Primitives.AtomicPrimitives();
    var suite := AlgorithmSuites.GetSuite(algorithmSuiteId);
    var signingKey: Option<seq<uint8>>;
    var verificationKey: Option<seq<uint8>>;
    if suite.signature.ECDSA? {
      var pair :- expect crypto.GenerateECDSASignatureKey(Crypto.GenerateECDSASignatureKeyInput(signatureAlgorithm := suite.signature.ECDSA.curve));
      signingKey := Some(pair.signingKey);
      verificationKey := Some(pair.verificationKey);
    } else {
      assert suite.signature.None?;
      signingKey := None;
      verificationKey := None;
    }
    encryptionMaterials :- expect mpl.InitializeEncryptionMaterials(Types.InitializeEncryptionMaterialsInput(algorithmSuiteId := algorithmSuiteId, encryptionContext := encryptionContext, requiredEncryptionContextKeys := [], signingKey := signingKey, verificationKey := verificationKey));
  }
}

module TestVectorConstants {

  import Types = AwsCryptographyMaterialProvidersTypes

  import TestVectorsUtils
  datatype EncryptDecryptKeyrings = AwsKmsKeyring | AwsKmsMultiKeyring | AwsKmsMrkKeyring | AwsKmsMrkMultiKeyring | RawAesKeyring | RawRsaKeyring

  const AllEncryptDecryptKeyrings := [AwsKmsKeyring, AwsKmsMultiKeyring, AwsKmsMrkKeyring, AwsKmsMrkMultiKeyring, RawAesKeyring, RawRsaKeyring]

  lemma AllEncryptDecryptKeyringsIsComplete(i: EncryptDecryptKeyrings)
    ensures AllSeqIsComplete(i, AllEncryptDecryptKeyrings)
    decreases i
  {
  }

  const AllAwsKMSKeys := [(""arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"", ""us-west-2"")]
  const AllESDKAlgorithmSuiteIds := [Types.ALG_AES_128_GCM_IV12_TAG16_NO_KDF, Types.ALG_AES_192_GCM_IV12_TAG16_NO_KDF, Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF, Types.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256, Types.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256, Types.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256, Types.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256, Types.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, Types.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY, Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384]

  lemma AllESDKAlgorithmSuiteIdsIsComplete(i: Types.ESDKAlgorithmSuiteId)
    ensures AllSeqIsComplete(i, AllESDKAlgorithmSuiteIds)
    decreases i
  {
  }

  const AllDBEAlgorithmSuiteIds := [Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384, Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384]

  lemma AllDBEAlgorithmSuiteIdsIsComplete(i: Types.DBEAlgorithmSuiteId)
    ensures AllSeqIsComplete(i, AllDBEAlgorithmSuiteIds)
    decreases i
  {
  }

  const AllAlgorithmSuiteIds := [Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_128_GCM_IV12_TAG16_NO_KDF), Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_192_GCM_IV12_TAG16_NO_KDF), Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF), Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256), Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA256), Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA256), Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256), Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384), Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384), Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY), Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384), Types.AlgorithmSuiteId.DBE(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_SYMSIG_HMAC_SHA384), Types.AlgorithmSuiteId.DBE(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384)]

  lemma AllAlgorithmSuiteIdsIsComplete(i: Types.AlgorithmSuiteId)
    ensures AllSeqIsComplete(i, AllAlgorithmSuiteIds)
    decreases i
  {
  }

  predicate AllSeqIsComplete<T>(i: T, all: seq<T>)
    decreases all
  {
    i in all &&
    forall i: nat, j: nat {:trigger all[j], all[i]} | 0 <= i < j < |all| :: 
      all[i] != all[j]
  }
}

module CreateKeyrings {

  import opened Wrappers

  import opened TestVectorConstants

  import CreateAwsKmsKeyrings

  import CreateAwsKmsMultiKeyrings

  import CreateAwsKmsMrkKeyrings

  import CreateAwsKmsMrkMultiKeyrings

  import CreateRawAesKeyrings

  import CreateRawRsaKeyrings
  method CreateAllEncryptDecryptKeyrings() returns (all: seq<Types.IKeyring>)
    ensures forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in all} | keyring in all :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
  {
    all := [];
    for i: int := 0 to |AllEncryptDecryptKeyrings|
      invariant forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in all} | keyring in all :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    {
      var keyringType := AllEncryptDecryptKeyrings[i];
      match keyringType
      case {:split false} AwsKmsKeyring() =>
        var allAwsKms := CreateAwsKmsKeyrings.CreateAllAwsKmsKeyring(keyringType);
        all := all + allAwsKms;
      case {:split false} AwsKmsMultiKeyring() =>
        var allAwsKms := CreateAwsKmsMultiKeyrings.CreateAllAwsKmsMultiKeyring(keyringType);
        all := all + allAwsKms;
      case {:split false} AwsKmsMrkKeyring() =>
        var allAwsKmsMrk := CreateAwsKmsMrkKeyrings.CreateAllAwsKmsMrkKeyring(keyringType);
        all := all + allAwsKmsMrk;
      case {:split false} AwsKmsMrkMultiKeyring() =>
        var allAwsKmsMrkMult := CreateAwsKmsMrkMultiKeyrings.CreateAllAwsKmsMrkMultiKeyring(keyringType);
        all := all + allAwsKmsMrkMult;
      case {:split false} RawAesKeyring() =>
        var allRSA := CreateRawAesKeyrings.CreateAllRawAesKeyring(keyringType);
        all := all + allRSA;
      case {:split false} RawRsaKeyring() =>
        var allAES := CreateRawRsaKeyrings.CreateAllRawRsaKeyring(keyringType);
        all := all + allAES;
    }
  }
}

module CreateAwsKmsKeyrings {

  import Types = AwsCryptographyMaterialProvidersTypes

  import WrappedMaterialProviders

  import opened Wrappers

  import TestVectorsUtils

  import opened TestVectorConstants
  method CreateAllAwsKmsKeyring(input: EncryptDecryptKeyrings) returns (allAwsKms: seq<Types.IKeyring>)
    requires input.AwsKmsKeyring?
    ensures forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allAwsKms} | keyring in allAwsKms :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases input
  {
    allAwsKms := [];
    for i: int := 0 to |AllAwsKMSKeys|
      invariant forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allAwsKms} | keyring in allAwsKms :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    {
      var (kmsKeyId, region) := AllAwsKMSKeys[i];
      var keyring := CreateAwsKmsKeyring(kmsKeyId, region);
      allAwsKms := allAwsKms + [keyring];
    }
  }

  method CreateAwsKmsKeyring(kmsKeyId: string, region: string) returns (keyring: Types.IKeyring)
    ensures keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases kmsKeyId, region
  {
    print ""\n CreateAwsKmsKeyring: "", kmsKeyId, "" "", region;
    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput);
    var kmsClient :- expect clientSupplier.GetClient(Types.GetClientInput(region := region));
    keyring :- expect mpl.CreateAwsKmsKeyring(Types.CreateAwsKmsKeyringInput(kmsKeyId := kmsKeyId, kmsClient := kmsClient, grantTokens := None));
  }
}

module CreateAwsKmsMultiKeyrings {

  import Types = AwsCryptographyMaterialProvidersTypes

  import WrappedMaterialProviders

  import opened Wrappers

  import TestVectorsUtils

  import opened TestVectorConstants
  method CreateAllAwsKmsMultiKeyring(input: EncryptDecryptKeyrings) returns (allAwsKmsMrkMult: seq<Types.IKeyring>)
    requires input.AwsKmsMultiKeyring?
    ensures forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allAwsKmsMrkMult} | keyring in allAwsKmsMrkMult :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases input
  {
    allAwsKmsMrkMult := [];
    for i: int := 0 to |AllAwsKMSKeys|
      invariant forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allAwsKmsMrkMult} | keyring in allAwsKmsMrkMult :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    {
      var (kmsKeyId, _ /* _v0 */) := AllAwsKMSKeys[i];
      var keyring := CreateAwsKmsMultiKeyring(Some(kmsKeyId), None);
      allAwsKmsMrkMult := allAwsKmsMrkMult + [keyring];
    }
  }

  method CreateAwsKmsMultiKeyring(kmsKeyId: Option<Types.KmsKeyId>, kmsKeyIds: Option<Types.KmsKeyIdList>) returns (keyring: Types.IKeyring)
    ensures keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases kmsKeyId, kmsKeyIds
  {
    print ""\n CreateAwsKmsMultiKeyring: "", kmsKeyId, "" "", kmsKeyIds;
    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    keyring :- expect mpl.CreateAwsKmsMultiKeyring(Types.CreateAwsKmsMultiKeyringInput(generator := kmsKeyId, kmsKeyIds := kmsKeyIds, clientSupplier := None, grantTokens := None));
  }
}

module CreateAwsKmsMrkKeyrings {

  import Types = AwsCryptographyMaterialProvidersTypes

  import WrappedMaterialProviders

  import opened Wrappers

  import TestVectorsUtils

  import opened TestVectorConstants
  method CreateAllAwsKmsMrkKeyring(input: EncryptDecryptKeyrings) returns (allAwsKmsMrk: seq<Types.IKeyring>)
    requires input.AwsKmsMrkKeyring?
    ensures forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allAwsKmsMrk} | keyring in allAwsKmsMrk :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases input
  {
    allAwsKmsMrk := [];
    for i: int := 0 to |AllAwsKMSKeys|
      invariant forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allAwsKmsMrk} | keyring in allAwsKmsMrk :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    {
      var (kmsKeyId, region) := AllAwsKMSKeys[i];
      var keyring := CreateAwsKmsMrkKeyring(kmsKeyId, region);
      allAwsKmsMrk := allAwsKmsMrk + [keyring];
    }
  }

  method CreateAwsKmsMrkKeyring(kmsKeyId: string, region: string) returns (keyring: Types.IKeyring)
    ensures keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases kmsKeyId, region
  {
    print ""\n CreateAwsKmsMrkKeyring: "", kmsKeyId, "" "", region;
    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput);
    var kmsClient :- expect clientSupplier.GetClient(Types.GetClientInput(region := region));
    keyring :- expect mpl.CreateAwsKmsMrkKeyring(Types.CreateAwsKmsMrkKeyringInput(kmsKeyId := kmsKeyId, kmsClient := kmsClient, grantTokens := None));
  }
}

module CreateAwsKmsMrkMultiKeyrings {

  import Types = AwsCryptographyMaterialProvidersTypes

  import WrappedMaterialProviders

  import opened Wrappers

  import TestVectorsUtils

  import opened TestVectorConstants
  method CreateAllAwsKmsMrkMultiKeyring(input: EncryptDecryptKeyrings) returns (allAwsKmsMrkMult: seq<Types.IKeyring>)
    requires input.AwsKmsMrkMultiKeyring?
    ensures forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allAwsKmsMrkMult} | keyring in allAwsKmsMrkMult :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases input
  {
    allAwsKmsMrkMult := [];
    for i: int := 0 to |AllAwsKMSKeys|
      invariant forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allAwsKmsMrkMult} | keyring in allAwsKmsMrkMult :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    {
      var (kmsKeyId, _ /* _v0 */) := AllAwsKMSKeys[i];
      var keyring := CreateAwsKmsMrkMultiKeyring(Some(kmsKeyId), None);
      allAwsKmsMrkMult := allAwsKmsMrkMult + [keyring];
    }
  }

  method CreateAwsKmsMrkMultiKeyring(kmsKeyId: Option<Types.KmsKeyId>, kmsKeyIds: Option<Types.KmsKeyIdList>) returns (keyring: Types.IKeyring)
    ensures keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases kmsKeyId, kmsKeyIds
  {
    print ""\n CreateAwsKmsMrkMultiKeyring: "", kmsKeyId, "" "", kmsKeyIds;
    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    keyring :- expect mpl.CreateAwsKmsMrkMultiKeyring(Types.CreateAwsKmsMrkMultiKeyringInput(generator := kmsKeyId, kmsKeyIds := kmsKeyIds, clientSupplier := None, grantTokens := None));
  }
}

module CreateRawAesKeyrings {

  import Types = AwsCryptographyMaterialProvidersTypes

  import WrappedMaterialProviders

  import opened Wrappers

  import TestVectorsUtils

  import opened TestVectorConstants

  import Primitives = Aws.Cryptography.Primitives

  import Crypto = AwsCryptographyPrimitivesTypes
  method CreateAllRawAesKeyring(input: TestVectorConstants.EncryptDecryptKeyrings) returns (allAES: seq<Types.IKeyring>)
    requires input.RawAesKeyring?
    ensures forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allAES} | keyring in allAES :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases input
  {
    allAES := [];
    var AllAesWrappingAlgs := set w: Types.AesWrappingAlg | true;
    while AllAesWrappingAlgs != {}
      invariant forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allAES} | keyring in allAES :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
      decreases AllAesWrappingAlgs
    {
      var wrappingAlg :| wrappingAlg in AllAesWrappingAlgs;
      var keyring := CreateRawAesKeyring(wrappingAlg);
      allAES := allAES + [keyring];
      AllAesWrappingAlgs := AllAesWrappingAlgs - {wrappingAlg};
    }
  }

  method CreateRawAesKeyring(wrappingAlg: Types.AesWrappingAlg) returns (keyring: Types.IKeyring)
    ensures keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases wrappingAlg
  {
    print ""\n CreateRawAesKeyring: "", wrappingAlg;
    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    var crypto :- expect Primitives.AtomicPrimitives();
    var length := match wrappingAlg case ALG_AES128_GCM_IV12_TAG16() => 16 case ALG_AES192_GCM_IV12_TAG16() => 24 case ALG_AES256_GCM_IV12_TAG16() => 32;
    var wrappingKey :- expect crypto.GenerateRandomBytes(Crypto.GenerateRandomBytesInput(length := length));
    var namespace, name := TestVectorsUtils.NamespaceAndName(0);
    keyring :- expect mpl.CreateRawAesKeyring(Types.CreateRawAesKeyringInput(keyNamespace := namespace, keyName := name, wrappingKey := wrappingKey, wrappingAlg := wrappingAlg));
  }
}

module CreateRawRsaKeyrings {

  import Types = AwsCryptographyMaterialProvidersTypes

  import WrappedMaterialProviders

  import opened Wrappers

  import TestVectorsUtils

  import opened TestVectorConstants

  import Primitives = Aws.Cryptography.Primitives

  import Crypto = AwsCryptographyPrimitivesTypes
  method CreateAllRawRsaKeyring(input: TestVectorConstants.EncryptDecryptKeyrings) returns (allRSA: seq<Types.IKeyring>)
    requires input.RawRsaKeyring?
    ensures forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allRSA} | keyring in allRSA :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases input
  {
    allRSA := [];
    var AllPaddingSchemes := set w: Types.PaddingScheme | true;
    while AllPaddingSchemes != {}
      invariant forall keyring: Types.IKeyring {:trigger keyring.Modifies} {:trigger keyring.ValidState()} {:trigger keyring in allRSA} | keyring in allRSA :: keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
      decreases AllPaddingSchemes
    {
      var paddingScheme :| paddingScheme in AllPaddingSchemes;
      var keyring := CreateRawRsaKeyring(paddingScheme);
      allRSA := allRSA + [keyring];
      AllPaddingSchemes := AllPaddingSchemes - {paddingScheme};
    }
  }

  method CreateRawRsaKeyring(paddingScheme: Types.PaddingScheme) returns (keyring: Types.IKeyring)
    ensures keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases paddingScheme
  {
    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    var crypto :- expect Primitives.AtomicPrimitives();
    var keys :- expect crypto.GenerateRSAKeyPair(Crypto.GenerateRSAKeyPairInput(lengthBits := 2048));
    var namespace, name := TestVectorsUtils.NamespaceAndName(0);
    keyring :- expect mpl.CreateRawRsaKeyring(Types.CreateRawRsaKeyringInput(keyNamespace := namespace, keyName := name, paddingScheme := paddingScheme, publicKey := Option.Some(keys.publicKey.pem), privateKey := Option.Some(keys.privateKey.pem)));
  }
}

module {:options ""-functionSyntax:4""} TestManifests {

  import Types = AwsCryptographyMaterialProvidersTypes

  import opened Wrappers

  import TestVectors

  import FileIO

  import API = JSON.API

  import Values = JSON.Values

  import Seq

  import BoundedInts

  import opened JSONHelpers

  import ParseJsonManifests

  import KeyVectors

  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  method {:options ""-functionSyntax:4""} StartEncrypt(encryptManifestPath: string, keysManifiestPath: string)
    decreases encryptManifestPath, keysManifiestPath
  {
    var encryptManifestBv :- expect FileIO.ReadBytesFromFile(encryptManifestPath);
    var encryptManifestBytes := BvToBytes(encryptManifestBv);
    var encryptManifestJSON :- expect API.Deserialize(encryptManifestBytes);
    expect encryptManifestJSON.Object?, ""expectation violation""
    var keys :- expect KeyVectors.KeyVectors(KeyVectorsTypes.KeyVectorsConfig(keyManifiestPath := keysManifiestPath));
    var jsonTests :- expect GetObject(""tests"", encryptManifestJSON.obj);
    var encryptVectors :- expect ParseJsonManifests.BuildEncryptTestVector(keys, jsonTests);
    var encryptTests :- expect ToEncryptTests(keys, encryptVectors);
    var decryptTests := TestEncrypts(encryptTests, keys);
    var _ /* _v0 */ := TestDecrypts(decryptTests);
  }

  method TestEncrypts(tests: seq<TestVectors.EncryptTest>, keys: KeyVectors.KeyVectorsClient) returns (output: seq<TestVectors.DecryptTest>)
    requires keys.ValidState()
    requires forall t: TestVectors.EncryptTest {:trigger t.cmm} {:trigger t in tests} | t in tests :: t.cmm.ValidState()
    modifies keys.Modifies, set t: TestVectors.EncryptTest, o: object {:trigger o in t.cmm.Modifies} | t in tests && o in t.cmm.Modifies :: o
    ensures keys.ValidState()
    ensures forall t: TestVectors.EncryptTest {:trigger t.cmm} {:trigger t in tests} | t in tests :: t.cmm.ValidState()
    ensures forall t: TestVectors.DecryptTest {:trigger t.cmm} {:trigger t in output} | t in output :: t.cmm.ValidState() && fresh(t.cmm.Modifies)
    decreases tests, keys
  {
    var hasFailure := false;
    print ""\n=================== Starting Encrypt Tests =================== \n\n"";
    var decryptableTests: seq<(TestVectors.EncryptTest, Types.EncryptionMaterials)> := [];
    for i: int := 0 to |tests|
      invariant forall t: TestVectors.EncryptTest {:trigger t.cmm} {:trigger t in tests} | t in tests :: t.cmm.ValidState()
    {
      var test := tests[i];
      var pass, maybeEncryptionMaterials := TestVectors.TestGetEncryptionMaterials(test);
      if pass && test.vector.PositiveEncryptKeyringVector? {
        decryptableTests := decryptableTests + [(test, maybeEncryptionMaterials.value)];
      } else if !pass {
        hasFailure := true;
      }
    }
    print ""\n=================== Completed Encrypt Tests =================== \n\n"";
    expect !hasFailure, ""expectation violation""
    output :- expect ToDecryptTests(keys, decryptableTests);
  }

  method TestDecrypts(tests: seq<TestVectors.DecryptTest>) returns (manifest: seq<BoundedInts.byte>)
    requires forall t: TestVectors.DecryptTest {:trigger t.cmm} {:trigger t in tests} | t in tests :: t.cmm.ValidState()
    modifies set t: TestVectors.DecryptTest, o: object {:trigger o in t.cmm.Modifies} | t in tests && o in t.cmm.Modifies :: o
    ensures forall t: TestVectors.DecryptTest {:trigger t.cmm} {:trigger t in tests} | t in tests :: t.cmm.ValidState()
    decreases tests
  {
    print ""\n=================== Starting Decrypt Tests =================== \n\n"";
    var hasFailure := false;
    for i: int := 0 to |tests|
      invariant forall t: TestVectors.DecryptTest {:trigger t.cmm} {:trigger t in tests} | t in tests :: t.cmm.ValidState()
    {
      var pass := TestVectors.TestDecryptMaterials(tests[i]);
      if !pass {
        hasFailure := true;
      }
    }
    print ""\n=================== Completed Decrypt Tests =================== \n\n"";
    expect !hasFailure, ""expectation violation""
    manifest := ToJSONDecryptManifiest(tests);
  }

  method ToEncryptTests(keys: KeyVectors.KeyVectorsClient, encryptVectors: seq<TestVectors.EncryptTestVector>) returns (output: Result<seq<TestVectors.EncryptTest>, string>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    ensures output.Success? ==> true && forall t: TestVectors.EncryptTest {:trigger t.cmm} {:trigger t in output.value} | t in output.value :: t.cmm.ValidState() && fresh(t.cmm.Modifies)
    decreases keys, encryptVectors
  {
    var encryptTests: seq<TestVectors.EncryptTest> := [];
    for i: int := 0 to |encryptVectors|
      invariant forall t: TestVectors.EncryptTest {:trigger t.cmm} {:trigger t in encryptTests} | t in encryptTests :: t.cmm.ValidState() && fresh(t.cmm.Modifies)
    {
      var test :- TestVectors.ToEncryptTest(keys, encryptVectors[i]);
      encryptTests := encryptTests + [test];
    }
    return Success(encryptTests);
  }

  method ToDecryptTests(keys: KeyVectors.KeyVectorsClient, tests: seq<(TestVectors.EncryptTest, Types.EncryptionMaterials)>) returns (output: Result<seq<TestVectors.DecryptTest>, string>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    ensures output.Success? ==> true && forall t: TestVectors.DecryptTest {:trigger t.cmm} {:trigger t in output.value} | t in output.value :: t.cmm.ValidState() && fresh(t.cmm.Modifies)
    decreases keys, tests
  {
    var positiveEncryptTests := Seq.Filter((r: (TestVectors.EncryptTest, Types.EncryptionMaterials)) => r.0.vector.PositiveEncryptKeyringVector?, tests);
    var decryptTests: seq<TestVectors.DecryptTest> := [];
    for i: int := 0 to |positiveEncryptTests|
      invariant forall t: TestVectors.DecryptTest {:trigger t.cmm} {:trigger t in decryptTests} | t in decryptTests :: t.cmm.ValidState() && fresh(t.cmm.Modifies)
    {
      var test :- TestVectors.ToDecryptTest(keys, positiveEncryptTests[i].0, positiveEncryptTests[i].1);
      decryptTests := decryptTests + [test];
    }
    return Success(decryptTests);
  }

  function method ToJSONDecryptManifiest(tests: seq<TestVectors.DecryptTest>): seq<BoundedInts.byte>
    decreases tests
  {
    []
  }
}

module {:options ""-functionSyntax:4""} TestVectors {

  import Types = AwsCryptographyMaterialProvidersTypes

  import WrappedMaterialProviders

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import UTF8

  import KeyVectors

  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  datatype EncryptTest = EncryptTest(input: Types.GetEncryptionMaterialsInput, cmm: Types.ICryptographicMaterialsManager, vector: EncryptTestVector)

  datatype DecryptTest = DecryptTest(input: Types.DecryptMaterialsInput, cmm: Types.ICryptographicMaterialsManager, vector: DecryptTestVector)

  datatype EncryptTestVector = PositiveEncryptKeyringVector(name: string, description: Option<string>, encryptionContext: Types.EncryptionContext, commitmentPolicy: Types.CommitmentPolicy, algorithmSuite: Types.AlgorithmSuiteInfo, maxPlaintextLength: Option<UInt.int64>, requiredEncryptionContextKeys: Option<Types.EncryptionContextKeys>, encryptDescription: KeyVectorsTypes.KeyDescription, decryptDescription: KeyVectorsTypes.KeyDescription) | NegativeEncryptKeyringVector(name: string, description: Option<string>, encryptionContext: Types.EncryptionContext, commitmentPolicy: Types.CommitmentPolicy, algorithmSuite: Types.AlgorithmSuiteInfo, maxPlaintextLength: Option<UInt.int64>, requiredEncryptionContextKeys: Option<Types.EncryptionContextKeys>, errorDescription: string, keyDescription: KeyVectorsTypes.KeyDescription)

  datatype DecryptTestVector = PositiveDecryptKeyringTest(name: string, algorithmSuite: Types.AlgorithmSuiteInfo, commitmentPolicy: Types.CommitmentPolicy, encryptedDataKeys: Types.EncryptedDataKeyList, encryptionContext: Types.EncryptionContext, keyDescription: KeyVectorsTypes.KeyDescription, expectedResult: DecryptResult, description: Option<string> := None, reproducedEncryptionContext: Option<Types.EncryptionContext> := None) | NegativeDecryptKeyringTest(name: string, algorithmSuite: Types.AlgorithmSuiteInfo, commitmentPolicy: Types.CommitmentPolicy, encryptedDataKeys: Types.EncryptedDataKeyList, encryptionContext: Types.EncryptionContext, errorDescription: string, keyDescription: KeyVectorsTypes.KeyDescription, reproducedEncryptionContext: Option<Types.EncryptionContext> := None, description: Option<string> := None)

  datatype DecryptResult = DecryptResult(plaintextDataKey: Option<Types.Secret>, symmetricSigningKey: Option<Types.Secret>, requiredEncryptionContextKeys: Types.EncryptionContextKeys)

  method TestGetEncryptionMaterials(test: EncryptTest) returns (testResult: bool, materials: Option<Types.EncryptionMaterials>)
    requires test.cmm.ValidState()
    modifies test.cmm.Modifies
    ensures test.cmm.ValidState()
    ensures testResult && test.vector.PositiveEncryptKeyringVector? ==> materials.Some?
    decreases test
  {
    print ""\nTEST===> "", test.vector.name, if test.vector.description.Some? then ""\n"" + test.vector.description.value else """", if test.vector.NegativeEncryptKeyringVector? then ""\n"" + test.vector.errorDescription else """", ""\n"";
    var result := test.cmm.GetEncryptionMaterials(test.input);
    testResult := match test.vector case PositiveEncryptKeyringVector(_ /* _v0 */, _ /* _v1 */, _ /* _v2 */, _ /* _v3 */, _ /* _v4 */, _ /* _v5 */, _ /* _v6 */, _ /* _v7 */, _ /* _v8 */) => result.Success? case NegativeEncryptKeyringVector(_ /* _v9 */, _ /* _v10 */, _ /* _v11 */, _ /* _v12 */, _ /* _v13 */, _ /* _v14 */, _ /* _v15 */, _ /* _v16 */, _ /* _v17 */) => !result.Success?;
    materials := if test.vector.PositiveEncryptKeyringVector? && result.Success? then Some(result.value.encryptionMaterials) else None;
    if !testResult {
      if test.vector.PositiveEncryptKeyringVector? {
        print result.error;
      }
      print ""\nFAILED! <-----------\n"";
    }
  }

  method TestDecryptMaterials(test: DecryptTest) returns (output: bool)
    requires test.cmm.ValidState()
    modifies test.cmm.Modifies
    ensures test.cmm.ValidState()
    decreases test
  {
    print ""\nTEST===> "", test.vector.name, if test.vector.description.Some? then ""\n"" + test.vector.description.value else """", if test.vector.NegativeDecryptKeyringTest? then ""\n"" + test.vector.errorDescription else ""\n"";
    var result := test.cmm.DecryptMaterials(test.input);
    output := match test.vector case PositiveDecryptKeyringTest(_ /* _v18 */, _ /* _v19 */, _ /* _v20 */, _ /* _v21 */, _ /* _v22 */, _ /* _v23 */, _ /* _v24 */, _ /* _v25 */, _ /* _v26 */) => result.Success? && result.value.decryptionMaterials.plaintextDataKey == test.vector.expectedResult.plaintextDataKey && result.value.decryptionMaterials.symmetricSigningKey == test.vector.expectedResult.symmetricSigningKey && result.value.decryptionMaterials.requiredEncryptionContextKeys == test.vector.expectedResult.requiredEncryptionContextKeys case NegativeDecryptKeyringTest(_ /* _v27 */, _ /* _v28 */, _ /* _v29 */, _ /* _v30 */, _ /* _v31 */, _ /* _v32 */, _ /* _v33 */, _ /* _v34 */, _ /* _v35 */) => !result.Success?;
    if !output {
      if test.vector.PositiveDecryptKeyringTest? && result.Failure? {
        print result.error;
      }
      print ""\nFAILED! <-----------\n"";
    }
  }

  method ToEncryptTest(keys: KeyVectors.KeyVectorsClient, vector: EncryptTestVector) returns (output: Result<EncryptTest, string>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    ensures output.Success? ==> output.value.cmm.ValidState() && fresh(output.value.cmm.Modifies)
    decreases keys, vector
  {
    var input := match vector case PositiveEncryptKeyringVector(_ /* _v36 */, _ /* _v37 */, encryptionContext, commitmentPolicy, algorithmSuite, maxPlaintextLength, requiredEncryptionContextKeys, _ /* _v38 */, _ /* _v39 */) => Types.GetEncryptionMaterialsInput(encryptionContext := encryptionContext, commitmentPolicy := commitmentPolicy, algorithmSuiteId := Some(algorithmSuite.id), maxPlaintextLength := maxPlaintextLength, requiredEncryptionContextKeys := requiredEncryptionContextKeys) case NegativeEncryptKeyringVector(_ /* _v40 */, _ /* _v41 */, encryptionContext, commitmentPolicy, algorithmSuite, maxPlaintextLength, requiredEncryptionContextKeys, _ /* _v42 */, _ /* _v43 */) => Types.GetEncryptionMaterialsInput(encryptionContext := encryptionContext, commitmentPolicy := commitmentPolicy, algorithmSuiteId := Some(algorithmSuite.id), maxPlaintextLength := maxPlaintextLength, requiredEncryptionContextKeys := requiredEncryptionContextKeys);
    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    var maybeKeyring := keys.CreateWappedTestVectorKeyring(KeyVectorsTypes.TestVectorKeyringInput(keyDescription := if vector.PositiveEncryptKeyringVector? then vector.encryptDescription else vector.keyDescription));
    var keyring :- maybeKeyring.MapFailure((e: KeyVectorsTypes.Error) => var _ /* _v44 */: () := printErr(e); ""Keyring failure"");
    var maybeCmm := mpl.CreateDefaultCryptographicMaterialsManager(Types.CreateDefaultCryptographicMaterialsManagerInput(keyring := keyring));
    var cmm :- maybeCmm.MapFailure((e: Error) => ""CMM failure"");
    return Success(EncryptTest(input := input, cmm := cmm, vector := vector));
  }

  method ToDecryptTest(keys: KeyVectors.KeyVectorsClient, test: EncryptTest, materials: Types.EncryptionMaterials)
      returns (output: Result<DecryptTest, string>)
    requires test.vector.PositiveEncryptKeyringVector?
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    ensures output.Success? ==> output.value.cmm.ValidState() && fresh(output.value.cmm.Modifies)
    decreases keys, test, materials
  {
    var reproducedEncryptionContext := None;
    var input := Types.DecryptMaterialsInput(algorithmSuiteId := materials.algorithmSuite.id, commitmentPolicy := test.vector.commitmentPolicy, encryptedDataKeys := materials.encryptedDataKeys, encryptionContext := materials.encryptionContext, reproducedEncryptionContext := reproducedEncryptionContext);
    var vector := PositiveDecryptKeyringTest(name := test.vector.name + ""->Decryption"", algorithmSuite := materials.algorithmSuite, commitmentPolicy := test.vector.commitmentPolicy, encryptedDataKeys := materials.encryptedDataKeys, encryptionContext := materials.encryptionContext, keyDescription := test.vector.decryptDescription, expectedResult := DecryptResult(plaintextDataKey := materials.plaintextDataKey, symmetricSigningKey := if materials.symmetricSigningKeys.Some? && 0 < |materials.symmetricSigningKeys.value| then Some(materials.symmetricSigningKeys.value[0]) else None, requiredEncryptionContextKeys := materials.requiredEncryptionContextKeys), description := if test.vector.description.Some? then Some(""Decryption for "" + test.vector.description.value) else None, reproducedEncryptionContext := reproducedEncryptionContext);
    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();
    var maybeKeyring := keys.CreateWappedTestVectorKeyring(KeyVectorsTypes.TestVectorKeyringInput(keyDescription := vector.keyDescription));
    var keyring :- maybeKeyring.MapFailure((e: KeyVectorsTypes.Error) => var _ /* _v45 */: () := printErr(e); ""Keyring failure"");
    var maybeCmm := mpl.CreateDefaultCryptographicMaterialsManager(Types.CreateDefaultCryptographicMaterialsManagerInput(keyring := keyring));
    var cmm :- maybeCmm.MapFailure((e: Error) => ""CMM failure"");
    return Success(DecryptTest(input := input, cmm := cmm, vector := vector));
  }

  function printErr(e: KeyVectorsTypes.Error): ()
    decreases e
  {
    ()
  } by method {
    print e, ""\n"", ""\n"";
    return ();
  }
}

module {:options ""-functionSyntax:4""} ParseJsonManifests {

  import Types = AwsCryptographyMaterialProvidersTypes

  import API = JSON.API

  import opened Values = JSON.Values

  import Errors = JSON.Errors

  import opened Wrappers

  import UTF8

  import Seq

  import opened UInt = StandardLibrary.UInt

  import BoundedInts

  import opened JSONHelpers

  import opened TestVectors

  import HexStrings

  import Base64

  import CompleteVectors

  import KeyVectors

  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes

  import AlgorithmSuites
  function method BuildEncryptTestVector(keys: KeyVectors.KeyVectorsClient, obj: seq<(string, JSON)>): Result<seq<EncryptTestVector>, string>
    decreases keys, obj
  {
    if |obj| == 0 then
      Success([])
    else
      var name: string := obj[0].0; var encryptVector: EncryptTestVector :- ToEncryptTestVector(keys, name, obj[0].1); var tail: seq<EncryptTestVector> :- BuildEncryptTestVector(keys, obj[1..]); Success([encryptVector] + tail)
  }

  function method ToEncryptTestVector(keys: KeyVectors.KeyVectorsClient, name: string, obj: JSON): Result<EncryptTestVector, string>
    decreases keys, name, obj
  {
    Need(obj.Object?, ""EncryptTestVector not an object""); var obj: seq<(string, JSON)> := obj.obj; var typString: string := ""type""; var typ: string :- GetString(typString, obj); var description: Option<string> := GetString(""description"", obj).ToOption(); var encryptionContextStrings: map<string, string> :- SmallObjectToStringStringMap(""encryptionContext"", obj); var encryptionContext: Types.EncryptionContext :- utf8EncodeMap(encryptionContextStrings); var algorithmSuiteHex: string :- GetString(""algorithmSuiteId"", obj); Need(HexStrings.IsLooseHexString(algorithmSuiteHex), ""Not hex encoded binnary""); var binaryId: seq<uint8> := HexStrings.FromHexString(algorithmSuiteHex); var algorithmSuite: AlgorithmSuiteInfo :- AlgorithmSuites.GetAlgorithmSuiteInfo(binaryId).MapFailure((e: Error) => ""Invalid Suite:"" + algorithmSuiteHex); var keysAsStrings: Option<seq<string>> := GetArrayString(""requiredEncryptionContextKeys"", obj).ToOption(); var requiredEncryptionContextKeys: Option<seq<ValidUTF8Bytes>> :- if keysAsStrings.Some? then var result: Result<seq<Types.Utf8Bytes>, string> := utf8EncodeSeq(keysAsStrings.value); if result.Success? then Success(Some(result.value)) else Failure(result.error) else Success(None); var commitmentPolicy: Types.CommitmentPolicy := CompleteVectors.GetCompatableCommitmentPolicy(algorithmSuite); var maxPlaintextLength: Option<BoundedInts.int64> := None; match typ case ""positive-keyring"" => (var encryptKeyDescriptionObject: Values.JSON :- Get(""encryptKeyDescription"", obj); var decryptKeyDescriptionObject: Values.JSON :- Get(""decryptKeyDescription"", obj); var encryptStr: seq<byte> :- API.Serialize(encryptKeyDescriptionObject).MapFailure((e: Errors.SerializationError) => e.ToString()); var decryptStr: seq<byte> :- API.Serialize(decryptKeyDescriptionObject).MapFailure((e: Errors.SerializationError) => e.ToString()); var encryptKeyDescription: GetKeyDescriptionOutput :- keys.GetKeyDescription(KeyVectorsTypes.GetKeyDescriptionInput(json := encryptStr)).MapFailure(ErrorToString); var decryptKeyDescription: GetKeyDescriptionOutput :- keys.GetKeyDescription(KeyVectorsTypes.GetKeyDescriptionInput(json := decryptStr)).MapFailure(ErrorToString); Success(PositiveEncryptKeyringVector(name := name, description := description, encryptionContext := encryptionContext, commitmentPolicy := commitmentPolicy, algorithmSuite := algorithmSuite, maxPlaintextLength := maxPlaintextLength, requiredEncryptionContextKeys := requiredEncryptionContextKeys, encryptDescription := encryptKeyDescription.keyDescription, decryptDescription := decryptKeyDescription.keyDescription))) case ""negative-keyring"" => (var keyDescriptionObject: Values.JSON :- Get(""keyDescription"", obj); var keyStr: seq<byte> :- API.Serialize(keyDescriptionObject).MapFailure((e: Errors.SerializationError) => e.ToString()); var keyDescription: GetKeyDescriptionOutput :- keys.GetKeyDescription(KeyVectorsTypes.GetKeyDescriptionInput(json := keyStr)).MapFailure(ErrorToString); var errorDescription: string :- GetString(""errorDescription"", obj); Success(NegativeEncryptKeyringVector(name := name, description := description, encryptionContext := encryptionContext, commitmentPolicy := commitmentPolicy, algorithmSuite := algorithmSuite, maxPlaintextLength := maxPlaintextLength, requiredEncryptionContextKeys := requiredEncryptionContextKeys, errorDescription := errorDescription, keyDescription := keyDescription.keyDescription))) case _ /* _v0 */ => Failure(""Unsupported EncryptTestVector type:"" + typ)
  }

  function method ErrorToString(e: KeyVectorsTypes.Error): string
    decreases e
  {
    match e
    case KeyVectorException(message) =>
      message
    case AwsCryptographyMaterialProviders(mplError) =>
      (match mplError
      case AwsCryptographicMaterialProvidersException(message) =>
        message
      case _ /* _v1 */ =>
        ""Umapped AwsCryptographyMaterialProviders"")
    case _ /* _v2 */ =>
      ""Umapped KeyVectorException""
  }
}

module {:options ""-functionSyntax:4""} JSONHelpers {

  import API = JSON.API

  import BoundedInts

  import opened Values = JSON.Values

  import opened Wrappers

  import UTF8

  import Types = AwsCryptographyMaterialProvidersTypes
  function method BvToBytes(bits: seq<bv8>): seq<BoundedInts.uint8>
    decreases bits
  {
    seq(|bits|, (i: int) requires 0 <= i < |bits| => bits[i] as BoundedInts.byte)
  }

  function method BytesBv(bits: seq<BoundedInts.uint8>): seq<bv8>
    decreases bits
  {
    seq(|bits|, (i: int) requires 0 <= i < |bits| => bits[i] as bv8)
  }

  function method Get(key: string, obj: seq<(string, JSON)>): Result<Values.JSON, string>
    decreases key, obj
  {
    if |obj| == 0 then
      Failure(""Key: "" + key + "" does not exist"")
    else if obj[0].0 == key then
      Success(obj[0].1)
    else
      Get(key, obj[1..])
  }

  function method GetString(key: string, obj: seq<(string, JSON)>): Result<string, string>
    decreases key, obj
  {
    var obj: Values.JSON :- Get(key, obj); Need(obj.String?, ""Not a string""); Success(obj.str)
  }

  function method GetBool(key: string, obj: seq<(string, JSON)>): Result<bool, string>
    decreases key, obj
  {
    var obj: Values.JSON :- Get(key, obj); Need(obj.Bool?, ""Not a bool""); Success(obj.b)
  }

  function method GetNat(key: string, obj: seq<(string, JSON)>): Result<nat, string>
    decreases key, obj
  {
    var obj: Values.JSON :- Get(key, obj); Need(obj.Number?, ""Not a number""); Need(0 < obj.num.n, ""Not a nat""); Success(obj.num.n)
  }

  function method GetOptionalString(key: string, obj: seq<(string, JSON)>): Result<Option<string>, string>
    decreases key, obj
  {
    var obj: Option<Values.JSON> := Get(key, obj).ToOption();
    if obj.Some? then
      Need(obj.value.String?, ""Not a string""); Success(Some(obj.value.str))
    else
      Success(None)
  }

  function method GetObject(key: string, obj: seq<(string, JSON)>): Result<seq<(string, JSON)>, string>
    decreases key, obj
  {
    var obj: Values.JSON :- Get(key, obj); Need(obj.Object?, ""Not an object""); Success(obj.obj)
  }

  function method GetArray(key: string, obj: seq<(string, JSON)>): Result<seq<JSON>, string>
    decreases key, obj
  {
    var obj: Values.JSON :- Get(key, obj); Need(obj.Array?, ""Not an array""); Success(obj.arr)
  }

  function method GetArrayString(key: string, obj: seq<(string, JSON)>): Result<seq<string>, string>
    decreases key, obj
  {
    var obj: Values.JSON :- Get(key, obj); Need(obj.Array? && forall s: JSON {:trigger s.String?} {:trigger s in obj.arr} | s in obj.arr :: s.String?, ""Not an array of strings""); var arr: seq<JSON> := obj.arr; Success(seq(|arr|, (n: int) requires 0 <= n < |arr| => arr[n].str))
  }

  function method GetArrayObject(key: string, obj: seq<(string, JSON)>): Result<seq<seq<(string, JSON)>>, string>
    decreases key, obj
  {
    var obj: Values.JSON :- Get(key, obj); Need(obj.Array? && forall s: JSON {:trigger s.Object?} {:trigger s in obj.arr} | s in obj.arr :: s.Object?, ""Not an array of objects""); var arr: seq<JSON> := obj.arr; Success(seq(|arr|, (n: int) requires 0 <= n < |arr| => arr[n].obj))
  }

  function method SmallObjectToStringStringMap(key: string, obj: seq<(string, JSON)>): Result<map<string, string>, string>
    decreases key, obj
  {
    var item: Values.JSON :- Get(key, obj); Need(item.Object?, ""Not an object""); var obj: seq<(string, JSON)> := item.obj; Need(forall t: (string, JSON) {:trigger t.1} {:trigger t in obj} | t in obj :: t.1.String?, ""Not a string string object""); Need(forall i: int, j: int {:trigger obj[j], obj[i]} | 0 <= i < j < |obj| :: obj[i].0 != obj[j].0, ""JSON serialization Error""); Success(map t: (string, JSON) {:trigger t.1} {:trigger t.0} {:trigger t in obj} | t in obj :: t.0 := t.1.str)
  }

  function method utf8EncodePair(key: string, value: string): (res: Result<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), string>)
    decreases key, value
  {
    var utf8Key: ValidUTF8Bytes :- UTF8.Encode(key); var utf8Value: ValidUTF8Bytes :- UTF8.Encode(value); Success((utf8Key, utf8Value))
  }

  function method utf8EncodeMap(mapStringString: map<string, string>): (res: Result<Types.EncryptionContext, string>)
    decreases mapStringString
  {
    if |mapStringString| == 0 then
      Success(map[])
    else
      var encodedResults: map<seq<char>, Result<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), string>> := map key: seq<char> {:trigger mapStringString[key]} {:trigger key in mapStringString} | key in mapStringString :: key := utf8EncodePair(key, mapStringString[key]); Need(forall r: Result<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), string> {:trigger r.Success?} {:trigger r in encodedResults.Values} | r in encodedResults.Values :: r.Success?, ""String can not be UTF8 Encoded?""); Success(map r: Result<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), string> {:trigger r.value} {:trigger r in encodedResults.Values} | r in encodedResults.Values :: r.value.0 := r.value.1)
  }

  function method utf8EncodeSeq(seqOfStrings: seq<string>): (res: Result<seq<Types.Utf8Bytes>, string>)
    decreases seqOfStrings
  {
    var encodedResults: seq<Result<ValidUTF8Bytes, seq<char>>> := seq(|seqOfStrings|, (i: int) requires 0 <= i < |seqOfStrings| => UTF8.Encode(seqOfStrings[i]));
    Need(forall r: Result<ValidUTF8Bytes, seq<char>> {:trigger r.Success?} {:trigger r in encodedResults} | r in encodedResults :: r.Success?, ""String can not be UTF8 Encoded?""); Success(seq(|encodedResults|, (i: int) requires 0 <= i < |encodedResults| => encodedResults[i].value))
  }
}

module {:options ""-functionSyntax:4""} CompleteVectors {

  import Types = AwsCryptographyMaterialProvidersTypes

  import ComAmazonawsKmsTypes

  import MaterialProviders

  import TestVectors

  import Seq

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import HexStrings

  import opened Values = JSON.Values

  import UUID

  import JSONHelpers

  import API = JSON.API

  import SortedSets

  import FileIO

  import AlgorithmSuites
  datatype PositiveKeyDescriptionJSON = PositiveKeyDescriptionJSON(description: string, encrypt: JSON, decrypt: JSON)

  function method GetCompatableCommitmentPolicy(algorithmSuite: Types.AlgorithmSuiteInfo): (commitmentPolicy: Types.CommitmentPolicy)
    decreases algorithmSuite
  {
    match algorithmSuite.id
    case ESDK(_ /* _v0 */) =>
      if algorithmSuite.commitment.None? then
        Types.CommitmentPolicy.ESDK(Types.ESDKCommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT)
      else
        Types.CommitmentPolicy.ESDK(Types.ESDKCommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
    case DBE(_ /* _v1 */) =>
      Types.CommitmentPolicy.DBE(Types.DBECommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
  }

  const ESDKAlgorithmSuites := set id: Types.ESDKAlgorithmSuiteId | true :: AlgorithmSuites.GetESDKSuite(id)
  const DBEAlgorithmSuites := set id: Types.DBEAlgorithmSuiteId | true :: AlgorithmSuites.GetDBESuite(id)

  lemma AllAlgorithmSuitesIsComplete(id: Types.AlgorithmSuiteId)
    ensures AlgorithmSuites.GetSuite(id) in ESDKAlgorithmSuites + DBEAlgorithmSuites
    decreases id
  {
  }

  const aesPersistentKeyNames := [""aes-128"", ""aes-192"", ""aes-256""]
  const AllRawAES := set key: seq<char> | key in aesPersistentKeyNames :: var keyDescription: JSON := Object([(""type"", String(""raw"")), (""encryption-algorithm"", String(""aes"")), (""provider-id"", String(""aws-raw-vectors-persistent-"" + key)), (""key"", String(key))]); PositiveKeyDescriptionJSON(description := ""Generated RawAES "" + key, encrypt := keyDescription, decrypt := keyDescription)
  const rsaPersistentKeyNamesWithoutPublicPrivate := [""rsa-4096""]
  const AllRawRSA := set key: seq<char>, padding: Types.PaddingScheme | key in rsaPersistentKeyNamesWithoutPublicPrivate :: var sharedOptions: seq<(seq<char>, JSON)> := [(""type"", String(""raw"")), (""encryption-algorithm"", String(""rsa"")), (""provider-id"", String(""aws-raw-vectors-persistent-"" + key)), (""padding-algorithm"", String(match padding case PKCS1() => ""pkcs1"" case _ /* _v2 */ => ""oaep-mgf1"")), (""padding-hash"", String(match padding case PKCS1() => ""sha1"" case OAEP_SHA1_MGF1() => ""sha1"" case OAEP_SHA256_MGF1() => ""sha256"" case OAEP_SHA384_MGF1() => ""sha384"" case OAEP_SHA512_MGF1() => ""sha512""))]; PositiveKeyDescriptionJSON(description := ""Generated RawRSA "" + key + "" "" + match padding case PKCS1() => ""pkcs1-sha1"" case OAEP_SHA1_MGF1() => ""oaep-mgf1-sha1"" case OAEP_SHA256_MGF1() => ""oaep-mgf1-sha256"" case OAEP_SHA384_MGF1() => ""oaep-mgf1-sha384"" case OAEP_SHA512_MGF1() => ""oaep-mgf1-sha512"", encrypt := Object(sharedOptions + [(""key"", String(key + ""-public""))]), decrypt := Object(sharedOptions + [(""key"", String(key + ""-private""))]))
  const AllAwsKMSKeys := [""us-west-2-decryptable"", ""us-west-2-mrk""]
  const AllKMSInfo := set key: seq<char> | key in AllAwsKMSKeys :: var keyDescription: JSON := Object([(""type"", String(""aws-kms"")), (""key"", String(key))]); PositiveKeyDescriptionJSON(description := ""Generated KMS "" + key, encrypt := keyDescription, decrypt := keyDescription)
  const AllAwsKMSMrkKeys := [""us-west-2-mrk"", ""us-east-1-mrk""]
  const AllKmsMrkAware := set encryptKey: seq<char>, decryptKey: seq<char> | encryptKey in AllAwsKMSMrkKeys && decryptKey in AllAwsKMSMrkKeys :: PositiveKeyDescriptionJSON(description := ""Generated KMS MRK "" + encryptKey + ""->"" + decryptKey, encrypt := Object([(""type"", String(""aws-kms-mrk-aware"")), (""key"", String(encryptKey))]), decrypt := Object([(""type"", String(""aws-kms-mrk-aware"")), (""key"", String(decryptKey))]))
  const AwsPartitions := [""aws""]
  const AWSAccounts := [""658956600833""]
  const AllDiscoveryFilters: set<Option<Types.DiscoveryFilter>> := {Some(Types.DiscoveryFilter(partition := ""aws"", accountIds := [""658956600833""])), None}
  const AllKmsMrkAwareDiscovery := set keyId: seq<char>, filter: Option<Types.DiscoveryFilter> | keyId in AllAwsKMSMrkKeys && filter in AllDiscoveryFilters :: PositiveKeyDescriptionJSON(description := ""Discovery KMS MRK "" + keyId + ""->"" + if filter.Some? then ""Filter "" + filter.value.partition + "" "" + Seq.Flatten(filter.value.accountIds) else ""No Filter"", encrypt := Object([(""type"", String(""aws-kms-mrk-aware"")), (""key"", String(keyId))]), decrypt := if filter.Some? then Object([(""type"", String(""aws-kms-mrk-aware-discovery"")), (""default-mrk-region"", String(""us-west-2"")), (""aws-kms-discovery-filter"", Object([(""partition"", String(filter.value.partition)), (""account-ids"", Array(Seq.Map((s: seq<char>) => String(s), filter.value.accountIds)))]))]) else Object([(""type"", String(""aws-kms-mrk-aware-discovery"")), (""default-mrk-region"", String(""us-west-2""))]))
  const AllHierarchy := set keyId: seq<char> | keyId in [""static-branch-key-1""] :: PositiveKeyDescriptionJSON(description := ""Hierarchy KMS "" + keyId, encrypt := Object([(""type"", String(""aws-kms-hierarchy"")), (""key"", String(keyId))]), decrypt := Object([(""type"", String(""aws-kms-hierarchy"")), (""key"", String(keyId))]))
  const AllEncryptionAlgorithmSpec := set e: ComAmazonawsKmsTypes.EncryptionAlgorithmSpec | !e.SYMMETRIC_DEFAULT? :: match e case RSAES_OAEP_SHA_1() => ""RSAES_OAEP_SHA_1"" case RSAES_OAEP_SHA_256() => ""RSAES_OAEP_SHA_256""
  const AllKmsRsaKeys := [""us-west-2-rsa-mrk""]
  const KmsRsa := ""KMS RSA ""
  const AllKmsRsa := set keyId: seq<char>, algorithmSpec: string | keyId in AllKmsRsaKeys && algorithmSpec in AllEncryptionAlgorithmSpec :: PositiveKeyDescriptionJSON(description := KmsRsa + keyId, encrypt := Object([(""type"", String(""aws-kms-rsa"")), (""key"", String(keyId)), (""encryption-algorithm"", String(algorithmSpec))]), decrypt := Object([(""type"", String(""aws-kms-rsa"")), (""key"", String(keyId)), (""encryption-algorithm"", String(algorithmSpec))]))
  const AllPositiveKeyringTests := set postiveKeyDescription: PositiveKeyDescriptionJSON, algorithmSuite: AlgorithmSuiteInfo | postiveKeyDescription in AllKMSInfo + AllKmsMrkAware + AllKmsMrkAwareDiscovery + AllRawAES + AllRawRSA + AllHierarchy + AllKmsRsa && algorithmSuite in ESDKAlgorithmSuites + DBEAlgorithmSuites && !(postiveKeyDescription.description[..|KmsRsa|] == KmsRsa && algorithmSuite.signature.ECDSA?) :: var id: HexString := HexStrings.ToHexString(algorithmSuite.binaryId); Object([(""type"", String(""positive-keyring"")), (""description"", String(postiveKeyDescription.description + "" "" + id)), (""algorithmSuiteId"", String(id)), (""encryptionContext"", Object([])), (""requiredEncryptionContextKeys"", Array([])), (""encryptKeyDescription"", postiveKeyDescription.encrypt), (""decryptKeyDescription"", postiveKeyDescription.decrypt)])

  method WriteStuff()
  {
    var tests := SortedSets.ComputeSetToSequence(AllPositiveKeyringTests);
    var testsJSON: seq<(string, JSON)> := [];
    for i: int := 0 to |tests| {
      var name :- expect UUID.GenerateUUID();
      testsJSON := testsJSON + [(name, tests[i])];
    }
    var mplEncryptManifies := Object([(""tests"", Object(testsJSON))]);
    var mplEncryptManifiesBytes :- expect API.Serialize(mplEncryptManifies);
    var mplEncryptManifiesBv := JSONHelpers.BytesBv(mplEncryptManifiesBytes);
    var _ /* _v3 */ :- expect FileIO.WriteBytesToFile(""dafny/TestVectorsAwsCryptographicMaterialProviders/test/test.json"", mplEncryptManifiesBv);
  }
}

module {:options ""-functionSyntax:4""} KeyDescription {

  import opened Wrappers

  import opened Values = JSON.Values

  import AwsCryptographyMaterialProvidersTypes

  import opened Types = AwsCryptographyMaterialProvidersTestVectorKeysTypes

  import opened JSONHelpers

  import ComAmazonawsKmsTypes
  function printErr(e: string): ()
    decreases e
  {
    ()
  } by method {
    print e, ""\n"", ""\n"";
    return ();
  }

  function printJSON(e: seq<(string, JSON)>): ()
    decreases e
  {
    ()
  } by method {
    print e, ""\n"", ""\n"";
    return ();
  }

  function method ToKeyDescription(obj: JSON): Result<KeyDescription, string>
    decreases obj
  {
    Need(obj.Object?, ""KeyDescription not an object""); var obj: seq<(string, JSON)> := obj.obj; var typString: string := ""type""; var typ: string :- GetString(typString, obj); Need(KeyDescriptionString?(typ), ""Unsupported KeyDescription type:"" + typ); match typ case ""aws-kms-mrk-aware-discovery"" => (var defaultMrkRegion: string :- GetString(""default-mrk-region"", obj); var filter: Result<seq<(string, JSON)>, string> := GetObject(""aws-kms-discovery-filter"", obj); var awsKmsDiscoveryFilter: Option<AwsCryptographyMaterialProvidersTypes.DiscoveryFilter> := ToDiscoveryFilter(obj); Success(KmsMrkDiscovery(KmsMrkAwareDiscovery(keyId := ""aws-kms-mrk-aware-discovery"", defaultMrkRegion := defaultMrkRegion, awsKmsDiscoveryFilter := awsKmsDiscoveryFilter)))) case _ /* _v0 */ => var key: string :- GetString(""key"", obj); match typ case ""static-material-keyring"" => Success(Static(StaticKeyring(keyId := key))) case ""aws-kms"" => Success(Kms(KMSInfo(keyId := key))) case ""aws-kms-mrk-aware"" => Success(KmsMrk(KmsMrkAware(keyId := key))) case ""aws-kms-rsa"" => (var encryptionAlgorithmString: string :- GetString(""encryption-algorithm"", obj); Need(EncryptionAlgorithmSpec?(encryptionAlgorithmString), ""Unsupported EncryptionAlgorithmSpec:"" + encryptionAlgorithmString); var encryptionAlgorithm: EncryptionAlgorithmSpec := match encryptionAlgorithmString case ""RSAES_OAEP_SHA_1"" => ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1 case ""RSAES_OAEP_SHA_256"" => ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256; Success(KmsRsa(KmsRsaKeyring(keyId := key, encryptionAlgorithm := encryptionAlgorithm)))) case ""aws-kms-hierarchy"" => Success(Hierarchy(HierarchyKeyring(keyId := key))) case ""raw"" => var algorithm: string :- GetString(""encryption-algorithm"", obj); var providerId: string :- GetString(""provider-id"", obj); Need(RawAlgorithmString?(algorithm), ""Unsupported algorithm:"" + algorithm); match algorithm case ""aes"" => Success(AES(RawAES(keyId := key, providerId := providerId))) case ""rsa"" => var paddingAlgorithm: string :- GetString(""padding-algorithm"", obj); var paddingHash: string :- GetString(""padding-hash"", obj); Need(PaddingAlgorithmString?(paddingAlgorithm), ""Unsupported paddingAlgorithm:"" + paddingAlgorithm); Need(PaddingHashString?(paddingHash), ""Unsupported paddingHash:"" + paddingHash); match paddingAlgorithm case ""pkcs1"" => (Need(paddingHash == ""sha1"", ""Unsupported padding with pkcs1:"" + paddingHash); Success(RSA(RawRSA(keyId := key, providerId := providerId, padding := AwsCryptographyMaterialProvidersTypes.PKCS1)))) case ""oaep-mgf1"" => match paddingHash case ""sha1"" => Success(RSA(RawRSA(keyId := key, providerId := providerId, padding := AwsCryptographyMaterialProvidersTypes.OAEP_SHA1_MGF1))) case ""sha256"" => Success(RSA(RawRSA(keyId := key, providerId := providerId, padding := AwsCryptographyMaterialProvidersTypes.OAEP_SHA256_MGF1))) case ""sha384"" => Success(RSA(RawRSA(keyId := key, providerId := providerId, padding := AwsCryptographyMaterialProvidersTypes.OAEP_SHA384_MGF1))) case ""sha512"" => Success(RSA(RawRSA(keyId := key, providerId := providerId, padding := AwsCryptographyMaterialProvidersTypes.OAEP_SHA512_MGF1)))
  }

  function method ToDiscoveryFilter(obj: seq<(string, JSON)>): Option<AwsCryptographyMaterialProvidersTypes.DiscoveryFilter>
    decreases obj
  {
    var filter: seq<(string, JSON)> :- GetObject(""aws-kms-discovery-filter"", obj).ToOption(); var partition: string :- GetString(""partition"", filter).ToOption(); var accountIds: seq<string> :- GetArrayString(""account-ids"", filter).ToOption(); Some(AwsCryptographyMaterialProvidersTypes.DiscoveryFilter(partition := partition, accountIds := accountIds))
  }

  predicate method KeyDescriptionString?(s: string)
    decreases s
  {
    s == ""static-material-keyring"" || s == ""aws-kms"" || s == ""aws-kms-mrk-aware"" || s == ""aws-kms-mrk-aware-discovery"" || s == ""raw"" || s == ""aws-kms-hierarchy"" || s == ""aws-kms-rsa""
  }

  predicate method RawAlgorithmString?(s: string)
    decreases s
  {
    s == ""aes"" || s == ""rsa""
  }

  predicate method PaddingAlgorithmString?(s: string)
    decreases s
  {
    s == ""pkcs1"" || s == ""oaep-mgf1""
  }

  predicate method PaddingHashString?(s: string)
    decreases s
  {
    s == ""sha1"" || s == ""sha1"" || s == ""sha256"" || s == ""sha384"" || s == ""sha512""
  }

  predicate method EncryptionAlgorithmSpec?(s: string)
    decreases s
  {
    s == ""RSAES_OAEP_SHA_1"" || s == ""RSAES_OAEP_SHA_256""
  }
}

module {:options ""-functionSyntax:4""} KeyMaterial {

  import MPL = AwsCryptographyMaterialProvidersTypes

  import opened Values = JSON.Values

  import opened Wrappers

  import Seq

  import opened UInt = StandardLibrary.UInt

  import opened JSONHelpers

  import HexStrings

  import Base64
  datatype KeyMaterial = Symetric(name: string, encrypt: bool, decrypt: bool, algorithm: string, bits: nat, encoding: string, wrappingKey: MPL.Secret, keyIdentifier: string) | PrivateRSA(name: string, encrypt: bool, decrypt: bool, algorithm: string, bits: nat, encoding: string, material: string, keyIdentifier: string) | PublicRSA(name: string, encrypt: bool, decrypt: bool, bits: nat, algorithm: string, encoding: string, material: string, keyIdentifier: string) | KMS(name: string, encrypt: bool, decrypt: bool, keyIdentifier: string) | KMSAsymetric(name: string, encrypt: bool, decrypt: bool, keyIdentifier: string, bits: nat, algorithm: string, encoding: string, publicKey: MPL.Secret) | StaticMaterial(name: string, algorithmSuite: MPL.AlgorithmSuiteInfo, encryptionContext: MPL.EncryptionContext, encryptedDataKeys: MPL.EncryptedDataKeyList, requiredEncryptionContextKeys: MPL.EncryptionContextKeys, plaintextDataKey: Option<MPL.Secret> := None, signingKey: Option<MPL.Secret> := None, verificationKey: Option<MPL.Secret> := None, symmetricSigningKeys: Option<MPL.SymmetricSigningKeyList> := None) | StaticKeyStoreInformation(keyIdentifier: string, branchKeyVersion: MPL.Utf8Bytes, branchKey: MPL.Secret, beaconKey: MPL.Secret)

  function method BuildKeyMaterials(mpl: MPL.IAwsCryptographicMaterialProvidersClient, obj: seq<(string, JSON)>): Result<map<string, KeyMaterial>, string>
    decreases mpl, obj
  {
    if |obj| == 0 then
      Success(map[])
    else
      var name: string := obj[0].0; var keyMaterial: KeyMaterial :- ToKeyMaterial(mpl, name, obj[0].1); var tail: map<string, KeyMaterial> :- BuildKeyMaterials(mpl, obj[1..]); Success(map[name := keyMaterial] + tail)
  }

  function method ToKeyMaterial(mpl: MPL.IAwsCryptographicMaterialProvidersClient, name: string, obj: JSON): Result<KeyMaterial, string>
    decreases mpl, name, obj
  {
    Need(obj.Object?, ""KeyDescription not an object""); var obj: seq<(string, JSON)> := obj.obj; var typString: string := ""type""; var typ: string :- GetString(typString, obj); Need(KeyMaterialString?(typ), ""Unsupported KeyMaterial type:"" + typ); match typ case ""static-material"" => (var algorithmSuiteHex: string :- GetString(""algorithmSuiteId"", obj); Need(HexStrings.IsLooseHexString(algorithmSuiteHex), ""Not hex encoded binnary""); var binaryId: seq<uint8> := HexStrings.FromHexString(algorithmSuiteHex); var algorithmSuite: AlgorithmSuiteInfo :- mpl.GetAlgorithmSuiteInfo(binaryId).MapFailure((e: Error) => ""Invalid Suite:"" + algorithmSuiteHex); var encryptionContextStrings: map<string, string> :- SmallObjectToStringStringMap(""encryptionContext"", obj); var encryptionContext: Types.EncryptionContext :- utf8EncodeMap(encryptionContextStrings); var keysAsStrings: seq<string> :- GetArrayString(""requiredEncryptionContextKeys"", obj); var requiredEncryptionContextKeys: seq<Types.Utf8Bytes> :- utf8EncodeSeq(keysAsStrings); var encryptedDataKeysJSON: seq<seq<(string, JSON)>> :- GetArrayObject(""encryptedDataKeys"", obj); var encryptedDataKeys: seq<MPL.EncryptedDataKey> :- Seq.MapWithResult(ToEncryptedDataKey, encryptedDataKeysJSON); var plaintextDataKeyEncoded: Option<string> :- GetOptionalString(""plaintextDataKey"", obj); var plaintextDataKey: Option<seq<uint8>> :- if plaintextDataKeyEncoded.Some? then var result: Result<seq<uint8>, string> := Base64.Decode(plaintextDataKeyEncoded.value); if result.Success? then Success(Some(result.value)) else Failure(result.error) else Success(None); var signingKey: Option<string> :- GetOptionalString(""signingKey"", obj); var verificationKey: Option<string> :- GetOptionalString(""verificationKey"", obj); var symmetricSigningKeys: Option<seq<string>> := GetArrayString(""symmetricSigningKeys"", obj).ToOption(); Success(StaticMaterial(name := name, algorithmSuite := algorithmSuite, encryptionContext := encryptionContext, encryptedDataKeys := encryptedDataKeys, requiredEncryptionContextKeys := requiredEncryptionContextKeys, plaintextDataKey := plaintextDataKey, signingKey := None, verificationKey := None, symmetricSigningKeys := None))) case ""static-branch-key"" => (var keyIdentifier: string :- GetString(""key-id"", obj); var branchKeyVersionEncoded: string :- GetString(""branchKeyVersion"", obj); var branchKeyVersion: ValidUTF8Bytes :- UTF8.Encode(branchKeyVersionEncoded); var branchKeyEncoded: string :- GetString(""branchKey"", obj); var branchKey: seq<uint8> :- Base64.Decode(branchKeyEncoded); var beaconKeyEncoded: string :- GetString(""beaconKey"", obj); var beaconKey: seq<uint8> :- Base64.Decode(beaconKeyEncoded); Success(StaticKeyStoreInformation(keyIdentifier := keyIdentifier, branchKeyVersion := branchKeyVersion, branchKey := branchKey, beaconKey := beaconKey))) case _ /* _v0 */ => var encrypt: bool :- GetBool(""encrypt"", obj); var decrypt: bool :- GetBool(""decrypt"", obj); var keyIdentifier: string :- GetString(""key-id"", obj); match typ case ""aws-kms"" => Success(KeyMaterial.KMS(name := name, encrypt := encrypt, decrypt := decrypt, keyIdentifier := keyIdentifier)) case _ /* _v1 */ => var algorithm: string :- GetString(""algorithm"", obj); var bits: nat :- GetNat(""bits"", obj); var encoding: string :- GetString(""encoding"", obj); var material: string :- GetString(""material"", obj); match typ case ""symmetric"" => (var materialBytes: seq<uint8> :- Base64.Decode(material); Success(Symetric(name := name, encrypt := encrypt, decrypt := decrypt, keyIdentifier := keyIdentifier, algorithm := algorithm, bits := bits, encoding := encoding, wrappingKey := materialBytes))) case ""private"" => Success(PrivateRSA(name := name, encrypt := encrypt, decrypt := decrypt, keyIdentifier := keyIdentifier, algorithm := algorithm, bits := bits, encoding := encoding, material := material)) case ""public"" => Success(PublicRSA(name := name, encrypt := encrypt, decrypt := decrypt, keyIdentifier := keyIdentifier, algorithm := algorithm, bits := bits, encoding := encoding, material := material)) case ""aws-kms-rsa"" => var publicKey: ValidUTF8Bytes :- UTF8.Encode(material); Success(KMSAsymetric(name := name, encrypt := encrypt, decrypt := decrypt, keyIdentifier := keyIdentifier, algorithm := algorithm, bits := bits, encoding := encoding, publicKey := publicKey))
  }

  function method ToEncryptedDataKey(obj: seq<(string, JSON)>): Result<MPL.EncryptedDataKey, string>
    decreases obj
  {
    var keyProviderIdJSON: string :- GetString(""keyProviderId"", obj); var keyProviderInfoJSON: string :- GetString(""keyProviderInfo"", obj); var ciphertextJSON: string :- GetString(""ciphertext"", obj); var keyProviderId: ValidUTF8Bytes :- UTF8.Encode(keyProviderIdJSON); var keyProviderInfo: seq<uint8> :- Base64.Decode(keyProviderInfoJSON); var ciphertext: seq<uint8> :- Base64.Decode(ciphertextJSON); Success(MPL.EncryptedDataKey(keyProviderId := keyProviderId, keyProviderInfo := keyProviderInfo, ciphertext := ciphertext))
  }

  predicate method KeyMaterialString?(s: string)
    decreases s
  {
    s == ""static-material"" || s == ""aws-kms"" || s == ""symmetric"" || s == ""private"" || s == ""public"" || s == ""static-branch-key"" || s == ""aws-kms-rsa""
  }
}

module {:options ""-functionSyntax:4""} KeyringFromKeyDescription {

  import opened Types = AwsCryptographyMaterialProvidersTestVectorKeysTypes

  import MPL = AwsCryptographyMaterialProvidersTypes

  import opened Wrappers

  import KeyMaterial

  import CreateStaticKeyrings

  import CreateStaticKeyStores

  import AwsArnParsing
  datatype KeyringInfo = KeyringInfo(description: KeyDescription, material: Option<KeyMaterial.KeyMaterial>)

  method ToKeyring(mpl: MPL.IAwsCryptographicMaterialProvidersClient, info: KeyringInfo) returns (output: Result<MPL.IKeyring, Error>)
    requires mpl.ValidState()
    modifies mpl.Modifies
    ensures mpl.ValidState()
    ensures output.Success? ==> output.value.ValidState() && fresh(output.value.Modifies - mpl.Modifies - {mpl.History})
    decreases mpl, info
  {
    var KeyringInfo(description, material) := info;
    match description
    case {:split false} Static(StaticKeyring(key)) =>
      {
        :- Need(material.Some? && material.value.StaticMaterial?, KeyVectorException(message := ""Not type: StaticMaterial""));
        var encrypt := MPL.EncryptionMaterials(algorithmSuite := material.value.algorithmSuite, encryptedDataKeys := material.value.encryptedDataKeys, encryptionContext := material.value.encryptionContext, requiredEncryptionContextKeys := material.value.requiredEncryptionContextKeys, plaintextDataKey := material.value.plaintextDataKey, signingKey := material.value.signingKey, symmetricSigningKeys := material.value.symmetricSigningKeys);
        var decrypt := MPL.DecryptionMaterials(algorithmSuite := material.value.algorithmSuite, encryptionContext := material.value.encryptionContext, requiredEncryptionContextKeys := material.value.requiredEncryptionContextKeys, plaintextDataKey := material.value.plaintextDataKey, verificationKey := material.value.verificationKey, symmetricSigningKey := None);
        var keyring := CreateStaticKeyrings.CreateStaticMaterialsKeyring(encrypt, decrypt);
        return Success(keyring);
      }
    case {:split false} Kms(KMSInfo(key)) =>
      {
        :- Need(material.Some? && material.value.KMS?, KeyVectorException(message := ""Not type: KMS""));
        var kmsClient :- getKmsClient(mpl, material.value.keyIdentifier);
        var input := MPL.CreateAwsKmsKeyringInput(kmsKeyId := material.value.keyIdentifier, kmsClient := kmsClient, grantTokens := None);
        var keyring := mpl.CreateAwsKmsKeyring(input);
        return keyring.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
      }
    case {:split false} KmsMrk(KmsMrkAware(key)) =>
      {
        :- Need(material.Some? && material.value.KMS?, KeyVectorException(message := ""Not type: KMS""));
        var kmsClient :- getKmsClient(mpl, material.value.keyIdentifier);
        var input := MPL.CreateAwsKmsMrkKeyringInput(kmsKeyId := material.value.keyIdentifier, kmsClient := kmsClient, grantTokens := None);
        var keyring := mpl.CreateAwsKmsMrkKeyring(input);
        return keyring.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
      }
    case {:split false} KmsRsa(KmsRsaKeyring(key, encryptionAlgorithm)) =>
      {
        :- Need(material.Some? && material.value.KMSAsymetric?, KeyVectorException(message := ""Not type: KMSAsymetric""));
        var kmsClient :- getKmsClient(mpl, material.value.keyIdentifier);
        var input := MPL.CreateAwsKmsRsaKeyringInput(publicKey := Some(material.value.publicKey), kmsKeyId := material.value.keyIdentifier, encryptionAlgorithm := encryptionAlgorithm, kmsClient := Some(kmsClient), grantTokens := None);
        var keyring := mpl.CreateAwsKmsRsaKeyring(input);
        return keyring.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
      }
    case {:split false} Hierarchy(HierarchyKeyring(key)) =>
      {
        :- Need(material.Some? && material.value.StaticKeyStoreInformation?, KeyVectorException(message := ""Not type: StaticKeyStoreInformation""));
        var keyStore := CreateStaticKeyStores.CreateStaticKeyStore(material.value);
        var input := MPL.CreateAwsKmsHierarchicalKeyringInput(branchKeyId := Some(material.value.keyIdentifier), branchKeyIdSupplier := None, keyStore := keyStore, ttlSeconds := 0, cache := None);
        var keyring := mpl.CreateAwsKmsHierarchicalKeyring(input);
        return keyring.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
      }
    case {:split false} KmsMrkDiscovery(KmsMrkAwareDiscovery(_ /* _v0 */, defaultMrkRegion, awsKmsDiscoveryFilter)) =>
      {
        :- Need(material.None?, KeyVectorException(message := ""Discovery has not key""));
        var input := MPL.CreateAwsKmsMrkDiscoveryMultiKeyringInput(regions := [defaultMrkRegion], discoveryFilter := awsKmsDiscoveryFilter, clientSupplier := None, grantTokens := None);
        var keyring := mpl.CreateAwsKmsMrkDiscoveryMultiKeyring(input);
        return keyring.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
      }
    case {:split false} AES(RawAES(key, providerId)) =>
      {
        :- Need(material.Some? && material.value.Symetric?, KeyVectorException(message := ""Not type: Symetric""));
        var wrappingAlg :- match material.value.bits case 128 => Success(MPL.ALG_AES128_GCM_IV12_TAG16) case 192 => Success(MPL.ALG_AES192_GCM_IV12_TAG16) case 256 => Success(MPL.ALG_AES256_GCM_IV12_TAG16) case _ /* _v1 */ => Failure(KeyVectorException(message := ""Not a supported bit length""));
        var input := MPL.CreateRawAesKeyringInput(keyNamespace := providerId, keyName := material.value.keyIdentifier, wrappingKey := material.value.wrappingKey, wrappingAlg := wrappingAlg);
        var keyring := mpl.CreateRawAesKeyring(input);
        return keyring.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
      }
    case {:split false} RSA(RawRSA(key, providerId, padding)) =>
      {
        :- Need(material.Some? && (material.value.PrivateRSA? || material.value.PublicRSA?), KeyVectorException(message := ""Not type: PrivateRSA or PublicRSA""));
        match material
        case {:split false} Some(PrivateRSA(_ /* _v2 */, _ /* _v3 */, decrypt, _ /* _v4 */, _ /* _v5 */, _ /* _v6 */, material, keyIdentifier)) =>
          {
            :- Need(decrypt, KeyVectorException(message := ""Private RSA keys only supports decrypt.""));
            var privateKeyPemBytes :- UTF8.Encode(material).MapFailure((e: string) => KeyVectorException(message := e));
            var input := MPL.CreateRawRsaKeyringInput(keyNamespace := providerId, keyName := keyIdentifier, paddingScheme := padding, publicKey := None, privateKey := Some(privateKeyPemBytes));
            var keyring := mpl.CreateRawRsaKeyring(input);
            return keyring.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
          }
        case {:split false} Some(PublicRSA(_ /* _v7 */, encrypt, _ /* _v8 */, _ /* _v9 */, _ /* _v10 */, _ /* _v11 */, material, keyIdentifier)) =>
          {
            :- Need(encrypt, KeyVectorException(message := ""Public RSA keys only supports encrypt.""));
            var publicKeyPemBytes :- UTF8.Encode(material).MapFailure((e: string) => KeyVectorException(message := e));
            var input := MPL.CreateRawRsaKeyringInput(keyNamespace := providerId, keyName := keyIdentifier, paddingScheme := padding, publicKey := Some(publicKeyPemBytes), privateKey := None);
            var keyring := mpl.CreateRawRsaKeyring(input);
            return keyring.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
          }
      }
  }

  method getKmsClient(mpl: MPL.IAwsCryptographicMaterialProvidersClient, maybeKmsArn: string) returns (output: Result<ComAmazonawsKmsTypes.IKMSClient, Error>)
    requires mpl.ValidState()
    modifies mpl.Modifies
    ensures mpl.ValidState()
    ensures output.Success? ==> output.value.ValidState() && output.value.Modifies !! {mpl.History} && fresh(output.value) && fresh(output.value.Modifies - mpl.Modifies)
    decreases mpl, maybeKmsArn
  {
    var maybeClientSupplier := mpl.CreateDefaultClientSupplier(MPL.CreateDefaultClientSupplierInput);
    var clientSupplier :- maybeClientSupplier.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
    var arn :- AwsArnParsing.ParseAwsKmsArn(maybeKmsArn).MapFailure((e: string) => KeyVectorException(message := e));
    var tmp := clientSupplier.GetClient(MPL.GetClientInput(region := arn.region));
    output := tmp.MapFailure((e: Error) => AwsCryptographyMaterialProviders(e));
  }
}

module CreateStaticKeyrings {

  import opened Wrappers

  import Types = AwsCryptographyMaterialProvidersTypes
  class StaticMaterialsKeyring extends Types.IKeyring {
    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      true &&
      History in Modifies
    }

    constructor (encryptMaterial: Types.EncryptionMaterials, decryptMaterial: Types.DecryptionMaterials)
      ensures ValidState() && fresh(this) && fresh(History) && fresh(Modifies)
      decreases encryptMaterial, decryptMaterial
    {
      History := new Types.IKeyringCallHistory();
      Modifies := {History};
      this.encryptMaterial := encryptMaterial;
      this.decryptMaterial := decryptMaterial;
    }

    const encryptMaterial: Types.EncryptionMaterials
    const decryptMaterial: Types.DecryptionMaterials

    predicate OnEncryptEnsuresPublicly(input: Types.OnEncryptInput, output: Result<Types.OnEncryptOutput, Types.Error>)
      decreases input, output
    {
      true
    }

    method OnEncrypt'(input: Types.OnEncryptInput) returns (res: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, res)
      ensures unchanged(History)
      decreases Modifies - {History}
    {
      return Success(Types.OnEncryptOutput(materials := encryptMaterial));
    }

    predicate OnDecryptEnsuresPublicly(input: Types.OnDecryptInput, output: Result<Types.OnDecryptOutput, Types.Error>)
      decreases input, output
    {
      true
    }

    method OnDecrypt'(input: Types.OnDecryptInput) returns (res: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, res)
      ensures unchanged(History)
      decreases Modifies - {History}
    {
      return Success(Types.OnDecryptOutput(materials := decryptMaterial));
    }
  }

  method CreateStaticMaterialsKeyring(encryptMaterial: Types.EncryptionMaterials, decryptMaterial: Types.DecryptionMaterials) returns (keyring: Types.IKeyring)
    ensures keyring.ValidState() && fresh(keyring) && fresh(keyring.Modifies)
    decreases encryptMaterial, decryptMaterial
  {
    return new StaticMaterialsKeyring(encryptMaterial, decryptMaterial);
  }
}

module {:options ""-functionSyntax:4""} CreateStaticKeyStores {

  import MPL = AwsCryptographyMaterialProvidersTypes

  import opened Wrappers

  import opened AwsCryptographyKeyStoreTypes

  import KeyMaterial
  class StaticKeyStore extends IKeyStoreClient {
    constructor (staticKeyMaterial: KeyMaterial.KeyMaterial)
      requires staticKeyMaterial.StaticKeyStoreInformation?
      ensures ValidState() && fresh(History) && fresh(Modifies)
      decreases staticKeyMaterial
    {
      this.staticKeyMaterial := staticKeyMaterial;
      History := new IKeyStoreClientCallHistory();
      Modifies := {History};
    }

    const staticKeyMaterial: KeyMaterial.KeyMaterial

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      History in Modifies &&
      staticKeyMaterial.StaticKeyStoreInformation?
    }

    predicate GetActiveBranchKeyEnsuresPublicly(input: GetActiveBranchKeyInput, output: Result<GetActiveBranchKeyOutput, Error>)
      decreases input, output
    {
      true
    }

    method GetActiveBranchKey(input: GetActiveBranchKeyInput) returns (output: Result<GetActiveBranchKeyOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetActiveBranchKey
      ensures true && ValidState()
      ensures GetActiveBranchKeyEnsuresPublicly(input, output)
      ensures History.GetActiveBranchKey == old(History.GetActiveBranchKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Success(GetActiveBranchKeyOutput(branchKeyMaterials := BranchKeyMaterials(branchKeyIdentifier := input.branchKeyIdentifier, branchKeyVersion := staticKeyMaterial.branchKeyVersion, branchKey := staticKeyMaterial.branchKey, encryptionContext := map[])));
      History.GetActiveBranchKey := History.GetActiveBranchKey + [DafnyCallEvent(input, output)];
    }

    predicate GetBranchKeyVersionEnsuresPublicly(input: GetBranchKeyVersionInput, output: Result<GetBranchKeyVersionOutput, Error>)
      decreases input, output
    {
      true
    }

    method GetBranchKeyVersion(input: GetBranchKeyVersionInput) returns (output: Result<GetBranchKeyVersionOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetBranchKeyVersion
      ensures true && ValidState()
      ensures GetBranchKeyVersionEnsuresPublicly(input, output)
      ensures History.GetBranchKeyVersion == old(History.GetBranchKeyVersion) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Success(GetBranchKeyVersionOutput(branchKeyMaterials := BranchKeyMaterials(branchKeyIdentifier := input.branchKeyIdentifier, branchKeyVersion := staticKeyMaterial.branchKeyVersion, branchKey := staticKeyMaterial.branchKey, encryptionContext := map[])));
      History.GetBranchKeyVersion := History.GetBranchKeyVersion + [DafnyCallEvent(input, output)];
    }

    predicate GetBeaconKeyEnsuresPublicly(input: GetBeaconKeyInput, output: Result<GetBeaconKeyOutput, Error>)
      decreases input, output
    {
      true
    }

    method GetBeaconKey(input: GetBeaconKeyInput) returns (output: Result<GetBeaconKeyOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetBeaconKey
      ensures true && ValidState()
      ensures GetBeaconKeyEnsuresPublicly(input, output)
      ensures History.GetBeaconKey == old(History.GetBeaconKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Success(GetBeaconKeyOutput(beaconKeyMaterials := BeaconKeyMaterials(beaconKeyIdentifier := input.branchKeyIdentifier, beaconKey := Some(staticKeyMaterial.beaconKey), hmacKeys := None, encryptionContext := map[])));
      History.GetBeaconKey := History.GetBeaconKey + [DafnyCallEvent(input, output)];
    }

    predicate GetKeyStoreInfoEnsuresPublicly(output: Result<GetKeyStoreInfoOutput, Error>)
      decreases output
    {
      true
    }

    method GetKeyStoreInfo() returns (output: Result<GetKeyStoreInfoOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetKeyStoreInfo
      ensures true && ValidState()
      ensures GetKeyStoreInfoEnsuresPublicly(output)
      ensures History.GetKeyStoreInfo == old(History.GetKeyStoreInfo) + [DafnyCallEvent((), output)]
      decreases Modifies - {History}
    {
      output := Failure(KeyStoreException(message := ""Not Supported""));
      History.GetKeyStoreInfo := History.GetKeyStoreInfo + [DafnyCallEvent((), output)];
    }

    predicate CreateKeyStoreEnsuresPublicly(input: CreateKeyStoreInput, output: Result<CreateKeyStoreOutput, Error>)
      decreases input, output
    {
      true
    }

    method CreateKeyStore(input: CreateKeyStoreInput) returns (output: Result<CreateKeyStoreOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateKeyStore
      ensures true && ValidState()
      ensures CreateKeyStoreEnsuresPublicly(input, output)
      ensures History.CreateKeyStore == old(History.CreateKeyStore) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Failure(KeyStoreException(message := ""Not Supported""));
      History.CreateKeyStore := History.CreateKeyStore + [DafnyCallEvent(input, output)];
    }

    predicate CreateKeyEnsuresPublicly(input: CreateKeyInput, output: Result<CreateKeyOutput, Error>)
      decreases input, output
    {
      true
    }

    method CreateKey(input: CreateKeyInput) returns (output: Result<CreateKeyOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateKey
      ensures true && ValidState()
      ensures CreateKeyEnsuresPublicly(input, output)
      ensures History.CreateKey == old(History.CreateKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Failure(KeyStoreException(message := ""Not Supported""));
      History.CreateKey := History.CreateKey + [DafnyCallEvent(input, output)];
    }

    predicate VersionKeyEnsuresPublicly(input: VersionKeyInput, output: Result<VersionKeyOutput, Error>)
      decreases input, output
    {
      true
    }

    method VersionKey(input: VersionKeyInput) returns (output: Result<VersionKeyOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`VersionKey
      ensures true && ValidState()
      ensures VersionKeyEnsuresPublicly(input, output)
      ensures History.VersionKey == old(History.VersionKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Failure(KeyStoreException(message := ""Not Supported""));
      History.VersionKey := History.VersionKey + [DafnyCallEvent(input, output)];
    }
  }

  method CreateStaticKeyStore(staticKeyMaterial: KeyMaterial.KeyMaterial) returns (keyStore: IKeyStoreClient)
    requires staticKeyMaterial.StaticKeyStoreInformation?
    ensures keyStore.ValidState() && fresh(keyStore) && fresh(keyStore.Modifies)
    decreases staticKeyMaterial
  {
    return new StaticKeyStore(staticKeyMaterial);
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
namespace software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types {

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
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.DafnyCallEvent<I, O>;
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
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.DafnyCallEvent.DafnyCallEvent";
      s += "(";
      s += Dafny.Helpers.ToString(this._input);
      s += ", ";
      s += Dafny.Helpers.ToString(this._output);
      s += ")";
      return s;
    }
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IDafnyCallEvent<I, O> Default(I _default_I, O _default_O) {
      return create(_default_I, _default_O);
    }
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IDafnyCallEvent<I, O>> _TypeDescriptor(Dafny.TypeDescriptor<I> _td_I, Dafny.TypeDescriptor<O> _td_O) {
      return new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IDafnyCallEvent<I, O>>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.DafnyCallEvent<I, O>.Default(_td_I.Default(), _td_O.Default()));
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

  public interface _IGetKeyDescriptionInput {
    bool is_GetKeyDescriptionInput { get; }
    Dafny.ISequence<byte> dtor_json { get; }
    _IGetKeyDescriptionInput DowncastClone();
  }
  public class GetKeyDescriptionInput : _IGetKeyDescriptionInput {
    public readonly Dafny.ISequence<byte> _json;
    public GetKeyDescriptionInput(Dafny.ISequence<byte> json) {
      this._json = json;
    }
    public _IGetKeyDescriptionInput DowncastClone() {
      if (this is _IGetKeyDescriptionInput dt) { return dt; }
      return new GetKeyDescriptionInput(_json);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionInput;
      return oth != null && object.Equals(this._json, oth._json);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._json));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.GetKeyDescriptionInput.GetKeyDescriptionInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._json);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionInput theDefault = create(Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionInput>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetKeyDescriptionInput create(Dafny.ISequence<byte> json) {
      return new GetKeyDescriptionInput(json);
    }
    public static _IGetKeyDescriptionInput create_GetKeyDescriptionInput(Dafny.ISequence<byte> json) {
      return create(json);
    }
    public bool is_GetKeyDescriptionInput { get { return true; } }
    public Dafny.ISequence<byte> dtor_json {
      get {
        return this._json;
      }
    }
  }

  public interface _IGetKeyDescriptionOutput {
    bool is_GetKeyDescriptionOutput { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_keyDescription { get; }
    _IGetKeyDescriptionOutput DowncastClone();
  }
  public class GetKeyDescriptionOutput : _IGetKeyDescriptionOutput {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _keyDescription;
    public GetKeyDescriptionOutput(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription) {
      this._keyDescription = keyDescription;
    }
    public _IGetKeyDescriptionOutput DowncastClone() {
      if (this is _IGetKeyDescriptionOutput dt) { return dt; }
      return new GetKeyDescriptionOutput(_keyDescription);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionOutput;
      return oth != null && object.Equals(this._keyDescription, oth._keyDescription);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyDescription));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.GetKeyDescriptionOutput.GetKeyDescriptionOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyDescription);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput theDefault = create(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.Default());
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionOutput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetKeyDescriptionOutput create(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription) {
      return new GetKeyDescriptionOutput(keyDescription);
    }
    public static _IGetKeyDescriptionOutput create_GetKeyDescriptionOutput(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription) {
      return create(keyDescription);
    }
    public bool is_GetKeyDescriptionOutput { get { return true; } }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_keyDescription {
      get {
        return this._keyDescription;
      }
    }
  }

  public interface _IHierarchyKeyring {
    bool is_HierarchyKeyring { get; }
    Dafny.ISequence<char> dtor_keyId { get; }
    _IHierarchyKeyring DowncastClone();
  }
  public class HierarchyKeyring : _IHierarchyKeyring {
    public readonly Dafny.ISequence<char> _keyId;
    public HierarchyKeyring(Dafny.ISequence<char> keyId) {
      this._keyId = keyId;
    }
    public _IHierarchyKeyring DowncastClone() {
      if (this is _IHierarchyKeyring dt) { return dt; }
      return new HierarchyKeyring(_keyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.HierarchyKeyring;
      return oth != null && object.Equals(this._keyId, oth._keyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.HierarchyKeyring.HierarchyKeyring";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.HierarchyKeyring.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IHierarchyKeyring create(Dafny.ISequence<char> keyId) {
      return new HierarchyKeyring(keyId);
    }
    public static _IHierarchyKeyring create_HierarchyKeyring(Dafny.ISequence<char> keyId) {
      return create(keyId);
    }
    public bool is_HierarchyKeyring { get { return true; } }
    public Dafny.ISequence<char> dtor_keyId {
      get {
        return this._keyId;
      }
    }
  }

  public interface _IKeyDescription {
    bool is_Kms { get; }
    bool is_KmsMrk { get; }
    bool is_KmsMrkDiscovery { get; }
    bool is_RSA { get; }
    bool is_AES { get; }
    bool is_Static { get; }
    bool is_KmsRsa { get; }
    bool is_Hierarchy { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo dtor_Kms { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware dtor_KmsMrk { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery dtor_KmsMrkDiscovery { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA dtor_RSA { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES dtor_AES { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring dtor_Static { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring dtor_KmsRsa { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring dtor_Hierarchy { get; }
    _IKeyDescription DowncastClone();
  }
  public abstract class KeyDescription : _IKeyDescription {
    public KeyDescription() { }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription theDefault = create_Kms(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KMSInfo.Default());
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyDescription create_Kms(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo Kms) {
      return new KeyDescription_Kms(Kms);
    }
    public static _IKeyDescription create_KmsMrk(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware KmsMrk) {
      return new KeyDescription_KmsMrk(KmsMrk);
    }
    public static _IKeyDescription create_KmsMrkDiscovery(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery KmsMrkDiscovery) {
      return new KeyDescription_KmsMrkDiscovery(KmsMrkDiscovery);
    }
    public static _IKeyDescription create_RSA(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA RSA) {
      return new KeyDescription_RSA(RSA);
    }
    public static _IKeyDescription create_AES(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES AES) {
      return new KeyDescription_AES(AES);
    }
    public static _IKeyDescription create_Static(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring Static) {
      return new KeyDescription_Static(Static);
    }
    public static _IKeyDescription create_KmsRsa(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring KmsRsa) {
      return new KeyDescription_KmsRsa(KmsRsa);
    }
    public static _IKeyDescription create_Hierarchy(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring Hierarchy) {
      return new KeyDescription_Hierarchy(Hierarchy);
    }
    public bool is_Kms { get { return this is KeyDescription_Kms; } }
    public bool is_KmsMrk { get { return this is KeyDescription_KmsMrk; } }
    public bool is_KmsMrkDiscovery { get { return this is KeyDescription_KmsMrkDiscovery; } }
    public bool is_RSA { get { return this is KeyDescription_RSA; } }
    public bool is_AES { get { return this is KeyDescription_AES; } }
    public bool is_Static { get { return this is KeyDescription_Static; } }
    public bool is_KmsRsa { get { return this is KeyDescription_KmsRsa; } }
    public bool is_Hierarchy { get { return this is KeyDescription_Hierarchy; } }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo dtor_Kms {
      get {
        var d = this;
        return ((KeyDescription_Kms)d)._Kms;
      }
    }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware dtor_KmsMrk {
      get {
        var d = this;
        return ((KeyDescription_KmsMrk)d)._KmsMrk;
      }
    }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery dtor_KmsMrkDiscovery {
      get {
        var d = this;
        return ((KeyDescription_KmsMrkDiscovery)d)._KmsMrkDiscovery;
      }
    }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA dtor_RSA {
      get {
        var d = this;
        return ((KeyDescription_RSA)d)._RSA;
      }
    }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES dtor_AES {
      get {
        var d = this;
        return ((KeyDescription_AES)d)._AES;
      }
    }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring dtor_Static {
      get {
        var d = this;
        return ((KeyDescription_Static)d)._Static;
      }
    }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring dtor_KmsRsa {
      get {
        var d = this;
        return ((KeyDescription_KmsRsa)d)._KmsRsa;
      }
    }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring dtor_Hierarchy {
      get {
        var d = this;
        return ((KeyDescription_Hierarchy)d)._Hierarchy;
      }
    }
    public abstract _IKeyDescription DowncastClone();
  }
  public class KeyDescription_Kms : KeyDescription {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo _Kms;
    public KeyDescription_Kms(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo Kms) {
      this._Kms = Kms;
    }
    public override _IKeyDescription DowncastClone() {
      if (this is _IKeyDescription dt) { return dt; }
      return new KeyDescription_Kms(_Kms);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription_Kms;
      return oth != null && object.Equals(this._Kms, oth._Kms);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Kms));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KeyDescription.Kms";
      s += "(";
      s += Dafny.Helpers.ToString(this._Kms);
      s += ")";
      return s;
    }
  }
  public class KeyDescription_KmsMrk : KeyDescription {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware _KmsMrk;
    public KeyDescription_KmsMrk(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware KmsMrk) {
      this._KmsMrk = KmsMrk;
    }
    public override _IKeyDescription DowncastClone() {
      if (this is _IKeyDescription dt) { return dt; }
      return new KeyDescription_KmsMrk(_KmsMrk);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription_KmsMrk;
      return oth != null && object.Equals(this._KmsMrk, oth._KmsMrk);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KmsMrk));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KeyDescription.KmsMrk";
      s += "(";
      s += Dafny.Helpers.ToString(this._KmsMrk);
      s += ")";
      return s;
    }
  }
  public class KeyDescription_KmsMrkDiscovery : KeyDescription {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery _KmsMrkDiscovery;
    public KeyDescription_KmsMrkDiscovery(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery KmsMrkDiscovery) {
      this._KmsMrkDiscovery = KmsMrkDiscovery;
    }
    public override _IKeyDescription DowncastClone() {
      if (this is _IKeyDescription dt) { return dt; }
      return new KeyDescription_KmsMrkDiscovery(_KmsMrkDiscovery);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription_KmsMrkDiscovery;
      return oth != null && object.Equals(this._KmsMrkDiscovery, oth._KmsMrkDiscovery);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KmsMrkDiscovery));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KeyDescription.KmsMrkDiscovery";
      s += "(";
      s += Dafny.Helpers.ToString(this._KmsMrkDiscovery);
      s += ")";
      return s;
    }
  }
  public class KeyDescription_RSA : KeyDescription {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA _RSA;
    public KeyDescription_RSA(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA RSA) {
      this._RSA = RSA;
    }
    public override _IKeyDescription DowncastClone() {
      if (this is _IKeyDescription dt) { return dt; }
      return new KeyDescription_RSA(_RSA);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription_RSA;
      return oth != null && object.Equals(this._RSA, oth._RSA);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._RSA));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KeyDescription.RSA";
      s += "(";
      s += Dafny.Helpers.ToString(this._RSA);
      s += ")";
      return s;
    }
  }
  public class KeyDescription_AES : KeyDescription {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES _AES;
    public KeyDescription_AES(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES AES) {
      this._AES = AES;
    }
    public override _IKeyDescription DowncastClone() {
      if (this is _IKeyDescription dt) { return dt; }
      return new KeyDescription_AES(_AES);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription_AES;
      return oth != null && object.Equals(this._AES, oth._AES);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._AES));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KeyDescription.AES";
      s += "(";
      s += Dafny.Helpers.ToString(this._AES);
      s += ")";
      return s;
    }
  }
  public class KeyDescription_Static : KeyDescription {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring _Static;
    public KeyDescription_Static(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring Static) {
      this._Static = Static;
    }
    public override _IKeyDescription DowncastClone() {
      if (this is _IKeyDescription dt) { return dt; }
      return new KeyDescription_Static(_Static);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription_Static;
      return oth != null && object.Equals(this._Static, oth._Static);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Static));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KeyDescription.Static";
      s += "(";
      s += Dafny.Helpers.ToString(this._Static);
      s += ")";
      return s;
    }
  }
  public class KeyDescription_KmsRsa : KeyDescription {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring _KmsRsa;
    public KeyDescription_KmsRsa(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring KmsRsa) {
      this._KmsRsa = KmsRsa;
    }
    public override _IKeyDescription DowncastClone() {
      if (this is _IKeyDescription dt) { return dt; }
      return new KeyDescription_KmsRsa(_KmsRsa);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription_KmsRsa;
      return oth != null && object.Equals(this._KmsRsa, oth._KmsRsa);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KmsRsa));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KeyDescription.KmsRsa";
      s += "(";
      s += Dafny.Helpers.ToString(this._KmsRsa);
      s += ")";
      return s;
    }
  }
  public class KeyDescription_Hierarchy : KeyDescription {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring _Hierarchy;
    public KeyDescription_Hierarchy(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring Hierarchy) {
      this._Hierarchy = Hierarchy;
    }
    public override _IKeyDescription DowncastClone() {
      if (this is _IKeyDescription dt) { return dt; }
      return new KeyDescription_Hierarchy(_Hierarchy);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription_Hierarchy;
      return oth != null && object.Equals(this._Hierarchy, oth._Hierarchy);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Hierarchy));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KeyDescription.Hierarchy";
      s += "(";
      s += Dafny.Helpers.ToString(this._Hierarchy);
      s += ")";
      return s;
    }
  }

  public partial class IKeyVectorsClientCallHistory {
    public IKeyVectorsClientCallHistory() {
    }
  }

  public interface IKeyVectorsClient {
    Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> CreateTestVectorKeyring(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput input);
    Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> CreateWappedTestVectorKeyring(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput input);
    Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> GetKeyDescription(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionInput input);
    Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> SerializeKeyDescription(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionInput input);
  }
  public class _Companion_IKeyVectorsClient {
  }

  public interface _IKeyVectorsConfig {
    bool is_KeyVectorsConfig { get; }
    Dafny.ISequence<char> dtor_keyManifiestPath { get; }
    _IKeyVectorsConfig DowncastClone();
  }
  public class KeyVectorsConfig : _IKeyVectorsConfig {
    public readonly Dafny.ISequence<char> _keyManifiestPath;
    public KeyVectorsConfig(Dafny.ISequence<char> keyManifiestPath) {
      this._keyManifiestPath = keyManifiestPath;
    }
    public _IKeyVectorsConfig DowncastClone() {
      if (this is _IKeyVectorsConfig dt) { return dt; }
      return new KeyVectorsConfig(_keyManifiestPath);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyVectorsConfig;
      return oth != null && object.Equals(this._keyManifiestPath, oth._keyManifiestPath);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyManifiestPath));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KeyVectorsConfig.KeyVectorsConfig";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyManifiestPath);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyVectorsConfig theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyVectorsConfig Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyVectorsConfig> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyVectorsConfig>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyVectorsConfig.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyVectorsConfig> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyVectorsConfig create(Dafny.ISequence<char> keyManifiestPath) {
      return new KeyVectorsConfig(keyManifiestPath);
    }
    public static _IKeyVectorsConfig create_KeyVectorsConfig(Dafny.ISequence<char> keyManifiestPath) {
      return create(keyManifiestPath);
    }
    public bool is_KeyVectorsConfig { get { return true; } }
    public Dafny.ISequence<char> dtor_keyManifiestPath {
      get {
        return this._keyManifiestPath;
      }
    }
  }

  public interface _IKMSInfo {
    bool is_KMSInfo { get; }
    Dafny.ISequence<char> dtor_keyId { get; }
    _IKMSInfo DowncastClone();
  }
  public class KMSInfo : _IKMSInfo {
    public readonly Dafny.ISequence<char> _keyId;
    public KMSInfo(Dafny.ISequence<char> keyId) {
      this._keyId = keyId;
    }
    public _IKMSInfo DowncastClone() {
      if (this is _IKMSInfo dt) { return dt; }
      return new KMSInfo(_keyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KMSInfo;
      return oth != null && object.Equals(this._keyId, oth._keyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KMSInfo.KMSInfo";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KMSInfo.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKMSInfo create(Dafny.ISequence<char> keyId) {
      return new KMSInfo(keyId);
    }
    public static _IKMSInfo create_KMSInfo(Dafny.ISequence<char> keyId) {
      return create(keyId);
    }
    public bool is_KMSInfo { get { return true; } }
    public Dafny.ISequence<char> dtor_keyId {
      get {
        return this._keyId;
      }
    }
  }

  public interface _IKmsMrkAware {
    bool is_KmsMrkAware { get; }
    Dafny.ISequence<char> dtor_keyId { get; }
    _IKmsMrkAware DowncastClone();
  }
  public class KmsMrkAware : _IKmsMrkAware {
    public readonly Dafny.ISequence<char> _keyId;
    public KmsMrkAware(Dafny.ISequence<char> keyId) {
      this._keyId = keyId;
    }
    public _IKmsMrkAware DowncastClone() {
      if (this is _IKmsMrkAware dt) { return dt; }
      return new KmsMrkAware(_keyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsMrkAware;
      return oth != null && object.Equals(this._keyId, oth._keyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KmsMrkAware.KmsMrkAware";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsMrkAware.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKmsMrkAware create(Dafny.ISequence<char> keyId) {
      return new KmsMrkAware(keyId);
    }
    public static _IKmsMrkAware create_KmsMrkAware(Dafny.ISequence<char> keyId) {
      return create(keyId);
    }
    public bool is_KmsMrkAware { get { return true; } }
    public Dafny.ISequence<char> dtor_keyId {
      get {
        return this._keyId;
      }
    }
  }

  public interface _IKmsMrkAwareDiscovery {
    bool is_KmsMrkAwareDiscovery { get; }
    Dafny.ISequence<char> dtor_keyId { get; }
    Dafny.ISequence<char> dtor_defaultMrkRegion { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> dtor_awsKmsDiscoveryFilter { get; }
    _IKmsMrkAwareDiscovery DowncastClone();
  }
  public class KmsMrkAwareDiscovery : _IKmsMrkAwareDiscovery {
    public readonly Dafny.ISequence<char> _keyId;
    public readonly Dafny.ISequence<char> _defaultMrkRegion;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> _awsKmsDiscoveryFilter;
    public KmsMrkAwareDiscovery(Dafny.ISequence<char> keyId, Dafny.ISequence<char> defaultMrkRegion, Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> awsKmsDiscoveryFilter) {
      this._keyId = keyId;
      this._defaultMrkRegion = defaultMrkRegion;
      this._awsKmsDiscoveryFilter = awsKmsDiscoveryFilter;
    }
    public _IKmsMrkAwareDiscovery DowncastClone() {
      if (this is _IKmsMrkAwareDiscovery dt) { return dt; }
      return new KmsMrkAwareDiscovery(_keyId, _defaultMrkRegion, _awsKmsDiscoveryFilter);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsMrkAwareDiscovery;
      return oth != null && object.Equals(this._keyId, oth._keyId) && object.Equals(this._defaultMrkRegion, oth._defaultMrkRegion) && object.Equals(this._awsKmsDiscoveryFilter, oth._awsKmsDiscoveryFilter);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._defaultMrkRegion));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._awsKmsDiscoveryFilter));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KmsMrkAwareDiscovery.KmsMrkAwareDiscovery";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._defaultMrkRegion);
      s += ", ";
      s += Dafny.Helpers.ToString(this._awsKmsDiscoveryFilter);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>.Default());
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsMrkAwareDiscovery.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKmsMrkAwareDiscovery create(Dafny.ISequence<char> keyId, Dafny.ISequence<char> defaultMrkRegion, Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> awsKmsDiscoveryFilter) {
      return new KmsMrkAwareDiscovery(keyId, defaultMrkRegion, awsKmsDiscoveryFilter);
    }
    public static _IKmsMrkAwareDiscovery create_KmsMrkAwareDiscovery(Dafny.ISequence<char> keyId, Dafny.ISequence<char> defaultMrkRegion, Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> awsKmsDiscoveryFilter) {
      return create(keyId, defaultMrkRegion, awsKmsDiscoveryFilter);
    }
    public bool is_KmsMrkAwareDiscovery { get { return true; } }
    public Dafny.ISequence<char> dtor_keyId {
      get {
        return this._keyId;
      }
    }
    public Dafny.ISequence<char> dtor_defaultMrkRegion {
      get {
        return this._defaultMrkRegion;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> dtor_awsKmsDiscoveryFilter {
      get {
        return this._awsKmsDiscoveryFilter;
      }
    }
  }

  public interface _IKmsRsaKeyring {
    bool is_KmsRsaKeyring { get; }
    Dafny.ISequence<char> dtor_keyId { get; }
    software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec dtor_encryptionAlgorithm { get; }
    _IKmsRsaKeyring DowncastClone();
  }
  public class KmsRsaKeyring : _IKmsRsaKeyring {
    public readonly Dafny.ISequence<char> _keyId;
    public readonly software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec _encryptionAlgorithm;
    public KmsRsaKeyring(Dafny.ISequence<char> keyId, software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec encryptionAlgorithm) {
      this._keyId = keyId;
      this._encryptionAlgorithm = encryptionAlgorithm;
    }
    public _IKmsRsaKeyring DowncastClone() {
      if (this is _IKmsRsaKeyring dt) { return dt; }
      return new KmsRsaKeyring(_keyId, _encryptionAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsRsaKeyring;
      return oth != null && object.Equals(this._keyId, oth._keyId) && object.Equals(this._encryptionAlgorithm, oth._encryptionAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encryptionAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.KmsRsaKeyring.KmsRsaKeyring";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encryptionAlgorithm);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring theDefault = create(Dafny.Sequence<char>.Empty, software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.Default());
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsRsaKeyring.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKmsRsaKeyring create(Dafny.ISequence<char> keyId, software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec encryptionAlgorithm) {
      return new KmsRsaKeyring(keyId, encryptionAlgorithm);
    }
    public static _IKmsRsaKeyring create_KmsRsaKeyring(Dafny.ISequence<char> keyId, software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec encryptionAlgorithm) {
      return create(keyId, encryptionAlgorithm);
    }
    public bool is_KmsRsaKeyring { get { return true; } }
    public Dafny.ISequence<char> dtor_keyId {
      get {
        return this._keyId;
      }
    }
    public software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec dtor_encryptionAlgorithm {
      get {
        return this._encryptionAlgorithm;
      }
    }
  }

  public interface _IRawAES {
    bool is_RawAES { get; }
    Dafny.ISequence<char> dtor_keyId { get; }
    Dafny.ISequence<char> dtor_providerId { get; }
    _IRawAES DowncastClone();
  }
  public class RawAES : _IRawAES {
    public readonly Dafny.ISequence<char> _keyId;
    public readonly Dafny.ISequence<char> _providerId;
    public RawAES(Dafny.ISequence<char> keyId, Dafny.ISequence<char> providerId) {
      this._keyId = keyId;
      this._providerId = providerId;
    }
    public _IRawAES DowncastClone() {
      if (this is _IRawAES dt) { return dt; }
      return new RawAES(_keyId, _providerId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawAES;
      return oth != null && object.Equals(this._keyId, oth._keyId) && object.Equals(this._providerId, oth._providerId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._providerId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.RawAES.RawAES";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._providerId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawAES.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRawAES create(Dafny.ISequence<char> keyId, Dafny.ISequence<char> providerId) {
      return new RawAES(keyId, providerId);
    }
    public static _IRawAES create_RawAES(Dafny.ISequence<char> keyId, Dafny.ISequence<char> providerId) {
      return create(keyId, providerId);
    }
    public bool is_RawAES { get { return true; } }
    public Dafny.ISequence<char> dtor_keyId {
      get {
        return this._keyId;
      }
    }
    public Dafny.ISequence<char> dtor_providerId {
      get {
        return this._providerId;
      }
    }
  }

  public interface _IRawRSA {
    bool is_RawRSA { get; }
    Dafny.ISequence<char> dtor_keyId { get; }
    Dafny.ISequence<char> dtor_providerId { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme dtor_padding { get; }
    _IRawRSA DowncastClone();
  }
  public class RawRSA : _IRawRSA {
    public readonly Dafny.ISequence<char> _keyId;
    public readonly Dafny.ISequence<char> _providerId;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme _padding;
    public RawRSA(Dafny.ISequence<char> keyId, Dafny.ISequence<char> providerId, software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme padding) {
      this._keyId = keyId;
      this._providerId = providerId;
      this._padding = padding;
    }
    public _IRawRSA DowncastClone() {
      if (this is _IRawRSA dt) { return dt; }
      return new RawRSA(_keyId, _providerId, _padding);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawRSA;
      return oth != null && object.Equals(this._keyId, oth._keyId) && object.Equals(this._providerId, oth._providerId) && object.Equals(this._padding, oth._padding);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._providerId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._padding));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.RawRSA.RawRSA";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._providerId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._padding);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.Default());
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawRSA.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRawRSA create(Dafny.ISequence<char> keyId, Dafny.ISequence<char> providerId, software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme padding) {
      return new RawRSA(keyId, providerId, padding);
    }
    public static _IRawRSA create_RawRSA(Dafny.ISequence<char> keyId, Dafny.ISequence<char> providerId, software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme padding) {
      return create(keyId, providerId, padding);
    }
    public bool is_RawRSA { get { return true; } }
    public Dafny.ISequence<char> dtor_keyId {
      get {
        return this._keyId;
      }
    }
    public Dafny.ISequence<char> dtor_providerId {
      get {
        return this._providerId;
      }
    }
    public software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme dtor_padding {
      get {
        return this._padding;
      }
    }
  }

  public interface _ISerializeKeyDescriptionInput {
    bool is_SerializeKeyDescriptionInput { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_keyDescription { get; }
    _ISerializeKeyDescriptionInput DowncastClone();
  }
  public class SerializeKeyDescriptionInput : _ISerializeKeyDescriptionInput {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _keyDescription;
    public SerializeKeyDescriptionInput(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription) {
      this._keyDescription = keyDescription;
    }
    public _ISerializeKeyDescriptionInput DowncastClone() {
      if (this is _ISerializeKeyDescriptionInput dt) { return dt; }
      return new SerializeKeyDescriptionInput(_keyDescription);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.SerializeKeyDescriptionInput;
      return oth != null && object.Equals(this._keyDescription, oth._keyDescription);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyDescription));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.SerializeKeyDescriptionInput.SerializeKeyDescriptionInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyDescription);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionInput theDefault = create(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.Default());
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionInput>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.SerializeKeyDescriptionInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISerializeKeyDescriptionInput create(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription) {
      return new SerializeKeyDescriptionInput(keyDescription);
    }
    public static _ISerializeKeyDescriptionInput create_SerializeKeyDescriptionInput(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription) {
      return create(keyDescription);
    }
    public bool is_SerializeKeyDescriptionInput { get { return true; } }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_keyDescription {
      get {
        return this._keyDescription;
      }
    }
  }

  public interface _ISerializeKeyDescriptionOutput {
    bool is_SerializeKeyDescriptionOutput { get; }
    Dafny.ISequence<byte> dtor_json { get; }
    _ISerializeKeyDescriptionOutput DowncastClone();
  }
  public class SerializeKeyDescriptionOutput : _ISerializeKeyDescriptionOutput {
    public readonly Dafny.ISequence<byte> _json;
    public SerializeKeyDescriptionOutput(Dafny.ISequence<byte> json) {
      this._json = json;
    }
    public _ISerializeKeyDescriptionOutput DowncastClone() {
      if (this is _ISerializeKeyDescriptionOutput dt) { return dt; }
      return new SerializeKeyDescriptionOutput(_json);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.SerializeKeyDescriptionOutput;
      return oth != null && object.Equals(this._json, oth._json);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._json));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.SerializeKeyDescriptionOutput.SerializeKeyDescriptionOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this._json);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionOutput theDefault = create(Dafny.Sequence<byte>.Empty);
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionOutput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionOutput>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.SerializeKeyDescriptionOutput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISerializeKeyDescriptionOutput create(Dafny.ISequence<byte> json) {
      return new SerializeKeyDescriptionOutput(json);
    }
    public static _ISerializeKeyDescriptionOutput create_SerializeKeyDescriptionOutput(Dafny.ISequence<byte> json) {
      return create(json);
    }
    public bool is_SerializeKeyDescriptionOutput { get { return true; } }
    public Dafny.ISequence<byte> dtor_json {
      get {
        return this._json;
      }
    }
  }

  public interface _IStaticKeyring {
    bool is_StaticKeyring { get; }
    Dafny.ISequence<char> dtor_keyId { get; }
    _IStaticKeyring DowncastClone();
  }
  public class StaticKeyring : _IStaticKeyring {
    public readonly Dafny.ISequence<char> _keyId;
    public StaticKeyring(Dafny.ISequence<char> keyId) {
      this._keyId = keyId;
    }
    public _IStaticKeyring DowncastClone() {
      if (this is _IStaticKeyring dt) { return dt; }
      return new StaticKeyring(_keyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.StaticKeyring;
      return oth != null && object.Equals(this._keyId, oth._keyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.StaticKeyring.StaticKeyring";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.StaticKeyring.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStaticKeyring create(Dafny.ISequence<char> keyId) {
      return new StaticKeyring(keyId);
    }
    public static _IStaticKeyring create_StaticKeyring(Dafny.ISequence<char> keyId) {
      return create(keyId);
    }
    public bool is_StaticKeyring { get { return true; } }
    public Dafny.ISequence<char> dtor_keyId {
      get {
        return this._keyId;
      }
    }
  }

  public interface _ITestVectorKeyringInput {
    bool is_TestVectorKeyringInput { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_keyDescription { get; }
    _ITestVectorKeyringInput DowncastClone();
  }
  public class TestVectorKeyringInput : _ITestVectorKeyringInput {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _keyDescription;
    public TestVectorKeyringInput(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription) {
      this._keyDescription = keyDescription;
    }
    public _ITestVectorKeyringInput DowncastClone() {
      if (this is _ITestVectorKeyringInput dt) { return dt; }
      return new TestVectorKeyringInput(_keyDescription);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.TestVectorKeyringInput;
      return oth != null && object.Equals(this._keyDescription, oth._keyDescription);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyDescription));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.TestVectorKeyringInput.TestVectorKeyringInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyDescription);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput theDefault = create(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.Default());
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.TestVectorKeyringInput.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITestVectorKeyringInput create(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription) {
      return new TestVectorKeyringInput(keyDescription);
    }
    public static _ITestVectorKeyringInput create_TestVectorKeyringInput(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription) {
      return create(keyDescription);
    }
    public bool is_TestVectorKeyringInput { get { return true; } }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_keyDescription {
      get {
        return this._keyDescription;
      }
    }
  }

  public interface _IError {
    bool is_KeyVectorException { get; }
    bool is_AwsCryptographyMaterialProviders { get; }
    bool is_ComAmazonawsKms { get; }
    bool is_CollectionOfErrors { get; }
    bool is_Opaque { get; }
    Dafny.ISequence<char> dtor_message { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types._IError dtor_AwsCryptographyMaterialProviders { get; }
    software.amazon.cryptography.services.kms.internaldafny.types._IError dtor_ComAmazonawsKms { get; }
    Dafny.ISequence<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> dtor_list { get; }
    object dtor_obj { get; }
    _IError DowncastClone();
  }
  public abstract class Error : _IError {
    public Error() { }
    private static readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError theDefault = create_KeyVectorException(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IError create_KeyVectorException(Dafny.ISequence<char> message) {
      return new Error_KeyVectorException(message);
    }
    public static _IError create_AwsCryptographyMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.types._IError AwsCryptographyMaterialProviders) {
      return new Error_AwsCryptographyMaterialProviders(AwsCryptographyMaterialProviders);
    }
    public static _IError create_ComAmazonawsKms(software.amazon.cryptography.services.kms.internaldafny.types._IError ComAmazonawsKms) {
      return new Error_ComAmazonawsKms(ComAmazonawsKms);
    }
    public static _IError create_CollectionOfErrors(Dafny.ISequence<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> list, Dafny.ISequence<char> message) {
      return new Error_CollectionOfErrors(list, message);
    }
    public static _IError create_Opaque(object obj) {
      return new Error_Opaque(obj);
    }
    public bool is_KeyVectorException { get { return this is Error_KeyVectorException; } }
    public bool is_AwsCryptographyMaterialProviders { get { return this is Error_AwsCryptographyMaterialProviders; } }
    public bool is_ComAmazonawsKms { get { return this is Error_ComAmazonawsKms; } }
    public bool is_CollectionOfErrors { get { return this is Error_CollectionOfErrors; } }
    public bool is_Opaque { get { return this is Error_Opaque; } }
    public Dafny.ISequence<char> dtor_message {
      get {
        var d = this;
        if (d is Error_KeyVectorException) { return ((Error_KeyVectorException)d)._message; }
        return ((Error_CollectionOfErrors)d)._message;
      }
    }
    public software.amazon.cryptography.materialproviders.internaldafny.types._IError dtor_AwsCryptographyMaterialProviders {
      get {
        var d = this;
        return ((Error_AwsCryptographyMaterialProviders)d)._AwsCryptographyMaterialProviders;
      }
    }
    public software.amazon.cryptography.services.kms.internaldafny.types._IError dtor_ComAmazonawsKms {
      get {
        var d = this;
        return ((Error_ComAmazonawsKms)d)._ComAmazonawsKms;
      }
    }
    public Dafny.ISequence<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> dtor_list {
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
  public class Error_KeyVectorException : Error {
    public readonly Dafny.ISequence<char> _message;
    public Error_KeyVectorException(Dafny.ISequence<char> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_KeyVectorException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error_KeyVectorException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.Error.KeyVectorException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_AwsCryptographyMaterialProviders : Error {
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._IError _AwsCryptographyMaterialProviders;
    public Error_AwsCryptographyMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.types._IError AwsCryptographyMaterialProviders) {
      this._AwsCryptographyMaterialProviders = AwsCryptographyMaterialProviders;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_AwsCryptographyMaterialProviders(_AwsCryptographyMaterialProviders);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error_AwsCryptographyMaterialProviders;
      return oth != null && object.Equals(this._AwsCryptographyMaterialProviders, oth._AwsCryptographyMaterialProviders);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._AwsCryptographyMaterialProviders));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.Error.AwsCryptographyMaterialProviders";
      s += "(";
      s += Dafny.Helpers.ToString(this._AwsCryptographyMaterialProviders);
      s += ")";
      return s;
    }
  }
  public class Error_ComAmazonawsKms : Error {
    public readonly software.amazon.cryptography.services.kms.internaldafny.types._IError _ComAmazonawsKms;
    public Error_ComAmazonawsKms(software.amazon.cryptography.services.kms.internaldafny.types._IError ComAmazonawsKms) {
      this._ComAmazonawsKms = ComAmazonawsKms;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_ComAmazonawsKms(_ComAmazonawsKms);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error_ComAmazonawsKms;
      return oth != null && object.Equals(this._ComAmazonawsKms, oth._ComAmazonawsKms);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ComAmazonawsKms));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.Error.ComAmazonawsKms";
      s += "(";
      s += Dafny.Helpers.ToString(this._ComAmazonawsKms);
      s += ")";
      return s;
    }
  }
  public class Error_CollectionOfErrors : Error {
    public readonly Dafny.ISequence<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _list;
    public readonly Dafny.ISequence<char> _message;
    public Error_CollectionOfErrors(Dafny.ISequence<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> list, Dafny.ISequence<char> message) {
      this._list = list;
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CollectionOfErrors(_list, _message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error_CollectionOfErrors;
      return oth != null && object.Equals(this._list, oth._list) && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._list));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.Error.CollectionOfErrors";
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
      var oth = other as software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error_Opaque;
      return oth != null && this._obj == oth._obj;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types_Compile.Error.Opaque";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ")";
      return s;
    }
  }

  public partial class OpaqueError {
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _TypeDescriptor() {
      return _TYPE;
    }
  }

} // end of namespace software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types
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
namespace JSONHelpers_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> BvToBytes(Dafny.ISequence<byte> bits) {
      return ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim0 = new BigInteger((bits).Count);
        var arr0 = new byte[Dafny.Helpers.ToIntChecked(dim0, "array size exceeds memory limit")];
        for (int i0 = 0; i0 < dim0; i0++) {
          var _0_i = (BigInteger) i0;
          arr0[(int)(_0_i)] = (byte)((bits).Select(_0_i));
        }
        return Dafny.Sequence<byte>.FromArray(arr0);
      }))();
    }
    public static Dafny.ISequence<byte> BytesBv(Dafny.ISequence<byte> bits) {
      return ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim1 = new BigInteger((bits).Count);
        var arr1 = new byte[Dafny.Helpers.ToIntChecked(dim1, "array size exceeds memory limit")];
        for (int i1 = 0; i1 < dim1; i1++) {
          var _1_i = (BigInteger) i1;
          arr1[(int)(_1_i)] = (byte)((bits).Select(_1_i));
        }
        return Dafny.Sequence<byte>.FromArray(arr1);
      }))();
    }
    public static Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> Get(Dafny.ISequence<char> key, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((obj).Count)).Sign == 0) {
        return Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Key: "), key), Dafny.Sequence<char>.FromString(" does not exist")));
      } else if ((((obj).Select(BigInteger.Zero)).dtor__0).Equals(key)) {
        return Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>>.create_Success(((obj).Select(BigInteger.Zero)).dtor__1);
      } else {
        Dafny.ISequence<char> _in0 = key;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _in1 = (obj).Drop(BigInteger.One);
        key = _in0;
        obj = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> GetString(Dafny.ISequence<char> key, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _2_valueOrError0 = JSONHelpers_Compile.__default.Get(key, obj);
      if ((_2_valueOrError0).IsFailure()) {
        return (_2_valueOrError0).PropagateFailure<Dafny.ISequence<char>>();
      } else {
        JSON_mValues_Compile._IJSON _3_obj = (_2_valueOrError0).Extract();
        Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _4_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((_3_obj).is_String, Dafny.Sequence<char>.FromString("Not a string"));
        if ((_4_valueOrError1).IsFailure()) {
          return (_4_valueOrError1).PropagateFailure<Dafny.ISequence<char>>();
        } else {
          return Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.create_Success((_3_obj).dtor_str);
        }
      }
    }
    public static Wrappers_Compile._IResult<bool, Dafny.ISequence<char>> GetBool(Dafny.ISequence<char> key, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _5_valueOrError0 = JSONHelpers_Compile.__default.Get(key, obj);
      if ((_5_valueOrError0).IsFailure()) {
        return (_5_valueOrError0).PropagateFailure<bool>();
      } else {
        JSON_mValues_Compile._IJSON _6_obj = (_5_valueOrError0).Extract();
        Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _7_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((_6_obj).is_Bool, Dafny.Sequence<char>.FromString("Not a bool"));
        if ((_7_valueOrError1).IsFailure()) {
          return (_7_valueOrError1).PropagateFailure<bool>();
        } else {
          return Wrappers_Compile.Result<bool, Dafny.ISequence<char>>.create_Success((_6_obj).dtor_b);
        }
      }
    }
    public static Wrappers_Compile._IResult<BigInteger, Dafny.ISequence<char>> GetNat(Dafny.ISequence<char> key, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _8_valueOrError0 = JSONHelpers_Compile.__default.Get(key, obj);
      if ((_8_valueOrError0).IsFailure()) {
        return (_8_valueOrError0).PropagateFailure<BigInteger>();
      } else {
        JSON_mValues_Compile._IJSON _9_obj = (_8_valueOrError0).Extract();
        Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _10_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((_9_obj).is_Number, Dafny.Sequence<char>.FromString("Not a number"));
        if ((_10_valueOrError1).IsFailure()) {
          return (_10_valueOrError1).PropagateFailure<BigInteger>();
        } else {
          Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _11_valueOrError2 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((((_9_obj).dtor_num).dtor_n).Sign == 1, Dafny.Sequence<char>.FromString("Not a nat"));
          if ((_11_valueOrError2).IsFailure()) {
            return (_11_valueOrError2).PropagateFailure<BigInteger>();
          } else {
            return Wrappers_Compile.Result<BigInteger, Dafny.ISequence<char>>.create_Success(((_9_obj).dtor_num).dtor_n);
          }
        }
      }
    }
    public static Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.ISequence<char>> GetOptionalString(Dafny.ISequence<char> key, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
      Wrappers_Compile._IOption<JSON_mValues_Compile._IJSON> _12_obj = (JSONHelpers_Compile.__default.Get(key, obj)).ToOption();
      if ((_12_obj).is_Some) {
        Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _13_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(((_12_obj).dtor_value).is_String, Dafny.Sequence<char>.FromString("Not a string"));
        if ((_13_valueOrError0).IsFailure()) {
          return (_13_valueOrError0).PropagateFailure<Wrappers_Compile._IOption<Dafny.ISequence<char>>>();
        } else {
          return Wrappers_Compile.Result<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.ISequence<char>>.create_Success(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(((_12_obj).dtor_value).dtor_str));
        }
      } else {
        return Wrappers_Compile.Result<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.ISequence<char>>.create_Success(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None());
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, Dafny.ISequence<char>> GetObject(Dafny.ISequence<char> key, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _14_valueOrError0 = JSONHelpers_Compile.__default.Get(key, obj);
      if ((_14_valueOrError0).IsFailure()) {
        return (_14_valueOrError0).PropagateFailure<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>>();
      } else {
        JSON_mValues_Compile._IJSON _15_obj = (_14_valueOrError0).Extract();
        Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _16_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((_15_obj).is_Object, Dafny.Sequence<char>.FromString("Not an object"));
        if ((_16_valueOrError1).IsFailure()) {
          return (_16_valueOrError1).PropagateFailure<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>>();
        } else {
          return Wrappers_Compile.Result<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, Dafny.ISequence<char>>.create_Success((_15_obj).dtor_obj);
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<JSON_mValues_Compile._IJSON>, Dafny.ISequence<char>> GetArray(Dafny.ISequence<char> key, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _17_valueOrError0 = JSONHelpers_Compile.__default.Get(key, obj);
      if ((_17_valueOrError0).IsFailure()) {
        return (_17_valueOrError0).PropagateFailure<Dafny.ISequence<JSON_mValues_Compile._IJSON>>();
      } else {
        JSON_mValues_Compile._IJSON _18_obj = (_17_valueOrError0).Extract();
        Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _19_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((_18_obj).is_Array, Dafny.Sequence<char>.FromString("Not an array"));
        if ((_19_valueOrError1).IsFailure()) {
          return (_19_valueOrError1).PropagateFailure<Dafny.ISequence<JSON_mValues_Compile._IJSON>>();
        } else {
          return Wrappers_Compile.Result<Dafny.ISequence<JSON_mValues_Compile._IJSON>, Dafny.ISequence<char>>.create_Success((_18_obj).dtor_arr);
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<Dafny.ISequence<char>>, Dafny.ISequence<char>> GetArrayString(Dafny.ISequence<char> key, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _20_valueOrError0 = JSONHelpers_Compile.__default.Get(key, obj);
      if ((_20_valueOrError0).IsFailure()) {
        return (_20_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.ISequence<char>>>();
      } else {
        JSON_mValues_Compile._IJSON _21_obj = (_20_valueOrError0).Extract();
        Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _22_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(((_21_obj).is_Array) && (Dafny.Helpers.Id<Func<JSON_mValues_Compile._IJSON, bool>>((_23_obj) => Dafny.Helpers.Quantifier<JSON_mValues_Compile._IJSON>(((_23_obj).dtor_arr).UniqueElements, true, (((_forall_var_0) => {
          JSON_mValues_Compile._IJSON _24_s = (JSON_mValues_Compile._IJSON)_forall_var_0;
          return !(((_23_obj).dtor_arr).Contains(_24_s)) || ((_24_s).is_String);
        }))))(_21_obj)), Dafny.Sequence<char>.FromString("Not an array of strings"));
        if ((_22_valueOrError1).IsFailure()) {
          return (_22_valueOrError1).PropagateFailure<Dafny.ISequence<Dafny.ISequence<char>>>();
        } else {
          Dafny.ISequence<JSON_mValues_Compile._IJSON> _25_arr = (_21_obj).dtor_arr;
          return Wrappers_Compile.Result<Dafny.ISequence<Dafny.ISequence<char>>, Dafny.ISequence<char>>.create_Success(((System.Func<Dafny.ISequence<Dafny.ISequence<char>>>) (() => {
  BigInteger dim2 = new BigInteger((_25_arr).Count);
  var arr2 = new Dafny.ISequence<char>[Dafny.Helpers.ToIntChecked(dim2, "array size exceeds memory limit")];
  for (int i2 = 0; i2 < dim2; i2++) {
    var _26_n = (BigInteger) i2;
    arr2[(int)(_26_n)] = ((_25_arr).Select(_26_n)).dtor_str;
  }
  return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(arr2);
}))());
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>>, Dafny.ISequence<char>> GetArrayObject(Dafny.ISequence<char> key, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _27_valueOrError0 = JSONHelpers_Compile.__default.Get(key, obj);
      if ((_27_valueOrError0).IsFailure()) {
        return (_27_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>>>();
      } else {
        JSON_mValues_Compile._IJSON _28_obj = (_27_valueOrError0).Extract();
        Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _29_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(((_28_obj).is_Array) && (Dafny.Helpers.Id<Func<JSON_mValues_Compile._IJSON, bool>>((_30_obj) => Dafny.Helpers.Quantifier<JSON_mValues_Compile._IJSON>(((_30_obj).dtor_arr).UniqueElements, true, (((_forall_var_1) => {
          JSON_mValues_Compile._IJSON _31_s = (JSON_mValues_Compile._IJSON)_forall_var_1;
          return !(((_30_obj).dtor_arr).Contains(_31_s)) || ((_31_s).is_Object);
        }))))(_28_obj)), Dafny.Sequence<char>.FromString("Not an array of objects"));
        if ((_29_valueOrError1).IsFailure()) {
          return (_29_valueOrError1).PropagateFailure<Dafny.ISequence<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>>>();
        } else {
          Dafny.ISequence<JSON_mValues_Compile._IJSON> _32_arr = (_28_obj).dtor_arr;
          return Wrappers_Compile.Result<Dafny.ISequence<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>>, Dafny.ISequence<char>>.create_Success(((System.Func<Dafny.ISequence<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>>>) (() => {
  BigInteger dim3 = new BigInteger((_32_arr).Count);
  var arr3 = new Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>[Dafny.Helpers.ToIntChecked(dim3, "array size exceeds memory limit")];
  for (int i3 = 0; i3 < dim3; i3++) {
    var _33_n = (BigInteger) i3;
    arr3[(int)(_33_n)] = ((_32_arr).Select(_33_n)).dtor_obj;
  }
  return Dafny.Sequence<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>>.FromArray(arr3);
}))());
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>, Dafny.ISequence<char>> SmallObjectToStringStringMap(Dafny.ISequence<char> key, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _34_valueOrError0 = JSONHelpers_Compile.__default.Get(key, obj);
      if ((_34_valueOrError0).IsFailure()) {
        return (_34_valueOrError0).PropagateFailure<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>();
      } else {
        JSON_mValues_Compile._IJSON _35_item = (_34_valueOrError0).Extract();
        Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _36_valueOrError1 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((_35_item).is_Object, Dafny.Sequence<char>.FromString("Not an object"));
        if ((_36_valueOrError1).IsFailure()) {
          return (_36_valueOrError1).PropagateFailure<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>();
        } else {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _37_obj = (_35_item).dtor_obj;
          Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _38_valueOrError2 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(Dafny.Helpers.Id<Func<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, bool>>((_39_obj) => Dafny.Helpers.Quantifier<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>((_39_obj).UniqueElements, true, (((_forall_var_2) => {
            _System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON> _40_t = (_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>)_forall_var_2;
            return !((_39_obj).Contains(_40_t)) || (((_40_t).dtor__1).is_String);
          }))))(_37_obj), Dafny.Sequence<char>.FromString("Not a string string object"));
          if ((_38_valueOrError2).IsFailure()) {
            return (_38_valueOrError2).PropagateFailure<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>();
          } else {
            Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _41_valueOrError3 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(Dafny.Helpers.Id<Func<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, bool>>((_42_obj) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_42_obj).Count)), true, (((_forall_var_3) => {
              BigInteger _43_i = (BigInteger)_forall_var_3;
              return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange((_43_i) + (BigInteger.One), new BigInteger((_42_obj).Count)), true, (((_forall_var_4) => {
                BigInteger _44_j = (BigInteger)_forall_var_4;
                return !((((_43_i).Sign != -1) && ((_43_i) < (_44_j))) && ((_44_j) < (new BigInteger((_42_obj).Count)))) || (!(((_42_obj).Select(_43_i)).dtor__0).Equals(((_42_obj).Select(_44_j)).dtor__0));
              })));
            }))))(_37_obj), Dafny.Sequence<char>.FromString("JSON serialization Error"));
            if ((_41_valueOrError3).IsFailure()) {
              return (_41_valueOrError3).PropagateFailure<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>();
            } else {
              return Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>, Dafny.ISequence<char>>.create_Success(Dafny.Helpers.Id<Func<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>>((_45_obj) => ((System.Func<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>)(() => {
  var _coll0 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<char>,Dafny.ISequence<char>>>();
  foreach (_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON> _compr_0 in (_45_obj).Elements) {
    _System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON> _46_t = (_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>)_compr_0;
    if ((_45_obj).Contains(_46_t)) {
      _coll0.Add(new Dafny.Pair<Dafny.ISequence<char>,Dafny.ISequence<char>>((_46_t).dtor__0, ((_46_t).dtor__1).dtor_str));
    }
  }
  return Dafny.Map<Dafny.ISequence<char>,Dafny.ISequence<char>>.FromCollection(_coll0);
}))())(_37_obj));
            }
          }
        }
      }
    }
    public static Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>> utf8EncodePair(Dafny.ISequence<char> key, Dafny.ISequence<char> @value)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _47_valueOrError0 = UTF8.__default.Encode(key);
      if ((_47_valueOrError0).IsFailure()) {
        return (_47_valueOrError0).PropagateFailure<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>();
      } else {
        Dafny.ISequence<byte> _48_utf8Key = (_47_valueOrError0).Extract();
        Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _49_valueOrError1 = UTF8.__default.Encode(@value);
        if ((_49_valueOrError1).IsFailure()) {
          return (_49_valueOrError1).PropagateFailure<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>>();
        } else {
          Dafny.ISequence<byte> _50_utf8Value = (_49_valueOrError1).Extract();
          return Wrappers_Compile.Result<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Success(_System.Tuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.create(_48_utf8Key, _50_utf8Value));
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>> utf8EncodeMap(Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> mapStringString) {
      if ((new BigInteger((mapStringString).Count)).Sign == 0) {
        return Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Success(Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements());
      } else {
        Dafny.IMap<Dafny.ISequence<char>,Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>> _51_encodedResults = Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>, Dafny.IMap<Dafny.ISequence<char>,Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>>>>((_52_mapStringString) => ((System.Func<Dafny.IMap<Dafny.ISequence<char>,Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>>>)(() => {
          var _coll1 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<char>,Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>>>();
          foreach (Dafny.ISequence<char> _compr_1 in (_52_mapStringString).Keys.Elements) {
            Dafny.ISequence<char> _53_key = (Dafny.ISequence<char>)_compr_1;
            if ((_52_mapStringString).Contains(_53_key)) {
              _coll1.Add(new Dafny.Pair<Dafny.ISequence<char>,Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>>(_53_key, JSONHelpers_Compile.__default.utf8EncodePair(_53_key, Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.Select(_52_mapStringString,_53_key))));
            }
          }
          return Dafny.Map<Dafny.ISequence<char>,Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>>.FromCollection(_coll1);
        }))())(mapStringString);
        Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _54_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<char>,Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>>, bool>>((_55_encodedResults) => Dafny.Helpers.Quantifier<Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>>(((_55_encodedResults).Values).Elements, true, (((_forall_var_5) => {
          Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>> _56_r = (Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>)_forall_var_5;
          return !(((_55_encodedResults).Values).Contains(_56_r)) || ((_56_r).is_Success);
        }))))(_51_encodedResults), Dafny.Sequence<char>.FromString("String can not be UTF8 Encoded?"));
        if ((_54_valueOrError0).IsFailure()) {
          return (_54_valueOrError0).PropagateFailure<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>();
        } else {
          return Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Success(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<char>,Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>>, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>>((_57_encodedResults) => ((System.Func<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>)(() => {
  var _coll2 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>();
  foreach (Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>> _compr_2 in ((_57_encodedResults).Values).Elements) {
    Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>> _58_r = (Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<byte>, Dafny.ISequence<byte>>, Dafny.ISequence<char>>)_compr_2;
    if (((_57_encodedResults).Values).Contains(_58_r)) {
      _coll2.Add(new Dafny.Pair<Dafny.ISequence<byte>,Dafny.ISequence<byte>>(((_58_r).dtor_value).dtor__0, ((_58_r).dtor_value).dtor__1));
    }
  }
  return Dafny.Map<Dafny.ISequence<byte>,Dafny.ISequence<byte>>.FromCollection(_coll2);
}))())(_51_encodedResults));
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<Dafny.ISequence<byte>>, Dafny.ISequence<char>> utf8EncodeSeq(Dafny.ISequence<Dafny.ISequence<char>> seqOfStrings) {
      Dafny.ISequence<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>> _59_encodedResults = ((System.Func<Dafny.ISequence<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>>>) (() => {
        BigInteger dim4 = new BigInteger((seqOfStrings).Count);
        var arr4 = new Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>[Dafny.Helpers.ToIntChecked(dim4, "array size exceeds memory limit")];
        for (int i4 = 0; i4 < dim4; i4++) {
          var _60_i = (BigInteger) i4;
          arr4[(int)(_60_i)] = UTF8.__default.Encode((seqOfStrings).Select(_60_i));
        }
        return Dafny.Sequence<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>>.FromArray(arr4);
      }))();
      Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _61_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(Dafny.Helpers.Id<Func<Dafny.ISequence<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>>, bool>>((_62_encodedResults) => Dafny.Helpers.Quantifier<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>>((_62_encodedResults).UniqueElements, true, (((_forall_var_6) => {
        Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _63_r = (Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>)_forall_var_6;
        return !((_62_encodedResults).Contains(_63_r)) || ((_63_r).is_Success);
      }))))(_59_encodedResults), Dafny.Sequence<char>.FromString("String can not be UTF8 Encoded?"));
      if ((_61_valueOrError0).IsFailure()) {
        return (_61_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.ISequence<byte>>>();
      } else {
        return Wrappers_Compile.Result<Dafny.ISequence<Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Success(((System.Func<Dafny.ISequence<Dafny.ISequence<byte>>>) (() => {
  BigInteger dim5 = new BigInteger((_59_encodedResults).Count);
  var arr5 = new Dafny.ISequence<byte>[Dafny.Helpers.ToIntChecked(dim5, "array size exceeds memory limit")];
  for (int i5 = 0; i5 < dim5; i5++) {
    var _64_i = (BigInteger) i5;
    arr5[(int)(_64_i)] = ((_59_encodedResults).Select(_64_i)).dtor_value;
  }
  return Dafny.Sequence<Dafny.ISequence<byte>>.FromArray(arr5);
}))());
      }
    }
  }
} // end of namespace JSONHelpers_Compile
namespace KeyDescription_Compile {

  public partial class __default {
    public static _System._ITuple0 printErr(Dafny.ISequence<char> e)
    {
      _System._ITuple0 _hresult = _System.Tuple0.Default();
      Dafny.Helpers.Print((e));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
      _hresult = _System.Tuple0.create();
      return _hresult;
      return _hresult;
    }
    public static _System._ITuple0 printJSON(Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> e)
    {
      _System._ITuple0 _hresult = _System.Tuple0.Default();
      Dafny.Helpers.Print((e));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
      _hresult = _System.Tuple0.create();
      return _hresult;
      return _hresult;
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>> ToKeyDescription(JSON_mValues_Compile._IJSON obj) {
      Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _65_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((obj).is_Object, Dafny.Sequence<char>.FromString("KeyDescription not an object"));
      if ((_65_valueOrError0).IsFailure()) {
        return (_65_valueOrError0).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
      } else {
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _66_obj = (obj).dtor_obj;
        Dafny.ISequence<char> _67_typString = Dafny.Sequence<char>.FromString("type");
        Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _68_valueOrError1 = JSONHelpers_Compile.__default.GetString(_67_typString, _66_obj);
        if ((_68_valueOrError1).IsFailure()) {
          return (_68_valueOrError1).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
        } else {
          Dafny.ISequence<char> _69_typ = (_68_valueOrError1).Extract();
          Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _70_valueOrError2 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(KeyDescription_Compile.__default.KeyDescriptionString_q(_69_typ), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Unsupported KeyDescription type:"), _69_typ));
          if ((_70_valueOrError2).IsFailure()) {
            return (_70_valueOrError2).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
          } else {
            if (object.Equals(_69_typ, Dafny.Sequence<char>.FromString("aws-kms-mrk-aware-discovery"))) {
              Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _71_valueOrError3 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("default-mrk-region"), _66_obj);
              if ((_71_valueOrError3).IsFailure()) {
                return (_71_valueOrError3).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
              } else {
                Dafny.ISequence<char> _72_defaultMrkRegion = (_71_valueOrError3).Extract();
                Wrappers_Compile._IResult<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, Dafny.ISequence<char>> _73_filter = JSONHelpers_Compile.__default.GetObject(Dafny.Sequence<char>.FromString("aws-kms-discovery-filter"), _66_obj);
                Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> _74_awsKmsDiscoveryFilter = KeyDescription_Compile.__default.ToDiscoveryFilter(_66_obj);
                return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_KmsMrkDiscovery(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsMrkAwareDiscovery.create(Dafny.Sequence<char>.FromString("aws-kms-mrk-aware-discovery"), _72_defaultMrkRegion, _74_awsKmsDiscoveryFilter)));
              }
            } else {
              Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _75_valueOrError4 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("key"), _66_obj);
              if ((_75_valueOrError4).IsFailure()) {
                return (_75_valueOrError4).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
              } else {
                Dafny.ISequence<char> _76_key = (_75_valueOrError4).Extract();
                if (object.Equals(_69_typ, Dafny.Sequence<char>.FromString("static-material-keyring"))) {
                  return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_Static(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.StaticKeyring.create(_76_key)));
                } else if (object.Equals(_69_typ, Dafny.Sequence<char>.FromString("aws-kms"))) {
                  return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_Kms(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KMSInfo.create(_76_key)));
                } else if (object.Equals(_69_typ, Dafny.Sequence<char>.FromString("aws-kms-mrk-aware"))) {
                  return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_KmsMrk(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsMrkAware.create(_76_key)));
                } else if (object.Equals(_69_typ, Dafny.Sequence<char>.FromString("aws-kms-rsa"))) {
                  Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _77_valueOrError5 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("encryption-algorithm"), _66_obj);
                  if ((_77_valueOrError5).IsFailure()) {
                    return (_77_valueOrError5).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
                  } else {
                    Dafny.ISequence<char> _78_encryptionAlgorithmString = (_77_valueOrError5).Extract();
                    Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _79_valueOrError6 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(KeyDescription_Compile.__default.EncryptionAlgorithmSpec_q(_78_encryptionAlgorithmString), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Unsupported EncryptionAlgorithmSpec:"), _78_encryptionAlgorithmString));
                    if ((_79_valueOrError6).IsFailure()) {
                      return (_79_valueOrError6).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
                    } else {
                      software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec _80_encryptionAlgorithm = ((object.Equals(_78_encryptionAlgorithmString, Dafny.Sequence<char>.FromString("RSAES_OAEP_SHA_1"))) ? (software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__1()) : (software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__256()));
                      return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_KmsRsa(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsRsaKeyring.create(_76_key, _80_encryptionAlgorithm)));
                    }
                  }
                } else if (object.Equals(_69_typ, Dafny.Sequence<char>.FromString("aws-kms-hierarchy"))) {
                  return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_Hierarchy(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.HierarchyKeyring.create(_76_key)));
                } else {
                  Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _81_valueOrError7 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("encryption-algorithm"), _66_obj);
                  if ((_81_valueOrError7).IsFailure()) {
                    return (_81_valueOrError7).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
                  } else {
                    Dafny.ISequence<char> _82_algorithm = (_81_valueOrError7).Extract();
                    Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _83_valueOrError8 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("provider-id"), _66_obj);
                    if ((_83_valueOrError8).IsFailure()) {
                      return (_83_valueOrError8).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
                    } else {
                      Dafny.ISequence<char> _84_providerId = (_83_valueOrError8).Extract();
                      Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _85_valueOrError9 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(KeyDescription_Compile.__default.RawAlgorithmString_q(_82_algorithm), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Unsupported algorithm:"), _82_algorithm));
                      if ((_85_valueOrError9).IsFailure()) {
                        return (_85_valueOrError9).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
                      } else {
                        if (object.Equals(_82_algorithm, Dafny.Sequence<char>.FromString("aes"))) {
                          return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_AES(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawAES.create(_76_key, _84_providerId)));
                        } else {
                          Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _86_valueOrError10 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("padding-algorithm"), _66_obj);
                          if ((_86_valueOrError10).IsFailure()) {
                            return (_86_valueOrError10).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
                          } else {
                            Dafny.ISequence<char> _87_paddingAlgorithm = (_86_valueOrError10).Extract();
                            Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _88_valueOrError11 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("padding-hash"), _66_obj);
                            if ((_88_valueOrError11).IsFailure()) {
                              return (_88_valueOrError11).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
                            } else {
                              Dafny.ISequence<char> _89_paddingHash = (_88_valueOrError11).Extract();
                              Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _90_valueOrError12 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(KeyDescription_Compile.__default.PaddingAlgorithmString_q(_87_paddingAlgorithm), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Unsupported paddingAlgorithm:"), _87_paddingAlgorithm));
                              if ((_90_valueOrError12).IsFailure()) {
                                return (_90_valueOrError12).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
                              } else {
                                Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _91_valueOrError13 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(KeyDescription_Compile.__default.PaddingHashString_q(_89_paddingHash), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Unsupported paddingHash:"), _89_paddingHash));
                                if ((_91_valueOrError13).IsFailure()) {
                                  return (_91_valueOrError13).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
                                } else {
                                  if (object.Equals(_87_paddingAlgorithm, Dafny.Sequence<char>.FromString("pkcs1"))) {
                                    Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _92_valueOrError14 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((_89_paddingHash).Equals(Dafny.Sequence<char>.FromString("sha1")), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Unsupported padding with pkcs1:"), _89_paddingHash));
                                    if ((_92_valueOrError14).IsFailure()) {
                                      return (_92_valueOrError14).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription>();
                                    } else {
                                      return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_RSA(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawRSA.create(_76_key, _84_providerId, software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.create_PKCS1())));
                                    }
                                  } else {
                                    if (object.Equals(_89_paddingHash, Dafny.Sequence<char>.FromString("sha1"))) {
                                      return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_RSA(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawRSA.create(_76_key, _84_providerId, software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.create_OAEP__SHA1__MGF1())));
                                    } else if (object.Equals(_89_paddingHash, Dafny.Sequence<char>.FromString("sha256"))) {
                                      return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_RSA(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawRSA.create(_76_key, _84_providerId, software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.create_OAEP__SHA256__MGF1())));
                                    } else if (object.Equals(_89_paddingHash, Dafny.Sequence<char>.FromString("sha384"))) {
                                      return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_RSA(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawRSA.create(_76_key, _84_providerId, software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.create_OAEP__SHA384__MGF1())));
                                    } else {
                                      return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.create_RSA(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawRSA.create(_76_key, _84_providerId, software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.create_OAEP__SHA512__MGF1())));
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    public static Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> ToDiscoveryFilter(Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj) {
      Wrappers_Compile._IOption<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>> _93_valueOrError0 = (JSONHelpers_Compile.__default.GetObject(Dafny.Sequence<char>.FromString("aws-kms-discovery-filter"), obj)).ToOption();
      if ((_93_valueOrError0).IsFailure()) {
        return (_93_valueOrError0).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>();
      } else {
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _94_filter = (_93_valueOrError0).Extract();
        Wrappers_Compile._IOption<Dafny.ISequence<char>> _95_valueOrError1 = (JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("partition"), _94_filter)).ToOption();
        if ((_95_valueOrError1).IsFailure()) {
          return (_95_valueOrError1).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>();
        } else {
          Dafny.ISequence<char> _96_partition = (_95_valueOrError1).Extract();
          Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _97_valueOrError2 = (JSONHelpers_Compile.__default.GetArrayString(Dafny.Sequence<char>.FromString("account-ids"), _94_filter)).ToOption();
          if ((_97_valueOrError2).IsFailure()) {
            return (_97_valueOrError2).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>();
          } else {
            Dafny.ISequence<Dafny.ISequence<char>> _98_accountIds = (_97_valueOrError2).Extract();
            return Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>.create_Some(software.amazon.cryptography.materialproviders.internaldafny.types.DiscoveryFilter.create(_98_accountIds, _96_partition));
          }
        }
      }
    }
    public static bool KeyDescriptionString_q(Dafny.ISequence<char> s) {
      return (((((((s).Equals(Dafny.Sequence<char>.FromString("static-material-keyring"))) || ((s).Equals(Dafny.Sequence<char>.FromString("aws-kms")))) || ((s).Equals(Dafny.Sequence<char>.FromString("aws-kms-mrk-aware")))) || ((s).Equals(Dafny.Sequence<char>.FromString("aws-kms-mrk-aware-discovery")))) || ((s).Equals(Dafny.Sequence<char>.FromString("raw")))) || ((s).Equals(Dafny.Sequence<char>.FromString("aws-kms-hierarchy")))) || ((s).Equals(Dafny.Sequence<char>.FromString("aws-kms-rsa")));
    }
    public static bool RawAlgorithmString_q(Dafny.ISequence<char> s) {
      return ((s).Equals(Dafny.Sequence<char>.FromString("aes"))) || ((s).Equals(Dafny.Sequence<char>.FromString("rsa")));
    }
    public static bool PaddingAlgorithmString_q(Dafny.ISequence<char> s) {
      return ((s).Equals(Dafny.Sequence<char>.FromString("pkcs1"))) || ((s).Equals(Dafny.Sequence<char>.FromString("oaep-mgf1")));
    }
    public static bool PaddingHashString_q(Dafny.ISequence<char> s) {
      return (((((s).Equals(Dafny.Sequence<char>.FromString("sha1"))) || ((s).Equals(Dafny.Sequence<char>.FromString("sha1")))) || ((s).Equals(Dafny.Sequence<char>.FromString("sha256")))) || ((s).Equals(Dafny.Sequence<char>.FromString("sha384")))) || ((s).Equals(Dafny.Sequence<char>.FromString("sha512")));
    }
    public static bool EncryptionAlgorithmSpec_q(Dafny.ISequence<char> s) {
      return ((s).Equals(Dafny.Sequence<char>.FromString("RSAES_OAEP_SHA_1"))) || ((s).Equals(Dafny.Sequence<char>.FromString("RSAES_OAEP_SHA_256")));
    }
  }
} // end of namespace KeyDescription_Compile
namespace KeyMaterial_Compile {

  public interface _IKeyMaterial {
    bool is_Symetric { get; }
    bool is_PrivateRSA { get; }
    bool is_PublicRSA { get; }
    bool is_KMS { get; }
    bool is_KMSAsymetric { get; }
    bool is_StaticMaterial { get; }
    bool is_StaticKeyStoreInformation { get; }
    Dafny.ISequence<char> dtor_name { get; }
    bool dtor_encrypt { get; }
    bool dtor_decrypt { get; }
    Dafny.ISequence<char> dtor_algorithm { get; }
    BigInteger dtor_bits { get; }
    Dafny.ISequence<char> dtor_encoding { get; }
    Dafny.ISequence<byte> dtor_wrappingKey { get; }
    Dafny.ISequence<char> dtor_keyIdentifier { get; }
    Dafny.ISequence<char> dtor_material { get; }
    Dafny.ISequence<byte> dtor_publicKey { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo dtor_algorithmSuite { get; }
    Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext { get; }
    Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> dtor_encryptedDataKeys { get; }
    Dafny.ISequence<Dafny.ISequence<byte>> dtor_requiredEncryptionContextKeys { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_plaintextDataKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_signingKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_verificationKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> dtor_symmetricSigningKeys { get; }
    Dafny.ISequence<byte> dtor_branchKeyVersion { get; }
    Dafny.ISequence<byte> dtor_branchKey { get; }
    Dafny.ISequence<byte> dtor_beaconKey { get; }
    _IKeyMaterial DowncastClone();
  }
  public abstract class KeyMaterial : _IKeyMaterial {
    public KeyMaterial() { }
    private static readonly KeyMaterial_Compile._IKeyMaterial theDefault = create_Symetric(Dafny.Sequence<char>.Empty, false, false, Dafny.Sequence<char>.Empty, BigInteger.Zero, Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<char>.Empty);
    public static KeyMaterial_Compile._IKeyMaterial Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KeyMaterial_Compile._IKeyMaterial> _TYPE = new Dafny.TypeDescriptor<KeyMaterial_Compile._IKeyMaterial>(KeyMaterial_Compile.KeyMaterial.Default());
    public static Dafny.TypeDescriptor<KeyMaterial_Compile._IKeyMaterial> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyMaterial create_Symetric(Dafny.ISequence<char> name, bool encrypt, bool decrypt, Dafny.ISequence<char> algorithm, BigInteger bits, Dafny.ISequence<char> encoding, Dafny.ISequence<byte> wrappingKey, Dafny.ISequence<char> keyIdentifier) {
      return new KeyMaterial_Symetric(name, encrypt, decrypt, algorithm, bits, encoding, wrappingKey, keyIdentifier);
    }
    public static _IKeyMaterial create_PrivateRSA(Dafny.ISequence<char> name, bool encrypt, bool decrypt, Dafny.ISequence<char> algorithm, BigInteger bits, Dafny.ISequence<char> encoding, Dafny.ISequence<char> material, Dafny.ISequence<char> keyIdentifier) {
      return new KeyMaterial_PrivateRSA(name, encrypt, decrypt, algorithm, bits, encoding, material, keyIdentifier);
    }
    public static _IKeyMaterial create_PublicRSA(Dafny.ISequence<char> name, bool encrypt, bool decrypt, BigInteger bits, Dafny.ISequence<char> algorithm, Dafny.ISequence<char> encoding, Dafny.ISequence<char> material, Dafny.ISequence<char> keyIdentifier) {
      return new KeyMaterial_PublicRSA(name, encrypt, decrypt, bits, algorithm, encoding, material, keyIdentifier);
    }
    public static _IKeyMaterial create_KMS(Dafny.ISequence<char> name, bool encrypt, bool decrypt, Dafny.ISequence<char> keyIdentifier) {
      return new KeyMaterial_KMS(name, encrypt, decrypt, keyIdentifier);
    }
    public static _IKeyMaterial create_KMSAsymetric(Dafny.ISequence<char> name, bool encrypt, bool decrypt, Dafny.ISequence<char> keyIdentifier, BigInteger bits, Dafny.ISequence<char> algorithm, Dafny.ISequence<char> encoding, Dafny.ISequence<byte> publicKey) {
      return new KeyMaterial_KMSAsymetric(name, encrypt, decrypt, keyIdentifier, bits, algorithm, encoding, publicKey);
    }
    public static _IKeyMaterial create_StaticMaterial(Dafny.ISequence<char> name, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo algorithmSuite, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> encryptedDataKeys, Dafny.ISequence<Dafny.ISequence<byte>> requiredEncryptionContextKeys, Wrappers_Compile._IOption<Dafny.ISequence<byte>> plaintextDataKey, Wrappers_Compile._IOption<Dafny.ISequence<byte>> signingKey, Wrappers_Compile._IOption<Dafny.ISequence<byte>> verificationKey, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> symmetricSigningKeys) {
      return new KeyMaterial_StaticMaterial(name, algorithmSuite, encryptionContext, encryptedDataKeys, requiredEncryptionContextKeys, plaintextDataKey, signingKey, verificationKey, symmetricSigningKeys);
    }
    public static _IKeyMaterial create_StaticKeyStoreInformation(Dafny.ISequence<char> keyIdentifier, Dafny.ISequence<byte> branchKeyVersion, Dafny.ISequence<byte> branchKey, Dafny.ISequence<byte> beaconKey) {
      return new KeyMaterial_StaticKeyStoreInformation(keyIdentifier, branchKeyVersion, branchKey, beaconKey);
    }
    public bool is_Symetric { get { return this is KeyMaterial_Symetric; } }
    public bool is_PrivateRSA { get { return this is KeyMaterial_PrivateRSA; } }
    public bool is_PublicRSA { get { return this is KeyMaterial_PublicRSA; } }
    public bool is_KMS { get { return this is KeyMaterial_KMS; } }
    public bool is_KMSAsymetric { get { return this is KeyMaterial_KMSAsymetric; } }
    public bool is_StaticMaterial { get { return this is KeyMaterial_StaticMaterial; } }
    public bool is_StaticKeyStoreInformation { get { return this is KeyMaterial_StaticKeyStoreInformation; } }
    public Dafny.ISequence<char> dtor_name {
      get {
        var d = this;
        if (d is KeyMaterial_Symetric) { return ((KeyMaterial_Symetric)d)._name; }
        if (d is KeyMaterial_PrivateRSA) { return ((KeyMaterial_PrivateRSA)d)._name; }
        if (d is KeyMaterial_PublicRSA) { return ((KeyMaterial_PublicRSA)d)._name; }
        if (d is KeyMaterial_KMS) { return ((KeyMaterial_KMS)d)._name; }
        if (d is KeyMaterial_KMSAsymetric) { return ((KeyMaterial_KMSAsymetric)d)._name; }
        return ((KeyMaterial_StaticMaterial)d)._name;
      }
    }
    public bool dtor_encrypt {
      get {
        var d = this;
        if (d is KeyMaterial_Symetric) { return ((KeyMaterial_Symetric)d)._encrypt; }
        if (d is KeyMaterial_PrivateRSA) { return ((KeyMaterial_PrivateRSA)d)._encrypt; }
        if (d is KeyMaterial_PublicRSA) { return ((KeyMaterial_PublicRSA)d)._encrypt; }
        if (d is KeyMaterial_KMS) { return ((KeyMaterial_KMS)d)._encrypt; }
        return ((KeyMaterial_KMSAsymetric)d)._encrypt;
      }
    }
    public bool dtor_decrypt {
      get {
        var d = this;
        if (d is KeyMaterial_Symetric) { return ((KeyMaterial_Symetric)d)._decrypt; }
        if (d is KeyMaterial_PrivateRSA) { return ((KeyMaterial_PrivateRSA)d)._decrypt; }
        if (d is KeyMaterial_PublicRSA) { return ((KeyMaterial_PublicRSA)d)._decrypt; }
        if (d is KeyMaterial_KMS) { return ((KeyMaterial_KMS)d)._decrypt; }
        return ((KeyMaterial_KMSAsymetric)d)._decrypt;
      }
    }
    public Dafny.ISequence<char> dtor_algorithm {
      get {
        var d = this;
        if (d is KeyMaterial_Symetric) { return ((KeyMaterial_Symetric)d)._algorithm; }
        if (d is KeyMaterial_PrivateRSA) { return ((KeyMaterial_PrivateRSA)d)._algorithm; }
        if (d is KeyMaterial_PublicRSA) { return ((KeyMaterial_PublicRSA)d)._algorithm; }
        return ((KeyMaterial_KMSAsymetric)d)._algorithm;
      }
    }
    public BigInteger dtor_bits {
      get {
        var d = this;
        if (d is KeyMaterial_Symetric) { return ((KeyMaterial_Symetric)d)._bits; }
        if (d is KeyMaterial_PrivateRSA) { return ((KeyMaterial_PrivateRSA)d)._bits; }
        if (d is KeyMaterial_PublicRSA) { return ((KeyMaterial_PublicRSA)d)._bits; }
        return ((KeyMaterial_KMSAsymetric)d)._bits;
      }
    }
    public Dafny.ISequence<char> dtor_encoding {
      get {
        var d = this;
        if (d is KeyMaterial_Symetric) { return ((KeyMaterial_Symetric)d)._encoding; }
        if (d is KeyMaterial_PrivateRSA) { return ((KeyMaterial_PrivateRSA)d)._encoding; }
        if (d is KeyMaterial_PublicRSA) { return ((KeyMaterial_PublicRSA)d)._encoding; }
        return ((KeyMaterial_KMSAsymetric)d)._encoding;
      }
    }
    public Dafny.ISequence<byte> dtor_wrappingKey {
      get {
        var d = this;
        return ((KeyMaterial_Symetric)d)._wrappingKey;
      }
    }
    public Dafny.ISequence<char> dtor_keyIdentifier {
      get {
        var d = this;
        if (d is KeyMaterial_Symetric) { return ((KeyMaterial_Symetric)d)._keyIdentifier; }
        if (d is KeyMaterial_PrivateRSA) { return ((KeyMaterial_PrivateRSA)d)._keyIdentifier; }
        if (d is KeyMaterial_PublicRSA) { return ((KeyMaterial_PublicRSA)d)._keyIdentifier; }
        if (d is KeyMaterial_KMS) { return ((KeyMaterial_KMS)d)._keyIdentifier; }
        if (d is KeyMaterial_KMSAsymetric) { return ((KeyMaterial_KMSAsymetric)d)._keyIdentifier; }
        return ((KeyMaterial_StaticKeyStoreInformation)d)._keyIdentifier;
      }
    }
    public Dafny.ISequence<char> dtor_material {
      get {
        var d = this;
        if (d is KeyMaterial_PrivateRSA) { return ((KeyMaterial_PrivateRSA)d)._material; }
        return ((KeyMaterial_PublicRSA)d)._material;
      }
    }
    public Dafny.ISequence<byte> dtor_publicKey {
      get {
        var d = this;
        return ((KeyMaterial_KMSAsymetric)d)._publicKey;
      }
    }
    public software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo dtor_algorithmSuite {
      get {
        var d = this;
        return ((KeyMaterial_StaticMaterial)d)._algorithmSuite;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        var d = this;
        return ((KeyMaterial_StaticMaterial)d)._encryptionContext;
      }
    }
    public Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> dtor_encryptedDataKeys {
      get {
        var d = this;
        return ((KeyMaterial_StaticMaterial)d)._encryptedDataKeys;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<byte>> dtor_requiredEncryptionContextKeys {
      get {
        var d = this;
        return ((KeyMaterial_StaticMaterial)d)._requiredEncryptionContextKeys;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_plaintextDataKey {
      get {
        var d = this;
        return ((KeyMaterial_StaticMaterial)d)._plaintextDataKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_signingKey {
      get {
        var d = this;
        return ((KeyMaterial_StaticMaterial)d)._signingKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_verificationKey {
      get {
        var d = this;
        return ((KeyMaterial_StaticMaterial)d)._verificationKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> dtor_symmetricSigningKeys {
      get {
        var d = this;
        return ((KeyMaterial_StaticMaterial)d)._symmetricSigningKeys;
      }
    }
    public Dafny.ISequence<byte> dtor_branchKeyVersion {
      get {
        var d = this;
        return ((KeyMaterial_StaticKeyStoreInformation)d)._branchKeyVersion;
      }
    }
    public Dafny.ISequence<byte> dtor_branchKey {
      get {
        var d = this;
        return ((KeyMaterial_StaticKeyStoreInformation)d)._branchKey;
      }
    }
    public Dafny.ISequence<byte> dtor_beaconKey {
      get {
        var d = this;
        return ((KeyMaterial_StaticKeyStoreInformation)d)._beaconKey;
      }
    }
    public abstract _IKeyMaterial DowncastClone();
  }
  public class KeyMaterial_Symetric : KeyMaterial {
    public readonly Dafny.ISequence<char> _name;
    public readonly bool _encrypt;
    public readonly bool _decrypt;
    public readonly Dafny.ISequence<char> _algorithm;
    public readonly BigInteger _bits;
    public readonly Dafny.ISequence<char> _encoding;
    public readonly Dafny.ISequence<byte> _wrappingKey;
    public readonly Dafny.ISequence<char> _keyIdentifier;
    public KeyMaterial_Symetric(Dafny.ISequence<char> name, bool encrypt, bool decrypt, Dafny.ISequence<char> algorithm, BigInteger bits, Dafny.ISequence<char> encoding, Dafny.ISequence<byte> wrappingKey, Dafny.ISequence<char> keyIdentifier) {
      this._name = name;
      this._encrypt = encrypt;
      this._decrypt = decrypt;
      this._algorithm = algorithm;
      this._bits = bits;
      this._encoding = encoding;
      this._wrappingKey = wrappingKey;
      this._keyIdentifier = keyIdentifier;
    }
    public override _IKeyMaterial DowncastClone() {
      if (this is _IKeyMaterial dt) { return dt; }
      return new KeyMaterial_Symetric(_name, _encrypt, _decrypt, _algorithm, _bits, _encoding, _wrappingKey, _keyIdentifier);
    }
    public override bool Equals(object other) {
      var oth = other as KeyMaterial_Compile.KeyMaterial_Symetric;
      return oth != null && object.Equals(this._name, oth._name) && this._encrypt == oth._encrypt && this._decrypt == oth._decrypt && object.Equals(this._algorithm, oth._algorithm) && this._bits == oth._bits && object.Equals(this._encoding, oth._encoding) && object.Equals(this._wrappingKey, oth._wrappingKey) && object.Equals(this._keyIdentifier, oth._keyIdentifier);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encrypt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._decrypt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._algorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._bits));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encoding));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._wrappingKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyIdentifier));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyMaterial_Compile.KeyMaterial.Symetric";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encrypt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._decrypt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._algorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._bits);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encoding);
      s += ", ";
      s += Dafny.Helpers.ToString(this._wrappingKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._keyIdentifier);
      s += ")";
      return s;
    }
  }
  public class KeyMaterial_PrivateRSA : KeyMaterial {
    public readonly Dafny.ISequence<char> _name;
    public readonly bool _encrypt;
    public readonly bool _decrypt;
    public readonly Dafny.ISequence<char> _algorithm;
    public readonly BigInteger _bits;
    public readonly Dafny.ISequence<char> _encoding;
    public readonly Dafny.ISequence<char> _material;
    public readonly Dafny.ISequence<char> _keyIdentifier;
    public KeyMaterial_PrivateRSA(Dafny.ISequence<char> name, bool encrypt, bool decrypt, Dafny.ISequence<char> algorithm, BigInteger bits, Dafny.ISequence<char> encoding, Dafny.ISequence<char> material, Dafny.ISequence<char> keyIdentifier) {
      this._name = name;
      this._encrypt = encrypt;
      this._decrypt = decrypt;
      this._algorithm = algorithm;
      this._bits = bits;
      this._encoding = encoding;
      this._material = material;
      this._keyIdentifier = keyIdentifier;
    }
    public override _IKeyMaterial DowncastClone() {
      if (this is _IKeyMaterial dt) { return dt; }
      return new KeyMaterial_PrivateRSA(_name, _encrypt, _decrypt, _algorithm, _bits, _encoding, _material, _keyIdentifier);
    }
    public override bool Equals(object other) {
      var oth = other as KeyMaterial_Compile.KeyMaterial_PrivateRSA;
      return oth != null && object.Equals(this._name, oth._name) && this._encrypt == oth._encrypt && this._decrypt == oth._decrypt && object.Equals(this._algorithm, oth._algorithm) && this._bits == oth._bits && object.Equals(this._encoding, oth._encoding) && object.Equals(this._material, oth._material) && object.Equals(this._keyIdentifier, oth._keyIdentifier);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encrypt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._decrypt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._algorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._bits));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encoding));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._material));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyIdentifier));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyMaterial_Compile.KeyMaterial.PrivateRSA";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encrypt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._decrypt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._algorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._bits);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encoding);
      s += ", ";
      s += Dafny.Helpers.ToString(this._material);
      s += ", ";
      s += Dafny.Helpers.ToString(this._keyIdentifier);
      s += ")";
      return s;
    }
  }
  public class KeyMaterial_PublicRSA : KeyMaterial {
    public readonly Dafny.ISequence<char> _name;
    public readonly bool _encrypt;
    public readonly bool _decrypt;
    public readonly BigInteger _bits;
    public readonly Dafny.ISequence<char> _algorithm;
    public readonly Dafny.ISequence<char> _encoding;
    public readonly Dafny.ISequence<char> _material;
    public readonly Dafny.ISequence<char> _keyIdentifier;
    public KeyMaterial_PublicRSA(Dafny.ISequence<char> name, bool encrypt, bool decrypt, BigInteger bits, Dafny.ISequence<char> algorithm, Dafny.ISequence<char> encoding, Dafny.ISequence<char> material, Dafny.ISequence<char> keyIdentifier) {
      this._name = name;
      this._encrypt = encrypt;
      this._decrypt = decrypt;
      this._bits = bits;
      this._algorithm = algorithm;
      this._encoding = encoding;
      this._material = material;
      this._keyIdentifier = keyIdentifier;
    }
    public override _IKeyMaterial DowncastClone() {
      if (this is _IKeyMaterial dt) { return dt; }
      return new KeyMaterial_PublicRSA(_name, _encrypt, _decrypt, _bits, _algorithm, _encoding, _material, _keyIdentifier);
    }
    public override bool Equals(object other) {
      var oth = other as KeyMaterial_Compile.KeyMaterial_PublicRSA;
      return oth != null && object.Equals(this._name, oth._name) && this._encrypt == oth._encrypt && this._decrypt == oth._decrypt && this._bits == oth._bits && object.Equals(this._algorithm, oth._algorithm) && object.Equals(this._encoding, oth._encoding) && object.Equals(this._material, oth._material) && object.Equals(this._keyIdentifier, oth._keyIdentifier);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encrypt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._decrypt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._bits));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._algorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encoding));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._material));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyIdentifier));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyMaterial_Compile.KeyMaterial.PublicRSA";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encrypt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._decrypt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._bits);
      s += ", ";
      s += Dafny.Helpers.ToString(this._algorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encoding);
      s += ", ";
      s += Dafny.Helpers.ToString(this._material);
      s += ", ";
      s += Dafny.Helpers.ToString(this._keyIdentifier);
      s += ")";
      return s;
    }
  }
  public class KeyMaterial_KMS : KeyMaterial {
    public readonly Dafny.ISequence<char> _name;
    public readonly bool _encrypt;
    public readonly bool _decrypt;
    public readonly Dafny.ISequence<char> _keyIdentifier;
    public KeyMaterial_KMS(Dafny.ISequence<char> name, bool encrypt, bool decrypt, Dafny.ISequence<char> keyIdentifier) {
      this._name = name;
      this._encrypt = encrypt;
      this._decrypt = decrypt;
      this._keyIdentifier = keyIdentifier;
    }
    public override _IKeyMaterial DowncastClone() {
      if (this is _IKeyMaterial dt) { return dt; }
      return new KeyMaterial_KMS(_name, _encrypt, _decrypt, _keyIdentifier);
    }
    public override bool Equals(object other) {
      var oth = other as KeyMaterial_Compile.KeyMaterial_KMS;
      return oth != null && object.Equals(this._name, oth._name) && this._encrypt == oth._encrypt && this._decrypt == oth._decrypt && object.Equals(this._keyIdentifier, oth._keyIdentifier);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encrypt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._decrypt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyIdentifier));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyMaterial_Compile.KeyMaterial.KMS";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encrypt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._decrypt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._keyIdentifier);
      s += ")";
      return s;
    }
  }
  public class KeyMaterial_KMSAsymetric : KeyMaterial {
    public readonly Dafny.ISequence<char> _name;
    public readonly bool _encrypt;
    public readonly bool _decrypt;
    public readonly Dafny.ISequence<char> _keyIdentifier;
    public readonly BigInteger _bits;
    public readonly Dafny.ISequence<char> _algorithm;
    public readonly Dafny.ISequence<char> _encoding;
    public readonly Dafny.ISequence<byte> _publicKey;
    public KeyMaterial_KMSAsymetric(Dafny.ISequence<char> name, bool encrypt, bool decrypt, Dafny.ISequence<char> keyIdentifier, BigInteger bits, Dafny.ISequence<char> algorithm, Dafny.ISequence<char> encoding, Dafny.ISequence<byte> publicKey) {
      this._name = name;
      this._encrypt = encrypt;
      this._decrypt = decrypt;
      this._keyIdentifier = keyIdentifier;
      this._bits = bits;
      this._algorithm = algorithm;
      this._encoding = encoding;
      this._publicKey = publicKey;
    }
    public override _IKeyMaterial DowncastClone() {
      if (this is _IKeyMaterial dt) { return dt; }
      return new KeyMaterial_KMSAsymetric(_name, _encrypt, _decrypt, _keyIdentifier, _bits, _algorithm, _encoding, _publicKey);
    }
    public override bool Equals(object other) {
      var oth = other as KeyMaterial_Compile.KeyMaterial_KMSAsymetric;
      return oth != null && object.Equals(this._name, oth._name) && this._encrypt == oth._encrypt && this._decrypt == oth._decrypt && object.Equals(this._keyIdentifier, oth._keyIdentifier) && this._bits == oth._bits && object.Equals(this._algorithm, oth._algorithm) && object.Equals(this._encoding, oth._encoding) && object.Equals(this._publicKey, oth._publicKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encrypt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._decrypt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyIdentifier));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._bits));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._algorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encoding));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._publicKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyMaterial_Compile.KeyMaterial.KMSAsymetric";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encrypt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._decrypt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._keyIdentifier);
      s += ", ";
      s += Dafny.Helpers.ToString(this._bits);
      s += ", ";
      s += Dafny.Helpers.ToString(this._algorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encoding);
      s += ", ";
      s += Dafny.Helpers.ToString(this._publicKey);
      s += ")";
      return s;
    }
  }
  public class KeyMaterial_StaticMaterial : KeyMaterial {
    public readonly Dafny.ISequence<char> _name;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _algorithmSuite;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _encryptionContext;
    public readonly Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> _encryptedDataKeys;
    public readonly Dafny.ISequence<Dafny.ISequence<byte>> _requiredEncryptionContextKeys;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _plaintextDataKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _signingKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _verificationKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> _symmetricSigningKeys;
    public KeyMaterial_StaticMaterial(Dafny.ISequence<char> name, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo algorithmSuite, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> encryptedDataKeys, Dafny.ISequence<Dafny.ISequence<byte>> requiredEncryptionContextKeys, Wrappers_Compile._IOption<Dafny.ISequence<byte>> plaintextDataKey, Wrappers_Compile._IOption<Dafny.ISequence<byte>> signingKey, Wrappers_Compile._IOption<Dafny.ISequence<byte>> verificationKey, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> symmetricSigningKeys) {
      this._name = name;
      this._algorithmSuite = algorithmSuite;
      this._encryptionContext = encryptionContext;
      this._encryptedDataKeys = encryptedDataKeys;
      this._requiredEncryptionContextKeys = requiredEncryptionContextKeys;
      this._plaintextDataKey = plaintextDataKey;
      this._signingKey = signingKey;
      this._verificationKey = verificationKey;
      this._symmetricSigningKeys = symmetricSigningKeys;
    }
    public override _IKeyMaterial DowncastClone() {
      if (this is _IKeyMaterial dt) { return dt; }
      return new KeyMaterial_StaticMaterial(_name, _algorithmSuite, _encryptionContext, _encryptedDataKeys, _requiredEncryptionContextKeys, _plaintextDataKey, _signingKey, _verificationKey, _symmetricSigningKeys);
    }
    public override bool Equals(object other) {
      var oth = other as KeyMaterial_Compile.KeyMaterial_StaticMaterial;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._algorithmSuite, oth._algorithmSuite) && object.Equals(this._encryptionContext, oth._encryptionContext) && object.Equals(this._encryptedDataKeys, oth._encryptedDataKeys) && object.Equals(this._requiredEncryptionContextKeys, oth._requiredEncryptionContextKeys) && object.Equals(this._plaintextDataKey, oth._plaintextDataKey) && object.Equals(this._signingKey, oth._signingKey) && object.Equals(this._verificationKey, oth._verificationKey) && object.Equals(this._symmetricSigningKeys, oth._symmetricSigningKeys);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._algorithmSuite));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encryptedDataKeys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._requiredEncryptionContextKeys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._plaintextDataKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._signingKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._verificationKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._symmetricSigningKeys));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyMaterial_Compile.KeyMaterial.StaticMaterial";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._algorithmSuite);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encryptedDataKeys);
      s += ", ";
      s += Dafny.Helpers.ToString(this._requiredEncryptionContextKeys);
      s += ", ";
      s += Dafny.Helpers.ToString(this._plaintextDataKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._signingKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._verificationKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._symmetricSigningKeys);
      s += ")";
      return s;
    }
  }
  public class KeyMaterial_StaticKeyStoreInformation : KeyMaterial {
    public readonly Dafny.ISequence<char> _keyIdentifier;
    public readonly Dafny.ISequence<byte> _branchKeyVersion;
    public readonly Dafny.ISequence<byte> _branchKey;
    public readonly Dafny.ISequence<byte> _beaconKey;
    public KeyMaterial_StaticKeyStoreInformation(Dafny.ISequence<char> keyIdentifier, Dafny.ISequence<byte> branchKeyVersion, Dafny.ISequence<byte> branchKey, Dafny.ISequence<byte> beaconKey) {
      this._keyIdentifier = keyIdentifier;
      this._branchKeyVersion = branchKeyVersion;
      this._branchKey = branchKey;
      this._beaconKey = beaconKey;
    }
    public override _IKeyMaterial DowncastClone() {
      if (this is _IKeyMaterial dt) { return dt; }
      return new KeyMaterial_StaticKeyStoreInformation(_keyIdentifier, _branchKeyVersion, _branchKey, _beaconKey);
    }
    public override bool Equals(object other) {
      var oth = other as KeyMaterial_Compile.KeyMaterial_StaticKeyStoreInformation;
      return oth != null && object.Equals(this._keyIdentifier, oth._keyIdentifier) && object.Equals(this._branchKeyVersion, oth._branchKeyVersion) && object.Equals(this._branchKey, oth._branchKey) && object.Equals(this._beaconKey, oth._beaconKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyIdentifier));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._branchKeyVersion));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._branchKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._beaconKey));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyMaterial_Compile.KeyMaterial.StaticKeyStoreInformation";
      s += "(";
      s += Dafny.Helpers.ToString(this._keyIdentifier);
      s += ", ";
      s += Dafny.Helpers.ToString(this._branchKeyVersion);
      s += ", ";
      s += Dafny.Helpers.ToString(this._branchKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._beaconKey);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial>, Dafny.ISequence<char>> BuildKeyMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient mpl, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
      if ((new BigInteger((obj).Count)).Sign == 0) {
        return Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial>, Dafny.ISequence<char>>.create_Success(Dafny.Map<Dafny.ISequence<char>, KeyMaterial_Compile._IKeyMaterial>.FromElements());
      } else {
        Dafny.ISequence<char> _99_name = ((obj).Select(BigInteger.Zero)).dtor__0;
        Wrappers_Compile._IResult<KeyMaterial_Compile._IKeyMaterial, Dafny.ISequence<char>> _100_valueOrError0 = KeyMaterial_Compile.__default.ToKeyMaterial(mpl, _99_name, ((obj).Select(BigInteger.Zero)).dtor__1);
        if ((_100_valueOrError0).IsFailure()) {
          return (_100_valueOrError0).PropagateFailure<Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial>>();
        } else {
          KeyMaterial_Compile._IKeyMaterial _101_keyMaterial = (_100_valueOrError0).Extract();
          Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial>, Dafny.ISequence<char>> _102_valueOrError1 = KeyMaterial_Compile.__default.BuildKeyMaterials(mpl, (obj).Drop(BigInteger.One));
          if ((_102_valueOrError1).IsFailure()) {
            return (_102_valueOrError1).PropagateFailure<Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial>>();
          } else {
            Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial> _103_tail = (_102_valueOrError1).Extract();
            return Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial>, Dafny.ISequence<char>>.create_Success(Dafny.Map<Dafny.ISequence<char>, KeyMaterial_Compile._IKeyMaterial>.Merge(Dafny.Map<Dafny.ISequence<char>, KeyMaterial_Compile._IKeyMaterial>.FromElements(new Dafny.Pair<Dafny.ISequence<char>, KeyMaterial_Compile._IKeyMaterial>(_99_name, _101_keyMaterial)), _103_tail));
          }
        }
      }
    }
    public static Wrappers_Compile._IResult<KeyMaterial_Compile._IKeyMaterial, Dafny.ISequence<char>> ToKeyMaterial(software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient mpl, Dafny.ISequence<char> name, JSON_mValues_Compile._IJSON obj)
    {
      Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _104_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((obj).is_Object, Dafny.Sequence<char>.FromString("KeyDescription not an object"));
      if ((_104_valueOrError0).IsFailure()) {
        return (_104_valueOrError0).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
      } else {
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _105_obj = (obj).dtor_obj;
        Dafny.ISequence<char> _106_typString = Dafny.Sequence<char>.FromString("type");
        Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _107_valueOrError1 = JSONHelpers_Compile.__default.GetString(_106_typString, _105_obj);
        if ((_107_valueOrError1).IsFailure()) {
          return (_107_valueOrError1).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
        } else {
          Dafny.ISequence<char> _108_typ = (_107_valueOrError1).Extract();
          Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _109_valueOrError2 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(KeyMaterial_Compile.__default.KeyMaterialString_q(_108_typ), Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Unsupported KeyMaterial type:"), _108_typ));
          if ((_109_valueOrError2).IsFailure()) {
            return (_109_valueOrError2).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
          } else {
            if (object.Equals(_108_typ, Dafny.Sequence<char>.FromString("static-material"))) {
              Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _110_valueOrError3 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("algorithmSuiteId"), _105_obj);
              if ((_110_valueOrError3).IsFailure()) {
                return (_110_valueOrError3).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
              } else {
                Dafny.ISequence<char> _111_algorithmSuiteHex = (_110_valueOrError3).Extract();
                Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _112_valueOrError4 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(HexStrings_Compile.__default.IsLooseHexString(_111_algorithmSuiteHex), Dafny.Sequence<char>.FromString("Not hex encoded binnary"));
                if ((_112_valueOrError4).IsFailure()) {
                  return (_112_valueOrError4).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                } else {
                  Dafny.ISequence<byte> _113_binaryId = HexStrings_Compile.__default.FromHexString(_111_algorithmSuiteHex);
                  Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, Dafny.ISequence<char>> _114_valueOrError5 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<Dafny.ISequence<char>>((mpl).GetAlgorithmSuiteInfo(_113_binaryId), Dafny.Helpers.Id<Func<Dafny.ISequence<char>, Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, Dafny.ISequence<char>>>>((_115_algorithmSuiteHex) => ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, Dafny.ISequence<char>>)((_116_e) => {
                    return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Invalid Suite:"), _115_algorithmSuiteHex);
                  })))(_111_algorithmSuiteHex));
                  if ((_114_valueOrError5).IsFailure()) {
                    return (_114_valueOrError5).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                  } else {
                    software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _117_algorithmSuite = (_114_valueOrError5).Extract();
                    Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>, Dafny.ISequence<char>> _118_valueOrError6 = JSONHelpers_Compile.__default.SmallObjectToStringStringMap(Dafny.Sequence<char>.FromString("encryptionContext"), _105_obj);
                    if ((_118_valueOrError6).IsFailure()) {
                      return (_118_valueOrError6).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                    } else {
                      Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> _119_encryptionContextStrings = (_118_valueOrError6).Extract();
                      Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>> _120_valueOrError7 = JSONHelpers_Compile.__default.utf8EncodeMap(_119_encryptionContextStrings);
                      if ((_120_valueOrError7).IsFailure()) {
                        return (_120_valueOrError7).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                      } else {
                        Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _121_encryptionContext = (_120_valueOrError7).Extract();
                        Wrappers_Compile._IResult<Dafny.ISequence<Dafny.ISequence<char>>, Dafny.ISequence<char>> _122_valueOrError8 = JSONHelpers_Compile.__default.GetArrayString(Dafny.Sequence<char>.FromString("requiredEncryptionContextKeys"), _105_obj);
                        if ((_122_valueOrError8).IsFailure()) {
                          return (_122_valueOrError8).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                        } else {
                          Dafny.ISequence<Dafny.ISequence<char>> _123_keysAsStrings = (_122_valueOrError8).Extract();
                          Wrappers_Compile._IResult<Dafny.ISequence<Dafny.ISequence<byte>>, Dafny.ISequence<char>> _124_valueOrError9 = JSONHelpers_Compile.__default.utf8EncodeSeq(_123_keysAsStrings);
                          if ((_124_valueOrError9).IsFailure()) {
                            return (_124_valueOrError9).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                          } else {
                            Dafny.ISequence<Dafny.ISequence<byte>> _125_requiredEncryptionContextKeys = (_124_valueOrError9).Extract();
                            Wrappers_Compile._IResult<Dafny.ISequence<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>>, Dafny.ISequence<char>> _126_valueOrError10 = JSONHelpers_Compile.__default.GetArrayObject(Dafny.Sequence<char>.FromString("encryptedDataKeys"), _105_obj);
                            if ((_126_valueOrError10).IsFailure()) {
                              return (_126_valueOrError10).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                            } else {
                              Dafny.ISequence<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>> _127_encryptedDataKeysJSON = (_126_valueOrError10).Extract();
                              Wrappers_Compile._IResult<Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>, Dafny.ISequence<char>> _128_valueOrError11 = Seq_Compile.__default.MapWithResult<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey, Dafny.ISequence<char>>(KeyMaterial_Compile.__default.ToEncryptedDataKey, _127_encryptedDataKeysJSON);
                              if ((_128_valueOrError11).IsFailure()) {
                                return (_128_valueOrError11).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                              } else {
                                Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> _129_encryptedDataKeys = (_128_valueOrError11).Extract();
                                Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.ISequence<char>> _130_valueOrError12 = JSONHelpers_Compile.__default.GetOptionalString(Dafny.Sequence<char>.FromString("plaintextDataKey"), _105_obj);
                                if ((_130_valueOrError12).IsFailure()) {
                                  return (_130_valueOrError12).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                                } else {
                                  Wrappers_Compile._IOption<Dafny.ISequence<char>> _131_plaintextDataKeyEncoded = (_130_valueOrError12).Extract();
                                  Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, Dafny.ISequence<char>> _132_valueOrError13 = (((_131_plaintextDataKeyEncoded).is_Some) ? (Dafny.Helpers.Let<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, Dafny.ISequence<char>>>(Base64_Compile.__default.Decode((_131_plaintextDataKeyEncoded).dtor_value), _pat_let0_0 => Dafny.Helpers.Let<Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, Dafny.ISequence<char>>>(_pat_let0_0, _133_result => (((_133_result).is_Success) ? (Wrappers_Compile.Result<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Success(Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some((_133_result).dtor_value))) : (Wrappers_Compile.Result<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Failure((_133_result).dtor_error)))))) : (Wrappers_Compile.Result<Wrappers_Compile._IOption<Dafny.ISequence<byte>>, Dafny.ISequence<char>>.create_Success(Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None())));
                                  if ((_132_valueOrError13).IsFailure()) {
                                    return (_132_valueOrError13).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                                  } else {
                                    Wrappers_Compile._IOption<Dafny.ISequence<byte>> _134_plaintextDataKey = (_132_valueOrError13).Extract();
                                    Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.ISequence<char>> _135_valueOrError14 = JSONHelpers_Compile.__default.GetOptionalString(Dafny.Sequence<char>.FromString("signingKey"), _105_obj);
                                    if ((_135_valueOrError14).IsFailure()) {
                                      return (_135_valueOrError14).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                                    } else {
                                      Wrappers_Compile._IOption<Dafny.ISequence<char>> _136_signingKey = (_135_valueOrError14).Extract();
                                      Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.ISequence<char>> _137_valueOrError15 = JSONHelpers_Compile.__default.GetOptionalString(Dafny.Sequence<char>.FromString("verificationKey"), _105_obj);
                                      if ((_137_valueOrError15).IsFailure()) {
                                        return (_137_valueOrError15).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                                      } else {
                                        Wrappers_Compile._IOption<Dafny.ISequence<char>> _138_verificationKey = (_137_valueOrError15).Extract();
                                        Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _139_symmetricSigningKeys = (JSONHelpers_Compile.__default.GetArrayString(Dafny.Sequence<char>.FromString("symmetricSigningKeys"), _105_obj)).ToOption();
                                        return Wrappers_Compile.Result<KeyMaterial_Compile._IKeyMaterial, Dafny.ISequence<char>>.create_Success(KeyMaterial_Compile.KeyMaterial.create_StaticMaterial(name, _117_algorithmSuite, _121_encryptionContext, _129_encryptedDataKeys, _125_requiredEncryptionContextKeys, _134_plaintextDataKey, Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<byte>>>.create_None()));
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            } else if (object.Equals(_108_typ, Dafny.Sequence<char>.FromString("static-branch-key"))) {
              Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _140_valueOrError16 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("key-id"), _105_obj);
              if ((_140_valueOrError16).IsFailure()) {
                return (_140_valueOrError16).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
              } else {
                Dafny.ISequence<char> _141_keyIdentifier = (_140_valueOrError16).Extract();
                Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _142_valueOrError17 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("branchKeyVersion"), _105_obj);
                if ((_142_valueOrError17).IsFailure()) {
                  return (_142_valueOrError17).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                } else {
                  Dafny.ISequence<char> _143_branchKeyVersionEncoded = (_142_valueOrError17).Extract();
                  Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _144_valueOrError18 = UTF8.__default.Encode(_143_branchKeyVersionEncoded);
                  if ((_144_valueOrError18).IsFailure()) {
                    return (_144_valueOrError18).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                  } else {
                    Dafny.ISequence<byte> _145_branchKeyVersion = (_144_valueOrError18).Extract();
                    Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _146_valueOrError19 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("branchKey"), _105_obj);
                    if ((_146_valueOrError19).IsFailure()) {
                      return (_146_valueOrError19).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                    } else {
                      Dafny.ISequence<char> _147_branchKeyEncoded = (_146_valueOrError19).Extract();
                      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _148_valueOrError20 = Base64_Compile.__default.Decode(_147_branchKeyEncoded);
                      if ((_148_valueOrError20).IsFailure()) {
                        return (_148_valueOrError20).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                      } else {
                        Dafny.ISequence<byte> _149_branchKey = (_148_valueOrError20).Extract();
                        Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _150_valueOrError21 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("beaconKey"), _105_obj);
                        if ((_150_valueOrError21).IsFailure()) {
                          return (_150_valueOrError21).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                        } else {
                          Dafny.ISequence<char> _151_beaconKeyEncoded = (_150_valueOrError21).Extract();
                          Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _152_valueOrError22 = Base64_Compile.__default.Decode(_151_beaconKeyEncoded);
                          if ((_152_valueOrError22).IsFailure()) {
                            return (_152_valueOrError22).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                          } else {
                            Dafny.ISequence<byte> _153_beaconKey = (_152_valueOrError22).Extract();
                            return Wrappers_Compile.Result<KeyMaterial_Compile._IKeyMaterial, Dafny.ISequence<char>>.create_Success(KeyMaterial_Compile.KeyMaterial.create_StaticKeyStoreInformation(_141_keyIdentifier, _145_branchKeyVersion, _149_branchKey, _153_beaconKey));
                          }
                        }
                      }
                    }
                  }
                }
              }
            } else {
              Wrappers_Compile._IResult<bool, Dafny.ISequence<char>> _154_valueOrError23 = JSONHelpers_Compile.__default.GetBool(Dafny.Sequence<char>.FromString("encrypt"), _105_obj);
              if ((_154_valueOrError23).IsFailure()) {
                return (_154_valueOrError23).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
              } else {
                bool _155_encrypt = (_154_valueOrError23).Extract();
                Wrappers_Compile._IResult<bool, Dafny.ISequence<char>> _156_valueOrError24 = JSONHelpers_Compile.__default.GetBool(Dafny.Sequence<char>.FromString("decrypt"), _105_obj);
                if ((_156_valueOrError24).IsFailure()) {
                  return (_156_valueOrError24).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                } else {
                  bool _157_decrypt = (_156_valueOrError24).Extract();
                  Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _158_valueOrError25 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("key-id"), _105_obj);
                  if ((_158_valueOrError25).IsFailure()) {
                    return (_158_valueOrError25).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                  } else {
                    Dafny.ISequence<char> _159_keyIdentifier = (_158_valueOrError25).Extract();
                    if (object.Equals(_108_typ, Dafny.Sequence<char>.FromString("aws-kms"))) {
                      return Wrappers_Compile.Result<KeyMaterial_Compile._IKeyMaterial, Dafny.ISequence<char>>.create_Success(KeyMaterial_Compile.KeyMaterial.create_KMS(name, _155_encrypt, _157_decrypt, _159_keyIdentifier));
                    } else {
                      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _160_valueOrError26 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("algorithm"), _105_obj);
                      if ((_160_valueOrError26).IsFailure()) {
                        return (_160_valueOrError26).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                      } else {
                        Dafny.ISequence<char> _161_algorithm = (_160_valueOrError26).Extract();
                        Wrappers_Compile._IResult<BigInteger, Dafny.ISequence<char>> _162_valueOrError27 = JSONHelpers_Compile.__default.GetNat(Dafny.Sequence<char>.FromString("bits"), _105_obj);
                        if ((_162_valueOrError27).IsFailure()) {
                          return (_162_valueOrError27).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                        } else {
                          BigInteger _163_bits = (_162_valueOrError27).Extract();
                          Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _164_valueOrError28 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("encoding"), _105_obj);
                          if ((_164_valueOrError28).IsFailure()) {
                            return (_164_valueOrError28).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                          } else {
                            Dafny.ISequence<char> _165_encoding = (_164_valueOrError28).Extract();
                            Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _166_valueOrError29 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("material"), _105_obj);
                            if ((_166_valueOrError29).IsFailure()) {
                              return (_166_valueOrError29).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                            } else {
                              Dafny.ISequence<char> _167_material = (_166_valueOrError29).Extract();
                              if (object.Equals(_108_typ, Dafny.Sequence<char>.FromString("symmetric"))) {
                                Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _168_valueOrError30 = Base64_Compile.__default.Decode(_167_material);
                                if ((_168_valueOrError30).IsFailure()) {
                                  return (_168_valueOrError30).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                                } else {
                                  Dafny.ISequence<byte> _169_materialBytes = (_168_valueOrError30).Extract();
                                  return Wrappers_Compile.Result<KeyMaterial_Compile._IKeyMaterial, Dafny.ISequence<char>>.create_Success(KeyMaterial_Compile.KeyMaterial.create_Symetric(name, _155_encrypt, _157_decrypt, _161_algorithm, _163_bits, _165_encoding, _169_materialBytes, _159_keyIdentifier));
                                }
                              } else if (object.Equals(_108_typ, Dafny.Sequence<char>.FromString("private"))) {
                                return Wrappers_Compile.Result<KeyMaterial_Compile._IKeyMaterial, Dafny.ISequence<char>>.create_Success(KeyMaterial_Compile.KeyMaterial.create_PrivateRSA(name, _155_encrypt, _157_decrypt, _161_algorithm, _163_bits, _165_encoding, _167_material, _159_keyIdentifier));
                              } else if (object.Equals(_108_typ, Dafny.Sequence<char>.FromString("public"))) {
                                return Wrappers_Compile.Result<KeyMaterial_Compile._IKeyMaterial, Dafny.ISequence<char>>.create_Success(KeyMaterial_Compile.KeyMaterial.create_PublicRSA(name, _155_encrypt, _157_decrypt, _163_bits, _161_algorithm, _165_encoding, _167_material, _159_keyIdentifier));
                              } else {
                                Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _170_valueOrError31 = UTF8.__default.Encode(_167_material);
                                if ((_170_valueOrError31).IsFailure()) {
                                  return (_170_valueOrError31).PropagateFailure<KeyMaterial_Compile._IKeyMaterial>();
                                } else {
                                  Dafny.ISequence<byte> _171_publicKey = (_170_valueOrError31).Extract();
                                  return Wrappers_Compile.Result<KeyMaterial_Compile._IKeyMaterial, Dafny.ISequence<char>>.create_Success(KeyMaterial_Compile.KeyMaterial.create_KMSAsymetric(name, _155_encrypt, _157_decrypt, _159_keyIdentifier, _163_bits, _161_algorithm, _165_encoding, _171_publicKey));
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey, Dafny.ISequence<char>> ToEncryptedDataKey(Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj) {
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _172_valueOrError0 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("keyProviderId"), obj);
      if ((_172_valueOrError0).IsFailure()) {
        return (_172_valueOrError0).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>();
      } else {
        Dafny.ISequence<char> _173_keyProviderIdJSON = (_172_valueOrError0).Extract();
        Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _174_valueOrError1 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("keyProviderInfo"), obj);
        if ((_174_valueOrError1).IsFailure()) {
          return (_174_valueOrError1).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>();
        } else {
          Dafny.ISequence<char> _175_keyProviderInfoJSON = (_174_valueOrError1).Extract();
          Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _176_valueOrError2 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("ciphertext"), obj);
          if ((_176_valueOrError2).IsFailure()) {
            return (_176_valueOrError2).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>();
          } else {
            Dafny.ISequence<char> _177_ciphertextJSON = (_176_valueOrError2).Extract();
            Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _178_valueOrError3 = UTF8.__default.Encode(_173_keyProviderIdJSON);
            if ((_178_valueOrError3).IsFailure()) {
              return (_178_valueOrError3).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>();
            } else {
              Dafny.ISequence<byte> _179_keyProviderId = (_178_valueOrError3).Extract();
              Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _180_valueOrError4 = Base64_Compile.__default.Decode(_175_keyProviderInfoJSON);
              if ((_180_valueOrError4).IsFailure()) {
                return (_180_valueOrError4).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>();
              } else {
                Dafny.ISequence<byte> _181_keyProviderInfo = (_180_valueOrError4).Extract();
                Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _182_valueOrError5 = Base64_Compile.__default.Decode(_177_ciphertextJSON);
                if ((_182_valueOrError5).IsFailure()) {
                  return (_182_valueOrError5).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>();
                } else {
                  Dafny.ISequence<byte> _183_ciphertext = (_182_valueOrError5).Extract();
                  return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey, Dafny.ISequence<char>>.create_Success(software.amazon.cryptography.materialproviders.internaldafny.types.EncryptedDataKey.create(_179_keyProviderId, _181_keyProviderInfo, _183_ciphertext));
                }
              }
            }
          }
        }
      }
    }
    public static bool KeyMaterialString_q(Dafny.ISequence<char> s) {
      return (((((((s).Equals(Dafny.Sequence<char>.FromString("static-material"))) || ((s).Equals(Dafny.Sequence<char>.FromString("aws-kms")))) || ((s).Equals(Dafny.Sequence<char>.FromString("symmetric")))) || ((s).Equals(Dafny.Sequence<char>.FromString("private")))) || ((s).Equals(Dafny.Sequence<char>.FromString("public")))) || ((s).Equals(Dafny.Sequence<char>.FromString("static-branch-key")))) || ((s).Equals(Dafny.Sequence<char>.FromString("aws-kms-rsa")));
    }
  }
} // end of namespace KeyMaterial_Compile
namespace CreateStaticKeyrings_Compile {

  public partial class StaticMaterialsKeyring : software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring {
    public StaticMaterialsKeyring() {
      this._encryptMaterial = default(software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials);
      this._decryptMaterial = default(software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials);
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out0;
      _out0 = software.amazon.cryptography.materialproviders.internaldafny.types._Companion_IKeyring.OnEncrypt(this, input);
      return _out0;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out1;
      _out1 = software.amazon.cryptography.materialproviders.internaldafny.types._Companion_IKeyring.OnDecrypt(this, input);
      return _out1;
    }
    public void __ctor(software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials encryptMaterial, software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials decryptMaterial)
    {
      (this)._encryptMaterial = encryptMaterial;
      (this)._decryptMaterial = decryptMaterial;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnEncrypt_k(software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> res = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      res = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptOutput.create((this).encryptMaterial));
      return res;
      return res;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> OnDecrypt_k(software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> res = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      res = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.create_Success(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptOutput.create((this).decryptMaterial));
      return res;
      return res;
    }
    public software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _encryptMaterial {get; set;}
    public software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials encryptMaterial { get {
      return this._encryptMaterial;
    } }
    public software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _decryptMaterial {get; set;}
    public software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials decryptMaterial { get {
      return this._decryptMaterial;
    } }
  }

  public partial class __default {
    public static software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring CreateStaticMaterialsKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials encryptMaterial, software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials decryptMaterial)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring = default(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring);
      CreateStaticKeyrings_Compile.StaticMaterialsKeyring _nw0 = new CreateStaticKeyrings_Compile.StaticMaterialsKeyring();
      _nw0.__ctor(encryptMaterial, decryptMaterial);
      keyring = _nw0;
      return keyring;
      return keyring;
    }
  }
} // end of namespace CreateStaticKeyrings_Compile
namespace CreateStaticKeyStores_Compile {

  public partial class StaticKeyStore : software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient {
    public StaticKeyStore() {
      this._staticKeyMaterial = KeyMaterial_Compile.KeyMaterial.Default();
    }
    public void __ctor(KeyMaterial_Compile._IKeyMaterial staticKeyMaterial)
    {
      (this)._staticKeyMaterial = staticKeyMaterial;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> GetActiveBranchKey(software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput.Default());
      output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetActiveBranchKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.create_Success(software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput.create(software.amazon.cryptography.keystore.internaldafny.types.BranchKeyMaterials.create((input).dtor_branchKeyIdentifier, ((this).staticKeyMaterial).dtor_branchKeyVersion, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(), ((this).staticKeyMaterial).dtor_branchKey)));
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> GetBranchKeyVersion(software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput.Default());
      output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetBranchKeyVersionOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.create_Success(software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput.create(software.amazon.cryptography.keystore.internaldafny.types.BranchKeyMaterials.create((input).dtor_branchKeyIdentifier, ((this).staticKeyMaterial).dtor_branchKeyVersion, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(), ((this).staticKeyMaterial).dtor_branchKey)));
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> GetBeaconKey(software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyOutput.Default());
      output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetBeaconKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.create_Success(software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyOutput.create(software.amazon.cryptography.keystore.internaldafny.types.BeaconKeyMaterials.create((input).dtor_branchKeyIdentifier, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((this).staticKeyMaterial).dtor_beaconKey), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<byte>>>.create_None())));
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetKeyStoreInfoOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> GetKeyStoreInfo()
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetKeyStoreInfoOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> output = default(Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IGetKeyStoreInfoOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>);
      output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IGetKeyStoreInfoOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.create_Failure(software.amazon.cryptography.keystore.internaldafny.types.Error.create_KeyStoreException(Dafny.Sequence<char>.FromString("Not Supported")));
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> CreateKeyStore(software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreOutput.Default());
      output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyStoreOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.create_Failure(software.amazon.cryptography.keystore.internaldafny.types.Error.create_KeyStoreException(Dafny.Sequence<char>.FromString("Not Supported")));
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> CreateKey(software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.CreateKeyOutput.Default());
      output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._ICreateKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.create_Failure(software.amazon.cryptography.keystore.internaldafny.types.Error.create_KeyStoreException(Dafny.Sequence<char>.FromString("Not Supported")));
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> VersionKey(software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError> output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.Default(software.amazon.cryptography.keystore.internaldafny.types.VersionKeyOutput.Default());
      output = Wrappers_Compile.Result<software.amazon.cryptography.keystore.internaldafny.types._IVersionKeyOutput, software.amazon.cryptography.keystore.internaldafny.types._IError>.create_Failure(software.amazon.cryptography.keystore.internaldafny.types.Error.create_KeyStoreException(Dafny.Sequence<char>.FromString("Not Supported")));
      return output;
    }
    public KeyMaterial_Compile._IKeyMaterial _staticKeyMaterial {get; set;}
    public KeyMaterial_Compile._IKeyMaterial staticKeyMaterial { get {
      return this._staticKeyMaterial;
    } }
  }

  public partial class __default {
    public static software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient CreateStaticKeyStore(KeyMaterial_Compile._IKeyMaterial staticKeyMaterial)
    {
      software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient keyStore = default(software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient);
      CreateStaticKeyStores_Compile.StaticKeyStore _nw1 = new CreateStaticKeyStores_Compile.StaticKeyStore();
      _nw1.__ctor(staticKeyMaterial);
      keyStore = _nw1;
      return keyStore;
      return keyStore;
    }
  }
} // end of namespace CreateStaticKeyStores_Compile
namespace KeyringFromKeyDescription_Compile {

  public interface _IKeyringInfo {
    bool is_KeyringInfo { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_description { get; }
    Wrappers_Compile._IOption<KeyMaterial_Compile._IKeyMaterial> dtor_material { get; }
    _IKeyringInfo DowncastClone();
  }
  public class KeyringInfo : _IKeyringInfo {
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _description;
    public readonly Wrappers_Compile._IOption<KeyMaterial_Compile._IKeyMaterial> _material;
    public KeyringInfo(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription description, Wrappers_Compile._IOption<KeyMaterial_Compile._IKeyMaterial> material) {
      this._description = description;
      this._material = material;
    }
    public _IKeyringInfo DowncastClone() {
      if (this is _IKeyringInfo dt) { return dt; }
      return new KeyringInfo(_description, _material);
    }
    public override bool Equals(object other) {
      var oth = other as KeyringFromKeyDescription_Compile.KeyringInfo;
      return oth != null && object.Equals(this._description, oth._description) && object.Equals(this._material, oth._material);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._description));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._material));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyringFromKeyDescription_Compile.KeyringInfo.KeyringInfo";
      s += "(";
      s += Dafny.Helpers.ToString(this._description);
      s += ", ";
      s += Dafny.Helpers.ToString(this._material);
      s += ")";
      return s;
    }
    private static readonly KeyringFromKeyDescription_Compile._IKeyringInfo theDefault = create(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.Default(), Wrappers_Compile.Option<KeyMaterial_Compile._IKeyMaterial>.Default());
    public static KeyringFromKeyDescription_Compile._IKeyringInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KeyringFromKeyDescription_Compile._IKeyringInfo> _TYPE = new Dafny.TypeDescriptor<KeyringFromKeyDescription_Compile._IKeyringInfo>(KeyringFromKeyDescription_Compile.KeyringInfo.Default());
    public static Dafny.TypeDescriptor<KeyringFromKeyDescription_Compile._IKeyringInfo> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyringInfo create(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription description, Wrappers_Compile._IOption<KeyMaterial_Compile._IKeyMaterial> material) {
      return new KeyringInfo(description, material);
    }
    public static _IKeyringInfo create_KeyringInfo(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription description, Wrappers_Compile._IOption<KeyMaterial_Compile._IKeyMaterial> material) {
      return create(description, material);
    }
    public bool is_KeyringInfo { get { return true; } }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_description {
      get {
        return this._description;
      }
    }
    public Wrappers_Compile._IOption<KeyMaterial_Compile._IKeyMaterial> dtor_material {
      get {
        return this._material;
      }
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> ToKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient mpl, KeyringFromKeyDescription_Compile._IKeyringInfo info)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> output = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      KeyringFromKeyDescription_Compile._IKeyringInfo _let_tmp_rhs0 = info;
      software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _184_description = _let_tmp_rhs0.dtor_description;
      Wrappers_Compile._IOption<KeyMaterial_Compile._IKeyMaterial> _185_material = _let_tmp_rhs0.dtor_material;
      software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _source0 = _184_description;
      if (_source0.is_Kms) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo _186___mcc_h0 = _source0.dtor_Kms;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo _source1 = _186___mcc_h0;
        {
          Dafny.ISequence<char> _187___mcc_h1 = _source1.dtor_keyId;
          Dafny.ISequence<char> _188_key = _187___mcc_h1;
          {
            Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _189_valueOrError1 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default();
            _189_valueOrError1 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(((_185_material).is_Some) && (((_185_material).dtor_value).is_KMS), software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Not type: KMS")));
            if ((_189_valueOrError1).IsFailure()) {
              output = (_189_valueOrError1).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _190_kmsClient;
            Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _191_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
            Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _out2;
            _out2 = KeyringFromKeyDescription_Compile.__default.getKmsClient(mpl, ((_185_material).dtor_value).dtor_keyIdentifier);
            _191_valueOrError2 = _out2;
            if ((_191_valueOrError2).IsFailure()) {
              output = (_191_valueOrError2).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            _190_kmsClient = (_191_valueOrError2).Extract();
            software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsKeyringInput _192_input;
            _192_input = software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsKeyringInput.create(((_185_material).dtor_value).dtor_keyIdentifier, _190_kmsClient, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None());
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _193_keyring;
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out3;
            _out3 = (mpl).CreateAwsKmsKeyring(_192_input);
            _193_keyring = _out3;
            output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_193_keyring, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_194_e) => {
              return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_194_e);
            })));
            return output;
          }
        }
      } else if (_source0.is_KmsMrk) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware _195___mcc_h2 = _source0.dtor_KmsMrk;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware _source2 = _195___mcc_h2;
        {
          Dafny.ISequence<char> _196___mcc_h3 = _source2.dtor_keyId;
          Dafny.ISequence<char> _197_key = _196___mcc_h3;
          {
            Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _198_valueOrError3 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default();
            _198_valueOrError3 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(((_185_material).is_Some) && (((_185_material).dtor_value).is_KMS), software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Not type: KMS")));
            if ((_198_valueOrError3).IsFailure()) {
              output = (_198_valueOrError3).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _199_kmsClient;
            Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _200_valueOrError4 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
            Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _out4;
            _out4 = KeyringFromKeyDescription_Compile.__default.getKmsClient(mpl, ((_185_material).dtor_value).dtor_keyIdentifier);
            _200_valueOrError4 = _out4;
            if ((_200_valueOrError4).IsFailure()) {
              output = (_200_valueOrError4).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            _199_kmsClient = (_200_valueOrError4).Extract();
            software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMrkKeyringInput _201_input;
            _201_input = software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkKeyringInput.create(((_185_material).dtor_value).dtor_keyIdentifier, _199_kmsClient, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None());
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _202_keyring;
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out5;
            _out5 = (mpl).CreateAwsKmsMrkKeyring(_201_input);
            _202_keyring = _out5;
            output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_202_keyring, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_203_e) => {
              return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_203_e);
            })));
            return output;
          }
        }
      } else if (_source0.is_KmsMrkDiscovery) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery _204___mcc_h4 = _source0.dtor_KmsMrkDiscovery;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery _source3 = _204___mcc_h4;
        {
          Dafny.ISequence<char> _205___mcc_h5 = _source3.dtor_keyId;
          Dafny.ISequence<char> _206___mcc_h6 = _source3.dtor_defaultMrkRegion;
          Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> _207___mcc_h7 = _source3.dtor_awsKmsDiscoveryFilter;
          Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> _208_awsKmsDiscoveryFilter = _207___mcc_h7;
          Dafny.ISequence<char> _209_defaultMrkRegion = _206___mcc_h6;
          {
            Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _210_valueOrError8 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default();
            _210_valueOrError8 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>((_185_material).is_None, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Discovery has not key")));
            if ((_210_valueOrError8).IsFailure()) {
              output = (_210_valueOrError8).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsMrkDiscoveryMultiKeyringInput _211_input;
            _211_input = software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkDiscoveryMultiKeyringInput.create(Dafny.Sequence<Dafny.ISequence<char>>.FromElements(_209_defaultMrkRegion), _208_awsKmsDiscoveryFilter, Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None());
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _212_keyring;
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out6;
            _out6 = (mpl).CreateAwsKmsMrkDiscoveryMultiKeyring(_211_input);
            _212_keyring = _out6;
            output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_212_keyring, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_213_e) => {
              return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_213_e);
            })));
            return output;
          }
        }
      } else if (_source0.is_RSA) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA _214___mcc_h8 = _source0.dtor_RSA;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA _source4 = _214___mcc_h8;
        {
          Dafny.ISequence<char> _215___mcc_h9 = _source4.dtor_keyId;
          Dafny.ISequence<char> _216___mcc_h10 = _source4.dtor_providerId;
          software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme _217___mcc_h11 = _source4.dtor_padding;
          software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme _218_padding = _217___mcc_h11;
          Dafny.ISequence<char> _219_providerId = _216___mcc_h10;
          Dafny.ISequence<char> _220_key = _215___mcc_h9;
          {
            Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _221_valueOrError11 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default();
            _221_valueOrError11 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(((_185_material).is_Some) && ((((_185_material).dtor_value).is_PrivateRSA) || (((_185_material).dtor_value).is_PublicRSA)), software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Not type: PrivateRSA or PublicRSA")));
            if ((_221_valueOrError11).IsFailure()) {
              output = (_221_valueOrError11).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            Wrappers_Compile._IOption<KeyMaterial_Compile._IKeyMaterial> _source5 = _185_material;
            {
              KeyMaterial_Compile._IKeyMaterial _222___mcc_h22 = _source5.dtor_value;
              KeyMaterial_Compile._IKeyMaterial _source6 = _222___mcc_h22;
              if (_source6.is_PrivateRSA) {
                Dafny.ISequence<char> _223___mcc_h31 = _source6.dtor_name;
                bool _224___mcc_h32 = _source6.dtor_encrypt;
                bool _225___mcc_h33 = _source6.dtor_decrypt;
                Dafny.ISequence<char> _226___mcc_h34 = _source6.dtor_algorithm;
                BigInteger _227___mcc_h35 = _source6.dtor_bits;
                Dafny.ISequence<char> _228___mcc_h36 = _source6.dtor_encoding;
                Dafny.ISequence<char> _229___mcc_h37 = _source6.dtor_material;
                Dafny.ISequence<char> _230___mcc_h38 = _source6.dtor_keyIdentifier;
                Dafny.ISequence<char> _231_keyIdentifier = _230___mcc_h38;
                Dafny.ISequence<char> _232_material = _229___mcc_h37;
                bool _233_decrypt = _225___mcc_h33;
                {
                  Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _234_valueOrError12 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default();
                  _234_valueOrError12 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_233_decrypt, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Private RSA keys only supports decrypt.")));
                  if ((_234_valueOrError12).IsFailure()) {
                    output = (_234_valueOrError12).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
                    return output;
                  }
                  Dafny.ISequence<byte> _235_privateKeyPemBytes;
                  Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _236_valueOrError13 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default(UTF8.ValidUTF8Bytes.Default());
                  _236_valueOrError13 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(UTF8.__default.Encode(_232_material), ((System.Func<Dafny.ISequence<char>, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_237_e) => {
                    return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(_237_e);
                  })));
                  if ((_236_valueOrError13).IsFailure()) {
                    output = (_236_valueOrError13).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
                    return output;
                  }
                  _235_privateKeyPemBytes = (_236_valueOrError13).Extract();
                  software.amazon.cryptography.materialproviders.internaldafny.types._ICreateRawRsaKeyringInput _238_input;
                  _238_input = software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput.create(_219_providerId, _231_keyIdentifier, _218_padding, Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_235_privateKeyPemBytes));
                  Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _239_keyring;
                  Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out7;
                  _out7 = (mpl).CreateRawRsaKeyring(_238_input);
                  _239_keyring = _out7;
                  output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_239_keyring, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_240_e) => {
                    return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_240_e);
                  })));
                  return output;
                }
              } else {
                Dafny.ISequence<char> _241___mcc_h39 = _source6.dtor_name;
                bool _242___mcc_h40 = _source6.dtor_encrypt;
                bool _243___mcc_h41 = _source6.dtor_decrypt;
                BigInteger _244___mcc_h42 = _source6.dtor_bits;
                Dafny.ISequence<char> _245___mcc_h43 = _source6.dtor_algorithm;
                Dafny.ISequence<char> _246___mcc_h44 = _source6.dtor_encoding;
                Dafny.ISequence<char> _247___mcc_h45 = _source6.dtor_material;
                Dafny.ISequence<char> _248___mcc_h46 = _source6.dtor_keyIdentifier;
                Dafny.ISequence<char> _249_keyIdentifier = _248___mcc_h46;
                Dafny.ISequence<char> _250_material = _247___mcc_h45;
                bool _251_encrypt = _242___mcc_h40;
                {
                  Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _252_valueOrError14 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default();
                  _252_valueOrError14 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_251_encrypt, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Public RSA keys only supports encrypt.")));
                  if ((_252_valueOrError14).IsFailure()) {
                    output = (_252_valueOrError14).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
                    return output;
                  }
                  Dafny.ISequence<byte> _253_publicKeyPemBytes;
                  Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _254_valueOrError15 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default(UTF8.ValidUTF8Bytes.Default());
                  _254_valueOrError15 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(UTF8.__default.Encode(_250_material), ((System.Func<Dafny.ISequence<char>, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_255_e) => {
                    return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(_255_e);
                  })));
                  if ((_254_valueOrError15).IsFailure()) {
                    output = (_254_valueOrError15).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
                    return output;
                  }
                  _253_publicKeyPemBytes = (_254_valueOrError15).Extract();
                  software.amazon.cryptography.materialproviders.internaldafny.types._ICreateRawRsaKeyringInput _256_input;
                  _256_input = software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput.create(_219_providerId, _249_keyIdentifier, _218_padding, Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(_253_publicKeyPemBytes), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None());
                  Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _257_keyring;
                  Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out8;
                  _out8 = (mpl).CreateRawRsaKeyring(_256_input);
                  _257_keyring = _out8;
                  output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_257_keyring, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_258_e) => {
                    return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_258_e);
                  })));
                  return output;
                }
              }
            }
          }
        }
      } else if (_source0.is_AES) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES _259___mcc_h12 = _source0.dtor_AES;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES _source7 = _259___mcc_h12;
        {
          Dafny.ISequence<char> _260___mcc_h13 = _source7.dtor_keyId;
          Dafny.ISequence<char> _261___mcc_h14 = _source7.dtor_providerId;
          Dafny.ISequence<char> _262_providerId = _261___mcc_h14;
          Dafny.ISequence<char> _263_key = _260___mcc_h13;
          {
            Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _264_valueOrError9 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default();
            _264_valueOrError9 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(((_185_material).is_Some) && (((_185_material).dtor_value).is_Symetric), software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Not type: Symetric")));
            if ((_264_valueOrError9).IsFailure()) {
              output = (_264_valueOrError9).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg _265_wrappingAlg;
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _266_valueOrError10 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default(software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.Default());
            _266_valueOrError10 = (((((_185_material).dtor_value).dtor_bits) == (new BigInteger(128))) ? (Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.create_Success(software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES128__GCM__IV12__TAG16())) : ((((((_185_material).dtor_value).dtor_bits) == (new BigInteger(192))) ? (Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.create_Success(software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES192__GCM__IV12__TAG16())) : ((((((_185_material).dtor_value).dtor_bits) == (new BigInteger(256))) ? (Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.create_Success(software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.create_ALG__AES256__GCM__IV12__TAG16())) : (Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.create_Failure(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Not a supported bit length")))))))));
            if ((_266_valueOrError10).IsFailure()) {
              output = (_266_valueOrError10).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            _265_wrappingAlg = (_266_valueOrError10).Extract();
            software.amazon.cryptography.materialproviders.internaldafny.types._ICreateRawAesKeyringInput _267_input;
            _267_input = software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput.create(_262_providerId, ((_185_material).dtor_value).dtor_keyIdentifier, ((_185_material).dtor_value).dtor_wrappingKey, _265_wrappingAlg);
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _268_keyring;
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out9;
            _out9 = (mpl).CreateRawAesKeyring(_267_input);
            _268_keyring = _out9;
            output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_268_keyring, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_269_e) => {
              return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_269_e);
            })));
            return output;
          }
        }
      } else if (_source0.is_Static) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring _270___mcc_h15 = _source0.dtor_Static;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring _source8 = _270___mcc_h15;
        {
          Dafny.ISequence<char> _271___mcc_h16 = _source8.dtor_keyId;
          Dafny.ISequence<char> _272_key = _271___mcc_h16;
          {
            Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _273_valueOrError0 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default();
            _273_valueOrError0 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(((_185_material).is_Some) && (((_185_material).dtor_value).is_StaticMaterial), software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Not type: StaticMaterial")));
            if ((_273_valueOrError0).IsFailure()) {
              output = (_273_valueOrError0).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _274_encrypt;
            _274_encrypt = software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials.create(((_185_material).dtor_value).dtor_algorithmSuite, ((_185_material).dtor_value).dtor_encryptionContext, ((_185_material).dtor_value).dtor_encryptedDataKeys, ((_185_material).dtor_value).dtor_requiredEncryptionContextKeys, ((_185_material).dtor_value).dtor_plaintextDataKey, ((_185_material).dtor_value).dtor_signingKey, ((_185_material).dtor_value).dtor_symmetricSigningKeys);
            software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _275_decrypt;
            _275_decrypt = software.amazon.cryptography.materialproviders.internaldafny.types.DecryptionMaterials.create(((_185_material).dtor_value).dtor_algorithmSuite, ((_185_material).dtor_value).dtor_encryptionContext, ((_185_material).dtor_value).dtor_requiredEncryptionContextKeys, ((_185_material).dtor_value).dtor_plaintextDataKey, ((_185_material).dtor_value).dtor_verificationKey, Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None());
            software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _276_keyring;
            software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out10;
            _out10 = CreateStaticKeyrings_Compile.__default.CreateStaticMaterialsKeyring(_274_encrypt, _275_decrypt);
            _276_keyring = _out10;
            output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.create_Success(_276_keyring);
            return output;
          }
        }
      } else if (_source0.is_KmsRsa) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring _277___mcc_h17 = _source0.dtor_KmsRsa;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring _source9 = _277___mcc_h17;
        {
          Dafny.ISequence<char> _278___mcc_h18 = _source9.dtor_keyId;
          software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec _279___mcc_h19 = _source9.dtor_encryptionAlgorithm;
          software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec _280_encryptionAlgorithm = _279___mcc_h19;
          Dafny.ISequence<char> _281_key = _278___mcc_h18;
          {
            Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _282_valueOrError5 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default();
            _282_valueOrError5 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(((_185_material).is_Some) && (((_185_material).dtor_value).is_KMSAsymetric), software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Not type: KMSAsymetric")));
            if ((_282_valueOrError5).IsFailure()) {
              output = (_282_valueOrError5).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _283_kmsClient;
            Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _284_valueOrError6 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
            Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _out11;
            _out11 = KeyringFromKeyDescription_Compile.__default.getKmsClient(mpl, ((_185_material).dtor_value).dtor_keyIdentifier);
            _284_valueOrError6 = _out11;
            if ((_284_valueOrError6).IsFailure()) {
              output = (_284_valueOrError6).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            _283_kmsClient = (_284_valueOrError6).Extract();
            software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsRsaKeyringInput _285_input;
            _285_input = software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsRsaKeyringInput.create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_185_material).dtor_value).dtor_publicKey), ((_185_material).dtor_value).dtor_keyIdentifier, _280_encryptionAlgorithm, Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>.create_Some(_283_kmsClient), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None());
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _286_keyring;
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out12;
            _out12 = (mpl).CreateAwsKmsRsaKeyring(_285_input);
            _286_keyring = _out12;
            output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_286_keyring, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_287_e) => {
              return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_287_e);
            })));
            return output;
          }
        }
      } else {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring _288___mcc_h20 = _source0.dtor_Hierarchy;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring _source10 = _288___mcc_h20;
        {
          Dafny.ISequence<char> _289___mcc_h21 = _source10.dtor_keyId;
          Dafny.ISequence<char> _290_key = _289___mcc_h21;
          {
            Wrappers_Compile._IOutcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _291_valueOrError7 = Wrappers_Compile.Outcome<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default();
            _291_valueOrError7 = Wrappers_Compile.__default.Need<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(((_185_material).is_Some) && (((_185_material).dtor_value).is_StaticKeyStoreInformation), software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Not type: StaticKeyStoreInformation")));
            if ((_291_valueOrError7).IsFailure()) {
              output = (_291_valueOrError7).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
              return output;
            }
            software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient _292_keyStore;
            software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient _out13;
            _out13 = CreateStaticKeyStores_Compile.__default.CreateStaticKeyStore((_185_material).dtor_value);
            _292_keyStore = _out13;
            software.amazon.cryptography.materialproviders.internaldafny.types._ICreateAwsKmsHierarchicalKeyringInput _293_input;
            _293_input = software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsHierarchicalKeyringInput.create(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(((_185_material).dtor_value).dtor_keyIdentifier), Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IBranchKeyIdSupplier>.create_None(), _292_keyStore, 0L, Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._ICacheType>.create_None());
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _294_keyring;
            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out14;
            _out14 = (mpl).CreateAwsKmsHierarchicalKeyring(_293_input);
            _294_keyring = _out14;
            output = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_294_keyring, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_295_e) => {
              return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_295_e);
            })));
            return output;
          }
        }
      }
      return output;
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> getKmsClient(software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient mpl, Dafny.ISequence<char> maybeKmsArn)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> output = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _296_maybeClientSupplier;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out15;
      _out15 = (mpl).CreateDefaultClientSupplier(software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultClientSupplierInput.create());
      _296_maybeClientSupplier = _out15;
      software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier _297_clientSupplier;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _298_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      _298_valueOrError0 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_296_maybeClientSupplier, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_299_e) => {
        return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_299_e);
      })));
      if ((_298_valueOrError0).IsFailure()) {
        output = (_298_valueOrError0).PropagateFailure<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>();
        return output;
      }
      _297_clientSupplier = (_298_valueOrError0).Extract();
      AwsArnParsing_Compile._IAwsArn _300_arn;
      Wrappers_Compile._IResult<AwsArnParsing_Compile._IAwsArn, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _301_valueOrError1 = default(Wrappers_Compile._IResult<AwsArnParsing_Compile._IAwsArn, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      _301_valueOrError1 = Wrappers_Compile.Result<AwsArnParsing_Compile._IAwsArn, Dafny.ISequence<char>>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(AwsArnParsing_Compile.__default.ParseAwsKmsArn(maybeKmsArn), ((System.Func<Dafny.ISequence<char>, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_302_e) => {
        return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(_302_e);
      })));
      if ((_301_valueOrError1).IsFailure()) {
        output = (_301_valueOrError1).PropagateFailure<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient>();
        return output;
      }
      _300_arn = (_301_valueOrError1).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _303_tmp;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out16;
      _out16 = (_297_clientSupplier).GetClient(software.amazon.cryptography.materialproviders.internaldafny.types.GetClientInput.create((_300_arn).dtor_region));
      _303_tmp = _out16;
      output = Wrappers_Compile.Result<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_303_tmp, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_304_e) => {
        return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_304_e);
      })));
      return output;
    }
  }
} // end of namespace KeyringFromKeyDescription_Compile
namespace software.amazon.cryptography.materialproviders.internaldafny.wrapped {

  public partial class __default {
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IMaterialProvidersConfig WrappedDefaultMaterialProvidersConfig() {
      return software.amazon.cryptography.materialproviders.internaldafny.types.MaterialProvidersConfig.create();
    }
  }
} // end of namespace software.amazon.cryptography.materialproviders.internaldafny.wrapped
namespace KeysVectorOperations_Compile {

  public interface _IConfig {
    bool is_Config { get; }
    Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial> dtor_keys { get; }
    _IConfig DowncastClone();
  }
  public class Config : _IConfig {
    public readonly Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial> _keys;
    public Config(Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial> keys) {
      this._keys = keys;
    }
    public _IConfig DowncastClone() {
      if (this is _IConfig dt) { return dt; }
      return new Config(_keys);
    }
    public override bool Equals(object other) {
      var oth = other as KeysVectorOperations_Compile.Config;
      return oth != null && object.Equals(this._keys, oth._keys);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keys));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeysVectorOperations_Compile.Config.Config";
      s += "(";
      s += Dafny.Helpers.ToString(this._keys);
      s += ")";
      return s;
    }
    private static readonly KeysVectorOperations_Compile._IConfig theDefault = create(Dafny.Map<Dafny.ISequence<char>, KeyMaterial_Compile._IKeyMaterial>.Empty);
    public static KeysVectorOperations_Compile._IConfig Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KeysVectorOperations_Compile._IConfig> _TYPE = new Dafny.TypeDescriptor<KeysVectorOperations_Compile._IConfig>(KeysVectorOperations_Compile.Config.Default());
    public static Dafny.TypeDescriptor<KeysVectorOperations_Compile._IConfig> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConfig create(Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial> keys) {
      return new Config(keys);
    }
    public static _IConfig create_Config(Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial> keys) {
      return create(keys);
    }
    public bool is_Config { get { return true; } }
    public Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial> dtor_keys {
      get {
        return this._keys;
      }
    }
  }

  public partial class __default {
    public static bool CreateTestVectorKeyringEnsuresPublicly(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput input, Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> output)
    {
      return true;
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> CreateTestVectorKeyring(KeysVectorOperations_Compile._IConfig config, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> output = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _305_keyDescription;
      _305_keyDescription = (input).dtor_keyDescription;
      Dafny.ISequence<char> _306_keyId;
      _306_keyId = KeysVectorOperations_Compile.__default.GetKeyId(_305_keyDescription);
      KeyringFromKeyDescription_Compile._IKeyringInfo _307_info;
      _307_info = KeyringFromKeyDescription_Compile.KeyringInfo.create(_305_keyDescription, ((((config).dtor_keys).Contains(_306_keyId)) ? (Wrappers_Compile.Option<KeyMaterial_Compile._IKeyMaterial>.create_Some(Dafny.Map<Dafny.ISequence<char>, KeyMaterial_Compile._IKeyMaterial>.Select((config).dtor_keys,_306_keyId))) : (Wrappers_Compile.Option<KeyMaterial_Compile._IKeyMaterial>.create_None())));
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _308_maybeMpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out17;
      _out17 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _308_maybeMpl = _out17;
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _309_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _310_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      _310_valueOrError0 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_308_maybeMpl, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_311_e) => {
        return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_311_e);
      })));
      if ((_310_valueOrError0).IsFailure()) {
        output = (_310_valueOrError0).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
        return output;
      }
      _309_mpl = (_310_valueOrError0).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _out18;
      _out18 = KeyringFromKeyDescription_Compile.__default.ToKeyring(_309_mpl, _307_info);
      output = _out18;
      return output;
    }
    public static bool CreateWappedTestVectorKeyringEnsuresPublicly(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput input, Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> output)
    {
      return true;
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> CreateWappedTestVectorKeyring(KeysVectorOperations_Compile._IConfig config, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> output = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _312_keyDescription;
      _312_keyDescription = (input).dtor_keyDescription;
      Dafny.ISequence<char> _313_keyId;
      _313_keyId = KeysVectorOperations_Compile.__default.GetKeyId(_312_keyDescription);
      KeyringFromKeyDescription_Compile._IKeyringInfo _314_info;
      _314_info = KeyringFromKeyDescription_Compile.KeyringInfo.create(_312_keyDescription, ((((config).dtor_keys).Contains(_313_keyId)) ? (Wrappers_Compile.Option<KeyMaterial_Compile._IKeyMaterial>.create_Some(Dafny.Map<Dafny.ISequence<char>, KeyMaterial_Compile._IKeyMaterial>.Select((config).dtor_keys,_313_keyId))) : (Wrappers_Compile.Option<KeyMaterial_Compile._IKeyMaterial>.create_None())));
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _315_maybeMpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out19;
      _out19 = software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedDefaultMaterialProvidersConfig());
      _315_maybeMpl = _out19;
      software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient _316_wrappedMPL;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _317_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      _317_valueOrError0 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_315_maybeMpl, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_318_e) => {
        return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_318_e);
      })));
      if ((_317_valueOrError0).IsFailure()) {
        output = (_317_valueOrError0).PropagateFailure<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>();
        return output;
      }
      _316_wrappedMPL = (_317_valueOrError0).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _out20;
      _out20 = KeyringFromKeyDescription_Compile.__default.ToKeyring(_316_wrappedMPL, _314_info);
      output = _out20;
      return output;
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> GetKeyDescription(KeysVectorOperations_Compile._IConfig config, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionInput input)
    {
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _319_valueOrError0 = Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(JSON_mAPI_Compile.__default.Deserialize((input).dtor_json), ((System.Func<JSON_mErrors_Compile._IDeserializationError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_320_e) => {
        return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.types.Error.create_AwsCryptographicMaterialProvidersException((_320_e)._ToString()));
      })));
      if ((_319_valueOrError0).IsFailure()) {
        return (_319_valueOrError0).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput>();
      } else {
        JSON_mValues_Compile._IJSON _321_keyDescriptionJSON = (_319_valueOrError0).Extract();
        Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _322_valueOrError1 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription, Dafny.ISequence<char>>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(KeyDescription_Compile.__default.ToKeyDescription(_321_keyDescriptionJSON), ((System.Func<Dafny.ISequence<char>, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_323_e) => {
          return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.types.Error.create_AwsCryptographicMaterialProvidersException(_323_e));
        })));
        if ((_322_valueOrError1).IsFailure()) {
          return (_322_valueOrError1).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput>();
        } else {
          software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _324_keyDescription = (_322_valueOrError1).Extract();
          return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.create_Success(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionOutput.create(_324_keyDescription));
        }
      }
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> SerializeKeyDescription(KeysVectorOperations_Compile._IConfig config, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionInput input)
    {
      return Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.create_Failure(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(Dafny.Sequence<char>.FromString("Not Supported")));
    }
    public static Dafny.ISequence<char> GetKeyId(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription input) {
      software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _source11 = input;
      if (_source11.is_Kms) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo _325___mcc_h0 = _source11.dtor_Kms;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKMSInfo _326_i = _325___mcc_h0;
        return (_326_i).dtor_keyId;
      } else if (_source11.is_KmsMrk) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware _327___mcc_h1 = _source11.dtor_KmsMrk;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAware _328_i = _327___mcc_h1;
        return (_328_i).dtor_keyId;
      } else if (_source11.is_KmsMrkDiscovery) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery _329___mcc_h2 = _source11.dtor_KmsMrkDiscovery;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsMrkAwareDiscovery _330_i = _329___mcc_h2;
        return (_330_i).dtor_keyId;
      } else if (_source11.is_RSA) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA _331___mcc_h3 = _source11.dtor_RSA;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawRSA _332_i = _331___mcc_h3;
        return (_332_i).dtor_keyId;
      } else if (_source11.is_AES) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES _333___mcc_h4 = _source11.dtor_AES;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IRawAES _334_i = _333___mcc_h4;
        return (_334_i).dtor_keyId;
      } else if (_source11.is_Static) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring _335___mcc_h5 = _source11.dtor_Static;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IStaticKeyring _336_i = _335___mcc_h5;
        return (_336_i).dtor_keyId;
      } else if (_source11.is_KmsRsa) {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring _337___mcc_h6 = _source11.dtor_KmsRsa;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKmsRsaKeyring _338_i = _337___mcc_h6;
        return (_338_i).dtor_keyId;
      } else {
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring _339___mcc_h7 = _source11.dtor_Hierarchy;
        software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IHierarchyKeyring _340_i = _339___mcc_h7;
        return (_340_i).dtor_keyId;
      }
    }
  }
} // end of namespace KeysVectorOperations_Compile
namespace software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny {

  public partial class KeyVectorsClient : software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.IKeyVectorsClient {
    public KeyVectorsClient() {
      this._config = KeysVectorOperations_Compile.Config.Default();
    }
    public void __ctor(KeysVectorOperations_Compile._IConfig config)
    {
      (this)._config = config;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> CreateTestVectorKeyring(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> output = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _out21;
      _out21 = KeysVectorOperations_Compile.__default.CreateTestVectorKeyring((this).config, input);
      output = _out21;
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> CreateWappedTestVectorKeyring(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput input)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> output = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _out22;
      _out22 = KeysVectorOperations_Compile.__default.CreateWappedTestVectorKeyring((this).config, input);
      output = _out22;
      return output;
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> GetKeyDescription(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionInput input) {
      return KeysVectorOperations_Compile.__default.GetKeyDescription((this).config, input);
    }
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> SerializeKeyDescription(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionInput input) {
      return KeysVectorOperations_Compile.__default.SerializeKeyDescription((this).config, input);
    }
    public KeysVectorOperations_Compile._IConfig _config {get; set;}
    public KeysVectorOperations_Compile._IConfig config { get {
      return this._config;
    } }
  }

  public partial class __default {
    public static software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyVectorsConfig DefaultKeyVectorsConfig() {
      return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyVectorsConfig.create(Dafny.Sequence<char>.FromString(""));
    }
    public static Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> KeyVectors(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyVectorsConfig config)
    {
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> res = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      Dafny.ISequence<byte> _341_keysManifestBv;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _342_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out23;
      _out23 = FileIO_Compile.__default.ReadBytesFromFile((config).dtor_keyManifiestPath);
      _342_valueOrError0 = _out23;
      if (!(!((_342_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/KeyVectors/src/Index.dfy(26,23): " + _342_valueOrError0);}
      _341_keysManifestBv = (_342_valueOrError0).Extract();
      Dafny.ISequence<byte> _343_keysManifestBytes;
      _343_keysManifestBytes = JSONHelpers_Compile.__default.BvToBytes(_341_keysManifestBv);
      JSON_mValues_Compile._IJSON _344_keysManifestJSON;
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _345_valueOrError1 = Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default(JSON_mValues_Compile.JSON.Default());
      _345_valueOrError1 = Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(JSON_mAPI_Compile.__default.Deserialize(_343_keysManifestBytes), ((System.Func<JSON_mErrors_Compile._IDeserializationError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_346_e) => {
        return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException((_346_e)._ToString());
      })));
      if ((_345_valueOrError1).IsFailure()) {
        res = (_345_valueOrError1).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient>();
        return res;
      }
      _344_keysManifestJSON = (_345_valueOrError1).Extract();
      if (!((_344_keysManifestJSON).is_Object)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/KeyVectors/src/Index.dfy(32,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      JSON_mValues_Compile._IJSON _347_keysObject;
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _348_valueOrError2 = Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>>.Default(JSON_mValues_Compile.JSON.Default());
      _348_valueOrError2 = JSONHelpers_Compile.__default.Get(Dafny.Sequence<char>.FromString("keys"), (_344_keysManifestJSON).dtor_obj);
      if (!(!((_348_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/KeyVectors/src/Index.dfy(33,19): " + _348_valueOrError2);}
      _347_keysObject = (_348_valueOrError2).Extract();
      if (!((_347_keysObject).is_Object)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/KeyVectors/src/Index.dfy(34,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _349_maybeMpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out24;
      _out24 = software.amazon.cryptography.materialproviders.internaldafny.__default.MaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.__default.DefaultMaterialProvidersConfig());
      _349_maybeMpl = _out24;
      software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient _350_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _351_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      _351_valueOrError3 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.MaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(_349_maybeMpl, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_352_e) => {
        return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_AwsCryptographyMaterialProviders(_352_e);
      })));
      if ((_351_valueOrError3).IsFailure()) {
        res = (_351_valueOrError3).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient>();
        return res;
      }
      _350_mpl = (_351_valueOrError3).Extract();
      Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial> _353_keys;
      Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial>, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _354_valueOrError4 = Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial>, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.Default(Dafny.Map<Dafny.ISequence<char>, KeyMaterial_Compile._IKeyMaterial>.Empty);
      _354_valueOrError4 = Wrappers_Compile.Result<Dafny.IMap<Dafny.ISequence<char>,KeyMaterial_Compile._IKeyMaterial>, Dafny.ISequence<char>>.MapFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>(KeyMaterial_Compile.__default.BuildKeyMaterials(_350_mpl, (_347_keysObject).dtor_obj), ((System.Func<Dafny.ISequence<char>, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>)((_355_e) => {
        return software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error.create_KeyVectorException(_355_e);
      })));
      if ((_354_valueOrError4).IsFailure()) {
        res = (_354_valueOrError4).PropagateFailure<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient>();
        return res;
      }
      _353_keys = (_354_valueOrError4).Extract();
      KeysVectorOperations_Compile._IConfig _356_config;
      _356_config = KeysVectorOperations_Compile.Config.create(_353_keys);
      software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient _357_client;
      software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient _nw2 = new software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient();
      _nw2.__ctor(_356_config);
      _357_client = _nw2;
      res = Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.create_Success(_357_client);
      return res;
    }
  }
} // end of namespace software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny
namespace TestVectorsUtils_Compile {

  public interface _ISmallEncryptionContextVariation {
    bool is_Empty { get; }
    bool is_A { get; }
    bool is_AB { get; }
    bool is_BA { get; }
    _ISmallEncryptionContextVariation DowncastClone();
  }
  public abstract class SmallEncryptionContextVariation : _ISmallEncryptionContextVariation {
    public SmallEncryptionContextVariation() { }
    private static readonly TestVectorsUtils_Compile._ISmallEncryptionContextVariation theDefault = create_Empty();
    public static TestVectorsUtils_Compile._ISmallEncryptionContextVariation Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestVectorsUtils_Compile._ISmallEncryptionContextVariation> _TYPE = new Dafny.TypeDescriptor<TestVectorsUtils_Compile._ISmallEncryptionContextVariation>(TestVectorsUtils_Compile.SmallEncryptionContextVariation.Default());
    public static Dafny.TypeDescriptor<TestVectorsUtils_Compile._ISmallEncryptionContextVariation> _TypeDescriptor() {
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
      var oth = other as TestVectorsUtils_Compile.SmallEncryptionContextVariation_Empty;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorsUtils_Compile.SmallEncryptionContextVariation.Empty";
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
      var oth = other as TestVectorsUtils_Compile.SmallEncryptionContextVariation_A;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorsUtils_Compile.SmallEncryptionContextVariation.A";
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
      var oth = other as TestVectorsUtils_Compile.SmallEncryptionContextVariation_AB;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorsUtils_Compile.SmallEncryptionContextVariation.AB";
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
      var oth = other as TestVectorsUtils_Compile.SmallEncryptionContextVariation_BA;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorsUtils_Compile.SmallEncryptionContextVariation.BA";
      return s;
    }
  }

  public partial class __default {
    public static Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> GenerateInvalidEncryptionContext()
    {
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty;
      Dafny.ISequence<byte> _358_validUTF8char;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _359_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _359_valueOrError0 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("a"));
      if (!(!((_359_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(39,43): " + _359_valueOrError0);}
      _358_validUTF8char = (_359_valueOrError0).Extract();
      Dafny.ISequence<byte> _360_key;
      _360_key = Dafny.Sequence<byte>.FromElements();
      while ((new BigInteger((_360_key).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT)) {
        _360_key = Dafny.Sequence<byte>.Concat(_360_key, _358_validUTF8char);
      }
      encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_360_key, Dafny.Sequence<byte>.FromElements((byte)(0))));
      return encCtx;
    }
    public static Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> GenerateLargeValidEncryptionContext()
    {
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> r = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty;
      BigInteger _361_numMaxPairs;
      _361_numMaxPairs = new BigInteger(9361);
      Dafny.ISequence<byte> _362_val;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _363_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _363_valueOrError0 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("a"));
      if (!(!((_363_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(59,12): " + _363_valueOrError0);}
      _362_val = (_363_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _364_encCtx;
      _364_encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements();
      BigInteger _365_i;
      _365_i = BigInteger.Zero;
      while (((new BigInteger((_364_encCtx).Count)) < (_361_numMaxPairs)) && ((_365_i) < (new BigInteger(65536)))) {
        Dafny.ISequence<byte> _366_key;
        _366_key = StandardLibrary_mUInt_Compile.__default.UInt16ToSeq((ushort)(_365_i));
        if (UTF8.__default.ValidUTF8Seq(_366_key)) {
          _364_encCtx = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Update(_364_encCtx, _366_key, _362_val);
        }
        _365_i = (_365_i) + (BigInteger.One);
      }
      r = _364_encCtx;
      return r;
      return r;
    }
    public static Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> SmallEncryptionContext(TestVectorsUtils_Compile._ISmallEncryptionContextVariation v)
    {
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty;
      Dafny.ISequence<byte> _367_keyA;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _368_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _368_valueOrError0 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("keyA"));
      if (!(!((_368_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(86,13): " + _368_valueOrError0);}
      _367_keyA = (_368_valueOrError0).Extract();
      Dafny.ISequence<byte> _369_valA;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _370_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _370_valueOrError1 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("valA"));
      if (!(!((_370_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(87,13): " + _370_valueOrError1);}
      _369_valA = (_370_valueOrError1).Extract();
      Dafny.ISequence<byte> _371_keyB;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _372_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _372_valueOrError2 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("keyB"));
      if (!(!((_372_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(88,13): " + _372_valueOrError2);}
      _371_keyB = (_372_valueOrError2).Extract();
      Dafny.ISequence<byte> _373_valB;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _374_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _374_valueOrError3 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("valB"));
      if (!(!((_374_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(89,13): " + _374_valueOrError3);}
      _373_valB = (_374_valueOrError3).Extract();
      TestVectorsUtils_Compile._ISmallEncryptionContextVariation _source12 = v;
      if (_source12.is_Empty) {
        encryptionContext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements();
      } else if (_source12.is_A) {
        encryptionContext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_367_keyA, _369_valA));
      } else if (_source12.is_AB) {
        encryptionContext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_367_keyA, _369_valA), new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_371_keyB, _373_valB));
      } else {
        encryptionContext = Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.FromElements(new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_371_keyB, _373_valB), new Dafny.Pair<Dafny.ISequence<byte>, Dafny.ISequence<byte>>(_367_keyA, _369_valA));
      }
      return encryptionContext;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey GenerateMockEncryptedDataKey(Dafny.ISequence<char> keyProviderId, Dafny.ISequence<char> keyProviderInfo)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey edk = software.amazon.cryptography.materialproviders.internaldafny.types.EncryptedDataKey.Default();
      Dafny.ISequence<byte> _375_encodedkeyProviderId;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _376_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _376_valueOrError0 = UTF8.__default.Encode(keyProviderId);
      if (!(!((_376_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(109,29): " + _376_valueOrError0);}
      _375_encodedkeyProviderId = (_376_valueOrError0).Extract();
      Dafny.ISequence<byte> _377_encodedKeyProviderInfo;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _378_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _378_valueOrError1 = UTF8.__default.Encode(keyProviderInfo);
      if (!(!((_378_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(110,31): " + _378_valueOrError1);}
      _377_encodedKeyProviderInfo = (_378_valueOrError1).Extract();
      Dafny.ISequence<byte> _379_fakeCiphertext;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _380_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _380_valueOrError2 = UTF8.__default.Encode(Dafny.Sequence<char>.FromString("fakeCiphertext"));
      if (!(!((_380_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(111,23): " + _380_valueOrError2);}
      _379_fakeCiphertext = (_380_valueOrError2).Extract();
      edk = software.amazon.cryptography.materialproviders.internaldafny.types.EncryptedDataKey.create(_375_encodedkeyProviderId, _377_encodedKeyProviderInfo, _379_fakeCiphertext);
      return edk;
      return edk;
    }
    public static void NamespaceAndName(BigInteger n, out Dafny.ISequence<char> @namespace, out Dafny.ISequence<char> name)
    {
      @namespace = Dafny.Sequence<char>.Empty;
      name = Dafny.Sequence<char>.Empty;
      Dafny.ISequence<char> _381_s;
      _381_s = Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("child"), Dafny.Sequence<char>.FromElements((char)(((char)(n)) + ('0'))));
      @namespace = Dafny.Sequence<char>.Concat(_381_s, Dafny.Sequence<char>.FromString(" Namespace"));
      name = Dafny.Sequence<char>.Concat(_381_s, Dafny.Sequence<char>.FromString(" Name"));
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials GetEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient mpl, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId algorithmSuiteId, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials encryptionMaterials = default(software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials);
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _382_crypto;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _383_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out25;
      _out25 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _383_valueOrError0 = _out25;
      if (!(!((_383_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(139,15): " + _383_valueOrError0);}
      _382_crypto = (_383_valueOrError0).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _384_suite;
      _384_suite = AlgorithmSuites_Compile.__default.GetSuite(algorithmSuiteId);
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _385_signingKey = Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default();
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _386_verificationKey = Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default();
      if (((_384_suite).dtor_signature).is_ECDSA) {
        software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput _387_pair;
        Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _388_valueOrError1 = Wrappers_Compile.Result<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyOutput.Default());
        Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateECDSASignatureKeyOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _out26;
        _out26 = (_382_crypto).GenerateECDSASignatureKey(software.amazon.cryptography.primitives.internaldafny.types.GenerateECDSASignatureKeyInput.create((((_384_suite).dtor_signature).dtor_ECDSA).dtor_curve));
        _388_valueOrError1 = _out26;
        if (!(!((_388_valueOrError1).IsFailure()))) {
          throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(144,15): " + _388_valueOrError1);}
        _387_pair = (_388_valueOrError1).Extract();
        _385_signingKey = Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some((_387_pair).dtor_signingKey);
        _386_verificationKey = Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some((_387_pair).dtor_verificationKey);
      } else {
        _385_signingKey = Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None();
        _386_verificationKey = Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None();
      }
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _389_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _389_valueOrError2 = (mpl).InitializeEncryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeEncryptionMaterialsInput.create(algorithmSuiteId, encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(), _385_signingKey, _386_verificationKey));
      if (!(!((_389_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectorsUtils.dfy(157,24): " + _389_valueOrError2);}
      encryptionMaterials = (_389_valueOrError2).Extract();
      return encryptionMaterials;
    }
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
} // end of namespace TestVectorsUtils_Compile
namespace TestVectorConstants_Compile {

  public interface _IEncryptDecryptKeyrings {
    bool is_AwsKmsKeyring { get; }
    bool is_AwsKmsMultiKeyring { get; }
    bool is_AwsKmsMrkKeyring { get; }
    bool is_AwsKmsMrkMultiKeyring { get; }
    bool is_RawAesKeyring { get; }
    bool is_RawRsaKeyring { get; }
    _IEncryptDecryptKeyrings DowncastClone();
  }
  public abstract class EncryptDecryptKeyrings : _IEncryptDecryptKeyrings {
    public EncryptDecryptKeyrings() { }
    private static readonly TestVectorConstants_Compile._IEncryptDecryptKeyrings theDefault = create_AwsKmsKeyring();
    public static TestVectorConstants_Compile._IEncryptDecryptKeyrings Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestVectorConstants_Compile._IEncryptDecryptKeyrings> _TYPE = new Dafny.TypeDescriptor<TestVectorConstants_Compile._IEncryptDecryptKeyrings>(TestVectorConstants_Compile.EncryptDecryptKeyrings.Default());
    public static Dafny.TypeDescriptor<TestVectorConstants_Compile._IEncryptDecryptKeyrings> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEncryptDecryptKeyrings create_AwsKmsKeyring() {
      return new EncryptDecryptKeyrings_AwsKmsKeyring();
    }
    public static _IEncryptDecryptKeyrings create_AwsKmsMultiKeyring() {
      return new EncryptDecryptKeyrings_AwsKmsMultiKeyring();
    }
    public static _IEncryptDecryptKeyrings create_AwsKmsMrkKeyring() {
      return new EncryptDecryptKeyrings_AwsKmsMrkKeyring();
    }
    public static _IEncryptDecryptKeyrings create_AwsKmsMrkMultiKeyring() {
      return new EncryptDecryptKeyrings_AwsKmsMrkMultiKeyring();
    }
    public static _IEncryptDecryptKeyrings create_RawAesKeyring() {
      return new EncryptDecryptKeyrings_RawAesKeyring();
    }
    public static _IEncryptDecryptKeyrings create_RawRsaKeyring() {
      return new EncryptDecryptKeyrings_RawRsaKeyring();
    }
    public bool is_AwsKmsKeyring { get { return this is EncryptDecryptKeyrings_AwsKmsKeyring; } }
    public bool is_AwsKmsMultiKeyring { get { return this is EncryptDecryptKeyrings_AwsKmsMultiKeyring; } }
    public bool is_AwsKmsMrkKeyring { get { return this is EncryptDecryptKeyrings_AwsKmsMrkKeyring; } }
    public bool is_AwsKmsMrkMultiKeyring { get { return this is EncryptDecryptKeyrings_AwsKmsMrkMultiKeyring; } }
    public bool is_RawAesKeyring { get { return this is EncryptDecryptKeyrings_RawAesKeyring; } }
    public bool is_RawRsaKeyring { get { return this is EncryptDecryptKeyrings_RawRsaKeyring; } }
    public static System.Collections.Generic.IEnumerable<_IEncryptDecryptKeyrings> AllSingletonConstructors {
      get {
        yield return EncryptDecryptKeyrings.create_AwsKmsKeyring();
        yield return EncryptDecryptKeyrings.create_AwsKmsMultiKeyring();
        yield return EncryptDecryptKeyrings.create_AwsKmsMrkKeyring();
        yield return EncryptDecryptKeyrings.create_AwsKmsMrkMultiKeyring();
        yield return EncryptDecryptKeyrings.create_RawAesKeyring();
        yield return EncryptDecryptKeyrings.create_RawRsaKeyring();
      }
    }
    public abstract _IEncryptDecryptKeyrings DowncastClone();
  }
  public class EncryptDecryptKeyrings_AwsKmsKeyring : EncryptDecryptKeyrings {
    public EncryptDecryptKeyrings_AwsKmsKeyring() {
    }
    public override _IEncryptDecryptKeyrings DowncastClone() {
      if (this is _IEncryptDecryptKeyrings dt) { return dt; }
      return new EncryptDecryptKeyrings_AwsKmsKeyring();
    }
    public override bool Equals(object other) {
      var oth = other as TestVectorConstants_Compile.EncryptDecryptKeyrings_AwsKmsKeyring;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorConstants_Compile.EncryptDecryptKeyrings.AwsKmsKeyring";
      return s;
    }
  }
  public class EncryptDecryptKeyrings_AwsKmsMultiKeyring : EncryptDecryptKeyrings {
    public EncryptDecryptKeyrings_AwsKmsMultiKeyring() {
    }
    public override _IEncryptDecryptKeyrings DowncastClone() {
      if (this is _IEncryptDecryptKeyrings dt) { return dt; }
      return new EncryptDecryptKeyrings_AwsKmsMultiKeyring();
    }
    public override bool Equals(object other) {
      var oth = other as TestVectorConstants_Compile.EncryptDecryptKeyrings_AwsKmsMultiKeyring;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorConstants_Compile.EncryptDecryptKeyrings.AwsKmsMultiKeyring";
      return s;
    }
  }
  public class EncryptDecryptKeyrings_AwsKmsMrkKeyring : EncryptDecryptKeyrings {
    public EncryptDecryptKeyrings_AwsKmsMrkKeyring() {
    }
    public override _IEncryptDecryptKeyrings DowncastClone() {
      if (this is _IEncryptDecryptKeyrings dt) { return dt; }
      return new EncryptDecryptKeyrings_AwsKmsMrkKeyring();
    }
    public override bool Equals(object other) {
      var oth = other as TestVectorConstants_Compile.EncryptDecryptKeyrings_AwsKmsMrkKeyring;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorConstants_Compile.EncryptDecryptKeyrings.AwsKmsMrkKeyring";
      return s;
    }
  }
  public class EncryptDecryptKeyrings_AwsKmsMrkMultiKeyring : EncryptDecryptKeyrings {
    public EncryptDecryptKeyrings_AwsKmsMrkMultiKeyring() {
    }
    public override _IEncryptDecryptKeyrings DowncastClone() {
      if (this is _IEncryptDecryptKeyrings dt) { return dt; }
      return new EncryptDecryptKeyrings_AwsKmsMrkMultiKeyring();
    }
    public override bool Equals(object other) {
      var oth = other as TestVectorConstants_Compile.EncryptDecryptKeyrings_AwsKmsMrkMultiKeyring;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorConstants_Compile.EncryptDecryptKeyrings.AwsKmsMrkMultiKeyring";
      return s;
    }
  }
  public class EncryptDecryptKeyrings_RawAesKeyring : EncryptDecryptKeyrings {
    public EncryptDecryptKeyrings_RawAesKeyring() {
    }
    public override _IEncryptDecryptKeyrings DowncastClone() {
      if (this is _IEncryptDecryptKeyrings dt) { return dt; }
      return new EncryptDecryptKeyrings_RawAesKeyring();
    }
    public override bool Equals(object other) {
      var oth = other as TestVectorConstants_Compile.EncryptDecryptKeyrings_RawAesKeyring;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorConstants_Compile.EncryptDecryptKeyrings.RawAesKeyring";
      return s;
    }
  }
  public class EncryptDecryptKeyrings_RawRsaKeyring : EncryptDecryptKeyrings {
    public EncryptDecryptKeyrings_RawRsaKeyring() {
    }
    public override _IEncryptDecryptKeyrings DowncastClone() {
      if (this is _IEncryptDecryptKeyrings dt) { return dt; }
      return new EncryptDecryptKeyrings_RawRsaKeyring();
    }
    public override bool Equals(object other) {
      var oth = other as TestVectorConstants_Compile.EncryptDecryptKeyrings_RawRsaKeyring;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorConstants_Compile.EncryptDecryptKeyrings.RawRsaKeyring";
      return s;
    }
  }

  public partial class __default {
    public static Dafny.ISequence<TestVectorConstants_Compile._IEncryptDecryptKeyrings> AllEncryptDecryptKeyrings { get {
      return Dafny.Sequence<TestVectorConstants_Compile._IEncryptDecryptKeyrings>.FromElements(TestVectorConstants_Compile.EncryptDecryptKeyrings.create_AwsKmsKeyring(), TestVectorConstants_Compile.EncryptDecryptKeyrings.create_AwsKmsMultiKeyring(), TestVectorConstants_Compile.EncryptDecryptKeyrings.create_AwsKmsMrkKeyring(), TestVectorConstants_Compile.EncryptDecryptKeyrings.create_AwsKmsMrkMultiKeyring(), TestVectorConstants_Compile.EncryptDecryptKeyrings.create_RawAesKeyring(), TestVectorConstants_Compile.EncryptDecryptKeyrings.create_RawRsaKeyring());
    } }
    public static Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IESDKAlgorithmSuiteId> AllESDKAlgorithmSuiteIds { get {
      return Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IESDKAlgorithmSuiteId>.FromElements(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF(), software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF(), software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF(), software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256(), software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256(), software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256(), software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256(), software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384(), software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384(), software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY(), software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384());
    } }
    public static Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IDBEAlgorithmSuiteId> AllDBEAlgorithmSuiteIds { get {
      return Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IDBEAlgorithmSuiteId>.FromElements(software.amazon.cryptography.materialproviders.internaldafny.types.DBEAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__SYMSIG__HMAC__SHA384(), software.amazon.cryptography.materialproviders.internaldafny.types.DBEAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384__SYMSIG__HMAC__SHA384());
    } }
    public static Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId> AllAlgorithmSuiteIds { get {
      return Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId>.FromElements(software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__NO__KDF()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__NO__KDF()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__NO__KDF()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA256()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA256()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_DBE(software.amazon.cryptography.materialproviders.internaldafny.types.DBEAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__SYMSIG__HMAC__SHA384()), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteId.create_DBE(software.amazon.cryptography.materialproviders.internaldafny.types.DBEAlgorithmSuiteId.create_ALG__AES__256__GCM__HKDF__SHA512__COMMIT__KEY__ECDSA__P384__SYMSIG__HMAC__SHA384()));
    } }
    public static Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>>> AllAwsKMSKeys { get {
      return Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, Dafny.ISequence<char>>.create(Dafny.Sequence<char>.FromString("arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"), Dafny.Sequence<char>.FromString("us-west-2")));
    } }
  }
} // end of namespace TestVectorConstants_Compile
namespace KeyringExpectations_Compile {

  public interface _IMaterials {
    bool is_Materials { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials dtor_encryptionMaterials { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials dtor_decryptionMaterials { get; }
    _IMaterials DowncastClone();
  }
  public class Materials : _IMaterials {
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _encryptionMaterials;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _decryptionMaterials;
    public Materials(software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials encryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials decryptionMaterials) {
      this._encryptionMaterials = encryptionMaterials;
      this._decryptionMaterials = decryptionMaterials;
    }
    public _IMaterials DowncastClone() {
      if (this is _IMaterials dt) { return dt; }
      return new Materials(_encryptionMaterials, _decryptionMaterials);
    }
    public override bool Equals(object other) {
      var oth = other as KeyringExpectations_Compile.Materials;
      return oth != null && object.Equals(this._encryptionMaterials, oth._encryptionMaterials) && object.Equals(this._decryptionMaterials, oth._decryptionMaterials);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encryptionMaterials));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._decryptionMaterials));
      return (int) hash;
    }
    public override string ToString() {
      string s = "KeyringExpectations_Compile.Materials.Materials";
      s += "(";
      s += Dafny.Helpers.ToString(this._encryptionMaterials);
      s += ", ";
      s += Dafny.Helpers.ToString(this._decryptionMaterials);
      s += ")";
      return s;
    }
    private static readonly KeyringExpectations_Compile._IMaterials theDefault = create(software.amazon.cryptography.materialproviders.internaldafny.types.EncryptionMaterials.Default(), software.amazon.cryptography.materialproviders.internaldafny.types.DecryptionMaterials.Default());
    public static KeyringExpectations_Compile._IMaterials Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<KeyringExpectations_Compile._IMaterials> _TYPE = new Dafny.TypeDescriptor<KeyringExpectations_Compile._IMaterials>(KeyringExpectations_Compile.Materials.Default());
    public static Dafny.TypeDescriptor<KeyringExpectations_Compile._IMaterials> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMaterials create(software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials encryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials decryptionMaterials) {
      return new Materials(encryptionMaterials, decryptionMaterials);
    }
    public static _IMaterials create_Materials(software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials encryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials decryptionMaterials) {
      return create(encryptionMaterials, decryptionMaterials);
    }
    public bool is_Materials { get { return true; } }
    public software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials dtor_encryptionMaterials {
      get {
        return this._encryptionMaterials;
      }
    }
    public software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials dtor_decryptionMaterials {
      get {
        return this._decryptionMaterials;
      }
    }
  }

  public partial class __default {
    public static void ExpectAlgorithmSuiteKeyringSuccess(software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient mpl, software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring)
    {
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _390_encryptionContext;
      Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _out27;
      _out27 = TestVectorsUtils_Compile.__default.SmallEncryptionContext(TestVectorsUtils_Compile.SmallEncryptionContextVariation.create_A());
      _390_encryptionContext = _out27;
      BigInteger _hi0 = new BigInteger((TestVectorConstants_Compile.__default.AllAlgorithmSuiteIds).Count);
      for (BigInteger _391_i = BigInteger.Zero; _391_i < _hi0; _391_i++) {
        software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _392_algorithmSuiteId;
        _392_algorithmSuiteId = (TestVectorConstants_Compile.__default.AllAlgorithmSuiteIds).Select(_391_i);
        software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _393_encryptionMaterials;
        software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _out28;
        _out28 = TestVectorsUtils_Compile.__default.GetEncryptionMaterials(mpl, _392_algorithmSuiteId, _390_encryptionContext);
        _393_encryptionMaterials = _out28;
        KeyringExpectations_Compile._IMaterials _394___v0;
        KeyringExpectations_Compile._IMaterials _out29;
        _out29 = KeyringExpectations_Compile.__default.ExpectKeyringSuccess(mpl, keyring, _393_encryptionMaterials);
        _394___v0 = _out29;
      }
    }
    public static KeyringExpectations_Compile._IMaterials ExpectKeyringSuccess(software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient mpl, software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials encryptionMaterialsIn)
    {
      KeyringExpectations_Compile._IMaterials results = default(KeyringExpectations_Compile._IMaterials);
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n ExpectKeyringSuccess:\n")));
      Dafny.Helpers.Print((((encryptionMaterialsIn).dtor_algorithmSuite).dtor_id));
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _395_encryptionMaterials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials _out30;
      _out30 = KeyringExpectations_Compile.__default.ExpectOnEncryptSuccess(mpl, keyring, encryptionMaterialsIn);
      _395_encryptionMaterials = _out30;
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _396_decryptionMaterialsIn;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _397_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      _397_valueOrError0 = (mpl).InitializeDecryptionMaterials(software.amazon.cryptography.materialproviders.internaldafny.types.InitializeDecryptionMaterialsInput.create(((_395_encryptionMaterials).dtor_algorithmSuite).dtor_id, (_395_encryptionMaterials).dtor_encryptionContext, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements()));
      if (!(!((_397_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/KeyringExpectations.dfy(68,30): " + _397_valueOrError0);}
      _396_decryptionMaterialsIn = (_397_valueOrError0).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _398_decryptionMaterials;
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials _out31;
      _out31 = KeyringExpectations_Compile.__default.ExpectOnDecryptSuccess(mpl, keyring, _396_decryptionMaterialsIn, (_395_encryptionMaterials).dtor_encryptedDataKeys);
      _398_decryptionMaterials = _out31;
      if (!(object.Equals((_395_encryptionMaterials).dtor_plaintextDataKey, (_398_decryptionMaterials).dtor_plaintextDataKey))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/KeyringExpectations.dfy(85,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      results = KeyringExpectations_Compile.Materials.create(_395_encryptionMaterials, _398_decryptionMaterials);
      return results;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials ExpectOnEncryptSuccess(software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient mpl, software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials encryptionMaterialsIn)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials encryptionMaterials = default(software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials);
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput _399_encryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _400_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnEncryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out32;
      _out32 = (keyring).OnEncrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnEncryptInput.create(encryptionMaterialsIn));
      _400_valueOrError0 = _out32;
      if (!(!((_400_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/KeyringExpectations.dfy(110,31): " + _400_valueOrError0);}
      _399_encryptionMaterialsOut = (_400_valueOrError0).Extract();
      encryptionMaterials = (_399_encryptionMaterialsOut).dtor_materials;
      _System._ITuple0 _401___v1;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _402_valueOrError1 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _402_valueOrError1 = (mpl).ValidEncryptionMaterialsTransition(software.amazon.cryptography.materialproviders.internaldafny.types.ValidEncryptionMaterialsTransitionInput.create(encryptionMaterialsIn, encryptionMaterials));
      if (!(!((_402_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/KeyringExpectations.dfy(117,10): " + _402_valueOrError1);}
      _401___v1 = (_402_valueOrError1).Extract();
      _System._ITuple0 _403___v2;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _404_valueOrError2 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _404_valueOrError2 = (mpl).EncryptionMaterialsHasPlaintextDataKey(encryptionMaterials);
      if (!(!((_404_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/KeyringExpectations.dfy(125,10): " + _404_valueOrError2);}
      _403___v2 = (_404_valueOrError2).Extract();
      if (!((BigInteger.One) <= (new BigInteger((((_399_encryptionMaterialsOut).dtor_materials).dtor_encryptedDataKeys).Count)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/KeyringExpectations.dfy(128,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      return encryptionMaterials;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials ExpectOnDecryptSuccess(software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient mpl, software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring, software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials decryptionMaterialsIn, Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> encryptedDataKeys)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials decryptionMaterials = default(software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptionMaterials);
      software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput _405_decryptionMaterialsOut;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _406_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IOnDecryptOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out33;
      _out33 = (keyring).OnDecrypt(software.amazon.cryptography.materialproviders.internaldafny.types.OnDecryptInput.create(decryptionMaterialsIn, encryptedDataKeys));
      _406_valueOrError0 = _out33;
      if (!(!((_406_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/KeyringExpectations.dfy(152,31): " + _406_valueOrError0);}
      _405_decryptionMaterialsOut = (_406_valueOrError0).Extract();
      decryptionMaterials = (_405_decryptionMaterialsOut).dtor_materials;
      _System._ITuple0 _407___v3;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _408_valueOrError1 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _408_valueOrError1 = (mpl).ValidDecryptionMaterialsTransition(software.amazon.cryptography.materialproviders.internaldafny.types.ValidDecryptionMaterialsTransitionInput.create(decryptionMaterialsIn, decryptionMaterials));
      if (!(!((_408_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/KeyringExpectations.dfy(162,10): " + _408_valueOrError1);}
      _407___v3 = (_408_valueOrError1).Extract();
      _System._ITuple0 _409___v4;
      Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _410_valueOrError2 = Wrappers_Compile.Result<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.Default(_System.Tuple0.Default());
      _410_valueOrError2 = (mpl).DecryptionMaterialsWithPlaintextDataKey(decryptionMaterials);
      if (!(!((_410_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/KeyringExpectations.dfy(170,10): " + _410_valueOrError2);}
      _409___v4 = (_410_valueOrError2).Extract();
      return decryptionMaterials;
    }
  }
} // end of namespace KeyringExpectations_Compile
namespace CreateAwsKmsKeyrings_Compile {

  public partial class __default {
    public static Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> CreateAllAwsKmsKeyring(TestVectorConstants_Compile._IEncryptDecryptKeyrings input)
    {
      Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> allAwsKms = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Empty;
      allAwsKms = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements();
      BigInteger _hi1 = new BigInteger((TestVectorConstants_Compile.__default.AllAwsKMSKeys).Count);
      for (BigInteger _411_i = BigInteger.Zero; _411_i < _hi1; _411_i++) {
        _System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>> _let_tmp_rhs1 = (TestVectorConstants_Compile.__default.AllAwsKMSKeys).Select(_411_i);
        Dafny.ISequence<char> _412_kmsKeyId = _let_tmp_rhs1.dtor__0;
        Dafny.ISequence<char> _413_region = _let_tmp_rhs1.dtor__1;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _414_keyring;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out34;
        _out34 = CreateAwsKmsKeyrings_Compile.__default.CreateAwsKmsKeyring(_412_kmsKeyId, _413_region);
        _414_keyring = _out34;
        allAwsKms = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(allAwsKms, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_414_keyring));
      }
      return allAwsKms;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring CreateAwsKmsKeyring(Dafny.ISequence<char> kmsKeyId, Dafny.ISequence<char> region)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring = default(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring);
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n CreateAwsKmsKeyring: ")));
      Dafny.Helpers.Print((kmsKeyId));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(" ")));
      Dafny.Helpers.Print((region));
      software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient _415_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _416_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out35;
      _out35 = software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedDefaultMaterialProvidersConfig());
      _416_valueOrError0 = _out35;
      if (!(!((_416_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsKeyrings.dfy(53,12): " + _416_valueOrError0);}
      _415_mpl = (_416_valueOrError0).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier _417_clientSupplier;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _418_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out36;
      _out36 = (_415_mpl).CreateDefaultClientSupplier(software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultClientSupplierInput.create());
      _418_valueOrError1 = _out36;
      if (!(!((_418_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsKeyrings.dfy(55,23): " + _418_valueOrError1);}
      _417_clientSupplier = (_418_valueOrError1).Extract();
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _419_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _420_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out37;
      _out37 = (_417_clientSupplier).GetClient(software.amazon.cryptography.materialproviders.internaldafny.types.GetClientInput.create(region));
      _420_valueOrError2 = _out37;
      if (!(!((_420_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsKeyrings.dfy(56,18): " + _420_valueOrError2);}
      _419_kmsClient = (_420_valueOrError2).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _421_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out38;
      _out38 = (_415_mpl).CreateAwsKmsKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsKeyringInput.create(kmsKeyId, _419_kmsClient, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()));
      _421_valueOrError3 = _out38;
      if (!(!((_421_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsKeyrings.dfy(58,12): " + _421_valueOrError3);}
      keyring = (_421_valueOrError3).Extract();
      return keyring;
    }
  }
} // end of namespace CreateAwsKmsKeyrings_Compile
namespace CreateAwsKmsMultiKeyrings_Compile {

  public partial class __default {
    public static Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> CreateAllAwsKmsMultiKeyring(TestVectorConstants_Compile._IEncryptDecryptKeyrings input)
    {
      Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> allAwsKmsMrkMult = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Empty;
      allAwsKmsMrkMult = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements();
      BigInteger _hi2 = new BigInteger((TestVectorConstants_Compile.__default.AllAwsKMSKeys).Count);
      for (BigInteger _422_i = BigInteger.Zero; _422_i < _hi2; _422_i++) {
        _System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>> _let_tmp_rhs2 = (TestVectorConstants_Compile.__default.AllAwsKMSKeys).Select(_422_i);
        Dafny.ISequence<char> _423_kmsKeyId = _let_tmp_rhs2.dtor__0;
        Dafny.ISequence<char> _424___v0 = _let_tmp_rhs2.dtor__1;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _425_keyring;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out39;
        _out39 = CreateAwsKmsMultiKeyrings_Compile.__default.CreateAwsKmsMultiKeyring(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(_423_kmsKeyId), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None());
        _425_keyring = _out39;
        allAwsKmsMrkMult = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(allAwsKmsMrkMult, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_425_keyring));
      }
      return allAwsKmsMrkMult;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring CreateAwsKmsMultiKeyring(Wrappers_Compile._IOption<Dafny.ISequence<char>> kmsKeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> kmsKeyIds)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring = default(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring);
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n CreateAwsKmsMultiKeyring: ")));
      Dafny.Helpers.Print((kmsKeyId));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(" ")));
      Dafny.Helpers.Print((kmsKeyIds));
      software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient _426_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _427_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out40;
      _out40 = software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedDefaultMaterialProvidersConfig());
      _427_valueOrError0 = _out40;
      if (!(!((_427_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsMultiKeyrings.dfy(53,12): " + _427_valueOrError0);}
      _426_mpl = (_427_valueOrError0).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _428_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out41;
      _out41 = (_426_mpl).CreateAwsKmsMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMultiKeyringInput.create(kmsKeyId, kmsKeyIds, Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()));
      _428_valueOrError1 = _out41;
      if (!(!((_428_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsMultiKeyrings.dfy(55,12): " + _428_valueOrError1);}
      keyring = (_428_valueOrError1).Extract();
      return keyring;
    }
  }
} // end of namespace CreateAwsKmsMultiKeyrings_Compile
namespace CreateAwsKmsMrkKeyrings_Compile {

  public partial class __default {
    public static Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> CreateAllAwsKmsMrkKeyring(TestVectorConstants_Compile._IEncryptDecryptKeyrings input)
    {
      Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> allAwsKmsMrk = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Empty;
      allAwsKmsMrk = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements();
      BigInteger _hi3 = new BigInteger((TestVectorConstants_Compile.__default.AllAwsKMSKeys).Count);
      for (BigInteger _429_i = BigInteger.Zero; _429_i < _hi3; _429_i++) {
        _System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>> _let_tmp_rhs3 = (TestVectorConstants_Compile.__default.AllAwsKMSKeys).Select(_429_i);
        Dafny.ISequence<char> _430_kmsKeyId = _let_tmp_rhs3.dtor__0;
        Dafny.ISequence<char> _431_region = _let_tmp_rhs3.dtor__1;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _432_keyring;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out42;
        _out42 = CreateAwsKmsMrkKeyrings_Compile.__default.CreateAwsKmsMrkKeyring(_430_kmsKeyId, _431_region);
        _432_keyring = _out42;
        allAwsKmsMrk = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(allAwsKmsMrk, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_432_keyring));
      }
      return allAwsKmsMrk;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring CreateAwsKmsMrkKeyring(Dafny.ISequence<char> kmsKeyId, Dafny.ISequence<char> region)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring = default(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring);
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n CreateAwsKmsMrkKeyring: ")));
      Dafny.Helpers.Print((kmsKeyId));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(" ")));
      Dafny.Helpers.Print((region));
      software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient _433_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _434_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out43;
      _out43 = software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedDefaultMaterialProvidersConfig());
      _434_valueOrError0 = _out43;
      if (!(!((_434_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsMrkKeyrings.dfy(53,12): " + _434_valueOrError0);}
      _433_mpl = (_434_valueOrError0).Extract();
      software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier _435_clientSupplier;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _436_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out44;
      _out44 = (_433_mpl).CreateDefaultClientSupplier(software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultClientSupplierInput.create());
      _436_valueOrError1 = _out44;
      if (!(!((_436_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsMrkKeyrings.dfy(55,23): " + _436_valueOrError1);}
      _435_clientSupplier = (_436_valueOrError1).Extract();
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _437_kmsClient;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _438_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out45;
      _out45 = (_435_clientSupplier).GetClient(software.amazon.cryptography.materialproviders.internaldafny.types.GetClientInput.create(region));
      _438_valueOrError2 = _out45;
      if (!(!((_438_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsMrkKeyrings.dfy(56,18): " + _438_valueOrError2);}
      _437_kmsClient = (_438_valueOrError2).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _439_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out46;
      _out46 = (_433_mpl).CreateAwsKmsMrkKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkKeyringInput.create(kmsKeyId, _437_kmsClient, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()));
      _439_valueOrError3 = _out46;
      if (!(!((_439_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsMrkKeyrings.dfy(58,12): " + _439_valueOrError3);}
      keyring = (_439_valueOrError3).Extract();
      return keyring;
    }
  }
} // end of namespace CreateAwsKmsMrkKeyrings_Compile
namespace CreateAwsKmsMrkMultiKeyrings_Compile {

  public partial class __default {
    public static Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> CreateAllAwsKmsMrkMultiKeyring(TestVectorConstants_Compile._IEncryptDecryptKeyrings input)
    {
      Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> allAwsKmsMrkMult = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Empty;
      allAwsKmsMrkMult = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements();
      BigInteger _hi4 = new BigInteger((TestVectorConstants_Compile.__default.AllAwsKMSKeys).Count);
      for (BigInteger _440_i = BigInteger.Zero; _440_i < _hi4; _440_i++) {
        _System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>> _let_tmp_rhs4 = (TestVectorConstants_Compile.__default.AllAwsKMSKeys).Select(_440_i);
        Dafny.ISequence<char> _441_kmsKeyId = _let_tmp_rhs4.dtor__0;
        Dafny.ISequence<char> _442___v0 = _let_tmp_rhs4.dtor__1;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _443_keyring;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out47;
        _out47 = CreateAwsKmsMrkMultiKeyrings_Compile.__default.CreateAwsKmsMrkMultiKeyring(Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(_441_kmsKeyId), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None());
        _443_keyring = _out47;
        allAwsKmsMrkMult = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(allAwsKmsMrkMult, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_443_keyring));
      }
      return allAwsKmsMrkMult;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring CreateAwsKmsMrkMultiKeyring(Wrappers_Compile._IOption<Dafny.ISequence<char>> kmsKeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> kmsKeyIds)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring = default(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring);
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n CreateAwsKmsMrkMultiKeyring: ")));
      Dafny.Helpers.Print((kmsKeyId));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(" ")));
      Dafny.Helpers.Print((kmsKeyIds));
      software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient _444_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _445_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out48;
      _out48 = software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedDefaultMaterialProvidersConfig());
      _445_valueOrError0 = _out48;
      if (!(!((_445_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsMrkMultiKeyrings.dfy(53,12): " + _445_valueOrError0);}
      _444_mpl = (_445_valueOrError0).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _446_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out49;
      _out49 = (_444_mpl).CreateAwsKmsMrkMultiKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateAwsKmsMrkMultiKeyringInput.create(kmsKeyId, kmsKeyIds, Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types.IClientSupplier>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()));
      _446_valueOrError1 = _out49;
      if (!(!((_446_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateAwsKmsMrkMultiKeyrings.dfy(55,12): " + _446_valueOrError1);}
      keyring = (_446_valueOrError1).Extract();
      return keyring;
    }
  }
} // end of namespace CreateAwsKmsMrkMultiKeyrings_Compile
namespace CreateRawAesKeyrings_Compile {

  public partial class __default {
    public static Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> CreateAllRawAesKeyring(TestVectorConstants_Compile._IEncryptDecryptKeyrings input)
    {
      Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> allAES = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Empty;
      allAES = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements();
      Dafny.ISet<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg> _447_AllAesWrappingAlgs;
      _447_AllAesWrappingAlgs = ((System.Func<Dafny.ISet<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg>>)(() => {
        var _coll3 = new System.Collections.Generic.List<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg>();
        foreach (software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg _compr_3 in software.amazon.cryptography.materialproviders.internaldafny.types.AesWrappingAlg.AllSingletonConstructors) {
          software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg _448_w = (software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg)_compr_3;
          if (true) {
            _coll3.Add(_448_w);
          }
        }
        return Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg>.FromCollection(_coll3);
      }))();
      while (!(_447_AllAesWrappingAlgs).Equals(Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg>.FromElements())) {
        software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg _449_wrappingAlg;
        foreach (software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg _assign_such_that_0 in (_447_AllAesWrappingAlgs).Elements) {
          _449_wrappingAlg = (software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg)_assign_such_that_0;
          if ((_447_AllAesWrappingAlgs).Contains(_449_wrappingAlg)) {
            goto after__ASSIGN_SUCH_THAT_0;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 40)");
      after__ASSIGN_SUCH_THAT_0: ;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _450_keyring;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out50;
        _out50 = CreateRawAesKeyrings_Compile.__default.CreateRawAesKeyring(_449_wrappingAlg);
        _450_keyring = _out50;
        allAES = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(allAES, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_450_keyring));
        _447_AllAesWrappingAlgs = Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg>.Difference(_447_AllAesWrappingAlgs, Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg>.FromElements(_449_wrappingAlg));
      }
      return allAES;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg wrappingAlg)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring = default(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring);
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n CreateRawAesKeyring: ")));
      Dafny.Helpers.Print((wrappingAlg));
      software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient _451_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _452_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out51;
      _out51 = software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedDefaultMaterialProvidersConfig());
      _452_valueOrError0 = _out51;
      if (!(!((_452_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateRawAesKeyrings.dfy(59,12): " + _452_valueOrError0);}
      _451_mpl = (_452_valueOrError0).Extract();
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _453_crypto;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _454_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out52;
      _out52 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _454_valueOrError1 = _out52;
      if (!(!((_454_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateRawAesKeyrings.dfy(60,15): " + _454_valueOrError1);}
      _453_crypto = (_454_valueOrError1).Extract();
      int _455_length;
      _455_length = ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IAesWrappingAlg, int>)((_source13) => {
        if (_source13.is_ALG__AES128__GCM__IV12__TAG16) {
          return 16;
        } else if (_source13.is_ALG__AES192__GCM__IV12__TAG16) {
          return 24;
        } else {
          return 32;
        }
      }))(wrappingAlg);
      Dafny.ISequence<byte> _456_wrappingKey;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _457_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, software.amazon.cryptography.primitives.internaldafny.types._IError> _out53;
      _out53 = (_453_crypto).GenerateRandomBytes(software.amazon.cryptography.primitives.internaldafny.types.GenerateRandomBytesInput.create(_455_length));
      _457_valueOrError2 = _out53;
      if (!(!((_457_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateRawAesKeyrings.dfy(67,20): " + _457_valueOrError2);}
      _456_wrappingKey = (_457_valueOrError2).Extract();
      Dafny.ISequence<char> _458_namespace;
      Dafny.ISequence<char> _459_name;
      Dafny.ISequence<char> _out54;
      Dafny.ISequence<char> _out55;
      TestVectorsUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out54, out _out55);
      _458_namespace = _out54;
      _459_name = _out55;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _460_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out56;
      _out56 = (_451_mpl).CreateRawAesKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawAesKeyringInput.create(_458_namespace, _459_name, _456_wrappingKey, wrappingAlg));
      _460_valueOrError3 = _out56;
      if (!(!((_460_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateRawAesKeyrings.dfy(74,12): " + _460_valueOrError3);}
      keyring = (_460_valueOrError3).Extract();
      return keyring;
    }
  }
} // end of namespace CreateRawAesKeyrings_Compile
namespace CreateRawRsaKeyrings_Compile {

  public partial class __default {
    public static Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> CreateAllRawRsaKeyring(TestVectorConstants_Compile._IEncryptDecryptKeyrings input)
    {
      Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> allRSA = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Empty;
      allRSA = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements();
      Dafny.ISet<software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme> _461_AllPaddingSchemes;
      _461_AllPaddingSchemes = ((System.Func<Dafny.ISet<software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme>>)(() => {
        var _coll4 = new System.Collections.Generic.List<software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme>();
        foreach (software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme _compr_4 in software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.AllSingletonConstructors) {
          software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme _462_w = (software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme)_compr_4;
          if (true) {
            _coll4.Add(_462_w);
          }
        }
        return Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme>.FromCollection(_coll4);
      }))();
      while (!(_461_AllPaddingSchemes).Equals(Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme>.FromElements())) {
        software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme _463_paddingScheme;
        foreach (software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme _assign_such_that_1 in (_461_AllPaddingSchemes).Elements) {
          _463_paddingScheme = (software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme)_assign_such_that_1;
          if ((_461_AllPaddingSchemes).Contains(_463_paddingScheme)) {
            goto after__ASSIGN_SUCH_THAT_1;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 40)");
      after__ASSIGN_SUCH_THAT_1: ;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _464_keyring;
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _out57;
        _out57 = CreateRawRsaKeyrings_Compile.__default.CreateRawRsaKeyring(_463_paddingScheme);
        _464_keyring = _out57;
        allRSA = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(allRSA, Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements(_464_keyring));
        _461_AllPaddingSchemes = Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme>.Difference(_461_AllPaddingSchemes, Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme>.FromElements(_463_paddingScheme));
      }
      return allRSA;
    }
    public static software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring CreateRawRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme paddingScheme)
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring keyring = default(software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring);
      software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient _465_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _466_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out58;
      _out58 = software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedDefaultMaterialProvidersConfig());
      _466_valueOrError0 = _out58;
      if (!(!((_466_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateRawRsaKeyrings.dfy(56,12): " + _466_valueOrError0);}
      _465_mpl = (_466_valueOrError0).Extract();
      software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient _467_crypto;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _468_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.AtomicPrimitivesClient, software.amazon.cryptography.primitives.internaldafny.types._IError> _out59;
      _out59 = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(software.amazon.cryptography.primitives.internaldafny.__default.DefaultCryptoConfig());
      _468_valueOrError1 = _out59;
      if (!(!((_468_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateRawRsaKeyrings.dfy(57,15): " + _468_valueOrError1);}
      _467_crypto = (_468_valueOrError1).Extract();
      software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput _469_keys;
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _470_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.primitives.internaldafny.types._IGenerateRSAKeyPairOutput, software.amazon.cryptography.primitives.internaldafny.types._IError> _out60;
      _out60 = (_467_crypto).GenerateRSAKeyPair(software.amazon.cryptography.primitives.internaldafny.types.GenerateRSAKeyPairInput.create(2048));
      _470_valueOrError2 = _out60;
      if (!(!((_470_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateRawRsaKeyrings.dfy(59,13): " + _470_valueOrError2);}
      _469_keys = (_470_valueOrError2).Extract();
      Dafny.ISequence<char> _471_namespace;
      Dafny.ISequence<char> _472_name;
      Dafny.ISequence<char> _out61;
      Dafny.ISequence<char> _out62;
      TestVectorsUtils_Compile.__default.NamespaceAndName(BigInteger.Zero, out _out61, out _out62);
      _471_namespace = _out61;
      _472_name = _out62;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _473_valueOrError3 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out63;
      _out63 = (_465_mpl).CreateRawRsaKeyring(software.amazon.cryptography.materialproviders.internaldafny.types.CreateRawRsaKeyringInput.create(_471_namespace, _472_name, paddingScheme, Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_469_keys).dtor_publicKey).dtor_pem), Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(((_469_keys).dtor_privateKey).dtor_pem)));
      _473_valueOrError3 = _out63;
      if (!(!((_473_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CreateKeyrings/CreateRawRsaKeyrings.dfy(66,12): " + _473_valueOrError3);}
      keyring = (_473_valueOrError3).Extract();
      return keyring;
    }
  }
} // end of namespace CreateRawRsaKeyrings_Compile
namespace CreateKeyrings_Compile {

  public partial class __default {
    public static Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> CreateAllEncryptDecryptKeyrings()
    {
      Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> all = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Empty;
      all = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.FromElements();
      BigInteger _hi5 = new BigInteger((TestVectorConstants_Compile.__default.AllEncryptDecryptKeyrings).Count);
      for (BigInteger _474_i = BigInteger.Zero; _474_i < _hi5; _474_i++) {
        TestVectorConstants_Compile._IEncryptDecryptKeyrings _475_keyringType;
        _475_keyringType = (TestVectorConstants_Compile.__default.AllEncryptDecryptKeyrings).Select(_474_i);
        TestVectorConstants_Compile._IEncryptDecryptKeyrings _source14 = _475_keyringType;
        if (_source14.is_AwsKmsKeyring) {
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _476_allAwsKms;
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _out64;
          _out64 = CreateAwsKmsKeyrings_Compile.__default.CreateAllAwsKmsKeyring(_475_keyringType);
          _476_allAwsKms = _out64;
          all = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(all, _476_allAwsKms);
        } else if (_source14.is_AwsKmsMultiKeyring) {
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _477_allAwsKms;
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _out65;
          _out65 = CreateAwsKmsMultiKeyrings_Compile.__default.CreateAllAwsKmsMultiKeyring(_475_keyringType);
          _477_allAwsKms = _out65;
          all = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(all, _477_allAwsKms);
        } else if (_source14.is_AwsKmsMrkKeyring) {
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _478_allAwsKmsMrk;
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _out66;
          _out66 = CreateAwsKmsMrkKeyrings_Compile.__default.CreateAllAwsKmsMrkKeyring(_475_keyringType);
          _478_allAwsKmsMrk = _out66;
          all = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(all, _478_allAwsKmsMrk);
        } else if (_source14.is_AwsKmsMrkMultiKeyring) {
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _479_allAwsKmsMrkMult;
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _out67;
          _out67 = CreateAwsKmsMrkMultiKeyrings_Compile.__default.CreateAllAwsKmsMrkMultiKeyring(_475_keyringType);
          _479_allAwsKmsMrkMult = _out67;
          all = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(all, _479_allAwsKmsMrkMult);
        } else if (_source14.is_RawAesKeyring) {
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _480_allRSA;
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _out68;
          _out68 = CreateRawAesKeyrings_Compile.__default.CreateAllRawAesKeyring(_475_keyringType);
          _480_allRSA = _out68;
          all = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(all, _480_allRSA);
        } else {
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _481_allAES;
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _out69;
          _out69 = CreateRawRsaKeyrings_Compile.__default.CreateAllRawRsaKeyring(_475_keyringType);
          _481_allAES = _out69;
          all = Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring>.Concat(all, _481_allAES);
        }
      }
      return all;
    }
  }
} // end of namespace CreateKeyrings_Compile
namespace TestVectors_Compile {

  public interface _IEncryptTest {
    bool is_EncryptTest { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput dtor_input { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager dtor_cmm { get; }
    TestVectors_Compile._IEncryptTestVector dtor_vector { get; }
    _IEncryptTest DowncastClone();
  }
  public class EncryptTest : _IEncryptTest {
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput _input;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager _cmm;
    public readonly TestVectors_Compile._IEncryptTestVector _vector;
    public EncryptTest(software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput input, software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager cmm, TestVectors_Compile._IEncryptTestVector vector) {
      this._input = input;
      this._cmm = cmm;
      this._vector = vector;
    }
    public _IEncryptTest DowncastClone() {
      if (this is _IEncryptTest dt) { return dt; }
      return new EncryptTest(_input, _cmm, _vector);
    }
    public override bool Equals(object other) {
      var oth = other as TestVectors_Compile.EncryptTest;
      return oth != null && object.Equals(this._input, oth._input) && this._cmm == oth._cmm && object.Equals(this._vector, oth._vector);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._input));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cmm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._vector));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectors_Compile.EncryptTest.EncryptTest";
      s += "(";
      s += Dafny.Helpers.ToString(this._input);
      s += ", ";
      s += Dafny.Helpers.ToString(this._cmm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._vector);
      s += ")";
      return s;
    }
    private static readonly TestVectors_Compile._IEncryptTest theDefault = create(software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsInput.Default(), default(software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager), TestVectors_Compile.EncryptTestVector.Default());
    public static TestVectors_Compile._IEncryptTest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestVectors_Compile._IEncryptTest> _TYPE = new Dafny.TypeDescriptor<TestVectors_Compile._IEncryptTest>(TestVectors_Compile.EncryptTest.Default());
    public static Dafny.TypeDescriptor<TestVectors_Compile._IEncryptTest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEncryptTest create(software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput input, software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager cmm, TestVectors_Compile._IEncryptTestVector vector) {
      return new EncryptTest(input, cmm, vector);
    }
    public static _IEncryptTest create_EncryptTest(software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput input, software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager cmm, TestVectors_Compile._IEncryptTestVector vector) {
      return create(input, cmm, vector);
    }
    public bool is_EncryptTest { get { return true; } }
    public software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput dtor_input {
      get {
        return this._input;
      }
    }
    public software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager dtor_cmm {
      get {
        return this._cmm;
      }
    }
    public TestVectors_Compile._IEncryptTestVector dtor_vector {
      get {
        return this._vector;
      }
    }
  }

  public interface _IDecryptTest {
    bool is_DecryptTest { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsInput dtor_input { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager dtor_cmm { get; }
    TestVectors_Compile._IDecryptTestVector dtor_vector { get; }
    _IDecryptTest DowncastClone();
  }
  public class DecryptTest : _IDecryptTest {
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsInput _input;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager _cmm;
    public readonly TestVectors_Compile._IDecryptTestVector _vector;
    public DecryptTest(software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsInput input, software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager cmm, TestVectors_Compile._IDecryptTestVector vector) {
      this._input = input;
      this._cmm = cmm;
      this._vector = vector;
    }
    public _IDecryptTest DowncastClone() {
      if (this is _IDecryptTest dt) { return dt; }
      return new DecryptTest(_input, _cmm, _vector);
    }
    public override bool Equals(object other) {
      var oth = other as TestVectors_Compile.DecryptTest;
      return oth != null && object.Equals(this._input, oth._input) && this._cmm == oth._cmm && object.Equals(this._vector, oth._vector);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._input));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cmm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._vector));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectors_Compile.DecryptTest.DecryptTest";
      s += "(";
      s += Dafny.Helpers.ToString(this._input);
      s += ", ";
      s += Dafny.Helpers.ToString(this._cmm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._vector);
      s += ")";
      return s;
    }
    private static readonly TestVectors_Compile._IDecryptTest theDefault = create(software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsInput.Default(), default(software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager), TestVectors_Compile.DecryptTestVector.Default());
    public static TestVectors_Compile._IDecryptTest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestVectors_Compile._IDecryptTest> _TYPE = new Dafny.TypeDescriptor<TestVectors_Compile._IDecryptTest>(TestVectors_Compile.DecryptTest.Default());
    public static Dafny.TypeDescriptor<TestVectors_Compile._IDecryptTest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDecryptTest create(software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsInput input, software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager cmm, TestVectors_Compile._IDecryptTestVector vector) {
      return new DecryptTest(input, cmm, vector);
    }
    public static _IDecryptTest create_DecryptTest(software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsInput input, software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager cmm, TestVectors_Compile._IDecryptTestVector vector) {
      return create(input, cmm, vector);
    }
    public bool is_DecryptTest { get { return true; } }
    public software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsInput dtor_input {
      get {
        return this._input;
      }
    }
    public software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager dtor_cmm {
      get {
        return this._cmm;
      }
    }
    public TestVectors_Compile._IDecryptTestVector dtor_vector {
      get {
        return this._vector;
      }
    }
  }

  public interface _IEncryptTestVector {
    bool is_PositiveEncryptKeyringVector { get; }
    bool is_NegativeEncryptKeyringVector { get; }
    Dafny.ISequence<char> dtor_name { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_description { get; }
    Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy dtor_commitmentPolicy { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo dtor_algorithmSuite { get; }
    Wrappers_Compile._IOption<long> dtor_maxPlaintextLength { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> dtor_requiredEncryptionContextKeys { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_encryptDescription { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_decryptDescription { get; }
    Dafny.ISequence<char> dtor_errorDescription { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_keyDescription { get; }
    _IEncryptTestVector DowncastClone();
  }
  public abstract class EncryptTestVector : _IEncryptTestVector {
    public EncryptTestVector() { }
    private static readonly TestVectors_Compile._IEncryptTestVector theDefault = create_PositiveEncryptKeyringVector(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, software.amazon.cryptography.materialproviders.internaldafny.types.CommitmentPolicy.Default(), software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteInfo.Default(), Wrappers_Compile.Option<long>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<byte>>>.Default(), software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.Default(), software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.Default());
    public static TestVectors_Compile._IEncryptTestVector Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestVectors_Compile._IEncryptTestVector> _TYPE = new Dafny.TypeDescriptor<TestVectors_Compile._IEncryptTestVector>(TestVectors_Compile.EncryptTestVector.Default());
    public static Dafny.TypeDescriptor<TestVectors_Compile._IEncryptTestVector> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEncryptTestVector create_PositiveEncryptKeyringVector(Dafny.ISequence<char> name, Wrappers_Compile._IOption<Dafny.ISequence<char>> description, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy commitmentPolicy, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo algorithmSuite, Wrappers_Compile._IOption<long> maxPlaintextLength, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> requiredEncryptionContextKeys, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription encryptDescription, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription decryptDescription) {
      return new EncryptTestVector_PositiveEncryptKeyringVector(name, description, encryptionContext, commitmentPolicy, algorithmSuite, maxPlaintextLength, requiredEncryptionContextKeys, encryptDescription, decryptDescription);
    }
    public static _IEncryptTestVector create_NegativeEncryptKeyringVector(Dafny.ISequence<char> name, Wrappers_Compile._IOption<Dafny.ISequence<char>> description, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy commitmentPolicy, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo algorithmSuite, Wrappers_Compile._IOption<long> maxPlaintextLength, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> requiredEncryptionContextKeys, Dafny.ISequence<char> errorDescription, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription) {
      return new EncryptTestVector_NegativeEncryptKeyringVector(name, description, encryptionContext, commitmentPolicy, algorithmSuite, maxPlaintextLength, requiredEncryptionContextKeys, errorDescription, keyDescription);
    }
    public bool is_PositiveEncryptKeyringVector { get { return this is EncryptTestVector_PositiveEncryptKeyringVector; } }
    public bool is_NegativeEncryptKeyringVector { get { return this is EncryptTestVector_NegativeEncryptKeyringVector; } }
    public Dafny.ISequence<char> dtor_name {
      get {
        var d = this;
        if (d is EncryptTestVector_PositiveEncryptKeyringVector) { return ((EncryptTestVector_PositiveEncryptKeyringVector)d)._name; }
        return ((EncryptTestVector_NegativeEncryptKeyringVector)d)._name;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_description {
      get {
        var d = this;
        if (d is EncryptTestVector_PositiveEncryptKeyringVector) { return ((EncryptTestVector_PositiveEncryptKeyringVector)d)._description; }
        return ((EncryptTestVector_NegativeEncryptKeyringVector)d)._description;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        var d = this;
        if (d is EncryptTestVector_PositiveEncryptKeyringVector) { return ((EncryptTestVector_PositiveEncryptKeyringVector)d)._encryptionContext; }
        return ((EncryptTestVector_NegativeEncryptKeyringVector)d)._encryptionContext;
      }
    }
    public software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy dtor_commitmentPolicy {
      get {
        var d = this;
        if (d is EncryptTestVector_PositiveEncryptKeyringVector) { return ((EncryptTestVector_PositiveEncryptKeyringVector)d)._commitmentPolicy; }
        return ((EncryptTestVector_NegativeEncryptKeyringVector)d)._commitmentPolicy;
      }
    }
    public software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo dtor_algorithmSuite {
      get {
        var d = this;
        if (d is EncryptTestVector_PositiveEncryptKeyringVector) { return ((EncryptTestVector_PositiveEncryptKeyringVector)d)._algorithmSuite; }
        return ((EncryptTestVector_NegativeEncryptKeyringVector)d)._algorithmSuite;
      }
    }
    public Wrappers_Compile._IOption<long> dtor_maxPlaintextLength {
      get {
        var d = this;
        if (d is EncryptTestVector_PositiveEncryptKeyringVector) { return ((EncryptTestVector_PositiveEncryptKeyringVector)d)._maxPlaintextLength; }
        return ((EncryptTestVector_NegativeEncryptKeyringVector)d)._maxPlaintextLength;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> dtor_requiredEncryptionContextKeys {
      get {
        var d = this;
        if (d is EncryptTestVector_PositiveEncryptKeyringVector) { return ((EncryptTestVector_PositiveEncryptKeyringVector)d)._requiredEncryptionContextKeys; }
        return ((EncryptTestVector_NegativeEncryptKeyringVector)d)._requiredEncryptionContextKeys;
      }
    }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_encryptDescription {
      get {
        var d = this;
        return ((EncryptTestVector_PositiveEncryptKeyringVector)d)._encryptDescription;
      }
    }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_decryptDescription {
      get {
        var d = this;
        return ((EncryptTestVector_PositiveEncryptKeyringVector)d)._decryptDescription;
      }
    }
    public Dafny.ISequence<char> dtor_errorDescription {
      get {
        var d = this;
        return ((EncryptTestVector_NegativeEncryptKeyringVector)d)._errorDescription;
      }
    }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_keyDescription {
      get {
        var d = this;
        return ((EncryptTestVector_NegativeEncryptKeyringVector)d)._keyDescription;
      }
    }
    public abstract _IEncryptTestVector DowncastClone();
  }
  public class EncryptTestVector_PositiveEncryptKeyringVector : EncryptTestVector {
    public readonly Dafny.ISequence<char> _name;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _description;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _encryptionContext;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy _commitmentPolicy;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _algorithmSuite;
    public readonly Wrappers_Compile._IOption<long> _maxPlaintextLength;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> _requiredEncryptionContextKeys;
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _encryptDescription;
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _decryptDescription;
    public EncryptTestVector_PositiveEncryptKeyringVector(Dafny.ISequence<char> name, Wrappers_Compile._IOption<Dafny.ISequence<char>> description, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy commitmentPolicy, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo algorithmSuite, Wrappers_Compile._IOption<long> maxPlaintextLength, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> requiredEncryptionContextKeys, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription encryptDescription, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription decryptDescription) {
      this._name = name;
      this._description = description;
      this._encryptionContext = encryptionContext;
      this._commitmentPolicy = commitmentPolicy;
      this._algorithmSuite = algorithmSuite;
      this._maxPlaintextLength = maxPlaintextLength;
      this._requiredEncryptionContextKeys = requiredEncryptionContextKeys;
      this._encryptDescription = encryptDescription;
      this._decryptDescription = decryptDescription;
    }
    public override _IEncryptTestVector DowncastClone() {
      if (this is _IEncryptTestVector dt) { return dt; }
      return new EncryptTestVector_PositiveEncryptKeyringVector(_name, _description, _encryptionContext, _commitmentPolicy, _algorithmSuite, _maxPlaintextLength, _requiredEncryptionContextKeys, _encryptDescription, _decryptDescription);
    }
    public override bool Equals(object other) {
      var oth = other as TestVectors_Compile.EncryptTestVector_PositiveEncryptKeyringVector;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._description, oth._description) && object.Equals(this._encryptionContext, oth._encryptionContext) && object.Equals(this._commitmentPolicy, oth._commitmentPolicy) && object.Equals(this._algorithmSuite, oth._algorithmSuite) && object.Equals(this._maxPlaintextLength, oth._maxPlaintextLength) && object.Equals(this._requiredEncryptionContextKeys, oth._requiredEncryptionContextKeys) && object.Equals(this._encryptDescription, oth._encryptDescription) && object.Equals(this._decryptDescription, oth._decryptDescription);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._description));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._commitmentPolicy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._algorithmSuite));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._maxPlaintextLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._requiredEncryptionContextKeys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encryptDescription));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._decryptDescription));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectors_Compile.EncryptTestVector.PositiveEncryptKeyringVector";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._description);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._commitmentPolicy);
      s += ", ";
      s += Dafny.Helpers.ToString(this._algorithmSuite);
      s += ", ";
      s += Dafny.Helpers.ToString(this._maxPlaintextLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this._requiredEncryptionContextKeys);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encryptDescription);
      s += ", ";
      s += Dafny.Helpers.ToString(this._decryptDescription);
      s += ")";
      return s;
    }
  }
  public class EncryptTestVector_NegativeEncryptKeyringVector : EncryptTestVector {
    public readonly Dafny.ISequence<char> _name;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _description;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _encryptionContext;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy _commitmentPolicy;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _algorithmSuite;
    public readonly Wrappers_Compile._IOption<long> _maxPlaintextLength;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> _requiredEncryptionContextKeys;
    public readonly Dafny.ISequence<char> _errorDescription;
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _keyDescription;
    public EncryptTestVector_NegativeEncryptKeyringVector(Dafny.ISequence<char> name, Wrappers_Compile._IOption<Dafny.ISequence<char>> description, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy commitmentPolicy, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo algorithmSuite, Wrappers_Compile._IOption<long> maxPlaintextLength, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> requiredEncryptionContextKeys, Dafny.ISequence<char> errorDescription, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription) {
      this._name = name;
      this._description = description;
      this._encryptionContext = encryptionContext;
      this._commitmentPolicy = commitmentPolicy;
      this._algorithmSuite = algorithmSuite;
      this._maxPlaintextLength = maxPlaintextLength;
      this._requiredEncryptionContextKeys = requiredEncryptionContextKeys;
      this._errorDescription = errorDescription;
      this._keyDescription = keyDescription;
    }
    public override _IEncryptTestVector DowncastClone() {
      if (this is _IEncryptTestVector dt) { return dt; }
      return new EncryptTestVector_NegativeEncryptKeyringVector(_name, _description, _encryptionContext, _commitmentPolicy, _algorithmSuite, _maxPlaintextLength, _requiredEncryptionContextKeys, _errorDescription, _keyDescription);
    }
    public override bool Equals(object other) {
      var oth = other as TestVectors_Compile.EncryptTestVector_NegativeEncryptKeyringVector;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._description, oth._description) && object.Equals(this._encryptionContext, oth._encryptionContext) && object.Equals(this._commitmentPolicy, oth._commitmentPolicy) && object.Equals(this._algorithmSuite, oth._algorithmSuite) && object.Equals(this._maxPlaintextLength, oth._maxPlaintextLength) && object.Equals(this._requiredEncryptionContextKeys, oth._requiredEncryptionContextKeys) && object.Equals(this._errorDescription, oth._errorDescription) && object.Equals(this._keyDescription, oth._keyDescription);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._description));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._commitmentPolicy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._algorithmSuite));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._maxPlaintextLength));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._requiredEncryptionContextKeys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._errorDescription));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyDescription));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectors_Compile.EncryptTestVector.NegativeEncryptKeyringVector";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._description);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._commitmentPolicy);
      s += ", ";
      s += Dafny.Helpers.ToString(this._algorithmSuite);
      s += ", ";
      s += Dafny.Helpers.ToString(this._maxPlaintextLength);
      s += ", ";
      s += Dafny.Helpers.ToString(this._requiredEncryptionContextKeys);
      s += ", ";
      s += Dafny.Helpers.ToString(this._errorDescription);
      s += ", ";
      s += Dafny.Helpers.ToString(this._keyDescription);
      s += ")";
      return s;
    }
  }

  public interface _IDecryptTestVector {
    bool is_PositiveDecryptKeyringTest { get; }
    bool is_NegativeDecryptKeyringTest { get; }
    Dafny.ISequence<char> dtor_name { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo dtor_algorithmSuite { get; }
    software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy dtor_commitmentPolicy { get; }
    Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> dtor_encryptedDataKeys { get; }
    Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext { get; }
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_keyDescription { get; }
    TestVectors_Compile._IDecryptResult dtor_expectedResult { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_description { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>> dtor_reproducedEncryptionContext { get; }
    Dafny.ISequence<char> dtor_errorDescription { get; }
    _IDecryptTestVector DowncastClone();
  }
  public abstract class DecryptTestVector : _IDecryptTestVector {
    public DecryptTestVector() { }
    private static readonly TestVectors_Compile._IDecryptTestVector theDefault = create_PositiveDecryptKeyringTest(Dafny.Sequence<char>.Empty, software.amazon.cryptography.materialproviders.internaldafny.types.AlgorithmSuiteInfo.Default(), software.amazon.cryptography.materialproviders.internaldafny.types.CommitmentPolicy.Default(), Dafny.Sequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey>.Empty, Dafny.Map<Dafny.ISequence<byte>, Dafny.ISequence<byte>>.Empty, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription.Default(), TestVectors_Compile.DecryptResult.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>.Default());
    public static TestVectors_Compile._IDecryptTestVector Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestVectors_Compile._IDecryptTestVector> _TYPE = new Dafny.TypeDescriptor<TestVectors_Compile._IDecryptTestVector>(TestVectors_Compile.DecryptTestVector.Default());
    public static Dafny.TypeDescriptor<TestVectors_Compile._IDecryptTestVector> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDecryptTestVector create_PositiveDecryptKeyringTest(Dafny.ISequence<char> name, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo algorithmSuite, software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy commitmentPolicy, Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> encryptedDataKeys, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription, TestVectors_Compile._IDecryptResult expectedResult, Wrappers_Compile._IOption<Dafny.ISequence<char>> description, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>> reproducedEncryptionContext) {
      return new DecryptTestVector_PositiveDecryptKeyringTest(name, algorithmSuite, commitmentPolicy, encryptedDataKeys, encryptionContext, keyDescription, expectedResult, description, reproducedEncryptionContext);
    }
    public static _IDecryptTestVector create_NegativeDecryptKeyringTest(Dafny.ISequence<char> name, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo algorithmSuite, software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy commitmentPolicy, Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> encryptedDataKeys, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<char> errorDescription, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>> reproducedEncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<char>> description) {
      return new DecryptTestVector_NegativeDecryptKeyringTest(name, algorithmSuite, commitmentPolicy, encryptedDataKeys, encryptionContext, errorDescription, keyDescription, reproducedEncryptionContext, description);
    }
    public bool is_PositiveDecryptKeyringTest { get { return this is DecryptTestVector_PositiveDecryptKeyringTest; } }
    public bool is_NegativeDecryptKeyringTest { get { return this is DecryptTestVector_NegativeDecryptKeyringTest; } }
    public Dafny.ISequence<char> dtor_name {
      get {
        var d = this;
        if (d is DecryptTestVector_PositiveDecryptKeyringTest) { return ((DecryptTestVector_PositiveDecryptKeyringTest)d)._name; }
        return ((DecryptTestVector_NegativeDecryptKeyringTest)d)._name;
      }
    }
    public software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo dtor_algorithmSuite {
      get {
        var d = this;
        if (d is DecryptTestVector_PositiveDecryptKeyringTest) { return ((DecryptTestVector_PositiveDecryptKeyringTest)d)._algorithmSuite; }
        return ((DecryptTestVector_NegativeDecryptKeyringTest)d)._algorithmSuite;
      }
    }
    public software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy dtor_commitmentPolicy {
      get {
        var d = this;
        if (d is DecryptTestVector_PositiveDecryptKeyringTest) { return ((DecryptTestVector_PositiveDecryptKeyringTest)d)._commitmentPolicy; }
        return ((DecryptTestVector_NegativeDecryptKeyringTest)d)._commitmentPolicy;
      }
    }
    public Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> dtor_encryptedDataKeys {
      get {
        var d = this;
        if (d is DecryptTestVector_PositiveDecryptKeyringTest) { return ((DecryptTestVector_PositiveDecryptKeyringTest)d)._encryptedDataKeys; }
        return ((DecryptTestVector_NegativeDecryptKeyringTest)d)._encryptedDataKeys;
      }
    }
    public Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> dtor_encryptionContext {
      get {
        var d = this;
        if (d is DecryptTestVector_PositiveDecryptKeyringTest) { return ((DecryptTestVector_PositiveDecryptKeyringTest)d)._encryptionContext; }
        return ((DecryptTestVector_NegativeDecryptKeyringTest)d)._encryptionContext;
      }
    }
    public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription dtor_keyDescription {
      get {
        var d = this;
        if (d is DecryptTestVector_PositiveDecryptKeyringTest) { return ((DecryptTestVector_PositiveDecryptKeyringTest)d)._keyDescription; }
        return ((DecryptTestVector_NegativeDecryptKeyringTest)d)._keyDescription;
      }
    }
    public TestVectors_Compile._IDecryptResult dtor_expectedResult {
      get {
        var d = this;
        return ((DecryptTestVector_PositiveDecryptKeyringTest)d)._expectedResult;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_description {
      get {
        var d = this;
        if (d is DecryptTestVector_PositiveDecryptKeyringTest) { return ((DecryptTestVector_PositiveDecryptKeyringTest)d)._description; }
        return ((DecryptTestVector_NegativeDecryptKeyringTest)d)._description;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>> dtor_reproducedEncryptionContext {
      get {
        var d = this;
        if (d is DecryptTestVector_PositiveDecryptKeyringTest) { return ((DecryptTestVector_PositiveDecryptKeyringTest)d)._reproducedEncryptionContext; }
        return ((DecryptTestVector_NegativeDecryptKeyringTest)d)._reproducedEncryptionContext;
      }
    }
    public Dafny.ISequence<char> dtor_errorDescription {
      get {
        var d = this;
        return ((DecryptTestVector_NegativeDecryptKeyringTest)d)._errorDescription;
      }
    }
    public abstract _IDecryptTestVector DowncastClone();
  }
  public class DecryptTestVector_PositiveDecryptKeyringTest : DecryptTestVector {
    public readonly Dafny.ISequence<char> _name;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _algorithmSuite;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy _commitmentPolicy;
    public readonly Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> _encryptedDataKeys;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _encryptionContext;
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _keyDescription;
    public readonly TestVectors_Compile._IDecryptResult _expectedResult;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _description;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>> _reproducedEncryptionContext;
    public DecryptTestVector_PositiveDecryptKeyringTest(Dafny.ISequence<char> name, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo algorithmSuite, software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy commitmentPolicy, Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> encryptedDataKeys, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription, TestVectors_Compile._IDecryptResult expectedResult, Wrappers_Compile._IOption<Dafny.ISequence<char>> description, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>> reproducedEncryptionContext) {
      this._name = name;
      this._algorithmSuite = algorithmSuite;
      this._commitmentPolicy = commitmentPolicy;
      this._encryptedDataKeys = encryptedDataKeys;
      this._encryptionContext = encryptionContext;
      this._keyDescription = keyDescription;
      this._expectedResult = expectedResult;
      this._description = description;
      this._reproducedEncryptionContext = reproducedEncryptionContext;
    }
    public override _IDecryptTestVector DowncastClone() {
      if (this is _IDecryptTestVector dt) { return dt; }
      return new DecryptTestVector_PositiveDecryptKeyringTest(_name, _algorithmSuite, _commitmentPolicy, _encryptedDataKeys, _encryptionContext, _keyDescription, _expectedResult, _description, _reproducedEncryptionContext);
    }
    public override bool Equals(object other) {
      var oth = other as TestVectors_Compile.DecryptTestVector_PositiveDecryptKeyringTest;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._algorithmSuite, oth._algorithmSuite) && object.Equals(this._commitmentPolicy, oth._commitmentPolicy) && object.Equals(this._encryptedDataKeys, oth._encryptedDataKeys) && object.Equals(this._encryptionContext, oth._encryptionContext) && object.Equals(this._keyDescription, oth._keyDescription) && object.Equals(this._expectedResult, oth._expectedResult) && object.Equals(this._description, oth._description) && object.Equals(this._reproducedEncryptionContext, oth._reproducedEncryptionContext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._algorithmSuite));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._commitmentPolicy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encryptedDataKeys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyDescription));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expectedResult));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._description));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._reproducedEncryptionContext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectors_Compile.DecryptTestVector.PositiveDecryptKeyringTest";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._algorithmSuite);
      s += ", ";
      s += Dafny.Helpers.ToString(this._commitmentPolicy);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encryptedDataKeys);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._keyDescription);
      s += ", ";
      s += Dafny.Helpers.ToString(this._expectedResult);
      s += ", ";
      s += Dafny.Helpers.ToString(this._description);
      s += ", ";
      s += Dafny.Helpers.ToString(this._reproducedEncryptionContext);
      s += ")";
      return s;
    }
  }
  public class DecryptTestVector_NegativeDecryptKeyringTest : DecryptTestVector {
    public readonly Dafny.ISequence<char> _name;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _algorithmSuite;
    public readonly software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy _commitmentPolicy;
    public readonly Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> _encryptedDataKeys;
    public readonly Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _encryptionContext;
    public readonly Dafny.ISequence<char> _errorDescription;
    public readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _keyDescription;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>> _reproducedEncryptionContext;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _description;
    public DecryptTestVector_NegativeDecryptKeyringTest(Dafny.ISequence<char> name, software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo algorithmSuite, software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy commitmentPolicy, Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> encryptedDataKeys, Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> encryptionContext, Dafny.ISequence<char> errorDescription, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription keyDescription, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>> reproducedEncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<char>> description) {
      this._name = name;
      this._algorithmSuite = algorithmSuite;
      this._commitmentPolicy = commitmentPolicy;
      this._encryptedDataKeys = encryptedDataKeys;
      this._encryptionContext = encryptionContext;
      this._errorDescription = errorDescription;
      this._keyDescription = keyDescription;
      this._reproducedEncryptionContext = reproducedEncryptionContext;
      this._description = description;
    }
    public override _IDecryptTestVector DowncastClone() {
      if (this is _IDecryptTestVector dt) { return dt; }
      return new DecryptTestVector_NegativeDecryptKeyringTest(_name, _algorithmSuite, _commitmentPolicy, _encryptedDataKeys, _encryptionContext, _errorDescription, _keyDescription, _reproducedEncryptionContext, _description);
    }
    public override bool Equals(object other) {
      var oth = other as TestVectors_Compile.DecryptTestVector_NegativeDecryptKeyringTest;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._algorithmSuite, oth._algorithmSuite) && object.Equals(this._commitmentPolicy, oth._commitmentPolicy) && object.Equals(this._encryptedDataKeys, oth._encryptedDataKeys) && object.Equals(this._encryptionContext, oth._encryptionContext) && object.Equals(this._errorDescription, oth._errorDescription) && object.Equals(this._keyDescription, oth._keyDescription) && object.Equals(this._reproducedEncryptionContext, oth._reproducedEncryptionContext) && object.Equals(this._description, oth._description);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._algorithmSuite));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._commitmentPolicy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encryptedDataKeys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._errorDescription));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keyDescription));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._reproducedEncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._description));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectors_Compile.DecryptTestVector.NegativeDecryptKeyringTest";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._algorithmSuite);
      s += ", ";
      s += Dafny.Helpers.ToString(this._commitmentPolicy);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encryptedDataKeys);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._errorDescription);
      s += ", ";
      s += Dafny.Helpers.ToString(this._keyDescription);
      s += ", ";
      s += Dafny.Helpers.ToString(this._reproducedEncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._description);
      s += ")";
      return s;
    }
  }

  public interface _IDecryptResult {
    bool is_DecryptResult { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_plaintextDataKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_symmetricSigningKey { get; }
    Dafny.ISequence<Dafny.ISequence<byte>> dtor_requiredEncryptionContextKeys { get; }
    _IDecryptResult DowncastClone();
  }
  public class DecryptResult : _IDecryptResult {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _plaintextDataKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _symmetricSigningKey;
    public readonly Dafny.ISequence<Dafny.ISequence<byte>> _requiredEncryptionContextKeys;
    public DecryptResult(Wrappers_Compile._IOption<Dafny.ISequence<byte>> plaintextDataKey, Wrappers_Compile._IOption<Dafny.ISequence<byte>> symmetricSigningKey, Dafny.ISequence<Dafny.ISequence<byte>> requiredEncryptionContextKeys) {
      this._plaintextDataKey = plaintextDataKey;
      this._symmetricSigningKey = symmetricSigningKey;
      this._requiredEncryptionContextKeys = requiredEncryptionContextKeys;
    }
    public _IDecryptResult DowncastClone() {
      if (this is _IDecryptResult dt) { return dt; }
      return new DecryptResult(_plaintextDataKey, _symmetricSigningKey, _requiredEncryptionContextKeys);
    }
    public override bool Equals(object other) {
      var oth = other as TestVectors_Compile.DecryptResult;
      return oth != null && object.Equals(this._plaintextDataKey, oth._plaintextDataKey) && object.Equals(this._symmetricSigningKey, oth._symmetricSigningKey) && object.Equals(this._requiredEncryptionContextKeys, oth._requiredEncryptionContextKeys);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._plaintextDataKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._symmetricSigningKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._requiredEncryptionContextKeys));
      return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectors_Compile.DecryptResult.DecryptResult";
      s += "(";
      s += Dafny.Helpers.ToString(this._plaintextDataKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._symmetricSigningKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._requiredEncryptionContextKeys);
      s += ")";
      return s;
    }
    private static readonly TestVectors_Compile._IDecryptResult theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Dafny.Sequence<Dafny.ISequence<byte>>.Empty);
    public static TestVectors_Compile._IDecryptResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TestVectors_Compile._IDecryptResult> _TYPE = new Dafny.TypeDescriptor<TestVectors_Compile._IDecryptResult>(TestVectors_Compile.DecryptResult.Default());
    public static Dafny.TypeDescriptor<TestVectors_Compile._IDecryptResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDecryptResult create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> plaintextDataKey, Wrappers_Compile._IOption<Dafny.ISequence<byte>> symmetricSigningKey, Dafny.ISequence<Dafny.ISequence<byte>> requiredEncryptionContextKeys) {
      return new DecryptResult(plaintextDataKey, symmetricSigningKey, requiredEncryptionContextKeys);
    }
    public static _IDecryptResult create_DecryptResult(Wrappers_Compile._IOption<Dafny.ISequence<byte>> plaintextDataKey, Wrappers_Compile._IOption<Dafny.ISequence<byte>> symmetricSigningKey, Dafny.ISequence<Dafny.ISequence<byte>> requiredEncryptionContextKeys) {
      return create(plaintextDataKey, symmetricSigningKey, requiredEncryptionContextKeys);
    }
    public bool is_DecryptResult { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_plaintextDataKey {
      get {
        return this._plaintextDataKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_symmetricSigningKey {
      get {
        return this._symmetricSigningKey;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<byte>> dtor_requiredEncryptionContextKeys {
      get {
        return this._requiredEncryptionContextKeys;
      }
    }
  }

  public partial class __default {
    public static void TestGetEncryptionMaterials(TestVectors_Compile._IEncryptTest test, out bool testResult, out Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials> materials)
    {
      testResult = false;
      materials = Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>.Default();
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\nTEST===> ")));
      Dafny.Helpers.Print((((test).dtor_vector).dtor_name));
      Dafny.Helpers.Print(((((((test).dtor_vector).dtor_description).is_Some) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("\n"), (((test).dtor_vector).dtor_description).dtor_value)) : (Dafny.Sequence<char>.FromString("")))));
      Dafny.Helpers.Print((((((test).dtor_vector).is_NegativeEncryptKeyringVector) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("\n"), ((test).dtor_vector).dtor_errorDescription)) : (Dafny.Sequence<char>.FromString("")))));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _482_result;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out70;
      _out70 = ((test).dtor_cmm).GetEncryptionMaterials((test).dtor_input);
      _482_result = _out70;
      testResult = ((System.Func<TestVectors_Compile._IEncryptTestVector, bool>)((_source15) => {
        if (_source15.is_PositiveEncryptKeyringVector) {
          Dafny.ISequence<char> _483___mcc_h0 = _source15.dtor_name;
          Wrappers_Compile._IOption<Dafny.ISequence<char>> _484___mcc_h1 = _source15.dtor_description;
          Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _485___mcc_h2 = _source15.dtor_encryptionContext;
          software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy _486___mcc_h3 = _source15.dtor_commitmentPolicy;
          software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _487___mcc_h4 = _source15.dtor_algorithmSuite;
          Wrappers_Compile._IOption<long> _488___mcc_h5 = _source15.dtor_maxPlaintextLength;
          Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> _489___mcc_h6 = _source15.dtor_requiredEncryptionContextKeys;
          software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _490___mcc_h7 = _source15.dtor_encryptDescription;
          software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _491___mcc_h8 = _source15.dtor_decryptDescription;
          return (_482_result).is_Success;
        } else {
          Dafny.ISequence<char> _492___mcc_h9 = _source15.dtor_name;
          Wrappers_Compile._IOption<Dafny.ISequence<char>> _493___mcc_h10 = _source15.dtor_description;
          Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _494___mcc_h11 = _source15.dtor_encryptionContext;
          software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy _495___mcc_h12 = _source15.dtor_commitmentPolicy;
          software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _496___mcc_h13 = _source15.dtor_algorithmSuite;
          Wrappers_Compile._IOption<long> _497___mcc_h14 = _source15.dtor_maxPlaintextLength;
          Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> _498___mcc_h15 = _source15.dtor_requiredEncryptionContextKeys;
          Dafny.ISequence<char> _499___mcc_h16 = _source15.dtor_errorDescription;
          software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _500___mcc_h17 = _source15.dtor_keyDescription;
          return !((_482_result).is_Success);
        }
      }))((test).dtor_vector);
      materials = (((((test).dtor_vector).is_PositiveEncryptKeyringVector) && ((_482_result).is_Success)) ? (Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>.create_Some(((_482_result).dtor_value).dtor_encryptionMaterials)) : (Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>.create_None()));
      if (!(testResult)) {
        if (((test).dtor_vector).is_PositiveEncryptKeyringVector) {
          Dafny.Helpers.Print(((_482_result).dtor_error));
        }
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\nFAILED! <-----------\n")));
      }
    }
    public static bool TestDecryptMaterials(TestVectors_Compile._IDecryptTest test)
    {
      bool output = false;
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\nTEST===> ")));
      Dafny.Helpers.Print((((test).dtor_vector).dtor_name));
      Dafny.Helpers.Print(((((((test).dtor_vector).dtor_description).is_Some) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("\n"), (((test).dtor_vector).dtor_description).dtor_value)) : (Dafny.Sequence<char>.FromString("")))));
      Dafny.Helpers.Print((((((test).dtor_vector).is_NegativeDecryptKeyringTest) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("\n"), ((test).dtor_vector).dtor_errorDescription)) : (Dafny.Sequence<char>.FromString("\n")))));
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _501_result;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out71;
      _out71 = ((test).dtor_cmm).DecryptMaterials((test).dtor_input);
      _501_result = _out71;
      output = ((System.Func<TestVectors_Compile._IDecryptTestVector, bool>)((_source16) => {
        if (_source16.is_PositiveDecryptKeyringTest) {
          Dafny.ISequence<char> _502___mcc_h0 = _source16.dtor_name;
          software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _503___mcc_h1 = _source16.dtor_algorithmSuite;
          software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy _504___mcc_h2 = _source16.dtor_commitmentPolicy;
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> _505___mcc_h3 = _source16.dtor_encryptedDataKeys;
          Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _506___mcc_h4 = _source16.dtor_encryptionContext;
          software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _507___mcc_h5 = _source16.dtor_keyDescription;
          TestVectors_Compile._IDecryptResult _508___mcc_h6 = _source16.dtor_expectedResult;
          Wrappers_Compile._IOption<Dafny.ISequence<char>> _509___mcc_h7 = _source16.dtor_description;
          Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>> _510___mcc_h8 = _source16.dtor_reproducedEncryptionContext;
          return ((((_501_result).is_Success) && (object.Equals((((_501_result).dtor_value).dtor_decryptionMaterials).dtor_plaintextDataKey, (((test).dtor_vector).dtor_expectedResult).dtor_plaintextDataKey))) && (object.Equals((((_501_result).dtor_value).dtor_decryptionMaterials).dtor_symmetricSigningKey, (((test).dtor_vector).dtor_expectedResult).dtor_symmetricSigningKey))) && (((((_501_result).dtor_value).dtor_decryptionMaterials).dtor_requiredEncryptionContextKeys).Equals((((test).dtor_vector).dtor_expectedResult).dtor_requiredEncryptionContextKeys));
        } else {
          Dafny.ISequence<char> _511___mcc_h9 = _source16.dtor_name;
          software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _512___mcc_h10 = _source16.dtor_algorithmSuite;
          software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy _513___mcc_h11 = _source16.dtor_commitmentPolicy;
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptedDataKey> _514___mcc_h12 = _source16.dtor_encryptedDataKeys;
          Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _515___mcc_h13 = _source16.dtor_encryptionContext;
          Dafny.ISequence<char> _516___mcc_h14 = _source16.dtor_errorDescription;
          software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _517___mcc_h15 = _source16.dtor_keyDescription;
          Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>> _518___mcc_h16 = _source16.dtor_reproducedEncryptionContext;
          Wrappers_Compile._IOption<Dafny.ISequence<char>> _519___mcc_h17 = _source16.dtor_description;
          return !((_501_result).is_Success);
        }
      }))((test).dtor_vector);
      if (!(output)) {
        if ((((test).dtor_vector).is_PositiveDecryptKeyringTest) && ((_501_result).is_Failure)) {
          Dafny.Helpers.Print(((_501_result).dtor_error));
        }
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\nFAILED! <-----------\n")));
      }
      return output;
    }
    public static Wrappers_Compile._IResult<TestVectors_Compile._IEncryptTest, Dafny.ISequence<char>> ToEncryptTest(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient keys, TestVectors_Compile._IEncryptTestVector vector)
    {
      Wrappers_Compile._IResult<TestVectors_Compile._IEncryptTest, Dafny.ISequence<char>> output = default(Wrappers_Compile._IResult<TestVectors_Compile._IEncryptTest, Dafny.ISequence<char>>);
      software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput _520_input;
      _520_input = ((System.Func<TestVectors_Compile._IEncryptTestVector, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>)((_source17) => {
        if (_source17.is_PositiveEncryptKeyringVector) {
          Dafny.ISequence<char> _521___mcc_h0 = _source17.dtor_name;
          Wrappers_Compile._IOption<Dafny.ISequence<char>> _522___mcc_h1 = _source17.dtor_description;
          Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _523___mcc_h2 = _source17.dtor_encryptionContext;
          software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy _524___mcc_h3 = _source17.dtor_commitmentPolicy;
          software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _525___mcc_h4 = _source17.dtor_algorithmSuite;
          Wrappers_Compile._IOption<long> _526___mcc_h5 = _source17.dtor_maxPlaintextLength;
          Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> _527___mcc_h6 = _source17.dtor_requiredEncryptionContextKeys;
          software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _528___mcc_h7 = _source17.dtor_encryptDescription;
          software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _529___mcc_h8 = _source17.dtor_decryptDescription;
          return Dafny.Helpers.Let<Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_527___mcc_h6, _pat_let1_0 => Dafny.Helpers.Let<Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_pat_let1_0, _530_requiredEncryptionContextKeys => Dafny.Helpers.Let<Wrappers_Compile._IOption<long>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_526___mcc_h5, _pat_let2_0 => Dafny.Helpers.Let<Wrappers_Compile._IOption<long>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_pat_let2_0, _531_maxPlaintextLength => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_525___mcc_h4, _pat_let3_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_pat_let3_0, _532_algorithmSuite => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_524___mcc_h3, _pat_let4_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_pat_let4_0, _533_commitmentPolicy => Dafny.Helpers.Let<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_523___mcc_h2, _pat_let5_0 => Dafny.Helpers.Let<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_pat_let5_0, _534_encryptionContext => software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsInput.create(_534_encryptionContext, _533_commitmentPolicy, Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId>.create_Some((_532_algorithmSuite).dtor_id), _531_maxPlaintextLength, _530_requiredEncryptionContextKeys)))))))))));
        } else {
          Dafny.ISequence<char> _535___mcc_h9 = _source17.dtor_name;
          Wrappers_Compile._IOption<Dafny.ISequence<char>> _536___mcc_h10 = _source17.dtor_description;
          Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _537___mcc_h11 = _source17.dtor_encryptionContext;
          software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy _538___mcc_h12 = _source17.dtor_commitmentPolicy;
          software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _539___mcc_h13 = _source17.dtor_algorithmSuite;
          Wrappers_Compile._IOption<long> _540___mcc_h14 = _source17.dtor_maxPlaintextLength;
          Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> _541___mcc_h15 = _source17.dtor_requiredEncryptionContextKeys;
          Dafny.ISequence<char> _542___mcc_h16 = _source17.dtor_errorDescription;
          software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyDescription _543___mcc_h17 = _source17.dtor_keyDescription;
          return Dafny.Helpers.Let<Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_541___mcc_h15, _pat_let6_0 => Dafny.Helpers.Let<Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_pat_let6_0, _544_requiredEncryptionContextKeys => Dafny.Helpers.Let<Wrappers_Compile._IOption<long>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_540___mcc_h14, _pat_let7_0 => Dafny.Helpers.Let<Wrappers_Compile._IOption<long>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_pat_let7_0, _545_maxPlaintextLength => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_539___mcc_h13, _pat_let8_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_pat_let8_0, _546_algorithmSuite => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_538___mcc_h12, _pat_let9_0 => Dafny.Helpers.Let<software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_pat_let9_0, _547_commitmentPolicy => Dafny.Helpers.Let<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_537___mcc_h11, _pat_let10_0 => Dafny.Helpers.Let<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, software.amazon.cryptography.materialproviders.internaldafny.types._IGetEncryptionMaterialsInput>(_pat_let10_0, _548_encryptionContext => software.amazon.cryptography.materialproviders.internaldafny.types.GetEncryptionMaterialsInput.create(_548_encryptionContext, _547_commitmentPolicy, Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId>.create_Some((_546_algorithmSuite).dtor_id), _545_maxPlaintextLength, _544_requiredEncryptionContextKeys)))))))))));
        }
      }))(vector);
      software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient _549_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _550_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out72;
      _out72 = software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedDefaultMaterialProvidersConfig());
      _550_valueOrError0 = _out72;
      if (!(!((_550_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectors.dfy(131,12): " + _550_valueOrError0);}
      _549_mpl = (_550_valueOrError0).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _551_maybeKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _out73;
      _out73 = (keys).CreateWappedTestVectorKeyring(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.TestVectorKeyringInput.create((((vector).is_PositiveEncryptKeyringVector) ? ((vector).dtor_encryptDescription) : ((vector).dtor_keyDescription))));
      _551_maybeKeyring = _out73;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _552_keyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Dafny.ISequence<char>> _553_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Dafny.ISequence<char>>);
      _553_valueOrError1 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.MapFailure<Dafny.ISequence<char>>(_551_maybeKeyring, ((System.Func<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError, Dafny.ISequence<char>>)((_554_e) => {
        return Dafny.Helpers.Let<_System._ITuple0, Dafny.ISequence<char>>(TestVectors_Compile.__default.printErr(_554_e), _pat_let11_0 => Dafny.Helpers.Let<_System._ITuple0, Dafny.ISequence<char>>(_pat_let11_0, _555___v44 => Dafny.Sequence<char>.FromString("Keyring failure")));
      })));
      if ((_553_valueOrError1).IsFailure()) {
        output = (_553_valueOrError1).PropagateFailure<TestVectors_Compile._IEncryptTest>();
        return output;
      }
      _552_keyring = (_553_valueOrError1).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _556_maybeCmm;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out74;
      _out74 = (_549_mpl).CreateDefaultCryptographicMaterialsManager(software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultCryptographicMaterialsManagerInput.create(_552_keyring));
      _556_maybeCmm = _out74;
      software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager _557_cmm;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, Dafny.ISequence<char>> _558_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, Dafny.ISequence<char>>);
      _558_valueOrError2 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<Dafny.ISequence<char>>(_556_maybeCmm, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, Dafny.ISequence<char>>)((_559_e) => {
        return Dafny.Sequence<char>.FromString("CMM failure");
      })));
      if ((_558_valueOrError2).IsFailure()) {
        output = (_558_valueOrError2).PropagateFailure<TestVectors_Compile._IEncryptTest>();
        return output;
      }
      _557_cmm = (_558_valueOrError2).Extract();
      output = Wrappers_Compile.Result<TestVectors_Compile._IEncryptTest, Dafny.ISequence<char>>.create_Success(TestVectors_Compile.EncryptTest.create(_520_input, _557_cmm, vector));
      return output;
      return output;
    }
    public static Wrappers_Compile._IResult<TestVectors_Compile._IDecryptTest, Dafny.ISequence<char>> ToDecryptTest(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient keys, TestVectors_Compile._IEncryptTest test, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials materials)
    {
      Wrappers_Compile._IResult<TestVectors_Compile._IDecryptTest, Dafny.ISequence<char>> output = default(Wrappers_Compile._IResult<TestVectors_Compile._IDecryptTest, Dafny.ISequence<char>>);
      Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>> _560_reproducedEncryptionContext;
      _560_reproducedEncryptionContext = Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>>.create_None();
      software.amazon.cryptography.materialproviders.internaldafny.types._IDecryptMaterialsInput _561_input;
      _561_input = software.amazon.cryptography.materialproviders.internaldafny.types.DecryptMaterialsInput.create(((materials).dtor_algorithmSuite).dtor_id, ((test).dtor_vector).dtor_commitmentPolicy, (materials).dtor_encryptedDataKeys, (materials).dtor_encryptionContext, _560_reproducedEncryptionContext);
      TestVectors_Compile._IDecryptTestVector _562_vector;
      _562_vector = TestVectors_Compile.DecryptTestVector.create_PositiveDecryptKeyringTest(Dafny.Sequence<char>.Concat(((test).dtor_vector).dtor_name, Dafny.Sequence<char>.FromString("->Decryption")), (materials).dtor_algorithmSuite, ((test).dtor_vector).dtor_commitmentPolicy, (materials).dtor_encryptedDataKeys, (materials).dtor_encryptionContext, ((test).dtor_vector).dtor_decryptDescription, TestVectors_Compile.DecryptResult.create((materials).dtor_plaintextDataKey, (((((materials).dtor_symmetricSigningKeys).is_Some) && ((new BigInteger((((materials).dtor_symmetricSigningKeys).dtor_value).Count)).Sign == 1)) ? (Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some((((materials).dtor_symmetricSigningKeys).dtor_value).Select(BigInteger.Zero))) : (Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None())), (materials).dtor_requiredEncryptionContextKeys), (((((test).dtor_vector).dtor_description).is_Some) ? (Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Decryption for "), (((test).dtor_vector).dtor_description).dtor_value))) : (Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None())), _560_reproducedEncryptionContext);
      software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient _563_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _564_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out75;
      _out75 = software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedDefaultMaterialProvidersConfig());
      _564_valueOrError0 = _out75;
      if (!(!((_564_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestVectors.dfy(196,12): " + _564_valueOrError0);}
      _563_mpl = (_564_valueOrError0).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _565_maybeKeyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _out76;
      _out76 = (keys).CreateWappedTestVectorKeyring(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.TestVectorKeyringInput.create((_562_vector).dtor_keyDescription));
      _565_maybeKeyring = _out76;
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _566_keyring;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Dafny.ISequence<char>> _567_valueOrError1 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, Dafny.ISequence<char>>);
      _567_valueOrError1 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.MapFailure<Dafny.ISequence<char>>(_565_maybeKeyring, ((System.Func<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError, Dafny.ISequence<char>>)((_568_e) => {
        return Dafny.Helpers.Let<_System._ITuple0, Dafny.ISequence<char>>(TestVectors_Compile.__default.printErr(_568_e), _pat_let12_0 => Dafny.Helpers.Let<_System._ITuple0, Dafny.ISequence<char>>(_pat_let12_0, _569___v45 => Dafny.Sequence<char>.FromString("Keyring failure")));
      })));
      if ((_567_valueOrError1).IsFailure()) {
        output = (_567_valueOrError1).PropagateFailure<TestVectors_Compile._IDecryptTest>();
        return output;
      }
      _566_keyring = (_567_valueOrError1).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _570_maybeCmm;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out77;
      _out77 = (_563_mpl).CreateDefaultCryptographicMaterialsManager(software.amazon.cryptography.materialproviders.internaldafny.types.CreateDefaultCryptographicMaterialsManagerInput.create(_566_keyring));
      _570_maybeCmm = _out77;
      software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager _571_cmm;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, Dafny.ISequence<char>> _572_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, Dafny.ISequence<char>>);
      _572_valueOrError2 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<Dafny.ISequence<char>>(_570_maybeCmm, ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, Dafny.ISequence<char>>)((_573_e) => {
        return Dafny.Sequence<char>.FromString("CMM failure");
      })));
      if ((_572_valueOrError2).IsFailure()) {
        output = (_572_valueOrError2).PropagateFailure<TestVectors_Compile._IDecryptTest>();
        return output;
      }
      _571_cmm = (_572_valueOrError2).Extract();
      output = Wrappers_Compile.Result<TestVectors_Compile._IDecryptTest, Dafny.ISequence<char>>.create_Success(TestVectors_Compile.DecryptTest.create(_561_input, _571_cmm, _562_vector));
      return output;
      return output;
    }
    public static _System._ITuple0 printErr(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError e)
    {
      _System._ITuple0 _hresult = _System.Tuple0.Default();
      Dafny.Helpers.Print((e));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
      _hresult = _System.Tuple0.create();
      return _hresult;
      return _hresult;
    }
  }
} // end of namespace TestVectors_Compile
namespace CompleteVectors_Compile {

  public interface _IPositiveKeyDescriptionJSON {
    bool is_PositiveKeyDescriptionJSON { get; }
    Dafny.ISequence<char> dtor_description { get; }
    JSON_mValues_Compile._IJSON dtor_encrypt { get; }
    JSON_mValues_Compile._IJSON dtor_decrypt { get; }
    _IPositiveKeyDescriptionJSON DowncastClone();
  }
  public class PositiveKeyDescriptionJSON : _IPositiveKeyDescriptionJSON {
    public readonly Dafny.ISequence<char> _description;
    public readonly JSON_mValues_Compile._IJSON _encrypt;
    public readonly JSON_mValues_Compile._IJSON _decrypt;
    public PositiveKeyDescriptionJSON(Dafny.ISequence<char> description, JSON_mValues_Compile._IJSON encrypt, JSON_mValues_Compile._IJSON decrypt) {
      this._description = description;
      this._encrypt = encrypt;
      this._decrypt = decrypt;
    }
    public _IPositiveKeyDescriptionJSON DowncastClone() {
      if (this is _IPositiveKeyDescriptionJSON dt) { return dt; }
      return new PositiveKeyDescriptionJSON(_description, _encrypt, _decrypt);
    }
    public override bool Equals(object other) {
      var oth = other as CompleteVectors_Compile.PositiveKeyDescriptionJSON;
      return oth != null && object.Equals(this._description, oth._description) && object.Equals(this._encrypt, oth._encrypt) && object.Equals(this._decrypt, oth._decrypt);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._description));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._encrypt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._decrypt));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CompleteVectors_Compile.PositiveKeyDescriptionJSON.PositiveKeyDescriptionJSON";
      s += "(";
      s += Dafny.Helpers.ToString(this._description);
      s += ", ";
      s += Dafny.Helpers.ToString(this._encrypt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._decrypt);
      s += ")";
      return s;
    }
    private static readonly CompleteVectors_Compile._IPositiveKeyDescriptionJSON theDefault = create(Dafny.Sequence<char>.Empty, JSON_mValues_Compile.JSON.Default(), JSON_mValues_Compile.JSON.Default());
    public static CompleteVectors_Compile._IPositiveKeyDescriptionJSON Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CompleteVectors_Compile._IPositiveKeyDescriptionJSON> _TYPE = new Dafny.TypeDescriptor<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>(CompleteVectors_Compile.PositiveKeyDescriptionJSON.Default());
    public static Dafny.TypeDescriptor<CompleteVectors_Compile._IPositiveKeyDescriptionJSON> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPositiveKeyDescriptionJSON create(Dafny.ISequence<char> description, JSON_mValues_Compile._IJSON encrypt, JSON_mValues_Compile._IJSON decrypt) {
      return new PositiveKeyDescriptionJSON(description, encrypt, decrypt);
    }
    public static _IPositiveKeyDescriptionJSON create_PositiveKeyDescriptionJSON(Dafny.ISequence<char> description, JSON_mValues_Compile._IJSON encrypt, JSON_mValues_Compile._IJSON decrypt) {
      return create(description, encrypt, decrypt);
    }
    public bool is_PositiveKeyDescriptionJSON { get { return true; } }
    public Dafny.ISequence<char> dtor_description {
      get {
        return this._description;
      }
    }
    public JSON_mValues_Compile._IJSON dtor_encrypt {
      get {
        return this._encrypt;
      }
    }
    public JSON_mValues_Compile._IJSON dtor_decrypt {
      get {
        return this._decrypt;
      }
    }
  }

  public partial class __default {
    public static software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy GetCompatableCommitmentPolicy(software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo algorithmSuite) {
      software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteId _source18 = (algorithmSuite).dtor_id;
      if (_source18.is_ESDK) {
        software.amazon.cryptography.materialproviders.internaldafny.types._IESDKAlgorithmSuiteId _574___mcc_h0 = _source18.dtor_ESDK;
        if (((algorithmSuite).dtor_commitment).is_None) {
          return software.amazon.cryptography.materialproviders.internaldafny.types.CommitmentPolicy.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKCommitmentPolicy.create_FORBID__ENCRYPT__ALLOW__DECRYPT());
        } else {
          return software.amazon.cryptography.materialproviders.internaldafny.types.CommitmentPolicy.create_ESDK(software.amazon.cryptography.materialproviders.internaldafny.types.ESDKCommitmentPolicy.create_REQUIRE__ENCRYPT__REQUIRE__DECRYPT());
        }
      } else {
        software.amazon.cryptography.materialproviders.internaldafny.types._IDBEAlgorithmSuiteId _575___mcc_h1 = _source18.dtor_DBE;
        return software.amazon.cryptography.materialproviders.internaldafny.types.CommitmentPolicy.create_DBE(software.amazon.cryptography.materialproviders.internaldafny.types.DBECommitmentPolicy.create());
      }
    }
    public static void WriteStuff()
    {
      Dafny.ISequence<JSON_mValues_Compile._IJSON> _576_tests;
      _576_tests = SortedSets.__default.SetToSequence<JSON_mValues_Compile._IJSON>(CompleteVectors_Compile.__default.AllPositiveKeyringTests);
      Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _577_testsJSON;
      _577_testsJSON = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements();
      BigInteger _hi6 = new BigInteger((_576_tests).Count);
      for (BigInteger _578_i = BigInteger.Zero; _578_i < _hi6; _578_i++) {
        Dafny.ISequence<char> _579_name;
        Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _580_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
        Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _out78;
        _out78 = UUID.__default.GenerateUUID();
        _580_valueOrError0 = _out78;
        if (!(!((_580_valueOrError0).IsFailure()))) {
          throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CompleteVectors.dfy(281,15): " + _580_valueOrError0);}
        _579_name = (_580_valueOrError0).Extract();
        _577_testsJSON = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.Concat(_577_testsJSON, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(_579_name, (_576_tests).Select(_578_i))));
      }
      JSON_mValues_Compile._IJSON _581_mplEncryptManifies;
      _581_mplEncryptManifies = JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("tests"), JSON_mValues_Compile.JSON.create_Object(_577_testsJSON))));
      Dafny.ISequence<byte> _582_mplEncryptManifiesBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> _583_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.Default(Dafny.Sequence<byte>.Empty);
      _583_valueOrError1 = JSON_mAPI_Compile.__default.Serialize(_581_mplEncryptManifies);
      if (!(!((_583_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CompleteVectors.dfy(290,32): " + _583_valueOrError1);}
      _582_mplEncryptManifiesBytes = (_583_valueOrError1).Extract();
      Dafny.ISequence<byte> _584_mplEncryptManifiesBv;
      _584_mplEncryptManifiesBv = JSONHelpers_Compile.__default.BytesBv(_582_mplEncryptManifiesBytes);
      _System._ITuple0 _585___v3;
      Wrappers_Compile._IResult<_System._ITuple0, Dafny.ISequence<char>> _586_valueOrError2 = Wrappers_Compile.Result<_System._ITuple0, Dafny.ISequence<char>>.Default(_System.Tuple0.Default());
      Wrappers_Compile._IResult<_System._ITuple0, Dafny.ISequence<char>> _out79;
      _out79 = FileIO_Compile.__default.WriteBytesToFile(Dafny.Sequence<char>.FromString("dafny/TestVectorsAwsCryptographicMaterialProviders/test/test.json"), _584_mplEncryptManifiesBv);
      _586_valueOrError2 = _out79;
      if (!(!((_586_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/CompleteVectors.dfy(293,10): " + _586_valueOrError2);}
      _585___v3 = (_586_valueOrError2).Extract();
    }
    public static Dafny.ISet<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo> ESDKAlgorithmSuites { get {
      return ((System.Func<Dafny.ISet<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo>>)(() => {
        var _coll5 = new System.Collections.Generic.List<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo>();
        foreach (software.amazon.cryptography.materialproviders.internaldafny.types._IESDKAlgorithmSuiteId _compr_5 in software.amazon.cryptography.materialproviders.internaldafny.types.ESDKAlgorithmSuiteId.AllSingletonConstructors) {
          software.amazon.cryptography.materialproviders.internaldafny.types._IESDKAlgorithmSuiteId _587_id = (software.amazon.cryptography.materialproviders.internaldafny.types._IESDKAlgorithmSuiteId)_compr_5;
          if (true) {
            _coll5.Add(AlgorithmSuites_Compile.__default.GetESDKSuite(_587_id));
          }
        }
        return Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo>.FromCollection(_coll5);
      }))();
    } }
    public static Dafny.ISet<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo> DBEAlgorithmSuites { get {
      return ((System.Func<Dafny.ISet<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo>>)(() => {
        var _coll6 = new System.Collections.Generic.List<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo>();
        foreach (software.amazon.cryptography.materialproviders.internaldafny.types._IDBEAlgorithmSuiteId _compr_6 in software.amazon.cryptography.materialproviders.internaldafny.types.DBEAlgorithmSuiteId.AllSingletonConstructors) {
          software.amazon.cryptography.materialproviders.internaldafny.types._IDBEAlgorithmSuiteId _588_id = (software.amazon.cryptography.materialproviders.internaldafny.types._IDBEAlgorithmSuiteId)_compr_6;
          if (true) {
            _coll6.Add(AlgorithmSuites_Compile.__default.GetDBESuite(_588_id));
          }
        }
        return Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo>.FromCollection(_coll6);
      }))();
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> aesPersistentKeyNames { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("aes-128"), Dafny.Sequence<char>.FromString("aes-192"), Dafny.Sequence<char>.FromString("aes-256"));
    } }
    public static Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON> AllRawAES { get {
      return ((System.Func<Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>>)(() => {
        var _coll7 = new System.Collections.Generic.List<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>();
        foreach (Dafny.ISequence<char> _compr_7 in (CompleteVectors_Compile.__default.aesPersistentKeyNames).Elements) {
          Dafny.ISequence<char> _589_key = (Dafny.ISequence<char>)_compr_7;
          if ((CompleteVectors_Compile.__default.aesPersistentKeyNames).Contains(_589_key)) {
            _coll7.Add(Dafny.Helpers.Let<JSON_mValues_Compile._IJSON, CompleteVectors_Compile._IPositiveKeyDescriptionJSON>(JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("raw"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("encryption-algorithm"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("aes"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("provider-id"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("aws-raw-vectors-persistent-"), _589_key))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("key"), JSON_mValues_Compile.JSON.create_String(_589_key)))), _pat_let13_0 => Dafny.Helpers.Let<JSON_mValues_Compile._IJSON, CompleteVectors_Compile._IPositiveKeyDescriptionJSON>(_pat_let13_0, _590_keyDescription => CompleteVectors_Compile.PositiveKeyDescriptionJSON.create(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Generated RawAES "), _589_key), _590_keyDescription, _590_keyDescription))));
          }
        }
        return Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.FromCollection(_coll7);
      }))();
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> rsaPersistentKeyNamesWithoutPublicPrivate { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("rsa-4096"));
    } }
    public static Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON> AllRawRSA { get {
      return ((System.Func<Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>>)(() => {
        var _coll8 = new System.Collections.Generic.List<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>();
        foreach (Dafny.ISequence<char> _compr_8 in (CompleteVectors_Compile.__default.rsaPersistentKeyNamesWithoutPublicPrivate).Elements) {
          Dafny.ISequence<char> _591_key = (Dafny.ISequence<char>)_compr_8;
          foreach (software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme _compr_9 in software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme.AllSingletonConstructors) {
            software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme _592_padding = (software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme)_compr_9;
            if ((CompleteVectors_Compile.__default.rsaPersistentKeyNamesWithoutPublicPrivate).Contains(_591_key)) {
              _coll8.Add(Dafny.Helpers.Let<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, CompleteVectors_Compile._IPositiveKeyDescriptionJSON>(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("raw"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("encryption-algorithm"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("rsa"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("provider-id"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("aws-raw-vectors-persistent-"), _591_key))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("padding-algorithm"), JSON_mValues_Compile.JSON.create_String(((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme, Dafny.ISequence<char>>)((_source19) => {
  if (_source19.is_PKCS1) {
    return Dafny.Sequence<char>.FromString("pkcs1");
  } else if (_source19.is_OAEP__SHA1__MGF1) {
    return Dafny.Sequence<char>.FromString("oaep-mgf1");
  } else if (_source19.is_OAEP__SHA256__MGF1) {
    return Dafny.Sequence<char>.FromString("oaep-mgf1");
  } else if (_source19.is_OAEP__SHA384__MGF1) {
    return Dafny.Sequence<char>.FromString("oaep-mgf1");
  } else {
    return Dafny.Sequence<char>.FromString("oaep-mgf1");
  }
}))(_592_padding))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("padding-hash"), JSON_mValues_Compile.JSON.create_String(((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme, Dafny.ISequence<char>>)((_source20) => {
  if (_source20.is_PKCS1) {
    return Dafny.Sequence<char>.FromString("sha1");
  } else if (_source20.is_OAEP__SHA1__MGF1) {
    return Dafny.Sequence<char>.FromString("sha1");
  } else if (_source20.is_OAEP__SHA256__MGF1) {
    return Dafny.Sequence<char>.FromString("sha256");
  } else if (_source20.is_OAEP__SHA384__MGF1) {
    return Dafny.Sequence<char>.FromString("sha384");
  } else {
    return Dafny.Sequence<char>.FromString("sha512");
  }
}))(_592_padding)))), _pat_let14_0 => Dafny.Helpers.Let<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, CompleteVectors_Compile._IPositiveKeyDescriptionJSON>(_pat_let14_0, _593_sharedOptions => CompleteVectors_Compile.PositiveKeyDescriptionJSON.create(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Generated RawRSA "), _591_key), Dafny.Sequence<char>.FromString(" ")), ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IPaddingScheme, Dafny.ISequence<char>>)((_source21) => {
  if (_source21.is_PKCS1) {
    return Dafny.Sequence<char>.FromString("pkcs1-sha1");
  } else if (_source21.is_OAEP__SHA1__MGF1) {
    return Dafny.Sequence<char>.FromString("oaep-mgf1-sha1");
  } else if (_source21.is_OAEP__SHA256__MGF1) {
    return Dafny.Sequence<char>.FromString("oaep-mgf1-sha256");
  } else if (_source21.is_OAEP__SHA384__MGF1) {
    return Dafny.Sequence<char>.FromString("oaep-mgf1-sha384");
  } else {
    return Dafny.Sequence<char>.FromString("oaep-mgf1-sha512");
  }
}))(_592_padding)), JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.Concat(_593_sharedOptions, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("key"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.Concat(_591_key, Dafny.Sequence<char>.FromString("-public"))))))), JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.Concat(_593_sharedOptions, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("key"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.Concat(_591_key, Dafny.Sequence<char>.FromString("-private")))))))))));
            }
          }
        }
        return Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.FromCollection(_coll8);
      }))();
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> AllAwsKMSKeys { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("us-west-2-decryptable"), Dafny.Sequence<char>.FromString("us-west-2-mrk"));
    } }
    public static Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON> AllKMSInfo { get {
      return ((System.Func<Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>>)(() => {
        var _coll9 = new System.Collections.Generic.List<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>();
        foreach (Dafny.ISequence<char> _compr_10 in (CompleteVectors_Compile.__default.AllAwsKMSKeys).Elements) {
          Dafny.ISequence<char> _594_key = (Dafny.ISequence<char>)_compr_10;
          if ((CompleteVectors_Compile.__default.AllAwsKMSKeys).Contains(_594_key)) {
            _coll9.Add(Dafny.Helpers.Let<JSON_mValues_Compile._IJSON, CompleteVectors_Compile._IPositiveKeyDescriptionJSON>(JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("aws-kms"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("key"), JSON_mValues_Compile.JSON.create_String(_594_key)))), _pat_let15_0 => Dafny.Helpers.Let<JSON_mValues_Compile._IJSON, CompleteVectors_Compile._IPositiveKeyDescriptionJSON>(_pat_let15_0, _595_keyDescription => CompleteVectors_Compile.PositiveKeyDescriptionJSON.create(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Generated KMS "), _594_key), _595_keyDescription, _595_keyDescription))));
          }
        }
        return Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.FromCollection(_coll9);
      }))();
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> AllAwsKMSMrkKeys { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("us-west-2-mrk"), Dafny.Sequence<char>.FromString("us-east-1-mrk"));
    } }
    public static Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON> AllKmsMrkAware { get {
      return ((System.Func<Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>>)(() => {
        var _coll10 = new System.Collections.Generic.List<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>();
        foreach (Dafny.ISequence<char> _compr_11 in (CompleteVectors_Compile.__default.AllAwsKMSMrkKeys).Elements) {
          Dafny.ISequence<char> _596_encryptKey = (Dafny.ISequence<char>)_compr_11;
          foreach (Dafny.ISequence<char> _compr_12 in (CompleteVectors_Compile.__default.AllAwsKMSMrkKeys).Elements) {
            Dafny.ISequence<char> _597_decryptKey = (Dafny.ISequence<char>)_compr_12;
            if (((CompleteVectors_Compile.__default.AllAwsKMSMrkKeys).Contains(_596_encryptKey)) && ((CompleteVectors_Compile.__default.AllAwsKMSMrkKeys).Contains(_597_decryptKey))) {
              _coll10.Add(CompleteVectors_Compile.PositiveKeyDescriptionJSON.create(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Generated KMS MRK "), _596_encryptKey), Dafny.Sequence<char>.FromString("->")), _597_decryptKey), JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("aws-kms-mrk-aware"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("key"), JSON_mValues_Compile.JSON.create_String(_596_encryptKey)))), JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("aws-kms-mrk-aware"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("key"), JSON_mValues_Compile.JSON.create_String(_597_decryptKey))))));
            }
          }
        }
        return Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.FromCollection(_coll10);
      }))();
    } }
    public static Dafny.ISet<Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>> AllDiscoveryFilters { get {
      return Dafny.Set<Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>>.FromElements(Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>.create_Some(software.amazon.cryptography.materialproviders.internaldafny.types.DiscoveryFilter.create(Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("658956600833")), Dafny.Sequence<char>.FromString("aws"))), Wrappers_Compile.Option<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>.create_None());
    } }
    public static Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON> AllKmsMrkAwareDiscovery { get {
      return ((System.Func<Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>>)(() => {
        var _coll11 = new System.Collections.Generic.List<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>();
        foreach (Dafny.ISequence<char> _compr_13 in (CompleteVectors_Compile.__default.AllAwsKMSMrkKeys).Elements) {
          Dafny.ISequence<char> _598_keyId = (Dafny.ISequence<char>)_compr_13;
          foreach (Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> _compr_14 in (CompleteVectors_Compile.__default.AllDiscoveryFilters).Elements) {
            Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter> _599_filter = (Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IDiscoveryFilter>)_compr_14;
            if (((CompleteVectors_Compile.__default.AllAwsKMSMrkKeys).Contains(_598_keyId)) && ((CompleteVectors_Compile.__default.AllDiscoveryFilters).Contains(_599_filter))) {
              _coll11.Add(CompleteVectors_Compile.PositiveKeyDescriptionJSON.create(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Discovery KMS MRK "), _598_keyId), Dafny.Sequence<char>.FromString("->")), (((_599_filter).is_Some) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Filter "), ((_599_filter).dtor_value).dtor_partition), Dafny.Sequence<char>.FromString(" ")), Seq_Compile.__default.Flatten<char>(((_599_filter).dtor_value).dtor_accountIds))) : (Dafny.Sequence<char>.FromString("No Filter")))), JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("aws-kms-mrk-aware"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("key"), JSON_mValues_Compile.JSON.create_String(_598_keyId)))), (((_599_filter).is_Some) ? (JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("aws-kms-mrk-aware-discovery"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("default-mrk-region"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("us-west-2"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("aws-kms-discovery-filter"), JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("partition"), JSON_mValues_Compile.JSON.create_String(((_599_filter).dtor_value).dtor_partition)), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("account-ids"), JSON_mValues_Compile.JSON.create_Array(Seq_Compile.__default.Map<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>(((System.Func<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>)((_600_s) => {
  return JSON_mValues_Compile.JSON.create_String(_600_s);
})), ((_599_filter).dtor_value).dtor_accountIds))))))))) : (JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("aws-kms-mrk-aware-discovery"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("default-mrk-region"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("us-west-2")))))))));
            }
          }
        }
        return Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.FromCollection(_coll11);
      }))();
    } }
    public static Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON> AllHierarchy { get {
      return ((System.Func<Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>>)(() => {
        var _coll12 = new System.Collections.Generic.List<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>();
        foreach (Dafny.ISequence<char> _compr_15 in (Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("static-branch-key-1"))).Elements) {
          Dafny.ISequence<char> _601_keyId = (Dafny.ISequence<char>)_compr_15;
          if ((Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("static-branch-key-1"))).Contains(_601_keyId)) {
            _coll12.Add(CompleteVectors_Compile.PositiveKeyDescriptionJSON.create(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Hierarchy KMS "), _601_keyId), JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("aws-kms-hierarchy"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("key"), JSON_mValues_Compile.JSON.create_String(_601_keyId)))), JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("aws-kms-hierarchy"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("key"), JSON_mValues_Compile.JSON.create_String(_601_keyId))))));
          }
        }
        return Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.FromCollection(_coll12);
      }))();
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> AllKmsRsaKeys { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("us-west-2-rsa-mrk"));
    } }
    public static Dafny.ISet<Dafny.ISequence<char>> AllEncryptionAlgorithmSpec { get {
      return ((System.Func<Dafny.ISet<Dafny.ISequence<char>>>)(() => {
        var _coll13 = new System.Collections.Generic.List<Dafny.ISequence<char>>();
        foreach (software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec _compr_16 in software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.AllSingletonConstructors) {
          software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec _602_e = (software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec)_compr_16;
          if (!((_602_e).is_SYMMETRIC__DEFAULT)) {
            _coll13.Add(((System.Func<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec, Dafny.ISequence<char>>)((_source22) => {
              if (_source22.is_RSAES__OAEP__SHA__1) {
                return Dafny.Sequence<char>.FromString("RSAES_OAEP_SHA_1");
              } else {
                return Dafny.Sequence<char>.FromString("RSAES_OAEP_SHA_256");
              }
            }))(_602_e));
          }
        }
        return Dafny.Set<Dafny.ISequence<char>>.FromCollection(_coll13);
      }))();
    } }
    public static Dafny.ISequence<char> KmsRsa { get {
      return Dafny.Sequence<char>.FromString("KMS RSA ");
    } }
    public static Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON> AllKmsRsa { get {
      return ((System.Func<Dafny.ISet<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>>)(() => {
        var _coll14 = new System.Collections.Generic.List<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>();
        foreach (Dafny.ISequence<char> _compr_17 in (CompleteVectors_Compile.__default.AllKmsRsaKeys).Elements) {
          Dafny.ISequence<char> _603_keyId = (Dafny.ISequence<char>)_compr_17;
          foreach (Dafny.ISequence<char> _compr_18 in (CompleteVectors_Compile.__default.AllEncryptionAlgorithmSpec).Elements) {
            Dafny.ISequence<char> _604_algorithmSpec = (Dafny.ISequence<char>)_compr_18;
            if (((CompleteVectors_Compile.__default.AllKmsRsaKeys).Contains(_603_keyId)) && ((CompleteVectors_Compile.__default.AllEncryptionAlgorithmSpec).Contains(_604_algorithmSpec))) {
              _coll14.Add(CompleteVectors_Compile.PositiveKeyDescriptionJSON.create(Dafny.Sequence<char>.Concat(CompleteVectors_Compile.__default.KmsRsa, _603_keyId), JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("aws-kms-rsa"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("key"), JSON_mValues_Compile.JSON.create_String(_603_keyId)), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("encryption-algorithm"), JSON_mValues_Compile.JSON.create_String(_604_algorithmSpec)))), JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("aws-kms-rsa"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("key"), JSON_mValues_Compile.JSON.create_String(_603_keyId)), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("encryption-algorithm"), JSON_mValues_Compile.JSON.create_String(_604_algorithmSpec))))));
            }
          }
        }
        return Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.FromCollection(_coll14);
      }))();
    } }
    public static Dafny.ISet<JSON_mValues_Compile._IJSON> AllPositiveKeyringTests { get {
      return ((System.Func<Dafny.ISet<JSON_mValues_Compile._IJSON>>)(() => {
        var _coll15 = new System.Collections.Generic.List<JSON_mValues_Compile._IJSON>();
        foreach (CompleteVectors_Compile._IPositiveKeyDescriptionJSON _compr_19 in (Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(CompleteVectors_Compile.__default.AllKMSInfo, CompleteVectors_Compile.__default.AllKmsMrkAware), CompleteVectors_Compile.__default.AllKmsMrkAwareDiscovery), CompleteVectors_Compile.__default.AllRawAES), CompleteVectors_Compile.__default.AllRawRSA), CompleteVectors_Compile.__default.AllHierarchy), CompleteVectors_Compile.__default.AllKmsRsa)).Elements) {
          CompleteVectors_Compile._IPositiveKeyDescriptionJSON _605_postiveKeyDescription = (CompleteVectors_Compile._IPositiveKeyDescriptionJSON)_compr_19;
          foreach (software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _compr_20 in (Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo>.Union(CompleteVectors_Compile.__default.ESDKAlgorithmSuites, CompleteVectors_Compile.__default.DBEAlgorithmSuites)).Elements) {
            software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _606_algorithmSuite = (software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo)_compr_20;
            if ((((Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(Dafny.Set<CompleteVectors_Compile._IPositiveKeyDescriptionJSON>.Union(CompleteVectors_Compile.__default.AllKMSInfo, CompleteVectors_Compile.__default.AllKmsMrkAware), CompleteVectors_Compile.__default.AllKmsMrkAwareDiscovery), CompleteVectors_Compile.__default.AllRawAES), CompleteVectors_Compile.__default.AllRawRSA), CompleteVectors_Compile.__default.AllHierarchy), CompleteVectors_Compile.__default.AllKmsRsa)).Contains(_605_postiveKeyDescription)) && ((Dafny.Set<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo>.Union(CompleteVectors_Compile.__default.ESDKAlgorithmSuites, CompleteVectors_Compile.__default.DBEAlgorithmSuites)).Contains(_606_algorithmSuite))) && (!(((((_605_postiveKeyDescription).dtor_description).Take(new BigInteger((CompleteVectors_Compile.__default.KmsRsa).Count))).Equals(CompleteVectors_Compile.__default.KmsRsa)) && (((_606_algorithmSuite).dtor_signature).is_ECDSA)))) {
              _coll15.Add(Dafny.Helpers.Let<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>(HexStrings_Compile.__default.ToHexString((_606_algorithmSuite).dtor_binaryId), _pat_let16_0 => Dafny.Helpers.Let<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>(_pat_let16_0, _607_id => JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("type"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.FromString("positive-keyring"))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("description"), JSON_mValues_Compile.JSON.create_String(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat((_605_postiveKeyDescription).dtor_description, Dafny.Sequence<char>.FromString(" ")), _607_id))), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("algorithmSuiteId"), JSON_mValues_Compile.JSON.create_String(_607_id)), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("encryptionContext"), JSON_mValues_Compile.JSON.create_Object(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.FromElements())), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("requiredEncryptionContextKeys"), JSON_mValues_Compile.JSON.create_Array(Dafny.Sequence<JSON_mValues_Compile._IJSON>.FromElements())), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("encryptKeyDescription"), (_605_postiveKeyDescription).dtor_encrypt), _System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(Dafny.Sequence<char>.FromString("decryptKeyDescription"), (_605_postiveKeyDescription).dtor_decrypt))))));
            }
          }
        }
        return Dafny.Set<JSON_mValues_Compile._IJSON>.FromCollection(_coll15);
      }))();
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> AwsPartitions { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("aws"));
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> AWSAccounts { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("658956600833"));
    } }
  }
} // end of namespace CompleteVectors_Compile
namespace ParseJsonManifests_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.ISequence<TestVectors_Compile._IEncryptTestVector>, Dafny.ISequence<char>> BuildEncryptTestVector(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient keys, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj)
    {
      if ((new BigInteger((obj).Count)).Sign == 0) {
        return Wrappers_Compile.Result<Dafny.ISequence<TestVectors_Compile._IEncryptTestVector>, Dafny.ISequence<char>>.create_Success(Dafny.Sequence<TestVectors_Compile._IEncryptTestVector>.FromElements());
      } else {
        Dafny.ISequence<char> _608_name = ((obj).Select(BigInteger.Zero)).dtor__0;
        Wrappers_Compile._IResult<TestVectors_Compile._IEncryptTestVector, Dafny.ISequence<char>> _609_valueOrError0 = ParseJsonManifests_Compile.__default.ToEncryptTestVector(keys, _608_name, ((obj).Select(BigInteger.Zero)).dtor__1);
        if ((_609_valueOrError0).IsFailure()) {
          return (_609_valueOrError0).PropagateFailure<Dafny.ISequence<TestVectors_Compile._IEncryptTestVector>>();
        } else {
          TestVectors_Compile._IEncryptTestVector _610_encryptVector = (_609_valueOrError0).Extract();
          Wrappers_Compile._IResult<Dafny.ISequence<TestVectors_Compile._IEncryptTestVector>, Dafny.ISequence<char>> _611_valueOrError1 = ParseJsonManifests_Compile.__default.BuildEncryptTestVector(keys, (obj).Drop(BigInteger.One));
          if ((_611_valueOrError1).IsFailure()) {
            return (_611_valueOrError1).PropagateFailure<Dafny.ISequence<TestVectors_Compile._IEncryptTestVector>>();
          } else {
            Dafny.ISequence<TestVectors_Compile._IEncryptTestVector> _612_tail = (_611_valueOrError1).Extract();
            return Wrappers_Compile.Result<Dafny.ISequence<TestVectors_Compile._IEncryptTestVector>, Dafny.ISequence<char>>.create_Success(Dafny.Sequence<TestVectors_Compile._IEncryptTestVector>.Concat(Dafny.Sequence<TestVectors_Compile._IEncryptTestVector>.FromElements(_610_encryptVector), _612_tail));
          }
        }
      }
    }
    public static Wrappers_Compile._IResult<TestVectors_Compile._IEncryptTestVector, Dafny.ISequence<char>> ToEncryptTestVector(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient keys, Dafny.ISequence<char> name, JSON_mValues_Compile._IJSON obj)
    {
      Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _613_valueOrError0 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>((obj).is_Object, Dafny.Sequence<char>.FromString("EncryptTestVector not an object"));
      if ((_613_valueOrError0).IsFailure()) {
        return (_613_valueOrError0).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
      } else {
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _614_obj = (obj).dtor_obj;
        Dafny.ISequence<char> _615_typString = Dafny.Sequence<char>.FromString("type");
        Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _616_valueOrError1 = JSONHelpers_Compile.__default.GetString(_615_typString, _614_obj);
        if ((_616_valueOrError1).IsFailure()) {
          return (_616_valueOrError1).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
        } else {
          Dafny.ISequence<char> _617_typ = (_616_valueOrError1).Extract();
          Wrappers_Compile._IOption<Dafny.ISequence<char>> _618_description = (JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("description"), _614_obj)).ToOption();
          Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>, Dafny.ISequence<char>> _619_valueOrError2 = JSONHelpers_Compile.__default.SmallObjectToStringStringMap(Dafny.Sequence<char>.FromString("encryptionContext"), _614_obj);
          if ((_619_valueOrError2).IsFailure()) {
            return (_619_valueOrError2).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
          } else {
            Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> _620_encryptionContextStrings = (_619_valueOrError2).Extract();
            Wrappers_Compile._IResult<Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>>, Dafny.ISequence<char>> _621_valueOrError3 = JSONHelpers_Compile.__default.utf8EncodeMap(_620_encryptionContextStrings);
            if ((_621_valueOrError3).IsFailure()) {
              return (_621_valueOrError3).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
            } else {
              Dafny.IMap<Dafny.ISequence<byte>,Dafny.ISequence<byte>> _622_encryptionContext = (_621_valueOrError3).Extract();
              Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _623_valueOrError4 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("algorithmSuiteId"), _614_obj);
              if ((_623_valueOrError4).IsFailure()) {
                return (_623_valueOrError4).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
              } else {
                Dafny.ISequence<char> _624_algorithmSuiteHex = (_623_valueOrError4).Extract();
                Wrappers_Compile._IOutcome<Dafny.ISequence<char>> _625_valueOrError5 = Wrappers_Compile.__default.Need<Dafny.ISequence<char>>(HexStrings_Compile.__default.IsLooseHexString(_624_algorithmSuiteHex), Dafny.Sequence<char>.FromString("Not hex encoded binnary"));
                if ((_625_valueOrError5).IsFailure()) {
                  return (_625_valueOrError5).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                } else {
                  Dafny.ISequence<byte> _626_binaryId = HexStrings_Compile.__default.FromHexString(_624_algorithmSuiteHex);
                  Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, Dafny.ISequence<char>> _627_valueOrError6 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo, software.amazon.cryptography.materialproviders.internaldafny.types._IError>.MapFailure<Dafny.ISequence<char>>(AlgorithmSuites_Compile.__default.GetAlgorithmSuiteInfo(_626_binaryId), Dafny.Helpers.Id<Func<Dafny.ISequence<char>, Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, Dafny.ISequence<char>>>>((_628_algorithmSuiteHex) => ((System.Func<software.amazon.cryptography.materialproviders.internaldafny.types._IError, Dafny.ISequence<char>>)((_629_e) => {
                    return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Invalid Suite:"), _628_algorithmSuiteHex);
                  })))(_624_algorithmSuiteHex));
                  if ((_627_valueOrError6).IsFailure()) {
                    return (_627_valueOrError6).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                  } else {
                    software.amazon.cryptography.materialproviders.internaldafny.types._IAlgorithmSuiteInfo _630_algorithmSuite = (_627_valueOrError6).Extract();
                    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _631_keysAsStrings = (JSONHelpers_Compile.__default.GetArrayString(Dafny.Sequence<char>.FromString("requiredEncryptionContextKeys"), _614_obj)).ToOption();
                    Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>>, Dafny.ISequence<char>> _632_valueOrError7 = (((_631_keysAsStrings).is_Some) ? (Dafny.Helpers.Let<Wrappers_Compile._IResult<Dafny.ISequence<Dafny.ISequence<byte>>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>>, Dafny.ISequence<char>>>(JSONHelpers_Compile.__default.utf8EncodeSeq((_631_keysAsStrings).dtor_value), _pat_let17_0 => Dafny.Helpers.Let<Wrappers_Compile._IResult<Dafny.ISequence<Dafny.ISequence<byte>>, Dafny.ISequence<char>>, Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>>, Dafny.ISequence<char>>>(_pat_let17_0, _633_result => (((_633_result).is_Success) ? (Wrappers_Compile.Result<Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>>, Dafny.ISequence<char>>.create_Success(Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<byte>>>.create_Some((_633_result).dtor_value))) : (Wrappers_Compile.Result<Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>>, Dafny.ISequence<char>>.create_Failure((_633_result).dtor_error)))))) : (Wrappers_Compile.Result<Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>>, Dafny.ISequence<char>>.create_Success(Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<byte>>>.create_None())));
                    if ((_632_valueOrError7).IsFailure()) {
                      return (_632_valueOrError7).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                    } else {
                      Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> _634_requiredEncryptionContextKeys = (_632_valueOrError7).Extract();
                      software.amazon.cryptography.materialproviders.internaldafny.types._ICommitmentPolicy _635_commitmentPolicy = CompleteVectors_Compile.__default.GetCompatableCommitmentPolicy(_630_algorithmSuite);
                      Wrappers_Compile._IOption<long> _636_maxPlaintextLength = Wrappers_Compile.Option<long>.create_None();
                      if (object.Equals(_617_typ, Dafny.Sequence<char>.FromString("positive-keyring"))) {
                        Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _637_valueOrError8 = JSONHelpers_Compile.__default.Get(Dafny.Sequence<char>.FromString("encryptKeyDescription"), _614_obj);
                        if ((_637_valueOrError8).IsFailure()) {
                          return (_637_valueOrError8).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                        } else {
                          JSON_mValues_Compile._IJSON _638_encryptKeyDescriptionObject = (_637_valueOrError8).Extract();
                          Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _639_valueOrError9 = JSONHelpers_Compile.__default.Get(Dafny.Sequence<char>.FromString("decryptKeyDescription"), _614_obj);
                          if ((_639_valueOrError9).IsFailure()) {
                            return (_639_valueOrError9).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                          } else {
                            JSON_mValues_Compile._IJSON _640_decryptKeyDescriptionObject = (_639_valueOrError9).Extract();
                            Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _641_valueOrError10 = Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.MapFailure<Dafny.ISequence<char>>(JSON_mAPI_Compile.__default.Serialize(_638_encryptKeyDescriptionObject), ((System.Func<JSON_mErrors_Compile._ISerializationError, Dafny.ISequence<char>>)((_642_e) => {
                              return (_642_e)._ToString();
                            })));
                            if ((_641_valueOrError10).IsFailure()) {
                              return (_641_valueOrError10).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                            } else {
                              Dafny.ISequence<byte> _643_encryptStr = (_641_valueOrError10).Extract();
                              Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _644_valueOrError11 = Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.MapFailure<Dafny.ISequence<char>>(JSON_mAPI_Compile.__default.Serialize(_640_decryptKeyDescriptionObject), ((System.Func<JSON_mErrors_Compile._ISerializationError, Dafny.ISequence<char>>)((_645_e) => {
                                return (_645_e)._ToString();
                              })));
                              if ((_644_valueOrError11).IsFailure()) {
                                return (_644_valueOrError11).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                              } else {
                                Dafny.ISequence<byte> _646_decryptStr = (_644_valueOrError11).Extract();
                                Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput, Dafny.ISequence<char>> _647_valueOrError12 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.MapFailure<Dafny.ISequence<char>>((keys).GetKeyDescription(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionInput.create(_643_encryptStr)), ParseJsonManifests_Compile.__default.ErrorToString);
                                if ((_647_valueOrError12).IsFailure()) {
                                  return (_647_valueOrError12).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                                } else {
                                  software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput _648_encryptKeyDescription = (_647_valueOrError12).Extract();
                                  Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput, Dafny.ISequence<char>> _649_valueOrError13 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.MapFailure<Dafny.ISequence<char>>((keys).GetKeyDescription(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionInput.create(_646_decryptStr)), ParseJsonManifests_Compile.__default.ErrorToString);
                                  if ((_649_valueOrError13).IsFailure()) {
                                    return (_649_valueOrError13).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                                  } else {
                                    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput _650_decryptKeyDescription = (_649_valueOrError13).Extract();
                                    return Wrappers_Compile.Result<TestVectors_Compile._IEncryptTestVector, Dafny.ISequence<char>>.create_Success(TestVectors_Compile.EncryptTestVector.create_PositiveEncryptKeyringVector(name, _618_description, _622_encryptionContext, _635_commitmentPolicy, _630_algorithmSuite, _636_maxPlaintextLength, _634_requiredEncryptionContextKeys, (_648_encryptKeyDescription).dtor_keyDescription, (_650_decryptKeyDescription).dtor_keyDescription));
                                  }
                                }
                              }
                            }
                          }
                        }
                      } else if (object.Equals(_617_typ, Dafny.Sequence<char>.FromString("negative-keyring"))) {
                        Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, Dafny.ISequence<char>> _651_valueOrError14 = JSONHelpers_Compile.__default.Get(Dafny.Sequence<char>.FromString("keyDescription"), _614_obj);
                        if ((_651_valueOrError14).IsFailure()) {
                          return (_651_valueOrError14).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                        } else {
                          JSON_mValues_Compile._IJSON _652_keyDescriptionObject = (_651_valueOrError14).Extract();
                          Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _653_valueOrError15 = Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.MapFailure<Dafny.ISequence<char>>(JSON_mAPI_Compile.__default.Serialize(_652_keyDescriptionObject), ((System.Func<JSON_mErrors_Compile._ISerializationError, Dafny.ISequence<char>>)((_654_e) => {
                            return (_654_e)._ToString();
                          })));
                          if ((_653_valueOrError15).IsFailure()) {
                            return (_653_valueOrError15).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                          } else {
                            Dafny.ISequence<byte> _655_keyStr = (_653_valueOrError15).Extract();
                            Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput, Dafny.ISequence<char>> _656_valueOrError16 = Wrappers_Compile.Result<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>.MapFailure<Dafny.ISequence<char>>((keys).GetKeyDescription(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionInput.create(_655_keyStr)), ParseJsonManifests_Compile.__default.ErrorToString);
                            if ((_656_valueOrError16).IsFailure()) {
                              return (_656_valueOrError16).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                            } else {
                              software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput _657_keyDescription = (_656_valueOrError16).Extract();
                              Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _658_valueOrError17 = JSONHelpers_Compile.__default.GetString(Dafny.Sequence<char>.FromString("errorDescription"), _614_obj);
                              if ((_658_valueOrError17).IsFailure()) {
                                return (_658_valueOrError17).PropagateFailure<TestVectors_Compile._IEncryptTestVector>();
                              } else {
                                Dafny.ISequence<char> _659_errorDescription = (_658_valueOrError17).Extract();
                                return Wrappers_Compile.Result<TestVectors_Compile._IEncryptTestVector, Dafny.ISequence<char>>.create_Success(TestVectors_Compile.EncryptTestVector.create_NegativeEncryptKeyringVector(name, _618_description, _622_encryptionContext, _635_commitmentPolicy, _630_algorithmSuite, _636_maxPlaintextLength, _634_requiredEncryptionContextKeys, _659_errorDescription, (_657_keyDescription).dtor_keyDescription));
                              }
                            }
                          }
                        }
                      } else {
                        return Wrappers_Compile.Result<TestVectors_Compile._IEncryptTestVector, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Unsupported EncryptTestVector type:"), _617_typ));
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    public static Dafny.ISequence<char> ErrorToString(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError e) {
      software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError _source23 = e;
      if (_source23.is_KeyVectorException) {
        Dafny.ISequence<char> _660___mcc_h0 = _source23.dtor_message;
        Dafny.ISequence<char> _661_message = _660___mcc_h0;
        return _661_message;
      } else if (_source23.is_AwsCryptographyMaterialProviders) {
        software.amazon.cryptography.materialproviders.internaldafny.types._IError _662___mcc_h2 = _source23.dtor_AwsCryptographyMaterialProviders;
        software.amazon.cryptography.materialproviders.internaldafny.types._IError _663_mplError = _662___mcc_h2;
        software.amazon.cryptography.materialproviders.internaldafny.types._IError _source24 = _663_mplError;
        if (_source24.is_AwsCryptographicMaterialProvidersException) {
          Dafny.ISequence<char> _664___mcc_h12 = _source24.dtor_message;
          Dafny.ISequence<char> _665_message = _664___mcc_h12;
          return _665_message;
        } else if (_source24.is_EntryAlreadyExists) {
          Dafny.ISequence<char> _666___mcc_h14 = _source24.dtor_message;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_EntryDoesNotExist) {
          Dafny.ISequence<char> _667___mcc_h16 = _source24.dtor_message;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_InvalidAlgorithmSuiteInfo) {
          Dafny.ISequence<char> _668___mcc_h18 = _source24.dtor_message;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_InvalidAlgorithmSuiteInfoOnDecrypt) {
          Dafny.ISequence<char> _669___mcc_h20 = _source24.dtor_message;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_InvalidAlgorithmSuiteInfoOnEncrypt) {
          Dafny.ISequence<char> _670___mcc_h22 = _source24.dtor_message;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_InvalidDecryptionMaterials) {
          Dafny.ISequence<char> _671___mcc_h24 = _source24.dtor_message;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_InvalidDecryptionMaterialsTransition) {
          Dafny.ISequence<char> _672___mcc_h26 = _source24.dtor_message;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_InvalidEncryptionMaterials) {
          Dafny.ISequence<char> _673___mcc_h28 = _source24.dtor_message;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_InvalidEncryptionMaterialsTransition) {
          Dafny.ISequence<char> _674___mcc_h30 = _source24.dtor_message;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_AwsCryptographyKeyStore) {
          software.amazon.cryptography.keystore.internaldafny.types._IError _675___mcc_h32 = _source24.dtor_AwsCryptographyKeyStore;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_AwsCryptographyPrimitives) {
          software.amazon.cryptography.primitives.internaldafny.types._IError _676___mcc_h34 = _source24.dtor_AwsCryptographyPrimitives;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_ComAmazonawsDynamodb) {
          software.amazon.cryptography.services.dynamodb.internaldafny.types._IError _677___mcc_h36 = _source24.dtor_ComAmazonawsDynamodb;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_ComAmazonawsKms) {
          software.amazon.cryptography.services.kms.internaldafny.types._IError _678___mcc_h38 = _source24.dtor_ComAmazonawsKms;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else if (_source24.is_CollectionOfErrors) {
          Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types._IError> _679___mcc_h40 = _source24.dtor_list;
          Dafny.ISequence<char> _680___mcc_h41 = _source24.dtor_message;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        } else {
          object _681___mcc_h44 = _source24.dtor_obj;
          return Dafny.Sequence<char>.FromString("Umapped AwsCryptographyMaterialProviders");
        }
      } else if (_source23.is_ComAmazonawsKms) {
        software.amazon.cryptography.services.kms.internaldafny.types._IError _682___mcc_h4 = _source23.dtor_ComAmazonawsKms;
        return Dafny.Sequence<char>.FromString("Umapped KeyVectorException");
      } else if (_source23.is_CollectionOfErrors) {
        Dafny.ISequence<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _683___mcc_h6 = _source23.dtor_list;
        Dafny.ISequence<char> _684___mcc_h7 = _source23.dtor_message;
        return Dafny.Sequence<char>.FromString("Umapped KeyVectorException");
      } else {
        object _685___mcc_h10 = _source23.dtor_obj;
        return Dafny.Sequence<char>.FromString("Umapped KeyVectorException");
      }
    }
  }
} // end of namespace ParseJsonManifests_Compile
namespace TestManifests_Compile {

  public partial class __default {
    public static void StartEncrypt(Dafny.ISequence<char> encryptManifestPath, Dafny.ISequence<char> keysManifiestPath)
    {
      Dafny.ISequence<byte> _686_encryptManifestBv;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _687_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out80;
      _out80 = FileIO_Compile.__default.ReadBytesFromFile(encryptManifestPath);
      _687_valueOrError0 = _out80;
      if (!(!((_687_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestManifests.dfy(28,26): " + _687_valueOrError0);}
      _686_encryptManifestBv = (_687_valueOrError0).Extract();
      Dafny.ISequence<byte> _688_encryptManifestBytes;
      _688_encryptManifestBytes = JSONHelpers_Compile.__default.BvToBytes(_686_encryptManifestBv);
      JSON_mValues_Compile._IJSON _689_encryptManifestJSON;
      Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError> _690_valueOrError1 = Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>.Default(JSON_mValues_Compile.JSON.Default());
      _690_valueOrError1 = JSON_mAPI_Compile.__default.Deserialize(_688_encryptManifestBytes);
      if (!(!((_690_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestManifests.dfy(30,28): " + _690_valueOrError1);}
      _689_encryptManifestJSON = (_690_valueOrError1).Extract();
      if (!((_689_encryptManifestJSON).is_Object)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestManifests.dfy(31,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient _691_keys;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _692_valueOrError2 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> _out81;
      _out81 = software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.__default.KeyVectors(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyVectorsConfig.create(keysManifiestPath));
      _692_valueOrError2 = _out81;
      if (!(!((_692_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestManifests.dfy(33,13): " + _692_valueOrError2);}
      _691_keys = (_692_valueOrError2).Extract();
      Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _693_jsonTests;
      Wrappers_Compile._IResult<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, Dafny.ISequence<char>> _694_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, Dafny.ISequence<char>>.Default(Dafny.Sequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>.Empty);
      _694_valueOrError3 = JSONHelpers_Compile.__default.GetObject(Dafny.Sequence<char>.FromString("tests"), (_689_encryptManifestJSON).dtor_obj);
      if (!(!((_694_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestManifests.dfy(37,18): " + _694_valueOrError3);}
      _693_jsonTests = (_694_valueOrError3).Extract();
      Dafny.ISequence<TestVectors_Compile._IEncryptTestVector> _695_encryptVectors;
      Wrappers_Compile._IResult<Dafny.ISequence<TestVectors_Compile._IEncryptTestVector>, Dafny.ISequence<char>> _696_valueOrError4 = Wrappers_Compile.Result<Dafny.ISequence<TestVectors_Compile._IEncryptTestVector>, Dafny.ISequence<char>>.Default(Dafny.Sequence<TestVectors_Compile._IEncryptTestVector>.Empty);
      _696_valueOrError4 = ParseJsonManifests_Compile.__default.BuildEncryptTestVector(_691_keys, _693_jsonTests);
      if (!(!((_696_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestManifests.dfy(38,23): " + _696_valueOrError4);}
      _695_encryptVectors = (_696_valueOrError4).Extract();
      Dafny.ISequence<TestVectors_Compile._IEncryptTest> _697_encryptTests;
      Wrappers_Compile._IResult<Dafny.ISequence<TestVectors_Compile._IEncryptTest>, Dafny.ISequence<char>> _698_valueOrError5 = Wrappers_Compile.Result<Dafny.ISequence<TestVectors_Compile._IEncryptTest>, Dafny.ISequence<char>>.Default(Dafny.Sequence<TestVectors_Compile._IEncryptTest>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<TestVectors_Compile._IEncryptTest>, Dafny.ISequence<char>> _out82;
      _out82 = TestManifests_Compile.__default.ToEncryptTests(_691_keys, _695_encryptVectors);
      _698_valueOrError5 = _out82;
      if (!(!((_698_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestManifests.dfy(40,21): " + _698_valueOrError5);}
      _697_encryptTests = (_698_valueOrError5).Extract();
      Dafny.ISequence<TestVectors_Compile._IDecryptTest> _699_decryptTests;
      Dafny.ISequence<TestVectors_Compile._IDecryptTest> _out83;
      _out83 = TestManifests_Compile.__default.TestEncrypts(_697_encryptTests, _691_keys);
      _699_decryptTests = _out83;
      Dafny.ISequence<byte> _700___v0;
      Dafny.ISequence<byte> _out84;
      _out84 = TestManifests_Compile.__default.TestDecrypts(_699_decryptTests);
      _700___v0 = _out84;
    }
    public static Dafny.ISequence<TestVectors_Compile._IDecryptTest> TestEncrypts(Dafny.ISequence<TestVectors_Compile._IEncryptTest> tests, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient keys)
    {
      Dafny.ISequence<TestVectors_Compile._IDecryptTest> output = Dafny.Sequence<TestVectors_Compile._IDecryptTest>.Empty;
      bool _701_hasFailure;
      _701_hasFailure = false;
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n=================== Starting Encrypt Tests =================== \n\n")));
      Dafny.ISequence<_System._ITuple2<TestVectors_Compile._IEncryptTest, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>> _702_decryptableTests;
      _702_decryptableTests = Dafny.Sequence<_System._ITuple2<TestVectors_Compile._IEncryptTest, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>>.FromElements();
      BigInteger _hi7 = new BigInteger((tests).Count);
      for (BigInteger _703_i = BigInteger.Zero; _703_i < _hi7; _703_i++) {
        TestVectors_Compile._IEncryptTest _704_test;
        _704_test = (tests).Select(_703_i);
        bool _705_pass;
        Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials> _706_maybeEncryptionMaterials;
        bool _out85;
        Wrappers_Compile._IOption<software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials> _out86;
        TestVectors_Compile.__default.TestGetEncryptionMaterials(_704_test, out _out85, out _out86);
        _705_pass = _out85;
        _706_maybeEncryptionMaterials = _out86;
        if ((_705_pass) && (((_704_test).dtor_vector).is_PositiveEncryptKeyringVector)) {
          _702_decryptableTests = Dafny.Sequence<_System._ITuple2<TestVectors_Compile._IEncryptTest, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>>.Concat(_702_decryptableTests, Dafny.Sequence<_System._ITuple2<TestVectors_Compile._IEncryptTest, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>>.FromElements(_System.Tuple2<TestVectors_Compile._IEncryptTest, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>.create(_704_test, (_706_maybeEncryptionMaterials).dtor_value)));
        } else if (!(_705_pass)) {
          _701_hasFailure = true;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n=================== Completed Encrypt Tests =================== \n\n")));
      if (!(!(_701_hasFailure))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestManifests.dfy(79,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<TestVectors_Compile._IDecryptTest>, Dafny.ISequence<char>> _707_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<TestVectors_Compile._IDecryptTest>, Dafny.ISequence<char>>.Default(Dafny.Sequence<TestVectors_Compile._IDecryptTest>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<TestVectors_Compile._IDecryptTest>, Dafny.ISequence<char>> _out87;
      _out87 = TestManifests_Compile.__default.ToDecryptTests(keys, _702_decryptableTests);
      _707_valueOrError0 = _out87;
      if (!(!((_707_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestManifests.dfy(80,11): " + _707_valueOrError0);}
      output = (_707_valueOrError0).Extract();
      return output;
    }
    public static Dafny.ISequence<byte> TestDecrypts(Dafny.ISequence<TestVectors_Compile._IDecryptTest> tests)
    {
      Dafny.ISequence<byte> manifest = Dafny.Sequence<byte>.Empty;
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n=================== Starting Decrypt Tests =================== \n\n")));
      bool _708_hasFailure;
      _708_hasFailure = false;
      BigInteger _hi8 = new BigInteger((tests).Count);
      for (BigInteger _709_i = BigInteger.Zero; _709_i < _hi8; _709_i++) {
        bool _710_pass;
        bool _out88;
        _out88 = TestVectors_Compile.__default.TestDecryptMaterials((tests).Select(_709_i));
        _710_pass = _out88;
        if (!(_710_pass)) {
          _708_hasFailure = true;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n=================== Completed Decrypt Tests =================== \n\n")));
      if (!(!(_708_hasFailure))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/TestManifests.dfy(104,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      manifest = TestManifests_Compile.__default.ToJSONDecryptManifiest(tests);
      return manifest;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<TestVectors_Compile._IEncryptTest>, Dafny.ISequence<char>> ToEncryptTests(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient keys, Dafny.ISequence<TestVectors_Compile._IEncryptTestVector> encryptVectors)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<TestVectors_Compile._IEncryptTest>, Dafny.ISequence<char>> output = Wrappers_Compile.Result<Dafny.ISequence<TestVectors_Compile._IEncryptTest>, Dafny.ISequence<char>>.Default(Dafny.Sequence<TestVectors_Compile._IEncryptTest>.Empty);
      Dafny.ISequence<TestVectors_Compile._IEncryptTest> _711_encryptTests;
      _711_encryptTests = Dafny.Sequence<TestVectors_Compile._IEncryptTest>.FromElements();
      BigInteger _hi9 = new BigInteger((encryptVectors).Count);
      for (BigInteger _712_i = BigInteger.Zero; _712_i < _hi9; _712_i++) {
        TestVectors_Compile._IEncryptTest _713_test;
        Wrappers_Compile._IResult<TestVectors_Compile._IEncryptTest, Dafny.ISequence<char>> _714_valueOrError0 = default(Wrappers_Compile._IResult<TestVectors_Compile._IEncryptTest, Dafny.ISequence<char>>);
        Wrappers_Compile._IResult<TestVectors_Compile._IEncryptTest, Dafny.ISequence<char>> _out89;
        _out89 = TestVectors_Compile.__default.ToEncryptTest(keys, (encryptVectors).Select(_712_i));
        _714_valueOrError0 = _out89;
        if ((_714_valueOrError0).IsFailure()) {
          output = (_714_valueOrError0).PropagateFailure<Dafny.ISequence<TestVectors_Compile._IEncryptTest>>();
          return output;
        }
        _713_test = (_714_valueOrError0).Extract();
        _711_encryptTests = Dafny.Sequence<TestVectors_Compile._IEncryptTest>.Concat(_711_encryptTests, Dafny.Sequence<TestVectors_Compile._IEncryptTest>.FromElements(_713_test));
      }
      output = Wrappers_Compile.Result<Dafny.ISequence<TestVectors_Compile._IEncryptTest>, Dafny.ISequence<char>>.create_Success(_711_encryptTests);
      return output;
      return output;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<TestVectors_Compile._IDecryptTest>, Dafny.ISequence<char>> ToDecryptTests(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient keys, Dafny.ISequence<_System._ITuple2<TestVectors_Compile._IEncryptTest, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>> tests)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<TestVectors_Compile._IDecryptTest>, Dafny.ISequence<char>> output = Wrappers_Compile.Result<Dafny.ISequence<TestVectors_Compile._IDecryptTest>, Dafny.ISequence<char>>.Default(Dafny.Sequence<TestVectors_Compile._IDecryptTest>.Empty);
      Dafny.ISequence<_System._ITuple2<TestVectors_Compile._IEncryptTest, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>> _715_positiveEncryptTests;
      _715_positiveEncryptTests = Seq_Compile.__default.Filter<_System._ITuple2<TestVectors_Compile._IEncryptTest, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>>(((System.Func<_System._ITuple2<TestVectors_Compile._IEncryptTest, software.amazon.cryptography.materialproviders.internaldafny.types._IEncryptionMaterials>, bool>)((_716_r) => {
        return (((_716_r).dtor__0).dtor_vector).is_PositiveEncryptKeyringVector;
      })), tests);
      Dafny.ISequence<TestVectors_Compile._IDecryptTest> _717_decryptTests;
      _717_decryptTests = Dafny.Sequence<TestVectors_Compile._IDecryptTest>.FromElements();
      BigInteger _hi10 = new BigInteger((_715_positiveEncryptTests).Count);
      for (BigInteger _718_i = BigInteger.Zero; _718_i < _hi10; _718_i++) {
        TestVectors_Compile._IDecryptTest _719_test;
        Wrappers_Compile._IResult<TestVectors_Compile._IDecryptTest, Dafny.ISequence<char>> _720_valueOrError0 = default(Wrappers_Compile._IResult<TestVectors_Compile._IDecryptTest, Dafny.ISequence<char>>);
        Wrappers_Compile._IResult<TestVectors_Compile._IDecryptTest, Dafny.ISequence<char>> _out90;
        _out90 = TestVectors_Compile.__default.ToDecryptTest(keys, ((_715_positiveEncryptTests).Select(_718_i)).dtor__0, ((_715_positiveEncryptTests).Select(_718_i)).dtor__1);
        _720_valueOrError0 = _out90;
        if ((_720_valueOrError0).IsFailure()) {
          output = (_720_valueOrError0).PropagateFailure<Dafny.ISequence<TestVectors_Compile._IDecryptTest>>();
          return output;
        }
        _719_test = (_720_valueOrError0).Extract();
        _717_decryptTests = Dafny.Sequence<TestVectors_Compile._IDecryptTest>.Concat(_717_decryptTests, Dafny.Sequence<TestVectors_Compile._IDecryptTest>.FromElements(_719_test));
      }
      output = Wrappers_Compile.Result<Dafny.ISequence<TestVectors_Compile._IDecryptTest>, Dafny.ISequence<char>>.create_Success(_717_decryptTests);
      return output;
      return output;
    }
    public static Dafny.ISequence<byte> ToJSONDecryptManifiest(Dafny.ISequence<TestVectors_Compile._IDecryptTest> tests) {
      return Dafny.Sequence<byte>.FromElements();
    }
  }
} // end of namespace TestManifests_Compile
namespace WrappedMaterialProvidersMain_Compile {

  public partial class __default {
    public static void CheckKeyrings()
    {
      software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient _721_mpl;
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _722_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IAwsCryptographicMaterialProvidersClient, software.amazon.cryptography.materialproviders.internaldafny.types._IError> _out91;
      _out91 = software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedMaterialProviders(software.amazon.cryptography.materialproviders.internaldafny.wrapped.__default.WrappedDefaultMaterialProvidersConfig());
      _722_valueOrError0 = _out91;
      if (!(!((_722_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/TestVectorsAwsCryptographicMaterialProviders/dafny/TestVectorsAwsCryptographicMaterialProviders/src/Index.dfy(21,12): " + _722_valueOrError0);}
      _721_mpl = (_722_valueOrError0).Extract();
      Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _723_all;
      Dafny.ISequence<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring> _out92;
      _out92 = CreateKeyrings_Compile.__default.CreateAllEncryptDecryptKeyrings();
      _723_all = _out92;
      BigInteger _hi11 = new BigInteger((_723_all).Count);
      for (BigInteger _724_i = BigInteger.Zero; _724_i < _hi11; _724_i++) {
        software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring _725_keyring;
        _725_keyring = (_723_all).Select(_724_i);
        KeyringExpectations_Compile.__default.ExpectAlgorithmSuiteKeyringSuccess(_721_mpl, _725_keyring);
      }
    }
    public static void EncryptTestVectors()
    {
    }
  }
} // end of namespace WrappedMaterialProvidersMain_Compile
namespace _module {

} // end of namespace _module
