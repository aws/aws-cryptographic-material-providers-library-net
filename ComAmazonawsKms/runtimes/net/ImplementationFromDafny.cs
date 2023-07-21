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
// Command Line Options: -stdin -noVerify -vcsCores:2 -compileTarget:cs -spillTargetCode:3 -compile:0 -optimizeErasableDatatypeWrapper:0 -quantifierSyntax:3 -unicodeChar:0 -functionSyntax:3 -useRuntimeLib -out runtimes/net/ImplementationFromDafny -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/src/Index.dfy
// the_program








































module {:extern ""software.amazon.cryptography.services.kms.internaldafny.types""} ComAmazonawsKmsTypes {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8
  datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)

  datatype AlgorithmSpec = RSAES_PKCS1_V1_5 | RSAES_OAEP_SHA_1 | RSAES_OAEP_SHA_256

  type AliasList = seq<AliasListEntry>

  datatype AliasListEntry = AliasListEntry(nameonly AliasName: Option<AliasNameType>, nameonly AliasArn: Option<ArnType>, nameonly TargetKeyId: Option<KeyIdType>, nameonly CreationDate: Option<string>, nameonly LastUpdatedDate: Option<string>)

  type AliasNameType = x: string
    | IsValid_AliasNameType(x)
    witness *

  type ArnType = x: string
    | IsValid_ArnType(x)
    witness *

  type AWSAccountIdType = string

  type BooleanType = bool

  datatype CancelKeyDeletionRequest = CancelKeyDeletionRequest(nameonly KeyId: KeyIdType)

  datatype CancelKeyDeletionResponse = CancelKeyDeletionResponse(nameonly KeyId: Option<KeyIdType>)

  type CiphertextType = x: seq<uint8>
    | IsValid_CiphertextType(x)
    witness *

  type CloudHsmClusterIdType = x: string
    | IsValid_CloudHsmClusterIdType(x)
    witness *

  datatype ConnectCustomKeyStoreRequest = ConnectCustomKeyStoreRequest(nameonly CustomKeyStoreId: CustomKeyStoreIdType)

  datatype ConnectCustomKeyStoreResponse = ConnectCustomKeyStoreResponse

  datatype ConnectionErrorCodeType = INVALID_CREDENTIALS | CLUSTER_NOT_FOUND | NETWORK_ERRORS | INTERNAL_ERROR | INSUFFICIENT_CLOUDHSM_HSMS | USER_LOCKED_OUT | USER_NOT_FOUND | USER_LOGGED_IN | SUBNET_NOT_FOUND

  datatype ConnectionStateType = CONNECTED | CONNECTING | FAILED | DISCONNECTED | DISCONNECTING

  datatype CreateAliasRequest = CreateAliasRequest(nameonly AliasName: AliasNameType, nameonly TargetKeyId: KeyIdType)

  datatype CreateCustomKeyStoreRequest = CreateCustomKeyStoreRequest(nameonly CustomKeyStoreName: CustomKeyStoreNameType, nameonly CloudHsmClusterId: CloudHsmClusterIdType, nameonly TrustAnchorCertificate: TrustAnchorCertificateType, nameonly KeyStorePassword: KeyStorePasswordType)

  datatype CreateCustomKeyStoreResponse = CreateCustomKeyStoreResponse(nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>)

  datatype CreateGrantRequest = CreateGrantRequest(nameonly KeyId: KeyIdType, nameonly GranteePrincipal: PrincipalIdType, nameonly RetiringPrincipal: Option<PrincipalIdType>, nameonly Operations: GrantOperationList, nameonly Constraints: Option<GrantConstraints>, nameonly GrantTokens: Option<GrantTokenList>, nameonly Name: Option<GrantNameType>)

  datatype CreateGrantResponse = CreateGrantResponse(nameonly GrantToken: Option<GrantTokenType>, nameonly GrantId: Option<GrantIdType>)

  datatype CreateKeyRequest = CreateKeyRequest(nameonly Policy: Option<PolicyType>, nameonly Description: Option<DescriptionType>, nameonly KeyUsage: Option<KeyUsageType>, nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec>, nameonly KeySpec: Option<KeySpec>, nameonly Origin: Option<OriginType>, nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>, nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType>, nameonly Tags: Option<TagList>, nameonly MultiRegion: Option<NullableBooleanType>)

  datatype CreateKeyResponse = CreateKeyResponse(nameonly KeyMetadata: Option<KeyMetadata>)

  datatype CustomerMasterKeySpec = RSA_2048 | RSA_3072 | RSA_4096 | ECC_NIST_P256 | ECC_NIST_P384 | ECC_NIST_P521 | ECC_SECG_P256K1 | SYMMETRIC_DEFAULT

  type CustomKeyStoreIdType = x: string
    | IsValid_CustomKeyStoreIdType(x)
    witness *

  type CustomKeyStoreNameType = x: string
    | IsValid_CustomKeyStoreNameType(x)
    witness *

  type CustomKeyStoresList = seq<CustomKeyStoresListEntry>

  datatype CustomKeyStoresListEntry = CustomKeyStoresListEntry(nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>, nameonly CustomKeyStoreName: Option<CustomKeyStoreNameType>, nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType>, nameonly TrustAnchorCertificate: Option<TrustAnchorCertificateType>, nameonly ConnectionState: Option<ConnectionStateType>, nameonly ConnectionErrorCode: Option<ConnectionErrorCodeType>, nameonly CreationDate: Option<string>)

  datatype DataKeyPairSpec = RSA_2048 | RSA_3072 | RSA_4096 | ECC_NIST_P256 | ECC_NIST_P384 | ECC_NIST_P521 | ECC_SECG_P256K1

  datatype DataKeySpec = AES_256 | AES_128

  datatype DecryptRequest = DecryptRequest(nameonly CiphertextBlob: CiphertextType, nameonly EncryptionContext: Option<EncryptionContextType>, nameonly GrantTokens: Option<GrantTokenList>, nameonly KeyId: Option<KeyIdType>, nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>)

  datatype DecryptResponse = DecryptResponse(nameonly KeyId: Option<KeyIdType>, nameonly Plaintext: Option<PlaintextType>, nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>)

  datatype DeleteAliasRequest = DeleteAliasRequest(nameonly AliasName: AliasNameType)

  datatype DeleteCustomKeyStoreRequest = DeleteCustomKeyStoreRequest(nameonly CustomKeyStoreId: CustomKeyStoreIdType)

  datatype DeleteCustomKeyStoreResponse = DeleteCustomKeyStoreResponse

  datatype DeleteImportedKeyMaterialRequest = DeleteImportedKeyMaterialRequest(nameonly KeyId: KeyIdType)

  datatype DescribeCustomKeyStoresRequest = DescribeCustomKeyStoresRequest(nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>, nameonly CustomKeyStoreName: Option<CustomKeyStoreNameType>, nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>)

  datatype DescribeCustomKeyStoresResponse = DescribeCustomKeyStoresResponse(nameonly CustomKeyStores: Option<CustomKeyStoresList>, nameonly NextMarker: Option<MarkerType>, nameonly Truncated: Option<BooleanType>)

  datatype DescribeKeyRequest = DescribeKeyRequest(nameonly KeyId: KeyIdType, nameonly GrantTokens: Option<GrantTokenList>)

  datatype DescribeKeyResponse = DescribeKeyResponse(nameonly KeyMetadata: Option<KeyMetadata>)

  type DescriptionType = x: string
    | IsValid_DescriptionType(x)
    witness *

  datatype DisableKeyRequest = DisableKeyRequest(nameonly KeyId: KeyIdType)

  datatype DisableKeyRotationRequest = DisableKeyRotationRequest(nameonly KeyId: KeyIdType)

  datatype DisconnectCustomKeyStoreRequest = DisconnectCustomKeyStoreRequest(nameonly CustomKeyStoreId: CustomKeyStoreIdType)

  datatype DisconnectCustomKeyStoreResponse = DisconnectCustomKeyStoreResponse

  datatype EnableKeyRequest = EnableKeyRequest(nameonly KeyId: KeyIdType)

  datatype EnableKeyRotationRequest = EnableKeyRotationRequest(nameonly KeyId: KeyIdType)

  datatype EncryptionAlgorithmSpec = SYMMETRIC_DEFAULT | RSAES_OAEP_SHA_1 | RSAES_OAEP_SHA_256

  type EncryptionAlgorithmSpecList = seq<EncryptionAlgorithmSpec>

  type EncryptionContextKey = string

  type EncryptionContextType = map<EncryptionContextKey, EncryptionContextValue>

  type EncryptionContextValue = string

  datatype EncryptRequest = EncryptRequest(nameonly KeyId: KeyIdType, nameonly Plaintext: PlaintextType, nameonly EncryptionContext: Option<EncryptionContextType>, nameonly GrantTokens: Option<GrantTokenList>, nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>)

  datatype EncryptResponse = EncryptResponse(nameonly CiphertextBlob: Option<CiphertextType>, nameonly KeyId: Option<KeyIdType>, nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec>)

  type ErrorMessageType = string

  datatype ExpirationModelType = KEY_MATERIAL_EXPIRES | KEY_MATERIAL_DOES_NOT_EXPIRE

  datatype GenerateDataKeyPairRequest = GenerateDataKeyPairRequest(nameonly EncryptionContext: Option<EncryptionContextType>, nameonly KeyId: KeyIdType, nameonly KeyPairSpec: DataKeyPairSpec, nameonly GrantTokens: Option<GrantTokenList>)

  datatype GenerateDataKeyPairResponse = GenerateDataKeyPairResponse(nameonly PrivateKeyCiphertextBlob: Option<CiphertextType>, nameonly PrivateKeyPlaintext: Option<PlaintextType>, nameonly PublicKey: Option<PublicKeyType>, nameonly KeyId: Option<KeyIdType>, nameonly KeyPairSpec: Option<DataKeyPairSpec>)

  datatype GenerateDataKeyPairWithoutPlaintextRequest = GenerateDataKeyPairWithoutPlaintextRequest(nameonly EncryptionContext: Option<EncryptionContextType>, nameonly KeyId: KeyIdType, nameonly KeyPairSpec: DataKeyPairSpec, nameonly GrantTokens: Option<GrantTokenList>)

  datatype GenerateDataKeyPairWithoutPlaintextResponse = GenerateDataKeyPairWithoutPlaintextResponse(nameonly PrivateKeyCiphertextBlob: Option<CiphertextType>, nameonly PublicKey: Option<PublicKeyType>, nameonly KeyId: Option<KeyIdType>, nameonly KeyPairSpec: Option<DataKeyPairSpec>)

  datatype GenerateDataKeyRequest = GenerateDataKeyRequest(nameonly KeyId: KeyIdType, nameonly EncryptionContext: Option<EncryptionContextType>, nameonly NumberOfBytes: Option<NumberOfBytesType>, nameonly KeySpec: Option<DataKeySpec>, nameonly GrantTokens: Option<GrantTokenList>)

  datatype GenerateDataKeyResponse = GenerateDataKeyResponse(nameonly CiphertextBlob: Option<CiphertextType>, nameonly Plaintext: Option<PlaintextType>, nameonly KeyId: Option<KeyIdType>)

  datatype GenerateDataKeyWithoutPlaintextRequest = GenerateDataKeyWithoutPlaintextRequest(nameonly KeyId: KeyIdType, nameonly EncryptionContext: Option<EncryptionContextType>, nameonly KeySpec: Option<DataKeySpec>, nameonly NumberOfBytes: Option<NumberOfBytesType>, nameonly GrantTokens: Option<GrantTokenList>)

  datatype GenerateDataKeyWithoutPlaintextResponse = GenerateDataKeyWithoutPlaintextResponse(nameonly CiphertextBlob: Option<CiphertextType>, nameonly KeyId: Option<KeyIdType>)

  datatype GenerateRandomRequest = GenerateRandomRequest(nameonly NumberOfBytes: Option<NumberOfBytesType>, nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>)

  datatype GenerateRandomResponse = GenerateRandomResponse(nameonly Plaintext: Option<PlaintextType>)

  datatype GetKeyPolicyRequest = GetKeyPolicyRequest(nameonly KeyId: KeyIdType, nameonly PolicyName: PolicyNameType)

  datatype GetKeyPolicyResponse = GetKeyPolicyResponse(nameonly Policy: Option<PolicyType>)

  datatype GetKeyRotationStatusRequest = GetKeyRotationStatusRequest(nameonly KeyId: KeyIdType)

  datatype GetKeyRotationStatusResponse = GetKeyRotationStatusResponse(nameonly KeyRotationEnabled: Option<BooleanType>)

  datatype GetParametersForImportRequest = GetParametersForImportRequest(nameonly KeyId: KeyIdType, nameonly WrappingAlgorithm: AlgorithmSpec, nameonly WrappingKeySpec: WrappingKeySpec)

  datatype GetParametersForImportResponse = GetParametersForImportResponse(nameonly KeyId: Option<KeyIdType>, nameonly ImportToken: Option<CiphertextType>, nameonly PublicKey: Option<PlaintextType>, nameonly ParametersValidTo: Option<string>)

  datatype GetPublicKeyRequest = GetPublicKeyRequest(nameonly KeyId: KeyIdType, nameonly GrantTokens: Option<GrantTokenList>)

  datatype GetPublicKeyResponse = GetPublicKeyResponse(nameonly KeyId: Option<KeyIdType>, nameonly PublicKey: Option<PublicKeyType>, nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec>, nameonly KeySpec: Option<KeySpec>, nameonly KeyUsage: Option<KeyUsageType>, nameonly EncryptionAlgorithms: Option<EncryptionAlgorithmSpecList>, nameonly SigningAlgorithms: Option<SigningAlgorithmSpecList>)

  datatype GrantConstraints = GrantConstraints(nameonly EncryptionContextSubset: Option<EncryptionContextType>, nameonly EncryptionContextEquals: Option<EncryptionContextType>)

  type GrantIdType = x: string
    | IsValid_GrantIdType(x)
    witness *

  type GrantList = seq<GrantListEntry>

  datatype GrantListEntry = GrantListEntry(nameonly KeyId: Option<KeyIdType>, nameonly GrantId: Option<GrantIdType>, nameonly Name: Option<GrantNameType>, nameonly CreationDate: Option<string>, nameonly GranteePrincipal: Option<PrincipalIdType>, nameonly RetiringPrincipal: Option<PrincipalIdType>, nameonly IssuingAccount: Option<PrincipalIdType>, nameonly Operations: Option<GrantOperationList>, nameonly Constraints: Option<GrantConstraints>)

  type GrantNameType = x: string
    | IsValid_GrantNameType(x)
    witness *

  datatype GrantOperation = Decrypt | Encrypt | GenerateDataKey | GenerateDataKeyWithoutPlaintext | ReEncryptFrom | ReEncryptTo | Sign | Verify | GetPublicKey | CreateGrant | RetireGrant | DescribeKey | GenerateDataKeyPair | GenerateDataKeyPairWithoutPlaintext

  type GrantOperationList = seq<GrantOperation>

  type GrantTokenList = x: seq<GrantTokenType>
    | IsValid_GrantTokenList(x)
    witness *

  type GrantTokenType = x: string
    | IsValid_GrantTokenType(x)
    witness *

  datatype ImportKeyMaterialRequest = ImportKeyMaterialRequest(nameonly KeyId: KeyIdType, nameonly ImportToken: CiphertextType, nameonly EncryptedKeyMaterial: CiphertextType, nameonly ValidTo: Option<string>, nameonly ExpirationModel: Option<ExpirationModelType>)

  datatype ImportKeyMaterialResponse = ImportKeyMaterialResponse

  type KeyIdType = x: string
    | IsValid_KeyIdType(x)
    witness *

  type KeyList = seq<KeyListEntry>

  datatype KeyListEntry = KeyListEntry(nameonly KeyId: Option<KeyIdType>, nameonly KeyArn: Option<ArnType>)

  datatype KeyManagerType = AWS | CUSTOMER

  datatype KeyMetadata = KeyMetadata(nameonly AWSAccountId: Option<AWSAccountIdType>, nameonly KeyId: KeyIdType, nameonly Arn: Option<ArnType>, nameonly CreationDate: Option<string>, nameonly Enabled: Option<BooleanType>, nameonly Description: Option<DescriptionType>, nameonly KeyUsage: Option<KeyUsageType>, nameonly KeyState: Option<KeyState>, nameonly DeletionDate: Option<string>, nameonly ValidTo: Option<string>, nameonly Origin: Option<OriginType>, nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType>, nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType>, nameonly ExpirationModel: Option<ExpirationModelType>, nameonly KeyManager: Option<KeyManagerType>, nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec>, nameonly KeySpec: Option<KeySpec>, nameonly EncryptionAlgorithms: Option<EncryptionAlgorithmSpecList>, nameonly SigningAlgorithms: Option<SigningAlgorithmSpecList>, nameonly MultiRegion: Option<NullableBooleanType>, nameonly MultiRegionConfiguration: Option<MultiRegionConfiguration>, nameonly PendingDeletionWindowInDays: Option<PendingWindowInDaysType>)

  datatype KeySpec = RSA_2048 | RSA_3072 | RSA_4096 | ECC_NIST_P256 | ECC_NIST_P384 | ECC_NIST_P521 | ECC_SECG_P256K1 | SYMMETRIC_DEFAULT

  datatype KeyState = Creating | Enabled | Disabled | PendingDeletion | PendingImport | PendingReplicaDeletion | Unavailable | Updating

  type KeyStorePasswordType = x: string
    | IsValid_KeyStorePasswordType(x)
    witness *

  datatype KeyUsageType = SIGN_VERIFY | ENCRYPT_DECRYPT

  type LimitType = x: int32
    | IsValid_LimitType(x)
    witness *

  datatype ListAliasesRequest = ListAliasesRequest(nameonly KeyId: Option<KeyIdType>, nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>)

  datatype ListAliasesResponse = ListAliasesResponse(nameonly Aliases: Option<AliasList>, nameonly NextMarker: Option<MarkerType>, nameonly Truncated: Option<BooleanType>)

  datatype ListGrantsRequest = ListGrantsRequest(nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>, nameonly KeyId: KeyIdType, nameonly GrantId: Option<GrantIdType>, nameonly GranteePrincipal: Option<PrincipalIdType>)

  datatype ListGrantsResponse = ListGrantsResponse(nameonly Grants: Option<GrantList>, nameonly NextMarker: Option<MarkerType>, nameonly Truncated: Option<BooleanType>)

  datatype ListKeyPoliciesRequest = ListKeyPoliciesRequest(nameonly KeyId: KeyIdType, nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>)

  datatype ListKeyPoliciesResponse = ListKeyPoliciesResponse(nameonly PolicyNames: Option<PolicyNameList>, nameonly NextMarker: Option<MarkerType>, nameonly Truncated: Option<BooleanType>)

  datatype ListKeysRequest = ListKeysRequest(nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>)

  datatype ListResourceTagsRequest = ListResourceTagsRequest(nameonly KeyId: KeyIdType, nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>)

  datatype ListResourceTagsResponse = ListResourceTagsResponse(nameonly Tags: Option<TagList>, nameonly NextMarker: Option<MarkerType>, nameonly Truncated: Option<BooleanType>)

  datatype ListRetirableGrantsRequest = ListRetirableGrantsRequest(nameonly Limit: Option<LimitType>, nameonly Marker: Option<MarkerType>, nameonly RetiringPrincipal: PrincipalIdType)

  type MarkerType = x: string
    | IsValid_MarkerType(x)
    witness *

  datatype MessageType = RAW | DIGEST

  datatype MultiRegionConfiguration = MultiRegionConfiguration(nameonly MultiRegionKeyType: Option<MultiRegionKeyType>, nameonly PrimaryKey: Option<MultiRegionKey>, nameonly ReplicaKeys: Option<MultiRegionKeyList>)

  datatype MultiRegionKey = MultiRegionKey(nameonly Arn: Option<ArnType>, nameonly Region: Option<RegionType>)

  type MultiRegionKeyList = seq<MultiRegionKey>

  datatype MultiRegionKeyType = PRIMARY | REPLICA

  type NullableBooleanType = bool

  type NumberOfBytesType = x: int32
    | IsValid_NumberOfBytesType(x)
    witness *

  datatype OriginType = AWS_KMS | EXTERNAL | AWS_CLOUDHSM

  type PendingWindowInDaysType = x: int32
    | IsValid_PendingWindowInDaysType(x)
    witness *

  type PlaintextType = x: seq<uint8>
    | IsValid_PlaintextType(x)
    witness *

  type PolicyNameList = seq<PolicyNameType>

  type PolicyNameType = x: string
    | IsValid_PolicyNameType(x)
    witness *

  type PolicyType = x: string
    | IsValid_PolicyType(x)
    witness *

  type PrincipalIdType = x: string
    | IsValid_PrincipalIdType(x)
    witness *

  type PublicKeyType = x: seq<uint8>
    | IsValid_PublicKeyType(x)
    witness *

  datatype PutKeyPolicyRequest = PutKeyPolicyRequest(nameonly KeyId: KeyIdType, nameonly PolicyName: PolicyNameType, nameonly Policy: PolicyType, nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType>)

  datatype ReEncryptRequest = ReEncryptRequest(nameonly CiphertextBlob: CiphertextType, nameonly SourceEncryptionContext: Option<EncryptionContextType>, nameonly SourceKeyId: Option<KeyIdType>, nameonly DestinationKeyId: KeyIdType, nameonly DestinationEncryptionContext: Option<EncryptionContextType>, nameonly SourceEncryptionAlgorithm: Option<EncryptionAlgorithmSpec>, nameonly DestinationEncryptionAlgorithm: Option<EncryptionAlgorithmSpec>, nameonly GrantTokens: Option<GrantTokenList>)

  datatype ReEncryptResponse = ReEncryptResponse(nameonly CiphertextBlob: Option<CiphertextType>, nameonly SourceKeyId: Option<KeyIdType>, nameonly KeyId: Option<KeyIdType>, nameonly SourceEncryptionAlgorithm: Option<EncryptionAlgorithmSpec>, nameonly DestinationEncryptionAlgorithm: Option<EncryptionAlgorithmSpec>)

  type RegionType = x: string
    | IsValid_RegionType(x)
    witness *

  datatype ReplicateKeyRequest = ReplicateKeyRequest(nameonly KeyId: KeyIdType, nameonly ReplicaRegion: RegionType, nameonly Policy: Option<PolicyType>, nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType>, nameonly Description: Option<DescriptionType>, nameonly Tags: Option<TagList>)

  datatype ReplicateKeyResponse = ReplicateKeyResponse(nameonly ReplicaKeyMetadata: Option<KeyMetadata>, nameonly ReplicaPolicy: Option<PolicyType>, nameonly ReplicaTags: Option<TagList>)

  datatype RetireGrantRequest = RetireGrantRequest(nameonly GrantToken: Option<GrantTokenType>, nameonly KeyId: Option<KeyIdType>, nameonly GrantId: Option<GrantIdType>)

  datatype RevokeGrantRequest = RevokeGrantRequest(nameonly KeyId: KeyIdType, nameonly GrantId: GrantIdType)

  datatype ScheduleKeyDeletionRequest = ScheduleKeyDeletionRequest(nameonly KeyId: KeyIdType, nameonly PendingWindowInDays: Option<PendingWindowInDaysType>)

  datatype ScheduleKeyDeletionResponse = ScheduleKeyDeletionResponse(nameonly KeyId: Option<KeyIdType>, nameonly DeletionDate: Option<string>, nameonly KeyState: Option<KeyState>, nameonly PendingWindowInDays: Option<PendingWindowInDaysType>)

  datatype SigningAlgorithmSpec = RSASSA_PSS_SHA_256 | RSASSA_PSS_SHA_384 | RSASSA_PSS_SHA_512 | RSASSA_PKCS1_V1_5_SHA_256 | RSASSA_PKCS1_V1_5_SHA_384 | RSASSA_PKCS1_V1_5_SHA_512 | ECDSA_SHA_256 | ECDSA_SHA_384 | ECDSA_SHA_512

  type SigningAlgorithmSpecList = seq<SigningAlgorithmSpec>

  datatype SignRequest = SignRequest(nameonly KeyId: KeyIdType, nameonly Message: PlaintextType, nameonly MessageType: Option<MessageType>, nameonly GrantTokens: Option<GrantTokenList>, nameonly SigningAlgorithm: SigningAlgorithmSpec)

  datatype SignResponse = SignResponse(nameonly KeyId: Option<KeyIdType>, nameonly Signature: Option<CiphertextType>, nameonly SigningAlgorithm: Option<SigningAlgorithmSpec>)

  datatype Tag = Tag(nameonly TagKey: TagKeyType, nameonly TagValue: TagValueType)

  type TagKeyList = seq<TagKeyType>

  type TagKeyType = x: string
    | IsValid_TagKeyType(x)
    witness *

  type TagList = seq<Tag>

  datatype TagResourceRequest = TagResourceRequest(nameonly KeyId: KeyIdType, nameonly Tags: TagList)

  type TagValueType = x: string
    | IsValid_TagValueType(x)
    witness *

  class IKMSClientCallHistory {
    ghost constructor ()
    {
      CancelKeyDeletion := [];
      ConnectCustomKeyStore := [];
      CreateAlias := [];
      CreateCustomKeyStore := [];
      CreateGrant := [];
      CreateKey := [];
      Decrypt := [];
      DeleteAlias := [];
      DeleteCustomKeyStore := [];
      DeleteImportedKeyMaterial := [];
      DescribeCustomKeyStores := [];
      DescribeKey := [];
      DisableKey := [];
      DisableKeyRotation := [];
      DisconnectCustomKeyStore := [];
      EnableKey := [];
      EnableKeyRotation := [];
      Encrypt := [];
      GenerateDataKey := [];
      GenerateDataKeyPair := [];
      GenerateDataKeyPairWithoutPlaintext := [];
      GenerateDataKeyWithoutPlaintext := [];
      GenerateRandom := [];
      GetKeyPolicy := [];
      GetKeyRotationStatus := [];
      GetParametersForImport := [];
      GetPublicKey := [];
      ImportKeyMaterial := [];
      ListAliases := [];
      ListGrants := [];
      ListKeyPolicies := [];
      ListResourceTags := [];
      PutKeyPolicy := [];
      ReEncrypt := [];
      ReplicateKey := [];
      RetireGrant := [];
      RevokeGrant := [];
      ScheduleKeyDeletion := [];
      Sign := [];
      TagResource := [];
      UntagResource := [];
      UpdateAlias := [];
      UpdateCustomKeyStore := [];
      UpdateKeyDescription := [];
      UpdatePrimaryRegion := [];
      Verify := [];
    }

    ghost var CancelKeyDeletion: seq<DafnyCallEvent<CancelKeyDeletionRequest, Result<CancelKeyDeletionResponse, Error>>>
    ghost var ConnectCustomKeyStore: seq<DafnyCallEvent<ConnectCustomKeyStoreRequest, Result<ConnectCustomKeyStoreResponse, Error>>>
    ghost var CreateAlias: seq<DafnyCallEvent<CreateAliasRequest, Result<(), Error>>>
    ghost var CreateCustomKeyStore: seq<DafnyCallEvent<CreateCustomKeyStoreRequest, Result<CreateCustomKeyStoreResponse, Error>>>
    ghost var CreateGrant: seq<DafnyCallEvent<CreateGrantRequest, Result<CreateGrantResponse, Error>>>
    ghost var CreateKey: seq<DafnyCallEvent<CreateKeyRequest, Result<CreateKeyResponse, Error>>>
    ghost var Decrypt: seq<DafnyCallEvent<DecryptRequest, Result<DecryptResponse, Error>>>
    ghost var DeleteAlias: seq<DafnyCallEvent<DeleteAliasRequest, Result<(), Error>>>
    ghost var DeleteCustomKeyStore: seq<DafnyCallEvent<DeleteCustomKeyStoreRequest, Result<DeleteCustomKeyStoreResponse, Error>>>
    ghost var DeleteImportedKeyMaterial: seq<DafnyCallEvent<DeleteImportedKeyMaterialRequest, Result<(), Error>>>
    ghost var DescribeCustomKeyStores: seq<DafnyCallEvent<DescribeCustomKeyStoresRequest, Result<DescribeCustomKeyStoresResponse, Error>>>
    ghost var DescribeKey: seq<DafnyCallEvent<DescribeKeyRequest, Result<DescribeKeyResponse, Error>>>
    ghost var DisableKey: seq<DafnyCallEvent<DisableKeyRequest, Result<(), Error>>>
    ghost var DisableKeyRotation: seq<DafnyCallEvent<DisableKeyRotationRequest, Result<(), Error>>>
    ghost var DisconnectCustomKeyStore: seq<DafnyCallEvent<DisconnectCustomKeyStoreRequest, Result<DisconnectCustomKeyStoreResponse, Error>>>
    ghost var EnableKey: seq<DafnyCallEvent<EnableKeyRequest, Result<(), Error>>>
    ghost var EnableKeyRotation: seq<DafnyCallEvent<EnableKeyRotationRequest, Result<(), Error>>>
    ghost var Encrypt: seq<DafnyCallEvent<EncryptRequest, Result<EncryptResponse, Error>>>
    ghost var GenerateDataKey: seq<DafnyCallEvent<GenerateDataKeyRequest, Result<GenerateDataKeyResponse, Error>>>
    ghost var GenerateDataKeyPair: seq<DafnyCallEvent<GenerateDataKeyPairRequest, Result<GenerateDataKeyPairResponse, Error>>>
    ghost var GenerateDataKeyPairWithoutPlaintext: seq<DafnyCallEvent<GenerateDataKeyPairWithoutPlaintextRequest, Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>>>
    ghost var GenerateDataKeyWithoutPlaintext: seq<DafnyCallEvent<GenerateDataKeyWithoutPlaintextRequest, Result<GenerateDataKeyWithoutPlaintextResponse, Error>>>
    ghost var GenerateRandom: seq<DafnyCallEvent<GenerateRandomRequest, Result<GenerateRandomResponse, Error>>>
    ghost var GetKeyPolicy: seq<DafnyCallEvent<GetKeyPolicyRequest, Result<GetKeyPolicyResponse, Error>>>
    ghost var GetKeyRotationStatus: seq<DafnyCallEvent<GetKeyRotationStatusRequest, Result<GetKeyRotationStatusResponse, Error>>>
    ghost var GetParametersForImport: seq<DafnyCallEvent<GetParametersForImportRequest, Result<GetParametersForImportResponse, Error>>>
    ghost var GetPublicKey: seq<DafnyCallEvent<GetPublicKeyRequest, Result<GetPublicKeyResponse, Error>>>
    ghost var ImportKeyMaterial: seq<DafnyCallEvent<ImportKeyMaterialRequest, Result<ImportKeyMaterialResponse, Error>>>
    ghost var ListAliases: seq<DafnyCallEvent<ListAliasesRequest, Result<ListAliasesResponse, Error>>>
    ghost var ListGrants: seq<DafnyCallEvent<ListGrantsRequest, Result<ListGrantsResponse, Error>>>
    ghost var ListKeyPolicies: seq<DafnyCallEvent<ListKeyPoliciesRequest, Result<ListKeyPoliciesResponse, Error>>>
    ghost var ListResourceTags: seq<DafnyCallEvent<ListResourceTagsRequest, Result<ListResourceTagsResponse, Error>>>
    ghost var PutKeyPolicy: seq<DafnyCallEvent<PutKeyPolicyRequest, Result<(), Error>>>
    ghost var ReEncrypt: seq<DafnyCallEvent<ReEncryptRequest, Result<ReEncryptResponse, Error>>>
    ghost var ReplicateKey: seq<DafnyCallEvent<ReplicateKeyRequest, Result<ReplicateKeyResponse, Error>>>
    ghost var RetireGrant: seq<DafnyCallEvent<RetireGrantRequest, Result<(), Error>>>
    ghost var RevokeGrant: seq<DafnyCallEvent<RevokeGrantRequest, Result<(), Error>>>
    ghost var ScheduleKeyDeletion: seq<DafnyCallEvent<ScheduleKeyDeletionRequest, Result<ScheduleKeyDeletionResponse, Error>>>
    ghost var Sign: seq<DafnyCallEvent<SignRequest, Result<SignResponse, Error>>>
    ghost var TagResource: seq<DafnyCallEvent<TagResourceRequest, Result<(), Error>>>
    ghost var UntagResource: seq<DafnyCallEvent<UntagResourceRequest, Result<(), Error>>>
    ghost var UpdateAlias: seq<DafnyCallEvent<UpdateAliasRequest, Result<(), Error>>>
    ghost var UpdateCustomKeyStore: seq<DafnyCallEvent<UpdateCustomKeyStoreRequest, Result<UpdateCustomKeyStoreResponse, Error>>>
    ghost var UpdateKeyDescription: seq<DafnyCallEvent<UpdateKeyDescriptionRequest, Result<(), Error>>>
    ghost var UpdatePrimaryRegion: seq<DafnyCallEvent<UpdatePrimaryRegionRequest, Result<(), Error>>>
    ghost var Verify: seq<DafnyCallEvent<VerifyRequest, Result<VerifyResponse, Error>>>
  }

  trait {:termination false} IKMSClient {
    ghost const Modifies: set<object>

    predicate ValidState()
      ensures ValidState() ==> History in Modifies

    ghost const History: IKMSClientCallHistory

    predicate CancelKeyDeletionEnsuresPublicly(input: CancelKeyDeletionRequest, output: Result<CancelKeyDeletionResponse, Error>)
      decreases input, output

    method CancelKeyDeletion(input: CancelKeyDeletionRequest) returns (output: Result<CancelKeyDeletionResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CancelKeyDeletion
      ensures true && ValidState()
      ensures CancelKeyDeletionEnsuresPublicly(input, output)
      ensures History.CancelKeyDeletion == old(History.CancelKeyDeletion) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate ConnectCustomKeyStoreEnsuresPublicly(input: ConnectCustomKeyStoreRequest, output: Result<ConnectCustomKeyStoreResponse, Error>)
      decreases input, output

    method ConnectCustomKeyStore(input: ConnectCustomKeyStoreRequest) returns (output: Result<ConnectCustomKeyStoreResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ConnectCustomKeyStore
      ensures true && ValidState()
      ensures ConnectCustomKeyStoreEnsuresPublicly(input, output)
      ensures History.ConnectCustomKeyStore == old(History.ConnectCustomKeyStore) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate CreateAliasEnsuresPublicly(input: CreateAliasRequest, output: Result<(), Error>)
      decreases input, output

    method CreateAlias(input: CreateAliasRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateAlias
      ensures true && ValidState()
      ensures CreateAliasEnsuresPublicly(input, output)
      ensures History.CreateAlias == old(History.CreateAlias) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate CreateCustomKeyStoreEnsuresPublicly(input: CreateCustomKeyStoreRequest, output: Result<CreateCustomKeyStoreResponse, Error>)
      decreases input, output

    method CreateCustomKeyStore(input: CreateCustomKeyStoreRequest) returns (output: Result<CreateCustomKeyStoreResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateCustomKeyStore
      ensures true && ValidState()
      ensures CreateCustomKeyStoreEnsuresPublicly(input, output)
      ensures History.CreateCustomKeyStore == old(History.CreateCustomKeyStore) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate CreateGrantEnsuresPublicly(input: CreateGrantRequest, output: Result<CreateGrantResponse, Error>)
      decreases input, output

    method CreateGrant(input: CreateGrantRequest) returns (output: Result<CreateGrantResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateGrant
      ensures true && ValidState()
      ensures CreateGrantEnsuresPublicly(input, output)
      ensures History.CreateGrant == old(History.CreateGrant) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate CreateKeyEnsuresPublicly(input: CreateKeyRequest, output: Result<CreateKeyResponse, Error>)
      decreases input, output

    method CreateKey(input: CreateKeyRequest) returns (output: Result<CreateKeyResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`CreateKey
      ensures true && ValidState()
      ensures CreateKeyEnsuresPublicly(input, output)
      ensures History.CreateKey == old(History.CreateKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate DecryptEnsuresPublicly(input: DecryptRequest, output: Result<DecryptResponse, Error>)
      decreases input, output

    method Decrypt(input: DecryptRequest) returns (output: Result<DecryptResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`Decrypt
      ensures true && ValidState()
      ensures DecryptEnsuresPublicly(input, output)
      ensures History.Decrypt == old(History.Decrypt) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate DeleteAliasEnsuresPublicly(input: DeleteAliasRequest, output: Result<(), Error>)
      decreases input, output

    method DeleteAlias(input: DeleteAliasRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`DeleteAlias
      ensures true && ValidState()
      ensures DeleteAliasEnsuresPublicly(input, output)
      ensures History.DeleteAlias == old(History.DeleteAlias) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate DeleteCustomKeyStoreEnsuresPublicly(input: DeleteCustomKeyStoreRequest, output: Result<DeleteCustomKeyStoreResponse, Error>)
      decreases input, output

    method DeleteCustomKeyStore(input: DeleteCustomKeyStoreRequest) returns (output: Result<DeleteCustomKeyStoreResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`DeleteCustomKeyStore
      ensures true && ValidState()
      ensures DeleteCustomKeyStoreEnsuresPublicly(input, output)
      ensures History.DeleteCustomKeyStore == old(History.DeleteCustomKeyStore) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate DeleteImportedKeyMaterialEnsuresPublicly(input: DeleteImportedKeyMaterialRequest, output: Result<(), Error>)
      decreases input, output

    method DeleteImportedKeyMaterial(input: DeleteImportedKeyMaterialRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`DeleteImportedKeyMaterial
      ensures true && ValidState()
      ensures DeleteImportedKeyMaterialEnsuresPublicly(input, output)
      ensures History.DeleteImportedKeyMaterial == old(History.DeleteImportedKeyMaterial) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate DescribeCustomKeyStoresEnsuresPublicly(input: DescribeCustomKeyStoresRequest, output: Result<DescribeCustomKeyStoresResponse, Error>)
      decreases input, output

    method DescribeCustomKeyStores(input: DescribeCustomKeyStoresRequest) returns (output: Result<DescribeCustomKeyStoresResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`DescribeCustomKeyStores
      ensures true && ValidState()
      ensures DescribeCustomKeyStoresEnsuresPublicly(input, output)
      ensures History.DescribeCustomKeyStores == old(History.DescribeCustomKeyStores) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate DescribeKeyEnsuresPublicly(input: DescribeKeyRequest, output: Result<DescribeKeyResponse, Error>)
      decreases input, output

    method DescribeKey(input: DescribeKeyRequest) returns (output: Result<DescribeKeyResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`DescribeKey
      ensures true && ValidState()
      ensures DescribeKeyEnsuresPublicly(input, output)
      ensures History.DescribeKey == old(History.DescribeKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate DisableKeyEnsuresPublicly(input: DisableKeyRequest, output: Result<(), Error>)
      decreases input, output

    method DisableKey(input: DisableKeyRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`DisableKey
      ensures true && ValidState()
      ensures DisableKeyEnsuresPublicly(input, output)
      ensures History.DisableKey == old(History.DisableKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate DisableKeyRotationEnsuresPublicly(input: DisableKeyRotationRequest, output: Result<(), Error>)
      decreases input, output

    method DisableKeyRotation(input: DisableKeyRotationRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`DisableKeyRotation
      ensures true && ValidState()
      ensures DisableKeyRotationEnsuresPublicly(input, output)
      ensures History.DisableKeyRotation == old(History.DisableKeyRotation) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate DisconnectCustomKeyStoreEnsuresPublicly(input: DisconnectCustomKeyStoreRequest, output: Result<DisconnectCustomKeyStoreResponse, Error>)
      decreases input, output

    method DisconnectCustomKeyStore(input: DisconnectCustomKeyStoreRequest) returns (output: Result<DisconnectCustomKeyStoreResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`DisconnectCustomKeyStore
      ensures true && ValidState()
      ensures DisconnectCustomKeyStoreEnsuresPublicly(input, output)
      ensures History.DisconnectCustomKeyStore == old(History.DisconnectCustomKeyStore) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate EnableKeyEnsuresPublicly(input: EnableKeyRequest, output: Result<(), Error>)
      decreases input, output

    method EnableKey(input: EnableKeyRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`EnableKey
      ensures true && ValidState()
      ensures EnableKeyEnsuresPublicly(input, output)
      ensures History.EnableKey == old(History.EnableKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate EnableKeyRotationEnsuresPublicly(input: EnableKeyRotationRequest, output: Result<(), Error>)
      decreases input, output

    method EnableKeyRotation(input: EnableKeyRotationRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`EnableKeyRotation
      ensures true && ValidState()
      ensures EnableKeyRotationEnsuresPublicly(input, output)
      ensures History.EnableKeyRotation == old(History.EnableKeyRotation) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate EncryptEnsuresPublicly(input: EncryptRequest, output: Result<EncryptResponse, Error>)
      decreases input, output

    method Encrypt(input: EncryptRequest) returns (output: Result<EncryptResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`Encrypt
      ensures true && ValidState()
      ensures EncryptEnsuresPublicly(input, output)
      ensures History.Encrypt == old(History.Encrypt) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate GenerateDataKeyEnsuresPublicly(input: GenerateDataKeyRequest, output: Result<GenerateDataKeyResponse, Error>)
      decreases input, output

    method GenerateDataKey(input: GenerateDataKeyRequest) returns (output: Result<GenerateDataKeyResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GenerateDataKey
      ensures true && ValidState()
      ensures GenerateDataKeyEnsuresPublicly(input, output)
      ensures History.GenerateDataKey == old(History.GenerateDataKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate GenerateDataKeyPairEnsuresPublicly(input: GenerateDataKeyPairRequest, output: Result<GenerateDataKeyPairResponse, Error>)
      decreases input, output

    method GenerateDataKeyPair(input: GenerateDataKeyPairRequest) returns (output: Result<GenerateDataKeyPairResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GenerateDataKeyPair
      ensures true && ValidState()
      ensures GenerateDataKeyPairEnsuresPublicly(input, output)
      ensures History.GenerateDataKeyPair == old(History.GenerateDataKeyPair) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate GenerateDataKeyPairWithoutPlaintextEnsuresPublicly(input: GenerateDataKeyPairWithoutPlaintextRequest, output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>)
      decreases input, output

    method GenerateDataKeyPairWithoutPlaintext(input: GenerateDataKeyPairWithoutPlaintextRequest) returns (output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GenerateDataKeyPairWithoutPlaintext
      ensures true && ValidState()
      ensures GenerateDataKeyPairWithoutPlaintextEnsuresPublicly(input, output)
      ensures History.GenerateDataKeyPairWithoutPlaintext == old(History.GenerateDataKeyPairWithoutPlaintext) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate GenerateDataKeyWithoutPlaintextEnsuresPublicly(input: GenerateDataKeyWithoutPlaintextRequest, output: Result<GenerateDataKeyWithoutPlaintextResponse, Error>)
      decreases input, output

    method GenerateDataKeyWithoutPlaintext(input: GenerateDataKeyWithoutPlaintextRequest) returns (output: Result<GenerateDataKeyWithoutPlaintextResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GenerateDataKeyWithoutPlaintext
      ensures true && ValidState()
      ensures GenerateDataKeyWithoutPlaintextEnsuresPublicly(input, output)
      ensures History.GenerateDataKeyWithoutPlaintext == old(History.GenerateDataKeyWithoutPlaintext) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate GenerateRandomEnsuresPublicly(input: GenerateRandomRequest, output: Result<GenerateRandomResponse, Error>)
      decreases input, output

    method GenerateRandom(input: GenerateRandomRequest) returns (output: Result<GenerateRandomResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GenerateRandom
      ensures true && ValidState()
      ensures GenerateRandomEnsuresPublicly(input, output)
      ensures History.GenerateRandom == old(History.GenerateRandom) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate GetKeyPolicyEnsuresPublicly(input: GetKeyPolicyRequest, output: Result<GetKeyPolicyResponse, Error>)
      decreases input, output

    method GetKeyPolicy(input: GetKeyPolicyRequest) returns (output: Result<GetKeyPolicyResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetKeyPolicy
      ensures true && ValidState()
      ensures GetKeyPolicyEnsuresPublicly(input, output)
      ensures History.GetKeyPolicy == old(History.GetKeyPolicy) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate GetKeyRotationStatusEnsuresPublicly(input: GetKeyRotationStatusRequest, output: Result<GetKeyRotationStatusResponse, Error>)
      decreases input, output

    method GetKeyRotationStatus(input: GetKeyRotationStatusRequest) returns (output: Result<GetKeyRotationStatusResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetKeyRotationStatus
      ensures true && ValidState()
      ensures GetKeyRotationStatusEnsuresPublicly(input, output)
      ensures History.GetKeyRotationStatus == old(History.GetKeyRotationStatus) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate GetParametersForImportEnsuresPublicly(input: GetParametersForImportRequest, output: Result<GetParametersForImportResponse, Error>)
      decreases input, output

    method GetParametersForImport(input: GetParametersForImportRequest) returns (output: Result<GetParametersForImportResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetParametersForImport
      ensures true && ValidState()
      ensures GetParametersForImportEnsuresPublicly(input, output)
      ensures History.GetParametersForImport == old(History.GetParametersForImport) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate GetPublicKeyEnsuresPublicly(input: GetPublicKeyRequest, output: Result<GetPublicKeyResponse, Error>)
      decreases input, output

    method GetPublicKey(input: GetPublicKeyRequest) returns (output: Result<GetPublicKeyResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetPublicKey
      ensures true && ValidState()
      ensures GetPublicKeyEnsuresPublicly(input, output)
      ensures History.GetPublicKey == old(History.GetPublicKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate ImportKeyMaterialEnsuresPublicly(input: ImportKeyMaterialRequest, output: Result<ImportKeyMaterialResponse, Error>)
      decreases input, output

    method ImportKeyMaterial(input: ImportKeyMaterialRequest) returns (output: Result<ImportKeyMaterialResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ImportKeyMaterial
      ensures true && ValidState()
      ensures ImportKeyMaterialEnsuresPublicly(input, output)
      ensures History.ImportKeyMaterial == old(History.ImportKeyMaterial) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate ListAliasesEnsuresPublicly(input: ListAliasesRequest, output: Result<ListAliasesResponse, Error>)
      decreases input, output

    method ListAliases(input: ListAliasesRequest) returns (output: Result<ListAliasesResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ListAliases
      ensures true && ValidState()
      ensures ListAliasesEnsuresPublicly(input, output)
      ensures History.ListAliases == old(History.ListAliases) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate ListGrantsEnsuresPublicly(input: ListGrantsRequest, output: Result<ListGrantsResponse, Error>)
      decreases input, output

    method ListGrants(input: ListGrantsRequest) returns (output: Result<ListGrantsResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ListGrants
      ensures true && ValidState()
      ensures ListGrantsEnsuresPublicly(input, output)
      ensures History.ListGrants == old(History.ListGrants) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate ListKeyPoliciesEnsuresPublicly(input: ListKeyPoliciesRequest, output: Result<ListKeyPoliciesResponse, Error>)
      decreases input, output

    method ListKeyPolicies(input: ListKeyPoliciesRequest) returns (output: Result<ListKeyPoliciesResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ListKeyPolicies
      ensures true && ValidState()
      ensures ListKeyPoliciesEnsuresPublicly(input, output)
      ensures History.ListKeyPolicies == old(History.ListKeyPolicies) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate ListResourceTagsEnsuresPublicly(input: ListResourceTagsRequest, output: Result<ListResourceTagsResponse, Error>)
      decreases input, output

    method ListResourceTags(input: ListResourceTagsRequest) returns (output: Result<ListResourceTagsResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ListResourceTags
      ensures true && ValidState()
      ensures ListResourceTagsEnsuresPublicly(input, output)
      ensures History.ListResourceTags == old(History.ListResourceTags) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate PutKeyPolicyEnsuresPublicly(input: PutKeyPolicyRequest, output: Result<(), Error>)
      decreases input, output

    method PutKeyPolicy(input: PutKeyPolicyRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`PutKeyPolicy
      ensures true && ValidState()
      ensures PutKeyPolicyEnsuresPublicly(input, output)
      ensures History.PutKeyPolicy == old(History.PutKeyPolicy) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate ReEncryptEnsuresPublicly(input: ReEncryptRequest, output: Result<ReEncryptResponse, Error>)
      decreases input, output

    method ReEncrypt(input: ReEncryptRequest) returns (output: Result<ReEncryptResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ReEncrypt
      ensures true && ValidState()
      ensures ReEncryptEnsuresPublicly(input, output)
      ensures History.ReEncrypt == old(History.ReEncrypt) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate ReplicateKeyEnsuresPublicly(input: ReplicateKeyRequest, output: Result<ReplicateKeyResponse, Error>)
      decreases input, output

    method ReplicateKey(input: ReplicateKeyRequest) returns (output: Result<ReplicateKeyResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ReplicateKey
      ensures true && ValidState()
      ensures ReplicateKeyEnsuresPublicly(input, output)
      ensures History.ReplicateKey == old(History.ReplicateKey) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate RetireGrantEnsuresPublicly(input: RetireGrantRequest, output: Result<(), Error>)
      decreases input, output

    method RetireGrant(input: RetireGrantRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`RetireGrant
      ensures true && ValidState()
      ensures RetireGrantEnsuresPublicly(input, output)
      ensures History.RetireGrant == old(History.RetireGrant) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate RevokeGrantEnsuresPublicly(input: RevokeGrantRequest, output: Result<(), Error>)
      decreases input, output

    method RevokeGrant(input: RevokeGrantRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`RevokeGrant
      ensures true && ValidState()
      ensures RevokeGrantEnsuresPublicly(input, output)
      ensures History.RevokeGrant == old(History.RevokeGrant) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate ScheduleKeyDeletionEnsuresPublicly(input: ScheduleKeyDeletionRequest, output: Result<ScheduleKeyDeletionResponse, Error>)
      decreases input, output

    method ScheduleKeyDeletion(input: ScheduleKeyDeletionRequest) returns (output: Result<ScheduleKeyDeletionResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`ScheduleKeyDeletion
      ensures true && ValidState()
      ensures ScheduleKeyDeletionEnsuresPublicly(input, output)
      ensures History.ScheduleKeyDeletion == old(History.ScheduleKeyDeletion) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate SignEnsuresPublicly(input: SignRequest, output: Result<SignResponse, Error>)
      decreases input, output

    method Sign(input: SignRequest) returns (output: Result<SignResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`Sign
      ensures true && ValidState()
      ensures SignEnsuresPublicly(input, output)
      ensures History.Sign == old(History.Sign) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate TagResourceEnsuresPublicly(input: TagResourceRequest, output: Result<(), Error>)
      decreases input, output

    method TagResource(input: TagResourceRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`TagResource
      ensures true && ValidState()
      ensures TagResourceEnsuresPublicly(input, output)
      ensures History.TagResource == old(History.TagResource) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate UntagResourceEnsuresPublicly(input: UntagResourceRequest, output: Result<(), Error>)
      decreases input, output

    method UntagResource(input: UntagResourceRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`UntagResource
      ensures true && ValidState()
      ensures UntagResourceEnsuresPublicly(input, output)
      ensures History.UntagResource == old(History.UntagResource) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate UpdateAliasEnsuresPublicly(input: UpdateAliasRequest, output: Result<(), Error>)
      decreases input, output

    method UpdateAlias(input: UpdateAliasRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`UpdateAlias
      ensures true && ValidState()
      ensures UpdateAliasEnsuresPublicly(input, output)
      ensures History.UpdateAlias == old(History.UpdateAlias) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate UpdateCustomKeyStoreEnsuresPublicly(input: UpdateCustomKeyStoreRequest, output: Result<UpdateCustomKeyStoreResponse, Error>)
      decreases input, output

    method UpdateCustomKeyStore(input: UpdateCustomKeyStoreRequest) returns (output: Result<UpdateCustomKeyStoreResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`UpdateCustomKeyStore
      ensures true && ValidState()
      ensures UpdateCustomKeyStoreEnsuresPublicly(input, output)
      ensures History.UpdateCustomKeyStore == old(History.UpdateCustomKeyStore) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate UpdateKeyDescriptionEnsuresPublicly(input: UpdateKeyDescriptionRequest, output: Result<(), Error>)
      decreases input, output

    method UpdateKeyDescription(input: UpdateKeyDescriptionRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`UpdateKeyDescription
      ensures true && ValidState()
      ensures UpdateKeyDescriptionEnsuresPublicly(input, output)
      ensures History.UpdateKeyDescription == old(History.UpdateKeyDescription) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate UpdatePrimaryRegionEnsuresPublicly(input: UpdatePrimaryRegionRequest, output: Result<(), Error>)
      decreases input, output

    method UpdatePrimaryRegion(input: UpdatePrimaryRegionRequest) returns (output: Result<(), Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`UpdatePrimaryRegion
      ensures true && ValidState()
      ensures UpdatePrimaryRegionEnsuresPublicly(input, output)
      ensures History.UpdatePrimaryRegion == old(History.UpdatePrimaryRegion) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}

    predicate VerifyEnsuresPublicly(input: VerifyRequest, output: Result<VerifyResponse, Error>)
      decreases input, output

    method Verify(input: VerifyRequest) returns (output: Result<VerifyResponse, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`Verify
      ensures true && ValidState()
      ensures VerifyEnsuresPublicly(input, output)
      ensures History.Verify == old(History.Verify) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
  }

  type TrustAnchorCertificateType = x: string
    | IsValid_TrustAnchorCertificateType(x)
    witness *

  datatype UntagResourceRequest = UntagResourceRequest(nameonly KeyId: KeyIdType, nameonly TagKeys: TagKeyList)

  datatype UpdateAliasRequest = UpdateAliasRequest(nameonly AliasName: AliasNameType, nameonly TargetKeyId: KeyIdType)

  datatype UpdateCustomKeyStoreRequest = UpdateCustomKeyStoreRequest(nameonly CustomKeyStoreId: CustomKeyStoreIdType, nameonly NewCustomKeyStoreName: Option<CustomKeyStoreNameType>, nameonly KeyStorePassword: Option<KeyStorePasswordType>, nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType>)

  datatype UpdateCustomKeyStoreResponse = UpdateCustomKeyStoreResponse

  datatype UpdateKeyDescriptionRequest = UpdateKeyDescriptionRequest(nameonly KeyId: KeyIdType, nameonly Description: DescriptionType)

  datatype UpdatePrimaryRegionRequest = UpdatePrimaryRegionRequest(nameonly KeyId: KeyIdType, nameonly PrimaryRegion: RegionType)

  datatype VerifyRequest = VerifyRequest(nameonly KeyId: KeyIdType, nameonly Message: PlaintextType, nameonly MessageType: Option<MessageType>, nameonly Signature: CiphertextType, nameonly SigningAlgorithm: SigningAlgorithmSpec, nameonly GrantTokens: Option<GrantTokenList>)

  datatype VerifyResponse = VerifyResponse(nameonly KeyId: Option<KeyIdType>, nameonly SignatureValid: Option<BooleanType>, nameonly SigningAlgorithm: Option<SigningAlgorithmSpec>)

  datatype WrappingKeySpec = RSA_2048

  datatype Error = AlreadyExistsException(nameonly message: Option<ErrorMessageType>) | CloudHsmClusterInUseException(nameonly message: Option<ErrorMessageType>) | CloudHsmClusterInvalidConfigurationException(nameonly message: Option<ErrorMessageType>) | CloudHsmClusterNotActiveException(nameonly message: Option<ErrorMessageType>) | CloudHsmClusterNotFoundException(nameonly message: Option<ErrorMessageType>) | CloudHsmClusterNotRelatedException(nameonly message: Option<ErrorMessageType>) | CustomKeyStoreHasCMKsException(nameonly message: Option<ErrorMessageType>) | CustomKeyStoreInvalidStateException(nameonly message: Option<ErrorMessageType>) | CustomKeyStoreNameInUseException(nameonly message: Option<ErrorMessageType>) | CustomKeyStoreNotFoundException(nameonly message: Option<ErrorMessageType>) | DependencyTimeoutException(nameonly message: Option<ErrorMessageType>) | DisabledException(nameonly message: Option<ErrorMessageType>) | ExpiredImportTokenException(nameonly message: Option<ErrorMessageType>) | IncorrectKeyException(nameonly message: Option<ErrorMessageType>) | IncorrectKeyMaterialException(nameonly message: Option<ErrorMessageType>) | IncorrectTrustAnchorException(nameonly message: Option<ErrorMessageType>) | InvalidAliasNameException(nameonly message: Option<ErrorMessageType>) | InvalidArnException(nameonly message: Option<ErrorMessageType>) | InvalidCiphertextException(nameonly message: Option<ErrorMessageType>) | InvalidGrantIdException(nameonly message: Option<ErrorMessageType>) | InvalidGrantTokenException(nameonly message: Option<ErrorMessageType>) | InvalidImportTokenException(nameonly message: Option<ErrorMessageType>) | InvalidKeyUsageException(nameonly message: Option<ErrorMessageType>) | InvalidMarkerException(nameonly message: Option<ErrorMessageType>) | KeyUnavailableException(nameonly message: Option<ErrorMessageType>) | KMSInternalException(nameonly message: Option<ErrorMessageType>) | KMSInvalidSignatureException(nameonly message: Option<ErrorMessageType>) | KMSInvalidStateException(nameonly message: Option<ErrorMessageType>) | LimitExceededException(nameonly message: Option<ErrorMessageType>) | MalformedPolicyDocumentException(nameonly message: Option<ErrorMessageType>) | NotFoundException(nameonly message: Option<ErrorMessageType>) | TagException(nameonly message: Option<ErrorMessageType>) | UnsupportedOperationException(nameonly message: Option<ErrorMessageType>) | Opaque(obj: object)

  type OpaqueError = e: Error
    | e.Opaque?
    witness *

  predicate method IsValid_AliasNameType(x: string)
    decreases x
  {
    1 <= |x| <= 256
  }

  predicate method IsValid_ArnType(x: string)
    decreases x
  {
    20 <= |x| <= 2048
  }

  predicate method IsValid_CiphertextType(x: seq<uint8>)
    decreases x
  {
    1 <= |x| <= 6144
  }

  predicate method IsValid_CloudHsmClusterIdType(x: string)
    decreases x
  {
    19 <= |x| <= 24
  }

  predicate method IsValid_CustomKeyStoreIdType(x: string)
    decreases x
  {
    1 <= |x| <= 64
  }

  predicate method IsValid_CustomKeyStoreNameType(x: string)
    decreases x
  {
    1 <= |x| <= 256
  }

  predicate method IsValid_DescriptionType(x: string)
    decreases x
  {
    0 <= |x| <= 8192
  }

  predicate method IsValid_GrantIdType(x: string)
    decreases x
  {
    1 <= |x| <= 128
  }

  predicate method IsValid_GrantNameType(x: string)
    decreases x
  {
    1 <= |x| <= 256
  }

  predicate method IsValid_GrantTokenList(x: seq<GrantTokenType>)
    decreases x
  {
    0 <= |x| <= 10
  }

  predicate method IsValid_GrantTokenType(x: string)
    decreases x
  {
    1 <= |x| <= 8192
  }

  predicate method IsValid_KeyIdType(x: string)
    decreases x
  {
    1 <= |x| <= 2048
  }

  predicate method IsValid_KeyStorePasswordType(x: string)
    decreases x
  {
    7 <= |x| <= 32
  }

  predicate method IsValid_LimitType(x: int32)
    decreases x
  {
    1 <= x <= 1000
  }

  predicate method IsValid_MarkerType(x: string)
    decreases x
  {
    1 <= |x| <= 1024
  }

  predicate method IsValid_NumberOfBytesType(x: int32)
    decreases x
  {
    1 <= x <= 1024
  }

  predicate method IsValid_PendingWindowInDaysType(x: int32)
    decreases x
  {
    1 <= x <= 365
  }

  predicate method IsValid_PlaintextType(x: seq<uint8>)
    decreases x
  {
    1 <= |x| <= 4096
  }

  predicate method IsValid_PolicyNameType(x: string)
    decreases x
  {
    1 <= |x| <= 128
  }

  predicate method IsValid_PolicyType(x: string)
    decreases x
  {
    1 <= |x| <= 131072
  }

  predicate method IsValid_PrincipalIdType(x: string)
    decreases x
  {
    1 <= |x| <= 256
  }

  predicate method IsValid_PublicKeyType(x: seq<uint8>)
    decreases x
  {
    1 <= |x| <= 8192
  }

  predicate method IsValid_RegionType(x: string)
    decreases x
  {
    1 <= |x| <= 32
  }

  predicate method IsValid_TagKeyType(x: string)
    decreases x
  {
    1 <= |x| <= 128
  }

  predicate method IsValid_TagValueType(x: string)
    decreases x
  {
    0 <= |x| <= 256
  }

  predicate method IsValid_TrustAnchorCertificateType(x: string)
    decreases x
  {
    1 <= |x| <= 5000
  }
}

abstract module AbstractComAmazonawsKmsService {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = ComAmazonawsKmsTypes
  datatype KMSClientConfigType = KMSClientConfigType

  function method DefaultKMSClientConfigType(): KMSClientConfigType

  method {:extern} KMSClient() returns (res: Result<IKMSClient, Error>)
    ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
}

abstract module AbstractComAmazonawsKmsOperations {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = ComAmazonawsKmsTypes
  type InternalConfig

  predicate ValidInternalConfig?(config: InternalConfig)

  function ModifiesInternalConfig(config: InternalConfig): set<object>

  predicate CancelKeyDeletionEnsuresPublicly(input: CancelKeyDeletionRequest, output: Result<CancelKeyDeletionResponse, Error>)
    decreases input, output

  method CancelKeyDeletion(config: InternalConfig, input: CancelKeyDeletionRequest) returns (output: Result<CancelKeyDeletionResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures CancelKeyDeletionEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate ConnectCustomKeyStoreEnsuresPublicly(input: ConnectCustomKeyStoreRequest, output: Result<ConnectCustomKeyStoreResponse, Error>)
    decreases input, output

  method ConnectCustomKeyStore(config: InternalConfig, input: ConnectCustomKeyStoreRequest) returns (output: Result<ConnectCustomKeyStoreResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ConnectCustomKeyStoreEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate CreateAliasEnsuresPublicly(input: CreateAliasRequest, output: Result<(), Error>)
    decreases input, output

  method CreateAlias(config: InternalConfig, input: CreateAliasRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures CreateAliasEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate CreateCustomKeyStoreEnsuresPublicly(input: CreateCustomKeyStoreRequest, output: Result<CreateCustomKeyStoreResponse, Error>)
    decreases input, output

  method CreateCustomKeyStore(config: InternalConfig, input: CreateCustomKeyStoreRequest) returns (output: Result<CreateCustomKeyStoreResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures CreateCustomKeyStoreEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate CreateGrantEnsuresPublicly(input: CreateGrantRequest, output: Result<CreateGrantResponse, Error>)
    decreases input, output

  method CreateGrant(config: InternalConfig, input: CreateGrantRequest) returns (output: Result<CreateGrantResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures CreateGrantEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate CreateKeyEnsuresPublicly(input: CreateKeyRequest, output: Result<CreateKeyResponse, Error>)
    decreases input, output

  method CreateKey(config: InternalConfig, input: CreateKeyRequest) returns (output: Result<CreateKeyResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures CreateKeyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate DecryptEnsuresPublicly(input: DecryptRequest, output: Result<DecryptResponse, Error>)
    decreases input, output

  method Decrypt(config: InternalConfig, input: DecryptRequest) returns (output: Result<DecryptResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures DecryptEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate DeleteAliasEnsuresPublicly(input: DeleteAliasRequest, output: Result<(), Error>)
    decreases input, output

  method DeleteAlias(config: InternalConfig, input: DeleteAliasRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures DeleteAliasEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate DeleteCustomKeyStoreEnsuresPublicly(input: DeleteCustomKeyStoreRequest, output: Result<DeleteCustomKeyStoreResponse, Error>)
    decreases input, output

  method DeleteCustomKeyStore(config: InternalConfig, input: DeleteCustomKeyStoreRequest) returns (output: Result<DeleteCustomKeyStoreResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures DeleteCustomKeyStoreEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate DeleteImportedKeyMaterialEnsuresPublicly(input: DeleteImportedKeyMaterialRequest, output: Result<(), Error>)
    decreases input, output

  method DeleteImportedKeyMaterial(config: InternalConfig, input: DeleteImportedKeyMaterialRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures DeleteImportedKeyMaterialEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate DescribeCustomKeyStoresEnsuresPublicly(input: DescribeCustomKeyStoresRequest, output: Result<DescribeCustomKeyStoresResponse, Error>)
    decreases input, output

  method DescribeCustomKeyStores(config: InternalConfig, input: DescribeCustomKeyStoresRequest) returns (output: Result<DescribeCustomKeyStoresResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures DescribeCustomKeyStoresEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate DescribeKeyEnsuresPublicly(input: DescribeKeyRequest, output: Result<DescribeKeyResponse, Error>)
    decreases input, output

  method DescribeKey(config: InternalConfig, input: DescribeKeyRequest) returns (output: Result<DescribeKeyResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures DescribeKeyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate DisableKeyEnsuresPublicly(input: DisableKeyRequest, output: Result<(), Error>)
    decreases input, output

  method DisableKey(config: InternalConfig, input: DisableKeyRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures DisableKeyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate DisableKeyRotationEnsuresPublicly(input: DisableKeyRotationRequest, output: Result<(), Error>)
    decreases input, output

  method DisableKeyRotation(config: InternalConfig, input: DisableKeyRotationRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures DisableKeyRotationEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate DisconnectCustomKeyStoreEnsuresPublicly(input: DisconnectCustomKeyStoreRequest, output: Result<DisconnectCustomKeyStoreResponse, Error>)
    decreases input, output

  method DisconnectCustomKeyStore(config: InternalConfig, input: DisconnectCustomKeyStoreRequest) returns (output: Result<DisconnectCustomKeyStoreResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures DisconnectCustomKeyStoreEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate EnableKeyEnsuresPublicly(input: EnableKeyRequest, output: Result<(), Error>)
    decreases input, output

  method EnableKey(config: InternalConfig, input: EnableKeyRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures EnableKeyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate EnableKeyRotationEnsuresPublicly(input: EnableKeyRotationRequest, output: Result<(), Error>)
    decreases input, output

  method EnableKeyRotation(config: InternalConfig, input: EnableKeyRotationRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures EnableKeyRotationEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate EncryptEnsuresPublicly(input: EncryptRequest, output: Result<EncryptResponse, Error>)
    decreases input, output

  method Encrypt(config: InternalConfig, input: EncryptRequest) returns (output: Result<EncryptResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures EncryptEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate GenerateDataKeyEnsuresPublicly(input: GenerateDataKeyRequest, output: Result<GenerateDataKeyResponse, Error>)
    decreases input, output

  method GenerateDataKey(config: InternalConfig, input: GenerateDataKeyRequest) returns (output: Result<GenerateDataKeyResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GenerateDataKeyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate GenerateDataKeyPairEnsuresPublicly(input: GenerateDataKeyPairRequest, output: Result<GenerateDataKeyPairResponse, Error>)
    decreases input, output

  method GenerateDataKeyPair(config: InternalConfig, input: GenerateDataKeyPairRequest) returns (output: Result<GenerateDataKeyPairResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GenerateDataKeyPairEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate GenerateDataKeyPairWithoutPlaintextEnsuresPublicly(input: GenerateDataKeyPairWithoutPlaintextRequest, output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>)
    decreases input, output

  method GenerateDataKeyPairWithoutPlaintext(config: InternalConfig, input: GenerateDataKeyPairWithoutPlaintextRequest) returns (output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GenerateDataKeyPairWithoutPlaintextEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate GenerateDataKeyWithoutPlaintextEnsuresPublicly(input: GenerateDataKeyWithoutPlaintextRequest, output: Result<GenerateDataKeyWithoutPlaintextResponse, Error>)
    decreases input, output

  method GenerateDataKeyWithoutPlaintext(config: InternalConfig, input: GenerateDataKeyWithoutPlaintextRequest) returns (output: Result<GenerateDataKeyWithoutPlaintextResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GenerateDataKeyWithoutPlaintextEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate GenerateRandomEnsuresPublicly(input: GenerateRandomRequest, output: Result<GenerateRandomResponse, Error>)
    decreases input, output

  method GenerateRandom(config: InternalConfig, input: GenerateRandomRequest) returns (output: Result<GenerateRandomResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GenerateRandomEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate GetKeyPolicyEnsuresPublicly(input: GetKeyPolicyRequest, output: Result<GetKeyPolicyResponse, Error>)
    decreases input, output

  method GetKeyPolicy(config: InternalConfig, input: GetKeyPolicyRequest) returns (output: Result<GetKeyPolicyResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GetKeyPolicyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate GetKeyRotationStatusEnsuresPublicly(input: GetKeyRotationStatusRequest, output: Result<GetKeyRotationStatusResponse, Error>)
    decreases input, output

  method GetKeyRotationStatus(config: InternalConfig, input: GetKeyRotationStatusRequest) returns (output: Result<GetKeyRotationStatusResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GetKeyRotationStatusEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate GetParametersForImportEnsuresPublicly(input: GetParametersForImportRequest, output: Result<GetParametersForImportResponse, Error>)
    decreases input, output

  method GetParametersForImport(config: InternalConfig, input: GetParametersForImportRequest) returns (output: Result<GetParametersForImportResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GetParametersForImportEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate GetPublicKeyEnsuresPublicly(input: GetPublicKeyRequest, output: Result<GetPublicKeyResponse, Error>)
    decreases input, output

  method GetPublicKey(config: InternalConfig, input: GetPublicKeyRequest) returns (output: Result<GetPublicKeyResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GetPublicKeyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate ImportKeyMaterialEnsuresPublicly(input: ImportKeyMaterialRequest, output: Result<ImportKeyMaterialResponse, Error>)
    decreases input, output

  method ImportKeyMaterial(config: InternalConfig, input: ImportKeyMaterialRequest) returns (output: Result<ImportKeyMaterialResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ImportKeyMaterialEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate ListAliasesEnsuresPublicly(input: ListAliasesRequest, output: Result<ListAliasesResponse, Error>)
    decreases input, output

  method ListAliases(config: InternalConfig, input: ListAliasesRequest) returns (output: Result<ListAliasesResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ListAliasesEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate ListGrantsEnsuresPublicly(input: ListGrantsRequest, output: Result<ListGrantsResponse, Error>)
    decreases input, output

  method ListGrants(config: InternalConfig, input: ListGrantsRequest) returns (output: Result<ListGrantsResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ListGrantsEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate ListKeyPoliciesEnsuresPublicly(input: ListKeyPoliciesRequest, output: Result<ListKeyPoliciesResponse, Error>)
    decreases input, output

  method ListKeyPolicies(config: InternalConfig, input: ListKeyPoliciesRequest) returns (output: Result<ListKeyPoliciesResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ListKeyPoliciesEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate ListResourceTagsEnsuresPublicly(input: ListResourceTagsRequest, output: Result<ListResourceTagsResponse, Error>)
    decreases input, output

  method ListResourceTags(config: InternalConfig, input: ListResourceTagsRequest) returns (output: Result<ListResourceTagsResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ListResourceTagsEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate PutKeyPolicyEnsuresPublicly(input: PutKeyPolicyRequest, output: Result<(), Error>)
    decreases input, output

  method PutKeyPolicy(config: InternalConfig, input: PutKeyPolicyRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures PutKeyPolicyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate ReEncryptEnsuresPublicly(input: ReEncryptRequest, output: Result<ReEncryptResponse, Error>)
    decreases input, output

  method ReEncrypt(config: InternalConfig, input: ReEncryptRequest) returns (output: Result<ReEncryptResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ReEncryptEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate ReplicateKeyEnsuresPublicly(input: ReplicateKeyRequest, output: Result<ReplicateKeyResponse, Error>)
    decreases input, output

  method ReplicateKey(config: InternalConfig, input: ReplicateKeyRequest) returns (output: Result<ReplicateKeyResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ReplicateKeyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate RetireGrantEnsuresPublicly(input: RetireGrantRequest, output: Result<(), Error>)
    decreases input, output

  method RetireGrant(config: InternalConfig, input: RetireGrantRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures RetireGrantEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate RevokeGrantEnsuresPublicly(input: RevokeGrantRequest, output: Result<(), Error>)
    decreases input, output

  method RevokeGrant(config: InternalConfig, input: RevokeGrantRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures RevokeGrantEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate ScheduleKeyDeletionEnsuresPublicly(input: ScheduleKeyDeletionRequest, output: Result<ScheduleKeyDeletionResponse, Error>)
    decreases input, output

  method ScheduleKeyDeletion(config: InternalConfig, input: ScheduleKeyDeletionRequest) returns (output: Result<ScheduleKeyDeletionResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures ScheduleKeyDeletionEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate SignEnsuresPublicly(input: SignRequest, output: Result<SignResponse, Error>)
    decreases input, output

  method Sign(config: InternalConfig, input: SignRequest) returns (output: Result<SignResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures SignEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate TagResourceEnsuresPublicly(input: TagResourceRequest, output: Result<(), Error>)
    decreases input, output

  method TagResource(config: InternalConfig, input: TagResourceRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures TagResourceEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate UntagResourceEnsuresPublicly(input: UntagResourceRequest, output: Result<(), Error>)
    decreases input, output

  method UntagResource(config: InternalConfig, input: UntagResourceRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures UntagResourceEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate UpdateAliasEnsuresPublicly(input: UpdateAliasRequest, output: Result<(), Error>)
    decreases input, output

  method UpdateAlias(config: InternalConfig, input: UpdateAliasRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures UpdateAliasEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate UpdateCustomKeyStoreEnsuresPublicly(input: UpdateCustomKeyStoreRequest, output: Result<UpdateCustomKeyStoreResponse, Error>)
    decreases input, output

  method UpdateCustomKeyStore(config: InternalConfig, input: UpdateCustomKeyStoreRequest) returns (output: Result<UpdateCustomKeyStoreResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures UpdateCustomKeyStoreEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate UpdateKeyDescriptionEnsuresPublicly(input: UpdateKeyDescriptionRequest, output: Result<(), Error>)
    decreases input, output

  method UpdateKeyDescription(config: InternalConfig, input: UpdateKeyDescriptionRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures UpdateKeyDescriptionEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate UpdatePrimaryRegionEnsuresPublicly(input: UpdatePrimaryRegionRequest, output: Result<(), Error>)
    decreases input, output

  method UpdatePrimaryRegion(config: InternalConfig, input: UpdatePrimaryRegionRequest) returns (output: Result<(), Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures UpdatePrimaryRegionEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)

  predicate VerifyEnsuresPublicly(input: VerifyRequest, output: Result<VerifyResponse, Error>)
    decreases input, output

  method Verify(config: InternalConfig, input: VerifyRequest) returns (output: Result<VerifyResponse, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures VerifyEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
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

module Com {

  module Amazonaws {

    module {:extern ""software.amazon.cryptography.services.kms.internaldafny""} Kms refines AbstractComAmazonawsKmsService {
      function method DefaultKMSClientConfigType(): KMSClientConfigType
      {
        KMSClientConfigType
      }

      function method {:extern ""RegionMatch""} RegionMatch(client: IKMSClient, region: string): Option<bool>
        decreases client, region

      method {:extern} KMSClientForRegion(region: string) returns (res: Result<IKMSClient, Error>)
        ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
        decreases region

      function method DafnyUserAgentSuffix(runtime: string): string
        decreases runtime
      {
        var version: string := ""1.0.0"";
        ""AwsCryptographicMPL/"" + runtime + ""/"" + version
      }

      method {:extern} KMSClient() returns (res: Result<IKMSClient, Error>)
        ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()

      import opened Wrappers

      import opened UInt = StandardLibrary.UInt

      import opened UTF8

      import opened Types = ComAmazonawsKmsTypes

      datatype KMSClientConfigType = KMSClientConfigType
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
namespace software.amazon.cryptography.services.kms.internaldafny.types {

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
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DafnyCallEvent<I, O>;
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
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DafnyCallEvent.DafnyCallEvent";
      s += "(";
      s += Dafny.Helpers.ToString(this._input);
      s += ", ";
      s += Dafny.Helpers.ToString(this._output);
      s += ")";
      return s;
    }
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDafnyCallEvent<I, O> Default(I _default_I, O _default_O) {
      return create(_default_I, _default_O);
    }
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDafnyCallEvent<I, O>> _TypeDescriptor(Dafny.TypeDescriptor<I> _td_I, Dafny.TypeDescriptor<O> _td_O) {
      return new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDafnyCallEvent<I, O>>(software.amazon.cryptography.services.kms.internaldafny.types.DafnyCallEvent<I, O>.Default(_td_I.Default(), _td_O.Default()));
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

  public interface _IAlgorithmSpec {
    bool is_RSAES__PKCS1__V1__5 { get; }
    bool is_RSAES__OAEP__SHA__1 { get; }
    bool is_RSAES__OAEP__SHA__256 { get; }
    _IAlgorithmSpec DowncastClone();
  }
  public abstract class AlgorithmSpec : _IAlgorithmSpec {
    public AlgorithmSpec() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec theDefault = create_RSAES__PKCS1__V1__5();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec>(software.amazon.cryptography.services.kms.internaldafny.types.AlgorithmSpec.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAlgorithmSpec create_RSAES__PKCS1__V1__5() {
      return new AlgorithmSpec_RSAES__PKCS1__V1__5();
    }
    public static _IAlgorithmSpec create_RSAES__OAEP__SHA__1() {
      return new AlgorithmSpec_RSAES__OAEP__SHA__1();
    }
    public static _IAlgorithmSpec create_RSAES__OAEP__SHA__256() {
      return new AlgorithmSpec_RSAES__OAEP__SHA__256();
    }
    public bool is_RSAES__PKCS1__V1__5 { get { return this is AlgorithmSpec_RSAES__PKCS1__V1__5; } }
    public bool is_RSAES__OAEP__SHA__1 { get { return this is AlgorithmSpec_RSAES__OAEP__SHA__1; } }
    public bool is_RSAES__OAEP__SHA__256 { get { return this is AlgorithmSpec_RSAES__OAEP__SHA__256; } }
    public static System.Collections.Generic.IEnumerable<_IAlgorithmSpec> AllSingletonConstructors {
      get {
        yield return AlgorithmSpec.create_RSAES__PKCS1__V1__5();
        yield return AlgorithmSpec.create_RSAES__OAEP__SHA__1();
        yield return AlgorithmSpec.create_RSAES__OAEP__SHA__256();
      }
    }
    public abstract _IAlgorithmSpec DowncastClone();
  }
  public class AlgorithmSpec_RSAES__PKCS1__V1__5 : AlgorithmSpec {
    public AlgorithmSpec_RSAES__PKCS1__V1__5() {
    }
    public override _IAlgorithmSpec DowncastClone() {
      if (this is _IAlgorithmSpec dt) { return dt; }
      return new AlgorithmSpec_RSAES__PKCS1__V1__5();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.AlgorithmSpec_RSAES__PKCS1__V1__5;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.AlgorithmSpec.RSAES_PKCS1_V1_5";
      return s;
    }
  }
  public class AlgorithmSpec_RSAES__OAEP__SHA__1 : AlgorithmSpec {
    public AlgorithmSpec_RSAES__OAEP__SHA__1() {
    }
    public override _IAlgorithmSpec DowncastClone() {
      if (this is _IAlgorithmSpec dt) { return dt; }
      return new AlgorithmSpec_RSAES__OAEP__SHA__1();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.AlgorithmSpec_RSAES__OAEP__SHA__1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.AlgorithmSpec.RSAES_OAEP_SHA_1";
      return s;
    }
  }
  public class AlgorithmSpec_RSAES__OAEP__SHA__256 : AlgorithmSpec {
    public AlgorithmSpec_RSAES__OAEP__SHA__256() {
    }
    public override _IAlgorithmSpec DowncastClone() {
      if (this is _IAlgorithmSpec dt) { return dt; }
      return new AlgorithmSpec_RSAES__OAEP__SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.AlgorithmSpec_RSAES__OAEP__SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.AlgorithmSpec.RSAES_OAEP_SHA_256";
      return s;
    }
  }

  public interface _IAliasListEntry {
    bool is_AliasListEntry { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AliasName { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AliasArn { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_TargetKeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_LastUpdatedDate { get; }
    _IAliasListEntry DowncastClone();
  }
  public class AliasListEntry : _IAliasListEntry {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _AliasName;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _AliasArn;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _TargetKeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CreationDate;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _LastUpdatedDate;
    public AliasListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasName, Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasArn, Wrappers_Compile._IOption<Dafny.ISequence<char>> TargetKeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> LastUpdatedDate) {
      this._AliasName = AliasName;
      this._AliasArn = AliasArn;
      this._TargetKeyId = TargetKeyId;
      this._CreationDate = CreationDate;
      this._LastUpdatedDate = LastUpdatedDate;
    }
    public _IAliasListEntry DowncastClone() {
      if (this is _IAliasListEntry dt) { return dt; }
      return new AliasListEntry(_AliasName, _AliasArn, _TargetKeyId, _CreationDate, _LastUpdatedDate);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.AliasListEntry;
      return oth != null && object.Equals(this._AliasName, oth._AliasName) && object.Equals(this._AliasArn, oth._AliasArn) && object.Equals(this._TargetKeyId, oth._TargetKeyId) && object.Equals(this._CreationDate, oth._CreationDate) && object.Equals(this._LastUpdatedDate, oth._LastUpdatedDate);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._AliasName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._AliasArn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._TargetKeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CreationDate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._LastUpdatedDate));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.AliasListEntry.AliasListEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this._AliasName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._AliasArn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._TargetKeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CreationDate);
      s += ", ";
      s += Dafny.Helpers.ToString(this._LastUpdatedDate);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>(software.amazon.cryptography.services.kms.internaldafny.types.AliasListEntry.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAliasListEntry create(Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasName, Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasArn, Wrappers_Compile._IOption<Dafny.ISequence<char>> TargetKeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> LastUpdatedDate) {
      return new AliasListEntry(AliasName, AliasArn, TargetKeyId, CreationDate, LastUpdatedDate);
    }
    public static _IAliasListEntry create_AliasListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasName, Wrappers_Compile._IOption<Dafny.ISequence<char>> AliasArn, Wrappers_Compile._IOption<Dafny.ISequence<char>> TargetKeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> LastUpdatedDate) {
      return create(AliasName, AliasArn, TargetKeyId, CreationDate, LastUpdatedDate);
    }
    public bool is_AliasListEntry { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AliasName {
      get {
        return this._AliasName;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AliasArn {
      get {
        return this._AliasArn;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_TargetKeyId {
      get {
        return this._TargetKeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate {
      get {
        return this._CreationDate;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_LastUpdatedDate {
      get {
        return this._LastUpdatedDate;
      }
    }
  }

  public partial class AliasNameType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class ArnType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ICancelKeyDeletionRequest {
    bool is_CancelKeyDeletionRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _ICancelKeyDeletionRequest DowncastClone();
  }
  public class CancelKeyDeletionRequest : _ICancelKeyDeletionRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public CancelKeyDeletionRequest(Dafny.ISequence<char> KeyId) {
      this._KeyId = KeyId;
    }
    public _ICancelKeyDeletionRequest DowncastClone() {
      if (this is _ICancelKeyDeletionRequest dt) { return dt; }
      return new CancelKeyDeletionRequest(_KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CancelKeyDeletionRequest.CancelKeyDeletionRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionRequest>(software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICancelKeyDeletionRequest create(Dafny.ISequence<char> KeyId) {
      return new CancelKeyDeletionRequest(KeyId);
    }
    public static _ICancelKeyDeletionRequest create_CancelKeyDeletionRequest(Dafny.ISequence<char> KeyId) {
      return create(KeyId);
    }
    public bool is_CancelKeyDeletionRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
  }

  public interface _ICancelKeyDeletionResponse {
    bool is_CancelKeyDeletionResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    _ICancelKeyDeletionResponse DowncastClone();
  }
  public class CancelKeyDeletionResponse : _ICancelKeyDeletionResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public CancelKeyDeletionResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      this._KeyId = KeyId;
    }
    public _ICancelKeyDeletionResponse DowncastClone() {
      if (this is _ICancelKeyDeletionResponse dt) { return dt; }
      return new CancelKeyDeletionResponse(_KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionResponse;
      return oth != null && object.Equals(this._KeyId, oth._KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CancelKeyDeletionResponse.CancelKeyDeletionResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionResponse>(software.amazon.cryptography.services.kms.internaldafny.types.CancelKeyDeletionResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICancelKeyDeletionResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      return new CancelKeyDeletionResponse(KeyId);
    }
    public static _ICancelKeyDeletionResponse create_CancelKeyDeletionResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      return create(KeyId);
    }
    public bool is_CancelKeyDeletionResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
  }

  public partial class CiphertextType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Dafny.Sequence<byte>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class CloudHsmClusterIdType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IConnectCustomKeyStoreRequest {
    bool is_ConnectCustomKeyStoreRequest { get; }
    Dafny.ISequence<char> dtor_CustomKeyStoreId { get; }
    _IConnectCustomKeyStoreRequest DowncastClone();
  }
  public class ConnectCustomKeyStoreRequest : _IConnectCustomKeyStoreRequest {
    public readonly Dafny.ISequence<char> _CustomKeyStoreId;
    public ConnectCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId) {
      this._CustomKeyStoreId = CustomKeyStoreId;
    }
    public _IConnectCustomKeyStoreRequest DowncastClone() {
      if (this is _IConnectCustomKeyStoreRequest dt) { return dt; }
      return new ConnectCustomKeyStoreRequest(_CustomKeyStoreId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreRequest;
      return oth != null && object.Equals(this._CustomKeyStoreId, oth._CustomKeyStoreId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectCustomKeyStoreRequest.ConnectCustomKeyStoreRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreRequest>(software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConnectCustomKeyStoreRequest create(Dafny.ISequence<char> CustomKeyStoreId) {
      return new ConnectCustomKeyStoreRequest(CustomKeyStoreId);
    }
    public static _IConnectCustomKeyStoreRequest create_ConnectCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId) {
      return create(CustomKeyStoreId);
    }
    public bool is_ConnectCustomKeyStoreRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_CustomKeyStoreId {
      get {
        return this._CustomKeyStoreId;
      }
    }
  }

  public interface _IConnectCustomKeyStoreResponse {
    bool is_ConnectCustomKeyStoreResponse { get; }
    _IConnectCustomKeyStoreResponse DowncastClone();
  }
  public class ConnectCustomKeyStoreResponse : _IConnectCustomKeyStoreResponse {
    public ConnectCustomKeyStoreResponse() {
    }
    public _IConnectCustomKeyStoreResponse DowncastClone() {
      if (this is _IConnectCustomKeyStoreResponse dt) { return dt; }
      return new ConnectCustomKeyStoreResponse();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreResponse;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectCustomKeyStoreResponse.ConnectCustomKeyStoreResponse";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreResponse theDefault = create();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreResponse>(software.amazon.cryptography.services.kms.internaldafny.types.ConnectCustomKeyStoreResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConnectCustomKeyStoreResponse create() {
      return new ConnectCustomKeyStoreResponse();
    }
    public static _IConnectCustomKeyStoreResponse create_ConnectCustomKeyStoreResponse() {
      return create();
    }
    public bool is_ConnectCustomKeyStoreResponse { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IConnectCustomKeyStoreResponse> AllSingletonConstructors {
      get {
        yield return ConnectCustomKeyStoreResponse.create();
      }
    }
  }

  public interface _IConnectionErrorCodeType {
    bool is_INVALID__CREDENTIALS { get; }
    bool is_CLUSTER__NOT__FOUND { get; }
    bool is_NETWORK__ERRORS { get; }
    bool is_INTERNAL__ERROR { get; }
    bool is_INSUFFICIENT__CLOUDHSM__HSMS { get; }
    bool is_USER__LOCKED__OUT { get; }
    bool is_USER__NOT__FOUND { get; }
    bool is_USER__LOGGED__IN { get; }
    bool is_SUBNET__NOT__FOUND { get; }
    _IConnectionErrorCodeType DowncastClone();
  }
  public abstract class ConnectionErrorCodeType : _IConnectionErrorCodeType {
    public ConnectionErrorCodeType() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType theDefault = create_INVALID__CREDENTIALS();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType>(software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConnectionErrorCodeType create_INVALID__CREDENTIALS() {
      return new ConnectionErrorCodeType_INVALID__CREDENTIALS();
    }
    public static _IConnectionErrorCodeType create_CLUSTER__NOT__FOUND() {
      return new ConnectionErrorCodeType_CLUSTER__NOT__FOUND();
    }
    public static _IConnectionErrorCodeType create_NETWORK__ERRORS() {
      return new ConnectionErrorCodeType_NETWORK__ERRORS();
    }
    public static _IConnectionErrorCodeType create_INTERNAL__ERROR() {
      return new ConnectionErrorCodeType_INTERNAL__ERROR();
    }
    public static _IConnectionErrorCodeType create_INSUFFICIENT__CLOUDHSM__HSMS() {
      return new ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS();
    }
    public static _IConnectionErrorCodeType create_USER__LOCKED__OUT() {
      return new ConnectionErrorCodeType_USER__LOCKED__OUT();
    }
    public static _IConnectionErrorCodeType create_USER__NOT__FOUND() {
      return new ConnectionErrorCodeType_USER__NOT__FOUND();
    }
    public static _IConnectionErrorCodeType create_USER__LOGGED__IN() {
      return new ConnectionErrorCodeType_USER__LOGGED__IN();
    }
    public static _IConnectionErrorCodeType create_SUBNET__NOT__FOUND() {
      return new ConnectionErrorCodeType_SUBNET__NOT__FOUND();
    }
    public bool is_INVALID__CREDENTIALS { get { return this is ConnectionErrorCodeType_INVALID__CREDENTIALS; } }
    public bool is_CLUSTER__NOT__FOUND { get { return this is ConnectionErrorCodeType_CLUSTER__NOT__FOUND; } }
    public bool is_NETWORK__ERRORS { get { return this is ConnectionErrorCodeType_NETWORK__ERRORS; } }
    public bool is_INTERNAL__ERROR { get { return this is ConnectionErrorCodeType_INTERNAL__ERROR; } }
    public bool is_INSUFFICIENT__CLOUDHSM__HSMS { get { return this is ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS; } }
    public bool is_USER__LOCKED__OUT { get { return this is ConnectionErrorCodeType_USER__LOCKED__OUT; } }
    public bool is_USER__NOT__FOUND { get { return this is ConnectionErrorCodeType_USER__NOT__FOUND; } }
    public bool is_USER__LOGGED__IN { get { return this is ConnectionErrorCodeType_USER__LOGGED__IN; } }
    public bool is_SUBNET__NOT__FOUND { get { return this is ConnectionErrorCodeType_SUBNET__NOT__FOUND; } }
    public static System.Collections.Generic.IEnumerable<_IConnectionErrorCodeType> AllSingletonConstructors {
      get {
        yield return ConnectionErrorCodeType.create_INVALID__CREDENTIALS();
        yield return ConnectionErrorCodeType.create_CLUSTER__NOT__FOUND();
        yield return ConnectionErrorCodeType.create_NETWORK__ERRORS();
        yield return ConnectionErrorCodeType.create_INTERNAL__ERROR();
        yield return ConnectionErrorCodeType.create_INSUFFICIENT__CLOUDHSM__HSMS();
        yield return ConnectionErrorCodeType.create_USER__LOCKED__OUT();
        yield return ConnectionErrorCodeType.create_USER__NOT__FOUND();
        yield return ConnectionErrorCodeType.create_USER__LOGGED__IN();
        yield return ConnectionErrorCodeType.create_SUBNET__NOT__FOUND();
      }
    }
    public abstract _IConnectionErrorCodeType DowncastClone();
  }
  public class ConnectionErrorCodeType_INVALID__CREDENTIALS : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_INVALID__CREDENTIALS() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_INVALID__CREDENTIALS();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType_INVALID__CREDENTIALS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionErrorCodeType.INVALID_CREDENTIALS";
      return s;
    }
  }
  public class ConnectionErrorCodeType_CLUSTER__NOT__FOUND : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_CLUSTER__NOT__FOUND() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_CLUSTER__NOT__FOUND();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType_CLUSTER__NOT__FOUND;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionErrorCodeType.CLUSTER_NOT_FOUND";
      return s;
    }
  }
  public class ConnectionErrorCodeType_NETWORK__ERRORS : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_NETWORK__ERRORS() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_NETWORK__ERRORS();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType_NETWORK__ERRORS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionErrorCodeType.NETWORK_ERRORS";
      return s;
    }
  }
  public class ConnectionErrorCodeType_INTERNAL__ERROR : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_INTERNAL__ERROR() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_INTERNAL__ERROR();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType_INTERNAL__ERROR;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionErrorCodeType.INTERNAL_ERROR";
      return s;
    }
  }
  public class ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionErrorCodeType.INSUFFICIENT_CLOUDHSM_HSMS";
      return s;
    }
  }
  public class ConnectionErrorCodeType_USER__LOCKED__OUT : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_USER__LOCKED__OUT() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_USER__LOCKED__OUT();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType_USER__LOCKED__OUT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionErrorCodeType.USER_LOCKED_OUT";
      return s;
    }
  }
  public class ConnectionErrorCodeType_USER__NOT__FOUND : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_USER__NOT__FOUND() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_USER__NOT__FOUND();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType_USER__NOT__FOUND;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionErrorCodeType.USER_NOT_FOUND";
      return s;
    }
  }
  public class ConnectionErrorCodeType_USER__LOGGED__IN : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_USER__LOGGED__IN() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_USER__LOGGED__IN();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType_USER__LOGGED__IN;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionErrorCodeType.USER_LOGGED_IN";
      return s;
    }
  }
  public class ConnectionErrorCodeType_SUBNET__NOT__FOUND : ConnectionErrorCodeType {
    public ConnectionErrorCodeType_SUBNET__NOT__FOUND() {
    }
    public override _IConnectionErrorCodeType DowncastClone() {
      if (this is _IConnectionErrorCodeType dt) { return dt; }
      return new ConnectionErrorCodeType_SUBNET__NOT__FOUND();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionErrorCodeType_SUBNET__NOT__FOUND;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionErrorCodeType.SUBNET_NOT_FOUND";
      return s;
    }
  }

  public interface _IConnectionStateType {
    bool is_CONNECTED { get; }
    bool is_CONNECTING { get; }
    bool is_FAILED { get; }
    bool is_DISCONNECTED { get; }
    bool is_DISCONNECTING { get; }
    _IConnectionStateType DowncastClone();
  }
  public abstract class ConnectionStateType : _IConnectionStateType {
    public ConnectionStateType() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType theDefault = create_CONNECTED();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType>(software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConnectionStateType create_CONNECTED() {
      return new ConnectionStateType_CONNECTED();
    }
    public static _IConnectionStateType create_CONNECTING() {
      return new ConnectionStateType_CONNECTING();
    }
    public static _IConnectionStateType create_FAILED() {
      return new ConnectionStateType_FAILED();
    }
    public static _IConnectionStateType create_DISCONNECTED() {
      return new ConnectionStateType_DISCONNECTED();
    }
    public static _IConnectionStateType create_DISCONNECTING() {
      return new ConnectionStateType_DISCONNECTING();
    }
    public bool is_CONNECTED { get { return this is ConnectionStateType_CONNECTED; } }
    public bool is_CONNECTING { get { return this is ConnectionStateType_CONNECTING; } }
    public bool is_FAILED { get { return this is ConnectionStateType_FAILED; } }
    public bool is_DISCONNECTED { get { return this is ConnectionStateType_DISCONNECTED; } }
    public bool is_DISCONNECTING { get { return this is ConnectionStateType_DISCONNECTING; } }
    public static System.Collections.Generic.IEnumerable<_IConnectionStateType> AllSingletonConstructors {
      get {
        yield return ConnectionStateType.create_CONNECTED();
        yield return ConnectionStateType.create_CONNECTING();
        yield return ConnectionStateType.create_FAILED();
        yield return ConnectionStateType.create_DISCONNECTED();
        yield return ConnectionStateType.create_DISCONNECTING();
      }
    }
    public abstract _IConnectionStateType DowncastClone();
  }
  public class ConnectionStateType_CONNECTED : ConnectionStateType {
    public ConnectionStateType_CONNECTED() {
    }
    public override _IConnectionStateType DowncastClone() {
      if (this is _IConnectionStateType dt) { return dt; }
      return new ConnectionStateType_CONNECTED();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType_CONNECTED;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionStateType.CONNECTED";
      return s;
    }
  }
  public class ConnectionStateType_CONNECTING : ConnectionStateType {
    public ConnectionStateType_CONNECTING() {
    }
    public override _IConnectionStateType DowncastClone() {
      if (this is _IConnectionStateType dt) { return dt; }
      return new ConnectionStateType_CONNECTING();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType_CONNECTING;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionStateType.CONNECTING";
      return s;
    }
  }
  public class ConnectionStateType_FAILED : ConnectionStateType {
    public ConnectionStateType_FAILED() {
    }
    public override _IConnectionStateType DowncastClone() {
      if (this is _IConnectionStateType dt) { return dt; }
      return new ConnectionStateType_FAILED();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType_FAILED;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionStateType.FAILED";
      return s;
    }
  }
  public class ConnectionStateType_DISCONNECTED : ConnectionStateType {
    public ConnectionStateType_DISCONNECTED() {
    }
    public override _IConnectionStateType DowncastClone() {
      if (this is _IConnectionStateType dt) { return dt; }
      return new ConnectionStateType_DISCONNECTED();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType_DISCONNECTED;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionStateType.DISCONNECTED";
      return s;
    }
  }
  public class ConnectionStateType_DISCONNECTING : ConnectionStateType {
    public ConnectionStateType_DISCONNECTING() {
    }
    public override _IConnectionStateType DowncastClone() {
      if (this is _IConnectionStateType dt) { return dt; }
      return new ConnectionStateType_DISCONNECTING();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ConnectionStateType_DISCONNECTING;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ConnectionStateType.DISCONNECTING";
      return s;
    }
  }

  public interface _ICreateAliasRequest {
    bool is_CreateAliasRequest { get; }
    Dafny.ISequence<char> dtor_AliasName { get; }
    Dafny.ISequence<char> dtor_TargetKeyId { get; }
    _ICreateAliasRequest DowncastClone();
  }
  public class CreateAliasRequest : _ICreateAliasRequest {
    public readonly Dafny.ISequence<char> _AliasName;
    public readonly Dafny.ISequence<char> _TargetKeyId;
    public CreateAliasRequest(Dafny.ISequence<char> AliasName, Dafny.ISequence<char> TargetKeyId) {
      this._AliasName = AliasName;
      this._TargetKeyId = TargetKeyId;
    }
    public _ICreateAliasRequest DowncastClone() {
      if (this is _ICreateAliasRequest dt) { return dt; }
      return new CreateAliasRequest(_AliasName, _TargetKeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CreateAliasRequest;
      return oth != null && object.Equals(this._AliasName, oth._AliasName) && object.Equals(this._TargetKeyId, oth._TargetKeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._AliasName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._TargetKeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CreateAliasRequest.CreateAliasRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._AliasName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._TargetKeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ICreateAliasRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._ICreateAliasRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateAliasRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateAliasRequest>(software.amazon.cryptography.services.kms.internaldafny.types.CreateAliasRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateAliasRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateAliasRequest create(Dafny.ISequence<char> AliasName, Dafny.ISequence<char> TargetKeyId) {
      return new CreateAliasRequest(AliasName, TargetKeyId);
    }
    public static _ICreateAliasRequest create_CreateAliasRequest(Dafny.ISequence<char> AliasName, Dafny.ISequence<char> TargetKeyId) {
      return create(AliasName, TargetKeyId);
    }
    public bool is_CreateAliasRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_AliasName {
      get {
        return this._AliasName;
      }
    }
    public Dafny.ISequence<char> dtor_TargetKeyId {
      get {
        return this._TargetKeyId;
      }
    }
  }

  public interface _ICreateCustomKeyStoreRequest {
    bool is_CreateCustomKeyStoreRequest { get; }
    Dafny.ISequence<char> dtor_CustomKeyStoreName { get; }
    Dafny.ISequence<char> dtor_CloudHsmClusterId { get; }
    Dafny.ISequence<char> dtor_TrustAnchorCertificate { get; }
    Dafny.ISequence<char> dtor_KeyStorePassword { get; }
    _ICreateCustomKeyStoreRequest DowncastClone();
  }
  public class CreateCustomKeyStoreRequest : _ICreateCustomKeyStoreRequest {
    public readonly Dafny.ISequence<char> _CustomKeyStoreName;
    public readonly Dafny.ISequence<char> _CloudHsmClusterId;
    public readonly Dafny.ISequence<char> _TrustAnchorCertificate;
    public readonly Dafny.ISequence<char> _KeyStorePassword;
    public CreateCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreName, Dafny.ISequence<char> CloudHsmClusterId, Dafny.ISequence<char> TrustAnchorCertificate, Dafny.ISequence<char> KeyStorePassword) {
      this._CustomKeyStoreName = CustomKeyStoreName;
      this._CloudHsmClusterId = CloudHsmClusterId;
      this._TrustAnchorCertificate = TrustAnchorCertificate;
      this._KeyStorePassword = KeyStorePassword;
    }
    public _ICreateCustomKeyStoreRequest DowncastClone() {
      if (this is _ICreateCustomKeyStoreRequest dt) { return dt; }
      return new CreateCustomKeyStoreRequest(_CustomKeyStoreName, _CloudHsmClusterId, _TrustAnchorCertificate, _KeyStorePassword);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreRequest;
      return oth != null && object.Equals(this._CustomKeyStoreName, oth._CustomKeyStoreName) && object.Equals(this._CloudHsmClusterId, oth._CloudHsmClusterId) && object.Equals(this._TrustAnchorCertificate, oth._TrustAnchorCertificate) && object.Equals(this._KeyStorePassword, oth._KeyStorePassword);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CloudHsmClusterId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._TrustAnchorCertificate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyStorePassword));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CreateCustomKeyStoreRequest.CreateCustomKeyStoreRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CloudHsmClusterId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._TrustAnchorCertificate);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyStorePassword);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreRequest>(software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateCustomKeyStoreRequest create(Dafny.ISequence<char> CustomKeyStoreName, Dafny.ISequence<char> CloudHsmClusterId, Dafny.ISequence<char> TrustAnchorCertificate, Dafny.ISequence<char> KeyStorePassword) {
      return new CreateCustomKeyStoreRequest(CustomKeyStoreName, CloudHsmClusterId, TrustAnchorCertificate, KeyStorePassword);
    }
    public static _ICreateCustomKeyStoreRequest create_CreateCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreName, Dafny.ISequence<char> CloudHsmClusterId, Dafny.ISequence<char> TrustAnchorCertificate, Dafny.ISequence<char> KeyStorePassword) {
      return create(CustomKeyStoreName, CloudHsmClusterId, TrustAnchorCertificate, KeyStorePassword);
    }
    public bool is_CreateCustomKeyStoreRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_CustomKeyStoreName {
      get {
        return this._CustomKeyStoreName;
      }
    }
    public Dafny.ISequence<char> dtor_CloudHsmClusterId {
      get {
        return this._CloudHsmClusterId;
      }
    }
    public Dafny.ISequence<char> dtor_TrustAnchorCertificate {
      get {
        return this._TrustAnchorCertificate;
      }
    }
    public Dafny.ISequence<char> dtor_KeyStorePassword {
      get {
        return this._KeyStorePassword;
      }
    }
  }

  public interface _ICreateCustomKeyStoreResponse {
    bool is_CreateCustomKeyStoreResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    _ICreateCustomKeyStoreResponse DowncastClone();
  }
  public class CreateCustomKeyStoreResponse : _ICreateCustomKeyStoreResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CustomKeyStoreId;
    public CreateCustomKeyStoreResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId) {
      this._CustomKeyStoreId = CustomKeyStoreId;
    }
    public _ICreateCustomKeyStoreResponse DowncastClone() {
      if (this is _ICreateCustomKeyStoreResponse dt) { return dt; }
      return new CreateCustomKeyStoreResponse(_CustomKeyStoreId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreResponse;
      return oth != null && object.Equals(this._CustomKeyStoreId, oth._CustomKeyStoreId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CreateCustomKeyStoreResponse.CreateCustomKeyStoreResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreResponse>(software.amazon.cryptography.services.kms.internaldafny.types.CreateCustomKeyStoreResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateCustomKeyStoreResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId) {
      return new CreateCustomKeyStoreResponse(CustomKeyStoreId);
    }
    public static _ICreateCustomKeyStoreResponse create_CreateCustomKeyStoreResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId) {
      return create(CustomKeyStoreId);
    }
    public bool is_CreateCustomKeyStoreResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this._CustomKeyStoreId;
      }
    }
  }

  public interface _ICreateGrantRequest {
    bool is_CreateGrantRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_GranteePrincipal { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_RetiringPrincipal { get; }
    Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> dtor_Operations { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> dtor_Constraints { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Name { get; }
    _ICreateGrantRequest DowncastClone();
  }
  public class CreateGrantRequest : _ICreateGrantRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<char> _GranteePrincipal;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _RetiringPrincipal;
    public readonly Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> _Operations;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> _Constraints;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Name;
    public CreateGrantRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> GranteePrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal, Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> Operations, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> Constraints, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<Dafny.ISequence<char>> Name) {
      this._KeyId = KeyId;
      this._GranteePrincipal = GranteePrincipal;
      this._RetiringPrincipal = RetiringPrincipal;
      this._Operations = Operations;
      this._Constraints = Constraints;
      this._GrantTokens = GrantTokens;
      this._Name = Name;
    }
    public _ICreateGrantRequest DowncastClone() {
      if (this is _ICreateGrantRequest dt) { return dt; }
      return new CreateGrantRequest(_KeyId, _GranteePrincipal, _RetiringPrincipal, _Operations, _Constraints, _GrantTokens, _Name);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._GranteePrincipal, oth._GranteePrincipal) && object.Equals(this._RetiringPrincipal, oth._RetiringPrincipal) && object.Equals(this._Operations, oth._Operations) && object.Equals(this._Constraints, oth._Constraints) && object.Equals(this._GrantTokens, oth._GrantTokens) && object.Equals(this._Name, oth._Name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GranteePrincipal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._RetiringPrincipal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Operations));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Constraints));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CreateGrantRequest.CreateGrantRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GranteePrincipal);
      s += ", ";
      s += Dafny.Helpers.ToString(this._RetiringPrincipal);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Operations);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Constraints);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Name);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Dafny.Sequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>.Empty, Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantRequest>(software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateGrantRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> GranteePrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal, Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> Operations, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> Constraints, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<Dafny.ISequence<char>> Name) {
      return new CreateGrantRequest(KeyId, GranteePrincipal, RetiringPrincipal, Operations, Constraints, GrantTokens, Name);
    }
    public static _ICreateGrantRequest create_CreateGrantRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> GranteePrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal, Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> Operations, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> Constraints, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<Dafny.ISequence<char>> Name) {
      return create(KeyId, GranteePrincipal, RetiringPrincipal, Operations, Constraints, GrantTokens, Name);
    }
    public bool is_CreateGrantRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_GranteePrincipal {
      get {
        return this._GranteePrincipal;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_RetiringPrincipal {
      get {
        return this._RetiringPrincipal;
      }
    }
    public Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> dtor_Operations {
      get {
        return this._Operations;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> dtor_Constraints {
      get {
        return this._Constraints;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Name {
      get {
        return this._Name;
      }
    }
  }

  public interface _ICreateGrantResponse {
    bool is_CreateGrantResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantToken { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId { get; }
    _ICreateGrantResponse DowncastClone();
  }
  public class CreateGrantResponse : _ICreateGrantResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _GrantToken;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _GrantId;
    public CreateGrantResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId) {
      this._GrantToken = GrantToken;
      this._GrantId = GrantId;
    }
    public _ICreateGrantResponse DowncastClone() {
      if (this is _ICreateGrantResponse dt) { return dt; }
      return new CreateGrantResponse(_GrantToken, _GrantId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantResponse;
      return oth != null && object.Equals(this._GrantToken, oth._GrantToken) && object.Equals(this._GrantId, oth._GrantId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantToken));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CreateGrantResponse.CreateGrantResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._GrantToken);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantResponse>(software.amazon.cryptography.services.kms.internaldafny.types.CreateGrantResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateGrantResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId) {
      return new CreateGrantResponse(GrantToken, GrantId);
    }
    public static _ICreateGrantResponse create_CreateGrantResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId) {
      return create(GrantToken, GrantId);
    }
    public bool is_CreateGrantResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantToken {
      get {
        return this._GrantToken;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId {
      get {
        return this._GrantId;
      }
    }
  }

  public interface _ICreateKeyRequest {
    bool is_CreateKeyRequest { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> dtor_KeyUsage { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> dtor_KeySpec { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> dtor_Origin { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> dtor_Tags { get; }
    Wrappers_Compile._IOption<bool> dtor_MultiRegion { get; }
    _ICreateKeyRequest DowncastClone();
  }
  public class CreateKeyRequest : _ICreateKeyRequest {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Policy;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Description;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> _KeyUsage;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> _CustomerMasterKeySpec;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> _KeySpec;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> _Origin;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CustomKeyStoreId;
    public readonly Wrappers_Compile._IOption<bool> _BypassPolicyLockoutSafetyCheck;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> _Tags;
    public readonly Wrappers_Compile._IOption<bool> _MultiRegion;
    public CreateKeyRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> KeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> Origin, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> Tags, Wrappers_Compile._IOption<bool> MultiRegion) {
      this._Policy = Policy;
      this._Description = Description;
      this._KeyUsage = KeyUsage;
      this._CustomerMasterKeySpec = CustomerMasterKeySpec;
      this._KeySpec = KeySpec;
      this._Origin = Origin;
      this._CustomKeyStoreId = CustomKeyStoreId;
      this._BypassPolicyLockoutSafetyCheck = BypassPolicyLockoutSafetyCheck;
      this._Tags = Tags;
      this._MultiRegion = MultiRegion;
    }
    public _ICreateKeyRequest DowncastClone() {
      if (this is _ICreateKeyRequest dt) { return dt; }
      return new CreateKeyRequest(_Policy, _Description, _KeyUsage, _CustomerMasterKeySpec, _KeySpec, _Origin, _CustomKeyStoreId, _BypassPolicyLockoutSafetyCheck, _Tags, _MultiRegion);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyRequest;
      return oth != null && object.Equals(this._Policy, oth._Policy) && object.Equals(this._Description, oth._Description) && object.Equals(this._KeyUsage, oth._KeyUsage) && object.Equals(this._CustomerMasterKeySpec, oth._CustomerMasterKeySpec) && object.Equals(this._KeySpec, oth._KeySpec) && object.Equals(this._Origin, oth._Origin) && object.Equals(this._CustomKeyStoreId, oth._CustomKeyStoreId) && object.Equals(this._BypassPolicyLockoutSafetyCheck, oth._BypassPolicyLockoutSafetyCheck) && object.Equals(this._Tags, oth._Tags) && object.Equals(this._MultiRegion, oth._MultiRegion);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Policy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Description));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyUsage));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomerMasterKeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Origin));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._BypassPolicyLockoutSafetyCheck));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Tags));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._MultiRegion));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CreateKeyRequest.CreateKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._Policy);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Description);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyUsage);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CustomerMasterKeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Origin);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._BypassPolicyLockoutSafetyCheck);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Tags);
      s += ", ";
      s += Dafny.Helpers.ToString(this._MultiRegion);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyRequest theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default(), Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyRequest>(software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateKeyRequest create(Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> KeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> Origin, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> Tags, Wrappers_Compile._IOption<bool> MultiRegion) {
      return new CreateKeyRequest(Policy, Description, KeyUsage, CustomerMasterKeySpec, KeySpec, Origin, CustomKeyStoreId, BypassPolicyLockoutSafetyCheck, Tags, MultiRegion);
    }
    public static _ICreateKeyRequest create_CreateKeyRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> KeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> Origin, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> Tags, Wrappers_Compile._IOption<bool> MultiRegion) {
      return create(Policy, Description, KeyUsage, CustomerMasterKeySpec, KeySpec, Origin, CustomKeyStoreId, BypassPolicyLockoutSafetyCheck, Tags, MultiRegion);
    }
    public bool is_CreateKeyRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy {
      get {
        return this._Policy;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description {
      get {
        return this._Description;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> dtor_KeyUsage {
      get {
        return this._KeyUsage;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec {
      get {
        return this._CustomerMasterKeySpec;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> dtor_KeySpec {
      get {
        return this._KeySpec;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> dtor_Origin {
      get {
        return this._Origin;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this._CustomKeyStoreId;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck {
      get {
        return this._BypassPolicyLockoutSafetyCheck;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> dtor_Tags {
      get {
        return this._Tags;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_MultiRegion {
      get {
        return this._MultiRegion;
      }
    }
  }

  public interface _ICreateKeyResponse {
    bool is_CreateKeyResponse { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> dtor_KeyMetadata { get; }
    _ICreateKeyResponse DowncastClone();
  }
  public class CreateKeyResponse : _ICreateKeyResponse {
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> _KeyMetadata;
    public CreateKeyResponse(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> KeyMetadata) {
      this._KeyMetadata = KeyMetadata;
    }
    public _ICreateKeyResponse DowncastClone() {
      if (this is _ICreateKeyResponse dt) { return dt; }
      return new CreateKeyResponse(_KeyMetadata);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyResponse;
      return oth != null && object.Equals(this._KeyMetadata, oth._KeyMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyMetadata));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CreateKeyResponse.CreateKeyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyMetadata);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyResponse theDefault = create(Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyResponse>(software.amazon.cryptography.services.kms.internaldafny.types.CreateKeyResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICreateKeyResponse create(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> KeyMetadata) {
      return new CreateKeyResponse(KeyMetadata);
    }
    public static _ICreateKeyResponse create_CreateKeyResponse(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> KeyMetadata) {
      return create(KeyMetadata);
    }
    public bool is_CreateKeyResponse { get { return true; } }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> dtor_KeyMetadata {
      get {
        return this._KeyMetadata;
      }
    }
  }

  public interface _ICustomerMasterKeySpec {
    bool is_RSA__2048 { get; }
    bool is_RSA__3072 { get; }
    bool is_RSA__4096 { get; }
    bool is_ECC__NIST__P256 { get; }
    bool is_ECC__NIST__P384 { get; }
    bool is_ECC__NIST__P521 { get; }
    bool is_ECC__SECG__P256K1 { get; }
    bool is_SYMMETRIC__DEFAULT { get; }
    _ICustomerMasterKeySpec DowncastClone();
  }
  public abstract class CustomerMasterKeySpec : _ICustomerMasterKeySpec {
    public CustomerMasterKeySpec() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec theDefault = create_RSA__2048();
    public static software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec>(software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICustomerMasterKeySpec create_RSA__2048() {
      return new CustomerMasterKeySpec_RSA__2048();
    }
    public static _ICustomerMasterKeySpec create_RSA__3072() {
      return new CustomerMasterKeySpec_RSA__3072();
    }
    public static _ICustomerMasterKeySpec create_RSA__4096() {
      return new CustomerMasterKeySpec_RSA__4096();
    }
    public static _ICustomerMasterKeySpec create_ECC__NIST__P256() {
      return new CustomerMasterKeySpec_ECC__NIST__P256();
    }
    public static _ICustomerMasterKeySpec create_ECC__NIST__P384() {
      return new CustomerMasterKeySpec_ECC__NIST__P384();
    }
    public static _ICustomerMasterKeySpec create_ECC__NIST__P521() {
      return new CustomerMasterKeySpec_ECC__NIST__P521();
    }
    public static _ICustomerMasterKeySpec create_ECC__SECG__P256K1() {
      return new CustomerMasterKeySpec_ECC__SECG__P256K1();
    }
    public static _ICustomerMasterKeySpec create_SYMMETRIC__DEFAULT() {
      return new CustomerMasterKeySpec_SYMMETRIC__DEFAULT();
    }
    public bool is_RSA__2048 { get { return this is CustomerMasterKeySpec_RSA__2048; } }
    public bool is_RSA__3072 { get { return this is CustomerMasterKeySpec_RSA__3072; } }
    public bool is_RSA__4096 { get { return this is CustomerMasterKeySpec_RSA__4096; } }
    public bool is_ECC__NIST__P256 { get { return this is CustomerMasterKeySpec_ECC__NIST__P256; } }
    public bool is_ECC__NIST__P384 { get { return this is CustomerMasterKeySpec_ECC__NIST__P384; } }
    public bool is_ECC__NIST__P521 { get { return this is CustomerMasterKeySpec_ECC__NIST__P521; } }
    public bool is_ECC__SECG__P256K1 { get { return this is CustomerMasterKeySpec_ECC__SECG__P256K1; } }
    public bool is_SYMMETRIC__DEFAULT { get { return this is CustomerMasterKeySpec_SYMMETRIC__DEFAULT; } }
    public static System.Collections.Generic.IEnumerable<_ICustomerMasterKeySpec> AllSingletonConstructors {
      get {
        yield return CustomerMasterKeySpec.create_RSA__2048();
        yield return CustomerMasterKeySpec.create_RSA__3072();
        yield return CustomerMasterKeySpec.create_RSA__4096();
        yield return CustomerMasterKeySpec.create_ECC__NIST__P256();
        yield return CustomerMasterKeySpec.create_ECC__NIST__P384();
        yield return CustomerMasterKeySpec.create_ECC__NIST__P521();
        yield return CustomerMasterKeySpec.create_ECC__SECG__P256K1();
        yield return CustomerMasterKeySpec.create_SYMMETRIC__DEFAULT();
      }
    }
    public abstract _ICustomerMasterKeySpec DowncastClone();
  }
  public class CustomerMasterKeySpec_RSA__2048 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_RSA__2048() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_RSA__2048();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec_RSA__2048;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CustomerMasterKeySpec.RSA_2048";
      return s;
    }
  }
  public class CustomerMasterKeySpec_RSA__3072 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_RSA__3072() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_RSA__3072();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec_RSA__3072;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CustomerMasterKeySpec.RSA_3072";
      return s;
    }
  }
  public class CustomerMasterKeySpec_RSA__4096 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_RSA__4096() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_RSA__4096();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec_RSA__4096;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CustomerMasterKeySpec.RSA_4096";
      return s;
    }
  }
  public class CustomerMasterKeySpec_ECC__NIST__P256 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_ECC__NIST__P256() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_ECC__NIST__P256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec_ECC__NIST__P256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CustomerMasterKeySpec.ECC_NIST_P256";
      return s;
    }
  }
  public class CustomerMasterKeySpec_ECC__NIST__P384 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_ECC__NIST__P384() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_ECC__NIST__P384();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec_ECC__NIST__P384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CustomerMasterKeySpec.ECC_NIST_P384";
      return s;
    }
  }
  public class CustomerMasterKeySpec_ECC__NIST__P521 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_ECC__NIST__P521() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_ECC__NIST__P521();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec_ECC__NIST__P521;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CustomerMasterKeySpec.ECC_NIST_P521";
      return s;
    }
  }
  public class CustomerMasterKeySpec_ECC__SECG__P256K1 : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_ECC__SECG__P256K1() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_ECC__SECG__P256K1();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec_ECC__SECG__P256K1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CustomerMasterKeySpec.ECC_SECG_P256K1";
      return s;
    }
  }
  public class CustomerMasterKeySpec_SYMMETRIC__DEFAULT : CustomerMasterKeySpec {
    public CustomerMasterKeySpec_SYMMETRIC__DEFAULT() {
    }
    public override _ICustomerMasterKeySpec DowncastClone() {
      if (this is _ICustomerMasterKeySpec dt) { return dt; }
      return new CustomerMasterKeySpec_SYMMETRIC__DEFAULT();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec_SYMMETRIC__DEFAULT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CustomerMasterKeySpec.SYMMETRIC_DEFAULT";
      return s;
    }
  }

  public partial class CustomKeyStoreIdType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class CustomKeyStoreNameType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ICustomKeyStoresListEntry {
    bool is_CustomKeyStoresListEntry { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreName { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_TrustAnchorCertificate { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType> dtor_ConnectionState { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType> dtor_ConnectionErrorCode { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate { get; }
    _ICustomKeyStoresListEntry DowncastClone();
  }
  public class CustomKeyStoresListEntry : _ICustomKeyStoresListEntry {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CustomKeyStoreId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CustomKeyStoreName;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CloudHsmClusterId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _TrustAnchorCertificate;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType> _ConnectionState;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType> _ConnectionErrorCode;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CreationDate;
    public CustomKeyStoresListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId, Wrappers_Compile._IOption<Dafny.ISequence<char>> TrustAnchorCertificate, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType> ConnectionState, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType> ConnectionErrorCode, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate) {
      this._CustomKeyStoreId = CustomKeyStoreId;
      this._CustomKeyStoreName = CustomKeyStoreName;
      this._CloudHsmClusterId = CloudHsmClusterId;
      this._TrustAnchorCertificate = TrustAnchorCertificate;
      this._ConnectionState = ConnectionState;
      this._ConnectionErrorCode = ConnectionErrorCode;
      this._CreationDate = CreationDate;
    }
    public _ICustomKeyStoresListEntry DowncastClone() {
      if (this is _ICustomKeyStoresListEntry dt) { return dt; }
      return new CustomKeyStoresListEntry(_CustomKeyStoreId, _CustomKeyStoreName, _CloudHsmClusterId, _TrustAnchorCertificate, _ConnectionState, _ConnectionErrorCode, _CreationDate);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.CustomKeyStoresListEntry;
      return oth != null && object.Equals(this._CustomKeyStoreId, oth._CustomKeyStoreId) && object.Equals(this._CustomKeyStoreName, oth._CustomKeyStoreName) && object.Equals(this._CloudHsmClusterId, oth._CloudHsmClusterId) && object.Equals(this._TrustAnchorCertificate, oth._TrustAnchorCertificate) && object.Equals(this._ConnectionState, oth._ConnectionState) && object.Equals(this._ConnectionErrorCode, oth._ConnectionErrorCode) && object.Equals(this._CreationDate, oth._CreationDate);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CloudHsmClusterId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._TrustAnchorCertificate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ConnectionState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ConnectionErrorCode));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CreationDate));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.CustomKeyStoresListEntry.CustomKeyStoresListEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CloudHsmClusterId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._TrustAnchorCertificate);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ConnectionState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ConnectionErrorCode);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CreationDate);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>(software.amazon.cryptography.services.kms.internaldafny.types.CustomKeyStoresListEntry.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICustomKeyStoresListEntry create(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId, Wrappers_Compile._IOption<Dafny.ISequence<char>> TrustAnchorCertificate, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType> ConnectionState, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType> ConnectionErrorCode, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate) {
      return new CustomKeyStoresListEntry(CustomKeyStoreId, CustomKeyStoreName, CloudHsmClusterId, TrustAnchorCertificate, ConnectionState, ConnectionErrorCode, CreationDate);
    }
    public static _ICustomKeyStoresListEntry create_CustomKeyStoresListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId, Wrappers_Compile._IOption<Dafny.ISequence<char>> TrustAnchorCertificate, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType> ConnectionState, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType> ConnectionErrorCode, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate) {
      return create(CustomKeyStoreId, CustomKeyStoreName, CloudHsmClusterId, TrustAnchorCertificate, ConnectionState, ConnectionErrorCode, CreationDate);
    }
    public bool is_CustomKeyStoresListEntry { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this._CustomKeyStoreId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreName {
      get {
        return this._CustomKeyStoreName;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId {
      get {
        return this._CloudHsmClusterId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_TrustAnchorCertificate {
      get {
        return this._TrustAnchorCertificate;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionStateType> dtor_ConnectionState {
      get {
        return this._ConnectionState;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IConnectionErrorCodeType> dtor_ConnectionErrorCode {
      get {
        return this._ConnectionErrorCode;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate {
      get {
        return this._CreationDate;
      }
    }
  }

  public interface _IDataKeyPairSpec {
    bool is_RSA__2048 { get; }
    bool is_RSA__3072 { get; }
    bool is_RSA__4096 { get; }
    bool is_ECC__NIST__P256 { get; }
    bool is_ECC__NIST__P384 { get; }
    bool is_ECC__NIST__P521 { get; }
    bool is_ECC__SECG__P256K1 { get; }
    _IDataKeyPairSpec DowncastClone();
  }
  public abstract class DataKeyPairSpec : _IDataKeyPairSpec {
    public DataKeyPairSpec() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec theDefault = create_RSA__2048();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec>(software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDataKeyPairSpec create_RSA__2048() {
      return new DataKeyPairSpec_RSA__2048();
    }
    public static _IDataKeyPairSpec create_RSA__3072() {
      return new DataKeyPairSpec_RSA__3072();
    }
    public static _IDataKeyPairSpec create_RSA__4096() {
      return new DataKeyPairSpec_RSA__4096();
    }
    public static _IDataKeyPairSpec create_ECC__NIST__P256() {
      return new DataKeyPairSpec_ECC__NIST__P256();
    }
    public static _IDataKeyPairSpec create_ECC__NIST__P384() {
      return new DataKeyPairSpec_ECC__NIST__P384();
    }
    public static _IDataKeyPairSpec create_ECC__NIST__P521() {
      return new DataKeyPairSpec_ECC__NIST__P521();
    }
    public static _IDataKeyPairSpec create_ECC__SECG__P256K1() {
      return new DataKeyPairSpec_ECC__SECG__P256K1();
    }
    public bool is_RSA__2048 { get { return this is DataKeyPairSpec_RSA__2048; } }
    public bool is_RSA__3072 { get { return this is DataKeyPairSpec_RSA__3072; } }
    public bool is_RSA__4096 { get { return this is DataKeyPairSpec_RSA__4096; } }
    public bool is_ECC__NIST__P256 { get { return this is DataKeyPairSpec_ECC__NIST__P256; } }
    public bool is_ECC__NIST__P384 { get { return this is DataKeyPairSpec_ECC__NIST__P384; } }
    public bool is_ECC__NIST__P521 { get { return this is DataKeyPairSpec_ECC__NIST__P521; } }
    public bool is_ECC__SECG__P256K1 { get { return this is DataKeyPairSpec_ECC__SECG__P256K1; } }
    public static System.Collections.Generic.IEnumerable<_IDataKeyPairSpec> AllSingletonConstructors {
      get {
        yield return DataKeyPairSpec.create_RSA__2048();
        yield return DataKeyPairSpec.create_RSA__3072();
        yield return DataKeyPairSpec.create_RSA__4096();
        yield return DataKeyPairSpec.create_ECC__NIST__P256();
        yield return DataKeyPairSpec.create_ECC__NIST__P384();
        yield return DataKeyPairSpec.create_ECC__NIST__P521();
        yield return DataKeyPairSpec.create_ECC__SECG__P256K1();
      }
    }
    public abstract _IDataKeyPairSpec DowncastClone();
  }
  public class DataKeyPairSpec_RSA__2048 : DataKeyPairSpec {
    public DataKeyPairSpec_RSA__2048() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_RSA__2048();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec_RSA__2048;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DataKeyPairSpec.RSA_2048";
      return s;
    }
  }
  public class DataKeyPairSpec_RSA__3072 : DataKeyPairSpec {
    public DataKeyPairSpec_RSA__3072() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_RSA__3072();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec_RSA__3072;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DataKeyPairSpec.RSA_3072";
      return s;
    }
  }
  public class DataKeyPairSpec_RSA__4096 : DataKeyPairSpec {
    public DataKeyPairSpec_RSA__4096() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_RSA__4096();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec_RSA__4096;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DataKeyPairSpec.RSA_4096";
      return s;
    }
  }
  public class DataKeyPairSpec_ECC__NIST__P256 : DataKeyPairSpec {
    public DataKeyPairSpec_ECC__NIST__P256() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_ECC__NIST__P256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec_ECC__NIST__P256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DataKeyPairSpec.ECC_NIST_P256";
      return s;
    }
  }
  public class DataKeyPairSpec_ECC__NIST__P384 : DataKeyPairSpec {
    public DataKeyPairSpec_ECC__NIST__P384() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_ECC__NIST__P384();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec_ECC__NIST__P384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DataKeyPairSpec.ECC_NIST_P384";
      return s;
    }
  }
  public class DataKeyPairSpec_ECC__NIST__P521 : DataKeyPairSpec {
    public DataKeyPairSpec_ECC__NIST__P521() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_ECC__NIST__P521();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec_ECC__NIST__P521;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DataKeyPairSpec.ECC_NIST_P521";
      return s;
    }
  }
  public class DataKeyPairSpec_ECC__SECG__P256K1 : DataKeyPairSpec {
    public DataKeyPairSpec_ECC__SECG__P256K1() {
    }
    public override _IDataKeyPairSpec DowncastClone() {
      if (this is _IDataKeyPairSpec dt) { return dt; }
      return new DataKeyPairSpec_ECC__SECG__P256K1();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec_ECC__SECG__P256K1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DataKeyPairSpec.ECC_SECG_P256K1";
      return s;
    }
  }

  public interface _IDataKeySpec {
    bool is_AES__256 { get; }
    bool is_AES__128 { get; }
    _IDataKeySpec DowncastClone();
  }
  public abstract class DataKeySpec : _IDataKeySpec {
    public DataKeySpec() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec theDefault = create_AES__256();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec>(software.amazon.cryptography.services.kms.internaldafny.types.DataKeySpec.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDataKeySpec create_AES__256() {
      return new DataKeySpec_AES__256();
    }
    public static _IDataKeySpec create_AES__128() {
      return new DataKeySpec_AES__128();
    }
    public bool is_AES__256 { get { return this is DataKeySpec_AES__256; } }
    public bool is_AES__128 { get { return this is DataKeySpec_AES__128; } }
    public static System.Collections.Generic.IEnumerable<_IDataKeySpec> AllSingletonConstructors {
      get {
        yield return DataKeySpec.create_AES__256();
        yield return DataKeySpec.create_AES__128();
      }
    }
    public abstract _IDataKeySpec DowncastClone();
  }
  public class DataKeySpec_AES__256 : DataKeySpec {
    public DataKeySpec_AES__256() {
    }
    public override _IDataKeySpec DowncastClone() {
      if (this is _IDataKeySpec dt) { return dt; }
      return new DataKeySpec_AES__256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DataKeySpec_AES__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DataKeySpec.AES_256";
      return s;
    }
  }
  public class DataKeySpec_AES__128 : DataKeySpec {
    public DataKeySpec_AES__128() {
    }
    public override _IDataKeySpec DowncastClone() {
      if (this is _IDataKeySpec dt) { return dt; }
      return new DataKeySpec_AES__128();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DataKeySpec_AES__128;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DataKeySpec.AES_128";
      return s;
    }
  }

  public interface _IDecryptRequest {
    bool is_DecryptRequest { get; }
    Dafny.ISequence<byte> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm { get; }
    _IDecryptRequest DowncastClone();
  }
  public class DecryptRequest : _IDecryptRequest {
    public readonly Dafny.ISequence<byte> _CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _EncryptionContext;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _EncryptionAlgorithm;
    public DecryptRequest(Dafny.ISequence<byte> CiphertextBlob, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      this._CiphertextBlob = CiphertextBlob;
      this._EncryptionContext = EncryptionContext;
      this._GrantTokens = GrantTokens;
      this._KeyId = KeyId;
      this._EncryptionAlgorithm = EncryptionAlgorithm;
    }
    public _IDecryptRequest DowncastClone() {
      if (this is _IDecryptRequest dt) { return dt; }
      return new DecryptRequest(_CiphertextBlob, _EncryptionContext, _GrantTokens, _KeyId, _EncryptionAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest;
      return oth != null && object.Equals(this._CiphertextBlob, oth._CiphertextBlob) && object.Equals(this._EncryptionContext, oth._EncryptionContext) && object.Equals(this._GrantTokens, oth._GrantTokens) && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._EncryptionAlgorithm, oth._EncryptionAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DecryptRequest.DecryptRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptionAlgorithm);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest theDefault = create(Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest>(software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDecryptRequest create(Dafny.ISequence<byte> CiphertextBlob, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return new DecryptRequest(CiphertextBlob, EncryptionContext, GrantTokens, KeyId, EncryptionAlgorithm);
    }
    public static _IDecryptRequest create_DecryptRequest(Dafny.ISequence<byte> CiphertextBlob, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return create(CiphertextBlob, EncryptionContext, GrantTokens, KeyId, EncryptionAlgorithm);
    }
    public bool is_DecryptRequest { get { return true; } }
    public Dafny.ISequence<byte> dtor_CiphertextBlob {
      get {
        return this._CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this._EncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm {
      get {
        return this._EncryptionAlgorithm;
      }
    }
  }

  public interface _IDecryptResponse {
    bool is_DecryptResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm { get; }
    _IDecryptResponse DowncastClone();
  }
  public class DecryptResponse : _IDecryptResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _Plaintext;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _EncryptionAlgorithm;
    public DecryptResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      this._KeyId = KeyId;
      this._Plaintext = Plaintext;
      this._EncryptionAlgorithm = EncryptionAlgorithm;
    }
    public _IDecryptResponse DowncastClone() {
      if (this is _IDecryptResponse dt) { return dt; }
      return new DecryptResponse(_KeyId, _Plaintext, _EncryptionAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DecryptResponse;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._Plaintext, oth._Plaintext) && object.Equals(this._EncryptionAlgorithm, oth._EncryptionAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Plaintext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DecryptResponse.DecryptResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Plaintext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptionAlgorithm);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse>(software.amazon.cryptography.services.kms.internaldafny.types.DecryptResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDecryptResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return new DecryptResponse(KeyId, Plaintext, EncryptionAlgorithm);
    }
    public static _IDecryptResponse create_DecryptResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return create(KeyId, Plaintext, EncryptionAlgorithm);
    }
    public bool is_DecryptResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext {
      get {
        return this._Plaintext;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm {
      get {
        return this._EncryptionAlgorithm;
      }
    }
  }

  public interface _IDeleteAliasRequest {
    bool is_DeleteAliasRequest { get; }
    Dafny.ISequence<char> dtor_AliasName { get; }
    _IDeleteAliasRequest DowncastClone();
  }
  public class DeleteAliasRequest : _IDeleteAliasRequest {
    public readonly Dafny.ISequence<char> _AliasName;
    public DeleteAliasRequest(Dafny.ISequence<char> AliasName) {
      this._AliasName = AliasName;
    }
    public _IDeleteAliasRequest DowncastClone() {
      if (this is _IDeleteAliasRequest dt) { return dt; }
      return new DeleteAliasRequest(_AliasName);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DeleteAliasRequest;
      return oth != null && object.Equals(this._AliasName, oth._AliasName);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._AliasName));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DeleteAliasRequest.DeleteAliasRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._AliasName);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDeleteAliasRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDeleteAliasRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteAliasRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteAliasRequest>(software.amazon.cryptography.services.kms.internaldafny.types.DeleteAliasRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteAliasRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeleteAliasRequest create(Dafny.ISequence<char> AliasName) {
      return new DeleteAliasRequest(AliasName);
    }
    public static _IDeleteAliasRequest create_DeleteAliasRequest(Dafny.ISequence<char> AliasName) {
      return create(AliasName);
    }
    public bool is_DeleteAliasRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_AliasName {
      get {
        return this._AliasName;
      }
    }
  }

  public interface _IDeleteCustomKeyStoreRequest {
    bool is_DeleteCustomKeyStoreRequest { get; }
    Dafny.ISequence<char> dtor_CustomKeyStoreId { get; }
    _IDeleteCustomKeyStoreRequest DowncastClone();
  }
  public class DeleteCustomKeyStoreRequest : _IDeleteCustomKeyStoreRequest {
    public readonly Dafny.ISequence<char> _CustomKeyStoreId;
    public DeleteCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId) {
      this._CustomKeyStoreId = CustomKeyStoreId;
    }
    public _IDeleteCustomKeyStoreRequest DowncastClone() {
      if (this is _IDeleteCustomKeyStoreRequest dt) { return dt; }
      return new DeleteCustomKeyStoreRequest(_CustomKeyStoreId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreRequest;
      return oth != null && object.Equals(this._CustomKeyStoreId, oth._CustomKeyStoreId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DeleteCustomKeyStoreRequest.DeleteCustomKeyStoreRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreRequest>(software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeleteCustomKeyStoreRequest create(Dafny.ISequence<char> CustomKeyStoreId) {
      return new DeleteCustomKeyStoreRequest(CustomKeyStoreId);
    }
    public static _IDeleteCustomKeyStoreRequest create_DeleteCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId) {
      return create(CustomKeyStoreId);
    }
    public bool is_DeleteCustomKeyStoreRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_CustomKeyStoreId {
      get {
        return this._CustomKeyStoreId;
      }
    }
  }

  public interface _IDeleteCustomKeyStoreResponse {
    bool is_DeleteCustomKeyStoreResponse { get; }
    _IDeleteCustomKeyStoreResponse DowncastClone();
  }
  public class DeleteCustomKeyStoreResponse : _IDeleteCustomKeyStoreResponse {
    public DeleteCustomKeyStoreResponse() {
    }
    public _IDeleteCustomKeyStoreResponse DowncastClone() {
      if (this is _IDeleteCustomKeyStoreResponse dt) { return dt; }
      return new DeleteCustomKeyStoreResponse();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreResponse;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DeleteCustomKeyStoreResponse.DeleteCustomKeyStoreResponse";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreResponse theDefault = create();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreResponse>(software.amazon.cryptography.services.kms.internaldafny.types.DeleteCustomKeyStoreResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeleteCustomKeyStoreResponse create() {
      return new DeleteCustomKeyStoreResponse();
    }
    public static _IDeleteCustomKeyStoreResponse create_DeleteCustomKeyStoreResponse() {
      return create();
    }
    public bool is_DeleteCustomKeyStoreResponse { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IDeleteCustomKeyStoreResponse> AllSingletonConstructors {
      get {
        yield return DeleteCustomKeyStoreResponse.create();
      }
    }
  }

  public interface _IDeleteImportedKeyMaterialRequest {
    bool is_DeleteImportedKeyMaterialRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IDeleteImportedKeyMaterialRequest DowncastClone();
  }
  public class DeleteImportedKeyMaterialRequest : _IDeleteImportedKeyMaterialRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public DeleteImportedKeyMaterialRequest(Dafny.ISequence<char> KeyId) {
      this._KeyId = KeyId;
    }
    public _IDeleteImportedKeyMaterialRequest DowncastClone() {
      if (this is _IDeleteImportedKeyMaterialRequest dt) { return dt; }
      return new DeleteImportedKeyMaterialRequest(_KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DeleteImportedKeyMaterialRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DeleteImportedKeyMaterialRequest.DeleteImportedKeyMaterialRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDeleteImportedKeyMaterialRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDeleteImportedKeyMaterialRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteImportedKeyMaterialRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteImportedKeyMaterialRequest>(software.amazon.cryptography.services.kms.internaldafny.types.DeleteImportedKeyMaterialRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteImportedKeyMaterialRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeleteImportedKeyMaterialRequest create(Dafny.ISequence<char> KeyId) {
      return new DeleteImportedKeyMaterialRequest(KeyId);
    }
    public static _IDeleteImportedKeyMaterialRequest create_DeleteImportedKeyMaterialRequest(Dafny.ISequence<char> KeyId) {
      return create(KeyId);
    }
    public bool is_DeleteImportedKeyMaterialRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
  }

  public interface _IDescribeCustomKeyStoresRequest {
    bool is_DescribeCustomKeyStoresRequest { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreName { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    _IDescribeCustomKeyStoresRequest DowncastClone();
  }
  public class DescribeCustomKeyStoresRequest : _IDescribeCustomKeyStoresRequest {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CustomKeyStoreId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CustomKeyStoreName;
    public readonly Wrappers_Compile._IOption<int> _Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Marker;
    public DescribeCustomKeyStoresRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      this._CustomKeyStoreId = CustomKeyStoreId;
      this._CustomKeyStoreName = CustomKeyStoreName;
      this._Limit = Limit;
      this._Marker = Marker;
    }
    public _IDescribeCustomKeyStoresRequest DowncastClone() {
      if (this is _IDescribeCustomKeyStoresRequest dt) { return dt; }
      return new DescribeCustomKeyStoresRequest(_CustomKeyStoreId, _CustomKeyStoreName, _Limit, _Marker);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresRequest;
      return oth != null && object.Equals(this._CustomKeyStoreId, oth._CustomKeyStoreId) && object.Equals(this._CustomKeyStoreName, oth._CustomKeyStoreName) && object.Equals(this._Limit, oth._Limit) && object.Equals(this._Marker, oth._Marker);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Marker));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DescribeCustomKeyStoresRequest.DescribeCustomKeyStoresRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Marker);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresRequest theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresRequest>(software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDescribeCustomKeyStoresRequest create(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return new DescribeCustomKeyStoresRequest(CustomKeyStoreId, CustomKeyStoreName, Limit, Marker);
    }
    public static _IDescribeCustomKeyStoresRequest create_DescribeCustomKeyStoresRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreName, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return create(CustomKeyStoreId, CustomKeyStoreName, Limit, Marker);
    }
    public bool is_DescribeCustomKeyStoresRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this._CustomKeyStoreId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreName {
      get {
        return this._CustomKeyStoreName;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this._Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this._Marker;
      }
    }
  }

  public interface _IDescribeCustomKeyStoresResponse {
    bool is_DescribeCustomKeyStoresResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>> dtor_CustomKeyStores { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker { get; }
    Wrappers_Compile._IOption<bool> dtor_Truncated { get; }
    _IDescribeCustomKeyStoresResponse DowncastClone();
  }
  public class DescribeCustomKeyStoresResponse : _IDescribeCustomKeyStoresResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>> _CustomKeyStores;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _NextMarker;
    public readonly Wrappers_Compile._IOption<bool> _Truncated;
    public DescribeCustomKeyStoresResponse(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>> CustomKeyStores, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      this._CustomKeyStores = CustomKeyStores;
      this._NextMarker = NextMarker;
      this._Truncated = Truncated;
    }
    public _IDescribeCustomKeyStoresResponse DowncastClone() {
      if (this is _IDescribeCustomKeyStoresResponse dt) { return dt; }
      return new DescribeCustomKeyStoresResponse(_CustomKeyStores, _NextMarker, _Truncated);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresResponse;
      return oth != null && object.Equals(this._CustomKeyStores, oth._CustomKeyStores) && object.Equals(this._NextMarker, oth._NextMarker) && object.Equals(this._Truncated, oth._Truncated);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStores));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._NextMarker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Truncated));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DescribeCustomKeyStoresResponse.DescribeCustomKeyStoresResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._CustomKeyStores);
      s += ", ";
      s += Dafny.Helpers.ToString(this._NextMarker);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Truncated);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresResponse>(software.amazon.cryptography.services.kms.internaldafny.types.DescribeCustomKeyStoresResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDescribeCustomKeyStoresResponse create(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>> CustomKeyStores, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return new DescribeCustomKeyStoresResponse(CustomKeyStores, NextMarker, Truncated);
    }
    public static _IDescribeCustomKeyStoresResponse create_DescribeCustomKeyStoresResponse(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>> CustomKeyStores, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return create(CustomKeyStores, NextMarker, Truncated);
    }
    public bool is_DescribeCustomKeyStoresResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ICustomKeyStoresListEntry>> dtor_CustomKeyStores {
      get {
        return this._CustomKeyStores;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker {
      get {
        return this._NextMarker;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Truncated {
      get {
        return this._Truncated;
      }
    }
  }

  public interface _IDescribeKeyRequest {
    bool is_DescribeKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IDescribeKeyRequest DowncastClone();
  }
  public class DescribeKeyRequest : _IDescribeKeyRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public DescribeKeyRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this._KeyId = KeyId;
      this._GrantTokens = GrantTokens;
    }
    public _IDescribeKeyRequest DowncastClone() {
      if (this is _IDescribeKeyRequest dt) { return dt; }
      return new DescribeKeyRequest(_KeyId, _GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._GrantTokens, oth._GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DescribeKeyRequest.DescribeKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyRequest>(software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDescribeKeyRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new DescribeKeyRequest(KeyId, GrantTokens);
    }
    public static _IDescribeKeyRequest create_DescribeKeyRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return create(KeyId, GrantTokens);
    }
    public bool is_DescribeKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
  }

  public interface _IDescribeKeyResponse {
    bool is_DescribeKeyResponse { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> dtor_KeyMetadata { get; }
    _IDescribeKeyResponse DowncastClone();
  }
  public class DescribeKeyResponse : _IDescribeKeyResponse {
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> _KeyMetadata;
    public DescribeKeyResponse(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> KeyMetadata) {
      this._KeyMetadata = KeyMetadata;
    }
    public _IDescribeKeyResponse DowncastClone() {
      if (this is _IDescribeKeyResponse dt) { return dt; }
      return new DescribeKeyResponse(_KeyMetadata);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyResponse;
      return oth != null && object.Equals(this._KeyMetadata, oth._KeyMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyMetadata));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DescribeKeyResponse.DescribeKeyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyMetadata);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyResponse theDefault = create(Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyResponse>(software.amazon.cryptography.services.kms.internaldafny.types.DescribeKeyResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDescribeKeyResponse create(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> KeyMetadata) {
      return new DescribeKeyResponse(KeyMetadata);
    }
    public static _IDescribeKeyResponse create_DescribeKeyResponse(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> KeyMetadata) {
      return create(KeyMetadata);
    }
    public bool is_DescribeKeyResponse { get { return true; } }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> dtor_KeyMetadata {
      get {
        return this._KeyMetadata;
      }
    }
  }

  public partial class DescriptionType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IDisableKeyRequest {
    bool is_DisableKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IDisableKeyRequest DowncastClone();
  }
  public class DisableKeyRequest : _IDisableKeyRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public DisableKeyRequest(Dafny.ISequence<char> KeyId) {
      this._KeyId = KeyId;
    }
    public _IDisableKeyRequest DowncastClone() {
      if (this is _IDisableKeyRequest dt) { return dt; }
      return new DisableKeyRequest(_KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DisableKeyRequest.DisableKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRequest>(software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDisableKeyRequest create(Dafny.ISequence<char> KeyId) {
      return new DisableKeyRequest(KeyId);
    }
    public static _IDisableKeyRequest create_DisableKeyRequest(Dafny.ISequence<char> KeyId) {
      return create(KeyId);
    }
    public bool is_DisableKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
  }

  public interface _IDisableKeyRotationRequest {
    bool is_DisableKeyRotationRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IDisableKeyRotationRequest DowncastClone();
  }
  public class DisableKeyRotationRequest : _IDisableKeyRotationRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public DisableKeyRotationRequest(Dafny.ISequence<char> KeyId) {
      this._KeyId = KeyId;
    }
    public _IDisableKeyRotationRequest DowncastClone() {
      if (this is _IDisableKeyRotationRequest dt) { return dt; }
      return new DisableKeyRotationRequest(_KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRotationRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DisableKeyRotationRequest.DisableKeyRotationRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRotationRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRotationRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRotationRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRotationRequest>(software.amazon.cryptography.services.kms.internaldafny.types.DisableKeyRotationRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRotationRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDisableKeyRotationRequest create(Dafny.ISequence<char> KeyId) {
      return new DisableKeyRotationRequest(KeyId);
    }
    public static _IDisableKeyRotationRequest create_DisableKeyRotationRequest(Dafny.ISequence<char> KeyId) {
      return create(KeyId);
    }
    public bool is_DisableKeyRotationRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
  }

  public interface _IDisconnectCustomKeyStoreRequest {
    bool is_DisconnectCustomKeyStoreRequest { get; }
    Dafny.ISequence<char> dtor_CustomKeyStoreId { get; }
    _IDisconnectCustomKeyStoreRequest DowncastClone();
  }
  public class DisconnectCustomKeyStoreRequest : _IDisconnectCustomKeyStoreRequest {
    public readonly Dafny.ISequence<char> _CustomKeyStoreId;
    public DisconnectCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId) {
      this._CustomKeyStoreId = CustomKeyStoreId;
    }
    public _IDisconnectCustomKeyStoreRequest DowncastClone() {
      if (this is _IDisconnectCustomKeyStoreRequest dt) { return dt; }
      return new DisconnectCustomKeyStoreRequest(_CustomKeyStoreId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreRequest;
      return oth != null && object.Equals(this._CustomKeyStoreId, oth._CustomKeyStoreId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DisconnectCustomKeyStoreRequest.DisconnectCustomKeyStoreRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreRequest>(software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDisconnectCustomKeyStoreRequest create(Dafny.ISequence<char> CustomKeyStoreId) {
      return new DisconnectCustomKeyStoreRequest(CustomKeyStoreId);
    }
    public static _IDisconnectCustomKeyStoreRequest create_DisconnectCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId) {
      return create(CustomKeyStoreId);
    }
    public bool is_DisconnectCustomKeyStoreRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_CustomKeyStoreId {
      get {
        return this._CustomKeyStoreId;
      }
    }
  }

  public interface _IDisconnectCustomKeyStoreResponse {
    bool is_DisconnectCustomKeyStoreResponse { get; }
    _IDisconnectCustomKeyStoreResponse DowncastClone();
  }
  public class DisconnectCustomKeyStoreResponse : _IDisconnectCustomKeyStoreResponse {
    public DisconnectCustomKeyStoreResponse() {
    }
    public _IDisconnectCustomKeyStoreResponse DowncastClone() {
      if (this is _IDisconnectCustomKeyStoreResponse dt) { return dt; }
      return new DisconnectCustomKeyStoreResponse();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreResponse;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.DisconnectCustomKeyStoreResponse.DisconnectCustomKeyStoreResponse";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreResponse theDefault = create();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreResponse>(software.amazon.cryptography.services.kms.internaldafny.types.DisconnectCustomKeyStoreResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDisconnectCustomKeyStoreResponse create() {
      return new DisconnectCustomKeyStoreResponse();
    }
    public static _IDisconnectCustomKeyStoreResponse create_DisconnectCustomKeyStoreResponse() {
      return create();
    }
    public bool is_DisconnectCustomKeyStoreResponse { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IDisconnectCustomKeyStoreResponse> AllSingletonConstructors {
      get {
        yield return DisconnectCustomKeyStoreResponse.create();
      }
    }
  }

  public interface _IEnableKeyRequest {
    bool is_EnableKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IEnableKeyRequest DowncastClone();
  }
  public class EnableKeyRequest : _IEnableKeyRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public EnableKeyRequest(Dafny.ISequence<char> KeyId) {
      this._KeyId = KeyId;
    }
    public _IEnableKeyRequest DowncastClone() {
      if (this is _IEnableKeyRequest dt) { return dt; }
      return new EnableKeyRequest(_KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.EnableKeyRequest.EnableKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRequest>(software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnableKeyRequest create(Dafny.ISequence<char> KeyId) {
      return new EnableKeyRequest(KeyId);
    }
    public static _IEnableKeyRequest create_EnableKeyRequest(Dafny.ISequence<char> KeyId) {
      return create(KeyId);
    }
    public bool is_EnableKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
  }

  public interface _IEnableKeyRotationRequest {
    bool is_EnableKeyRotationRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IEnableKeyRotationRequest DowncastClone();
  }
  public class EnableKeyRotationRequest : _IEnableKeyRotationRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public EnableKeyRotationRequest(Dafny.ISequence<char> KeyId) {
      this._KeyId = KeyId;
    }
    public _IEnableKeyRotationRequest DowncastClone() {
      if (this is _IEnableKeyRotationRequest dt) { return dt; }
      return new EnableKeyRotationRequest(_KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRotationRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.EnableKeyRotationRequest.EnableKeyRotationRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRotationRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRotationRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRotationRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRotationRequest>(software.amazon.cryptography.services.kms.internaldafny.types.EnableKeyRotationRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRotationRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnableKeyRotationRequest create(Dafny.ISequence<char> KeyId) {
      return new EnableKeyRotationRequest(KeyId);
    }
    public static _IEnableKeyRotationRequest create_EnableKeyRotationRequest(Dafny.ISequence<char> KeyId) {
      return create(KeyId);
    }
    public bool is_EnableKeyRotationRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
  }

  public interface _IEncryptionAlgorithmSpec {
    bool is_SYMMETRIC__DEFAULT { get; }
    bool is_RSAES__OAEP__SHA__1 { get; }
    bool is_RSAES__OAEP__SHA__256 { get; }
    _IEncryptionAlgorithmSpec DowncastClone();
  }
  public abstract class EncryptionAlgorithmSpec : _IEncryptionAlgorithmSpec {
    public EncryptionAlgorithmSpec() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec theDefault = create_SYMMETRIC__DEFAULT();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>(software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEncryptionAlgorithmSpec create_SYMMETRIC__DEFAULT() {
      return new EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT();
    }
    public static _IEncryptionAlgorithmSpec create_RSAES__OAEP__SHA__1() {
      return new EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1();
    }
    public static _IEncryptionAlgorithmSpec create_RSAES__OAEP__SHA__256() {
      return new EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256();
    }
    public bool is_SYMMETRIC__DEFAULT { get { return this is EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT; } }
    public bool is_RSAES__OAEP__SHA__1 { get { return this is EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1; } }
    public bool is_RSAES__OAEP__SHA__256 { get { return this is EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256; } }
    public static System.Collections.Generic.IEnumerable<_IEncryptionAlgorithmSpec> AllSingletonConstructors {
      get {
        yield return EncryptionAlgorithmSpec.create_SYMMETRIC__DEFAULT();
        yield return EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__1();
        yield return EncryptionAlgorithmSpec.create_RSAES__OAEP__SHA__256();
      }
    }
    public abstract _IEncryptionAlgorithmSpec DowncastClone();
  }
  public class EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT : EncryptionAlgorithmSpec {
    public EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT() {
    }
    public override _IEncryptionAlgorithmSpec DowncastClone() {
      if (this is _IEncryptionAlgorithmSpec dt) { return dt; }
      return new EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.EncryptionAlgorithmSpec.SYMMETRIC_DEFAULT";
      return s;
    }
  }
  public class EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1 : EncryptionAlgorithmSpec {
    public EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1() {
    }
    public override _IEncryptionAlgorithmSpec DowncastClone() {
      if (this is _IEncryptionAlgorithmSpec dt) { return dt; }
      return new EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1";
      return s;
    }
  }
  public class EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256 : EncryptionAlgorithmSpec {
    public EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256() {
    }
    public override _IEncryptionAlgorithmSpec DowncastClone() {
      if (this is _IEncryptionAlgorithmSpec dt) { return dt; }
      return new EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256";
      return s;
    }
  }

  public interface _IEncryptRequest {
    bool is_EncryptRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<byte> dtor_Plaintext { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm { get; }
    _IEncryptRequest DowncastClone();
  }
  public class EncryptRequest : _IEncryptRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<byte> _Plaintext;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _EncryptionContext;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _EncryptionAlgorithm;
    public EncryptRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Plaintext, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      this._KeyId = KeyId;
      this._Plaintext = Plaintext;
      this._EncryptionContext = EncryptionContext;
      this._GrantTokens = GrantTokens;
      this._EncryptionAlgorithm = EncryptionAlgorithm;
    }
    public _IEncryptRequest DowncastClone() {
      if (this is _IEncryptRequest dt) { return dt; }
      return new EncryptRequest(_KeyId, _Plaintext, _EncryptionContext, _GrantTokens, _EncryptionAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.EncryptRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._Plaintext, oth._Plaintext) && object.Equals(this._EncryptionContext, oth._EncryptionContext) && object.Equals(this._GrantTokens, oth._GrantTokens) && object.Equals(this._EncryptionAlgorithm, oth._EncryptionAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Plaintext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.EncryptRequest.EncryptRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Plaintext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptionAlgorithm);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IEncryptRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IEncryptRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptRequest>(software.amazon.cryptography.services.kms.internaldafny.types.EncryptRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEncryptRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Plaintext, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return new EncryptRequest(KeyId, Plaintext, EncryptionContext, GrantTokens, EncryptionAlgorithm);
    }
    public static _IEncryptRequest create_EncryptRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Plaintext, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return create(KeyId, Plaintext, EncryptionContext, GrantTokens, EncryptionAlgorithm);
    }
    public bool is_EncryptRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<byte> dtor_Plaintext {
      get {
        return this._Plaintext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this._EncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm {
      get {
        return this._EncryptionAlgorithm;
      }
    }
  }

  public interface _IEncryptResponse {
    bool is_EncryptResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm { get; }
    _IEncryptResponse DowncastClone();
  }
  public class EncryptResponse : _IEncryptResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _EncryptionAlgorithm;
    public EncryptResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      this._CiphertextBlob = CiphertextBlob;
      this._KeyId = KeyId;
      this._EncryptionAlgorithm = EncryptionAlgorithm;
    }
    public _IEncryptResponse DowncastClone() {
      if (this is _IEncryptResponse dt) { return dt; }
      return new EncryptResponse(_CiphertextBlob, _KeyId, _EncryptionAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.EncryptResponse;
      return oth != null && object.Equals(this._CiphertextBlob, oth._CiphertextBlob) && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._EncryptionAlgorithm, oth._EncryptionAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.EncryptResponse.EncryptResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptionAlgorithm);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse>(software.amazon.cryptography.services.kms.internaldafny.types.EncryptResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEncryptResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return new EncryptResponse(CiphertextBlob, KeyId, EncryptionAlgorithm);
    }
    public static _IEncryptResponse create_EncryptResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> EncryptionAlgorithm) {
      return create(CiphertextBlob, KeyId, EncryptionAlgorithm);
    }
    public bool is_EncryptResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob {
      get {
        return this._CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_EncryptionAlgorithm {
      get {
        return this._EncryptionAlgorithm;
      }
    }
  }

  public interface _IExpirationModelType {
    bool is_KEY__MATERIAL__EXPIRES { get; }
    bool is_KEY__MATERIAL__DOES__NOT__EXPIRE { get; }
    _IExpirationModelType DowncastClone();
  }
  public abstract class ExpirationModelType : _IExpirationModelType {
    public ExpirationModelType() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType theDefault = create_KEY__MATERIAL__EXPIRES();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType>(software.amazon.cryptography.services.kms.internaldafny.types.ExpirationModelType.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IExpirationModelType create_KEY__MATERIAL__EXPIRES() {
      return new ExpirationModelType_KEY__MATERIAL__EXPIRES();
    }
    public static _IExpirationModelType create_KEY__MATERIAL__DOES__NOT__EXPIRE() {
      return new ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE();
    }
    public bool is_KEY__MATERIAL__EXPIRES { get { return this is ExpirationModelType_KEY__MATERIAL__EXPIRES; } }
    public bool is_KEY__MATERIAL__DOES__NOT__EXPIRE { get { return this is ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE; } }
    public static System.Collections.Generic.IEnumerable<_IExpirationModelType> AllSingletonConstructors {
      get {
        yield return ExpirationModelType.create_KEY__MATERIAL__EXPIRES();
        yield return ExpirationModelType.create_KEY__MATERIAL__DOES__NOT__EXPIRE();
      }
    }
    public abstract _IExpirationModelType DowncastClone();
  }
  public class ExpirationModelType_KEY__MATERIAL__EXPIRES : ExpirationModelType {
    public ExpirationModelType_KEY__MATERIAL__EXPIRES() {
    }
    public override _IExpirationModelType DowncastClone() {
      if (this is _IExpirationModelType dt) { return dt; }
      return new ExpirationModelType_KEY__MATERIAL__EXPIRES();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ExpirationModelType_KEY__MATERIAL__EXPIRES;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ExpirationModelType.KEY_MATERIAL_EXPIRES";
      return s;
    }
  }
  public class ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE : ExpirationModelType {
    public ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE() {
    }
    public override _IExpirationModelType DowncastClone() {
      if (this is _IExpirationModelType dt) { return dt; }
      return new ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ExpirationModelType.KEY_MATERIAL_DOES_NOT_EXPIRE";
      return s;
    }
  }

  public interface _IGenerateDataKeyPairRequest {
    bool is_GenerateDataKeyPairRequest { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec dtor_KeyPairSpec { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IGenerateDataKeyPairRequest DowncastClone();
  }
  public class GenerateDataKeyPairRequest : _IGenerateDataKeyPairRequest {
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _EncryptionContext;
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec _KeyPairSpec;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public GenerateDataKeyPairRequest(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Dafny.ISequence<char> KeyId, software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec KeyPairSpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this._EncryptionContext = EncryptionContext;
      this._KeyId = KeyId;
      this._KeyPairSpec = KeyPairSpec;
      this._GrantTokens = GrantTokens;
    }
    public _IGenerateDataKeyPairRequest DowncastClone() {
      if (this is _IGenerateDataKeyPairRequest dt) { return dt; }
      return new GenerateDataKeyPairRequest(_EncryptionContext, _KeyId, _KeyPairSpec, _GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairRequest;
      return oth != null && object.Equals(this._EncryptionContext, oth._EncryptionContext) && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._KeyPairSpec, oth._KeyPairSpec) && object.Equals(this._GrantTokens, oth._GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyPairSpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GenerateDataKeyPairRequest.GenerateDataKeyPairRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyPairSpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairRequest theDefault = create(Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Dafny.Sequence<char>.Empty, software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairRequest>(software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyPairRequest create(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Dafny.ISequence<char> KeyId, software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec KeyPairSpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new GenerateDataKeyPairRequest(EncryptionContext, KeyId, KeyPairSpec, GrantTokens);
    }
    public static _IGenerateDataKeyPairRequest create_GenerateDataKeyPairRequest(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Dafny.ISequence<char> KeyId, software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec KeyPairSpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return create(EncryptionContext, KeyId, KeyPairSpec, GrantTokens);
    }
    public bool is_GenerateDataKeyPairRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this._EncryptionContext;
      }
    }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec dtor_KeyPairSpec {
      get {
        return this._KeyPairSpec;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
  }

  public interface _IGenerateDataKeyPairResponse {
    bool is_GenerateDataKeyPairResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyCiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyPlaintext { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> dtor_KeyPairSpec { get; }
    _IGenerateDataKeyPairResponse DowncastClone();
  }
  public class GenerateDataKeyPairResponse : _IGenerateDataKeyPairResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _PrivateKeyCiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _PrivateKeyPlaintext;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _PublicKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> _KeyPairSpec;
    public GenerateDataKeyPairResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyPlaintext, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> KeyPairSpec) {
      this._PrivateKeyCiphertextBlob = PrivateKeyCiphertextBlob;
      this._PrivateKeyPlaintext = PrivateKeyPlaintext;
      this._PublicKey = PublicKey;
      this._KeyId = KeyId;
      this._KeyPairSpec = KeyPairSpec;
    }
    public _IGenerateDataKeyPairResponse DowncastClone() {
      if (this is _IGenerateDataKeyPairResponse dt) { return dt; }
      return new GenerateDataKeyPairResponse(_PrivateKeyCiphertextBlob, _PrivateKeyPlaintext, _PublicKey, _KeyId, _KeyPairSpec);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairResponse;
      return oth != null && object.Equals(this._PrivateKeyCiphertextBlob, oth._PrivateKeyCiphertextBlob) && object.Equals(this._PrivateKeyPlaintext, oth._PrivateKeyPlaintext) && object.Equals(this._PublicKey, oth._PublicKey) && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._KeyPairSpec, oth._KeyPairSpec);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PrivateKeyCiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PrivateKeyPlaintext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PublicKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyPairSpec));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GenerateDataKeyPairResponse.GenerateDataKeyPairResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._PrivateKeyCiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PrivateKeyPlaintext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PublicKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyPairSpec);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairResponse>(software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyPairResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyPlaintext, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> KeyPairSpec) {
      return new GenerateDataKeyPairResponse(PrivateKeyCiphertextBlob, PrivateKeyPlaintext, PublicKey, KeyId, KeyPairSpec);
    }
    public static _IGenerateDataKeyPairResponse create_GenerateDataKeyPairResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyPlaintext, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> KeyPairSpec) {
      return create(PrivateKeyCiphertextBlob, PrivateKeyPlaintext, PublicKey, KeyId, KeyPairSpec);
    }
    public bool is_GenerateDataKeyPairResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyCiphertextBlob {
      get {
        return this._PrivateKeyCiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyPlaintext {
      get {
        return this._PrivateKeyPlaintext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey {
      get {
        return this._PublicKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> dtor_KeyPairSpec {
      get {
        return this._KeyPairSpec;
      }
    }
  }

  public interface _IGenerateDataKeyPairWithoutPlaintextRequest {
    bool is_GenerateDataKeyPairWithoutPlaintextRequest { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec dtor_KeyPairSpec { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IGenerateDataKeyPairWithoutPlaintextRequest DowncastClone();
  }
  public class GenerateDataKeyPairWithoutPlaintextRequest : _IGenerateDataKeyPairWithoutPlaintextRequest {
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _EncryptionContext;
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec _KeyPairSpec;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public GenerateDataKeyPairWithoutPlaintextRequest(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Dafny.ISequence<char> KeyId, software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec KeyPairSpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this._EncryptionContext = EncryptionContext;
      this._KeyId = KeyId;
      this._KeyPairSpec = KeyPairSpec;
      this._GrantTokens = GrantTokens;
    }
    public _IGenerateDataKeyPairWithoutPlaintextRequest DowncastClone() {
      if (this is _IGenerateDataKeyPairWithoutPlaintextRequest dt) { return dt; }
      return new GenerateDataKeyPairWithoutPlaintextRequest(_EncryptionContext, _KeyId, _KeyPairSpec, _GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextRequest;
      return oth != null && object.Equals(this._EncryptionContext, oth._EncryptionContext) && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._KeyPairSpec, oth._KeyPairSpec) && object.Equals(this._GrantTokens, oth._GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyPairSpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GenerateDataKeyPairWithoutPlaintextRequest.GenerateDataKeyPairWithoutPlaintextRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyPairSpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextRequest theDefault = create(Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Dafny.Sequence<char>.Empty, software.amazon.cryptography.services.kms.internaldafny.types.DataKeyPairSpec.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextRequest>(software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyPairWithoutPlaintextRequest create(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Dafny.ISequence<char> KeyId, software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec KeyPairSpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new GenerateDataKeyPairWithoutPlaintextRequest(EncryptionContext, KeyId, KeyPairSpec, GrantTokens);
    }
    public static _IGenerateDataKeyPairWithoutPlaintextRequest create_GenerateDataKeyPairWithoutPlaintextRequest(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Dafny.ISequence<char> KeyId, software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec KeyPairSpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return create(EncryptionContext, KeyId, KeyPairSpec, GrantTokens);
    }
    public bool is_GenerateDataKeyPairWithoutPlaintextRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this._EncryptionContext;
      }
    }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec dtor_KeyPairSpec {
      get {
        return this._KeyPairSpec;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
  }

  public interface _IGenerateDataKeyPairWithoutPlaintextResponse {
    bool is_GenerateDataKeyPairWithoutPlaintextResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyCiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> dtor_KeyPairSpec { get; }
    _IGenerateDataKeyPairWithoutPlaintextResponse DowncastClone();
  }
  public class GenerateDataKeyPairWithoutPlaintextResponse : _IGenerateDataKeyPairWithoutPlaintextResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _PrivateKeyCiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _PublicKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> _KeyPairSpec;
    public GenerateDataKeyPairWithoutPlaintextResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> KeyPairSpec) {
      this._PrivateKeyCiphertextBlob = PrivateKeyCiphertextBlob;
      this._PublicKey = PublicKey;
      this._KeyId = KeyId;
      this._KeyPairSpec = KeyPairSpec;
    }
    public _IGenerateDataKeyPairWithoutPlaintextResponse DowncastClone() {
      if (this is _IGenerateDataKeyPairWithoutPlaintextResponse dt) { return dt; }
      return new GenerateDataKeyPairWithoutPlaintextResponse(_PrivateKeyCiphertextBlob, _PublicKey, _KeyId, _KeyPairSpec);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextResponse;
      return oth != null && object.Equals(this._PrivateKeyCiphertextBlob, oth._PrivateKeyCiphertextBlob) && object.Equals(this._PublicKey, oth._PublicKey) && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._KeyPairSpec, oth._KeyPairSpec);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PrivateKeyCiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PublicKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyPairSpec));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GenerateDataKeyPairWithoutPlaintextResponse.GenerateDataKeyPairWithoutPlaintextResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._PrivateKeyCiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PublicKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyPairSpec);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextResponse>(software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyPairWithoutPlaintextResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyPairWithoutPlaintextResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> KeyPairSpec) {
      return new GenerateDataKeyPairWithoutPlaintextResponse(PrivateKeyCiphertextBlob, PublicKey, KeyId, KeyPairSpec);
    }
    public static _IGenerateDataKeyPairWithoutPlaintextResponse create_GenerateDataKeyPairWithoutPlaintextResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> PrivateKeyCiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> KeyPairSpec) {
      return create(PrivateKeyCiphertextBlob, PublicKey, KeyId, KeyPairSpec);
    }
    public bool is_GenerateDataKeyPairWithoutPlaintextResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PrivateKeyCiphertextBlob {
      get {
        return this._PrivateKeyCiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey {
      get {
        return this._PublicKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeyPairSpec> dtor_KeyPairSpec {
      get {
        return this._KeyPairSpec;
      }
    }
  }

  public interface _IGenerateDataKeyRequest {
    bool is_GenerateDataKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Wrappers_Compile._IOption<int> dtor_NumberOfBytes { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> dtor_KeySpec { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IGenerateDataKeyRequest DowncastClone();
  }
  public class GenerateDataKeyRequest : _IGenerateDataKeyRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _EncryptionContext;
    public readonly Wrappers_Compile._IOption<int> _NumberOfBytes;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> _KeySpec;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public GenerateDataKeyRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> KeySpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this._KeyId = KeyId;
      this._EncryptionContext = EncryptionContext;
      this._NumberOfBytes = NumberOfBytes;
      this._KeySpec = KeySpec;
      this._GrantTokens = GrantTokens;
    }
    public _IGenerateDataKeyRequest DowncastClone() {
      if (this is _IGenerateDataKeyRequest dt) { return dt; }
      return new GenerateDataKeyRequest(_KeyId, _EncryptionContext, _NumberOfBytes, _KeySpec, _GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._EncryptionContext, oth._EncryptionContext) && object.Equals(this._NumberOfBytes, oth._NumberOfBytes) && object.Equals(this._KeySpec, oth._KeySpec) && object.Equals(this._GrantTokens, oth._GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._NumberOfBytes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GenerateDataKeyRequest.GenerateDataKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._NumberOfBytes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyRequest>(software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> KeySpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new GenerateDataKeyRequest(KeyId, EncryptionContext, NumberOfBytes, KeySpec, GrantTokens);
    }
    public static _IGenerateDataKeyRequest create_GenerateDataKeyRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> KeySpec, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return create(KeyId, EncryptionContext, NumberOfBytes, KeySpec, GrantTokens);
    }
    public bool is_GenerateDataKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this._EncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_NumberOfBytes {
      get {
        return this._NumberOfBytes;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> dtor_KeySpec {
      get {
        return this._KeySpec;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
  }

  public interface _IGenerateDataKeyResponse {
    bool is_GenerateDataKeyResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    _IGenerateDataKeyResponse DowncastClone();
  }
  public class GenerateDataKeyResponse : _IGenerateDataKeyResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _Plaintext;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public GenerateDataKeyResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      this._CiphertextBlob = CiphertextBlob;
      this._Plaintext = Plaintext;
      this._KeyId = KeyId;
    }
    public _IGenerateDataKeyResponse DowncastClone() {
      if (this is _IGenerateDataKeyResponse dt) { return dt; }
      return new GenerateDataKeyResponse(_CiphertextBlob, _Plaintext, _KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyResponse;
      return oth != null && object.Equals(this._CiphertextBlob, oth._CiphertextBlob) && object.Equals(this._Plaintext, oth._Plaintext) && object.Equals(this._KeyId, oth._KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Plaintext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GenerateDataKeyResponse.GenerateDataKeyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Plaintext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse>(software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      return new GenerateDataKeyResponse(CiphertextBlob, Plaintext, KeyId);
    }
    public static _IGenerateDataKeyResponse create_GenerateDataKeyResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      return create(CiphertextBlob, Plaintext, KeyId);
    }
    public bool is_GenerateDataKeyResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob {
      get {
        return this._CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext {
      get {
        return this._Plaintext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
  }

  public interface _IGenerateDataKeyWithoutPlaintextRequest {
    bool is_GenerateDataKeyWithoutPlaintextRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> dtor_KeySpec { get; }
    Wrappers_Compile._IOption<int> dtor_NumberOfBytes { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IGenerateDataKeyWithoutPlaintextRequest DowncastClone();
  }
  public class GenerateDataKeyWithoutPlaintextRequest : _IGenerateDataKeyWithoutPlaintextRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _EncryptionContext;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> _KeySpec;
    public readonly Wrappers_Compile._IOption<int> _NumberOfBytes;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public GenerateDataKeyWithoutPlaintextRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> KeySpec, Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this._KeyId = KeyId;
      this._EncryptionContext = EncryptionContext;
      this._KeySpec = KeySpec;
      this._NumberOfBytes = NumberOfBytes;
      this._GrantTokens = GrantTokens;
    }
    public _IGenerateDataKeyWithoutPlaintextRequest DowncastClone() {
      if (this is _IGenerateDataKeyWithoutPlaintextRequest dt) { return dt; }
      return new GenerateDataKeyWithoutPlaintextRequest(_KeyId, _EncryptionContext, _KeySpec, _NumberOfBytes, _GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._EncryptionContext, oth._EncryptionContext) && object.Equals(this._KeySpec, oth._KeySpec) && object.Equals(this._NumberOfBytes, oth._NumberOfBytes) && object.Equals(this._GrantTokens, oth._GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._NumberOfBytes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GenerateDataKeyWithoutPlaintextRequest.GenerateDataKeyWithoutPlaintextRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._NumberOfBytes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec>.Default(), Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextRequest>(software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyWithoutPlaintextRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> KeySpec, Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new GenerateDataKeyWithoutPlaintextRequest(KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens);
    }
    public static _IGenerateDataKeyWithoutPlaintextRequest create_GenerateDataKeyWithoutPlaintextRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContext, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> KeySpec, Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return create(KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens);
    }
    public bool is_GenerateDataKeyWithoutPlaintextRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContext {
      get {
        return this._EncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec> dtor_KeySpec {
      get {
        return this._KeySpec;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_NumberOfBytes {
      get {
        return this._NumberOfBytes;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
  }

  public interface _IGenerateDataKeyWithoutPlaintextResponse {
    bool is_GenerateDataKeyWithoutPlaintextResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    _IGenerateDataKeyWithoutPlaintextResponse DowncastClone();
  }
  public class GenerateDataKeyWithoutPlaintextResponse : _IGenerateDataKeyWithoutPlaintextResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public GenerateDataKeyWithoutPlaintextResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      this._CiphertextBlob = CiphertextBlob;
      this._KeyId = KeyId;
    }
    public _IGenerateDataKeyWithoutPlaintextResponse DowncastClone() {
      if (this is _IGenerateDataKeyWithoutPlaintextResponse dt) { return dt; }
      return new GenerateDataKeyWithoutPlaintextResponse(_CiphertextBlob, _KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextResponse;
      return oth != null && object.Equals(this._CiphertextBlob, oth._CiphertextBlob) && object.Equals(this._KeyId, oth._KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GenerateDataKeyWithoutPlaintextResponse.GenerateDataKeyWithoutPlaintextResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextResponse>(software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateDataKeyWithoutPlaintextResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      return new GenerateDataKeyWithoutPlaintextResponse(CiphertextBlob, KeyId);
    }
    public static _IGenerateDataKeyWithoutPlaintextResponse create_GenerateDataKeyWithoutPlaintextResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId) {
      return create(CiphertextBlob, KeyId);
    }
    public bool is_GenerateDataKeyWithoutPlaintextResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob {
      get {
        return this._CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
  }

  public interface _IGenerateRandomRequest {
    bool is_GenerateRandomRequest { get; }
    Wrappers_Compile._IOption<int> dtor_NumberOfBytes { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    _IGenerateRandomRequest DowncastClone();
  }
  public class GenerateRandomRequest : _IGenerateRandomRequest {
    public readonly Wrappers_Compile._IOption<int> _NumberOfBytes;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CustomKeyStoreId;
    public GenerateRandomRequest(Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId) {
      this._NumberOfBytes = NumberOfBytes;
      this._CustomKeyStoreId = CustomKeyStoreId;
    }
    public _IGenerateRandomRequest DowncastClone() {
      if (this is _IGenerateRandomRequest dt) { return dt; }
      return new GenerateRandomRequest(_NumberOfBytes, _CustomKeyStoreId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomRequest;
      return oth != null && object.Equals(this._NumberOfBytes, oth._NumberOfBytes) && object.Equals(this._CustomKeyStoreId, oth._CustomKeyStoreId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._NumberOfBytes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GenerateRandomRequest.GenerateRandomRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._NumberOfBytes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomRequest theDefault = create(Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomRequest>(software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateRandomRequest create(Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId) {
      return new GenerateRandomRequest(NumberOfBytes, CustomKeyStoreId);
    }
    public static _IGenerateRandomRequest create_GenerateRandomRequest(Wrappers_Compile._IOption<int> NumberOfBytes, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId) {
      return create(NumberOfBytes, CustomKeyStoreId);
    }
    public bool is_GenerateRandomRequest { get { return true; } }
    public Wrappers_Compile._IOption<int> dtor_NumberOfBytes {
      get {
        return this._NumberOfBytes;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this._CustomKeyStoreId;
      }
    }
  }

  public interface _IGenerateRandomResponse {
    bool is_GenerateRandomResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext { get; }
    _IGenerateRandomResponse DowncastClone();
  }
  public class GenerateRandomResponse : _IGenerateRandomResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _Plaintext;
    public GenerateRandomResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext) {
      this._Plaintext = Plaintext;
    }
    public _IGenerateRandomResponse DowncastClone() {
      if (this is _IGenerateRandomResponse dt) { return dt; }
      return new GenerateRandomResponse(_Plaintext);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomResponse;
      return oth != null && object.Equals(this._Plaintext, oth._Plaintext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Plaintext));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GenerateRandomResponse.GenerateRandomResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._Plaintext);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomResponse>(software.amazon.cryptography.services.kms.internaldafny.types.GenerateRandomResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenerateRandomResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext) {
      return new GenerateRandomResponse(Plaintext);
    }
    public static _IGenerateRandomResponse create_GenerateRandomResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> Plaintext) {
      return create(Plaintext);
    }
    public bool is_GenerateRandomResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Plaintext {
      get {
        return this._Plaintext;
      }
    }
  }

  public interface _IGetKeyPolicyRequest {
    bool is_GetKeyPolicyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_PolicyName { get; }
    _IGetKeyPolicyRequest DowncastClone();
  }
  public class GetKeyPolicyRequest : _IGetKeyPolicyRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<char> _PolicyName;
    public GetKeyPolicyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PolicyName) {
      this._KeyId = KeyId;
      this._PolicyName = PolicyName;
    }
    public _IGetKeyPolicyRequest DowncastClone() {
      if (this is _IGetKeyPolicyRequest dt) { return dt; }
      return new GetKeyPolicyRequest(_KeyId, _PolicyName);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._PolicyName, oth._PolicyName);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PolicyName));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GetKeyPolicyRequest.GetKeyPolicyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PolicyName);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyRequest>(software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetKeyPolicyRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PolicyName) {
      return new GetKeyPolicyRequest(KeyId, PolicyName);
    }
    public static _IGetKeyPolicyRequest create_GetKeyPolicyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PolicyName) {
      return create(KeyId, PolicyName);
    }
    public bool is_GetKeyPolicyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_PolicyName {
      get {
        return this._PolicyName;
      }
    }
  }

  public interface _IGetKeyPolicyResponse {
    bool is_GetKeyPolicyResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy { get; }
    _IGetKeyPolicyResponse DowncastClone();
  }
  public class GetKeyPolicyResponse : _IGetKeyPolicyResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Policy;
    public GetKeyPolicyResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy) {
      this._Policy = Policy;
    }
    public _IGetKeyPolicyResponse DowncastClone() {
      if (this is _IGetKeyPolicyResponse dt) { return dt; }
      return new GetKeyPolicyResponse(_Policy);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyResponse;
      return oth != null && object.Equals(this._Policy, oth._Policy);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Policy));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GetKeyPolicyResponse.GetKeyPolicyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._Policy);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyResponse>(software.amazon.cryptography.services.kms.internaldafny.types.GetKeyPolicyResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetKeyPolicyResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy) {
      return new GetKeyPolicyResponse(Policy);
    }
    public static _IGetKeyPolicyResponse create_GetKeyPolicyResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy) {
      return create(Policy);
    }
    public bool is_GetKeyPolicyResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy {
      get {
        return this._Policy;
      }
    }
  }

  public interface _IGetKeyRotationStatusRequest {
    bool is_GetKeyRotationStatusRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    _IGetKeyRotationStatusRequest DowncastClone();
  }
  public class GetKeyRotationStatusRequest : _IGetKeyRotationStatusRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public GetKeyRotationStatusRequest(Dafny.ISequence<char> KeyId) {
      this._KeyId = KeyId;
    }
    public _IGetKeyRotationStatusRequest DowncastClone() {
      if (this is _IGetKeyRotationStatusRequest dt) { return dt; }
      return new GetKeyRotationStatusRequest(_KeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GetKeyRotationStatusRequest.GetKeyRotationStatusRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusRequest theDefault = create(Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusRequest>(software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetKeyRotationStatusRequest create(Dafny.ISequence<char> KeyId) {
      return new GetKeyRotationStatusRequest(KeyId);
    }
    public static _IGetKeyRotationStatusRequest create_GetKeyRotationStatusRequest(Dafny.ISequence<char> KeyId) {
      return create(KeyId);
    }
    public bool is_GetKeyRotationStatusRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
  }

  public interface _IGetKeyRotationStatusResponse {
    bool is_GetKeyRotationStatusResponse { get; }
    Wrappers_Compile._IOption<bool> dtor_KeyRotationEnabled { get; }
    _IGetKeyRotationStatusResponse DowncastClone();
  }
  public class GetKeyRotationStatusResponse : _IGetKeyRotationStatusResponse {
    public readonly Wrappers_Compile._IOption<bool> _KeyRotationEnabled;
    public GetKeyRotationStatusResponse(Wrappers_Compile._IOption<bool> KeyRotationEnabled) {
      this._KeyRotationEnabled = KeyRotationEnabled;
    }
    public _IGetKeyRotationStatusResponse DowncastClone() {
      if (this is _IGetKeyRotationStatusResponse dt) { return dt; }
      return new GetKeyRotationStatusResponse(_KeyRotationEnabled);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusResponse;
      return oth != null && object.Equals(this._KeyRotationEnabled, oth._KeyRotationEnabled);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyRotationEnabled));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GetKeyRotationStatusResponse.GetKeyRotationStatusResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyRotationEnabled);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusResponse theDefault = create(Wrappers_Compile.Option<bool>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusResponse>(software.amazon.cryptography.services.kms.internaldafny.types.GetKeyRotationStatusResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetKeyRotationStatusResponse create(Wrappers_Compile._IOption<bool> KeyRotationEnabled) {
      return new GetKeyRotationStatusResponse(KeyRotationEnabled);
    }
    public static _IGetKeyRotationStatusResponse create_GetKeyRotationStatusResponse(Wrappers_Compile._IOption<bool> KeyRotationEnabled) {
      return create(KeyRotationEnabled);
    }
    public bool is_GetKeyRotationStatusResponse { get { return true; } }
    public Wrappers_Compile._IOption<bool> dtor_KeyRotationEnabled {
      get {
        return this._KeyRotationEnabled;
      }
    }
  }

  public interface _IGetParametersForImportRequest {
    bool is_GetParametersForImportRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec dtor_WrappingAlgorithm { get; }
    software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec dtor_WrappingKeySpec { get; }
    _IGetParametersForImportRequest DowncastClone();
  }
  public class GetParametersForImportRequest : _IGetParametersForImportRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec _WrappingAlgorithm;
    public readonly software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec _WrappingKeySpec;
    public GetParametersForImportRequest(Dafny.ISequence<char> KeyId, software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec WrappingAlgorithm, software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec WrappingKeySpec) {
      this._KeyId = KeyId;
      this._WrappingAlgorithm = WrappingAlgorithm;
      this._WrappingKeySpec = WrappingKeySpec;
    }
    public _IGetParametersForImportRequest DowncastClone() {
      if (this is _IGetParametersForImportRequest dt) { return dt; }
      return new GetParametersForImportRequest(_KeyId, _WrappingAlgorithm, _WrappingKeySpec);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._WrappingAlgorithm, oth._WrappingAlgorithm) && object.Equals(this._WrappingKeySpec, oth._WrappingKeySpec);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._WrappingAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._WrappingKeySpec));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GetParametersForImportRequest.GetParametersForImportRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._WrappingAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._WrappingKeySpec);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportRequest theDefault = create(Dafny.Sequence<char>.Empty, software.amazon.cryptography.services.kms.internaldafny.types.AlgorithmSpec.Default(), software.amazon.cryptography.services.kms.internaldafny.types.WrappingKeySpec.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportRequest>(software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetParametersForImportRequest create(Dafny.ISequence<char> KeyId, software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec WrappingAlgorithm, software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec WrappingKeySpec) {
      return new GetParametersForImportRequest(KeyId, WrappingAlgorithm, WrappingKeySpec);
    }
    public static _IGetParametersForImportRequest create_GetParametersForImportRequest(Dafny.ISequence<char> KeyId, software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec WrappingAlgorithm, software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec WrappingKeySpec) {
      return create(KeyId, WrappingAlgorithm, WrappingKeySpec);
    }
    public bool is_GetParametersForImportRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public software.amazon.cryptography.services.kms.internaldafny.types._IAlgorithmSpec dtor_WrappingAlgorithm {
      get {
        return this._WrappingAlgorithm;
      }
    }
    public software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec dtor_WrappingKeySpec {
      get {
        return this._WrappingKeySpec;
      }
    }
  }

  public interface _IGetParametersForImportResponse {
    bool is_GetParametersForImportResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_ImportToken { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ParametersValidTo { get; }
    _IGetParametersForImportResponse DowncastClone();
  }
  public class GetParametersForImportResponse : _IGetParametersForImportResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _ImportToken;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _PublicKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _ParametersValidTo;
    public GetParametersForImportResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> ImportToken, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> ParametersValidTo) {
      this._KeyId = KeyId;
      this._ImportToken = ImportToken;
      this._PublicKey = PublicKey;
      this._ParametersValidTo = ParametersValidTo;
    }
    public _IGetParametersForImportResponse DowncastClone() {
      if (this is _IGetParametersForImportResponse dt) { return dt; }
      return new GetParametersForImportResponse(_KeyId, _ImportToken, _PublicKey, _ParametersValidTo);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportResponse;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._ImportToken, oth._ImportToken) && object.Equals(this._PublicKey, oth._PublicKey) && object.Equals(this._ParametersValidTo, oth._ParametersValidTo);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ImportToken));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PublicKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ParametersValidTo));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GetParametersForImportResponse.GetParametersForImportResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ImportToken);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PublicKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ParametersValidTo);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportResponse>(software.amazon.cryptography.services.kms.internaldafny.types.GetParametersForImportResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetParametersForImportResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> ImportToken, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> ParametersValidTo) {
      return new GetParametersForImportResponse(KeyId, ImportToken, PublicKey, ParametersValidTo);
    }
    public static _IGetParametersForImportResponse create_GetParametersForImportResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> ImportToken, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<Dafny.ISequence<char>> ParametersValidTo) {
      return create(KeyId, ImportToken, PublicKey, ParametersValidTo);
    }
    public bool is_GetParametersForImportResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_ImportToken {
      get {
        return this._ImportToken;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey {
      get {
        return this._PublicKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ParametersValidTo {
      get {
        return this._ParametersValidTo;
      }
    }
  }

  public interface _IGetPublicKeyRequest {
    bool is_GetPublicKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IGetPublicKeyRequest DowncastClone();
  }
  public class GetPublicKeyRequest : _IGetPublicKeyRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public GetPublicKeyRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this._KeyId = KeyId;
      this._GrantTokens = GrantTokens;
    }
    public _IGetPublicKeyRequest DowncastClone() {
      if (this is _IGetPublicKeyRequest dt) { return dt; }
      return new GetPublicKeyRequest(_KeyId, _GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._GrantTokens, oth._GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GetPublicKeyRequest.GetPublicKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyRequest>(software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetPublicKeyRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new GetPublicKeyRequest(KeyId, GrantTokens);
    }
    public static _IGetPublicKeyRequest create_GetPublicKeyRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return create(KeyId, GrantTokens);
    }
    public bool is_GetPublicKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
  }

  public interface _IGetPublicKeyResponse {
    bool is_GetPublicKeyResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> dtor_KeySpec { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> dtor_KeyUsage { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> dtor_EncryptionAlgorithms { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> dtor_SigningAlgorithms { get; }
    _IGetPublicKeyResponse DowncastClone();
  }
  public class GetPublicKeyResponse : _IGetPublicKeyResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _PublicKey;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> _CustomerMasterKeySpec;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> _KeySpec;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> _KeyUsage;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> _EncryptionAlgorithms;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> _SigningAlgorithms;
    public GetPublicKeyResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> KeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> EncryptionAlgorithms, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> SigningAlgorithms) {
      this._KeyId = KeyId;
      this._PublicKey = PublicKey;
      this._CustomerMasterKeySpec = CustomerMasterKeySpec;
      this._KeySpec = KeySpec;
      this._KeyUsage = KeyUsage;
      this._EncryptionAlgorithms = EncryptionAlgorithms;
      this._SigningAlgorithms = SigningAlgorithms;
    }
    public _IGetPublicKeyResponse DowncastClone() {
      if (this is _IGetPublicKeyResponse dt) { return dt; }
      return new GetPublicKeyResponse(_KeyId, _PublicKey, _CustomerMasterKeySpec, _KeySpec, _KeyUsage, _EncryptionAlgorithms, _SigningAlgorithms);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyResponse;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._PublicKey, oth._PublicKey) && object.Equals(this._CustomerMasterKeySpec, oth._CustomerMasterKeySpec) && object.Equals(this._KeySpec, oth._KeySpec) && object.Equals(this._KeyUsage, oth._KeyUsage) && object.Equals(this._EncryptionAlgorithms, oth._EncryptionAlgorithms) && object.Equals(this._SigningAlgorithms, oth._SigningAlgorithms);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PublicKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomerMasterKeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyUsage));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionAlgorithms));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SigningAlgorithms));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GetPublicKeyResponse.GetPublicKeyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PublicKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CustomerMasterKeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyUsage);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptionAlgorithms);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SigningAlgorithms);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType>.Default(), Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyResponse>(software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetPublicKeyResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> KeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> EncryptionAlgorithms, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> SigningAlgorithms) {
      return new GetPublicKeyResponse(KeyId, PublicKey, CustomerMasterKeySpec, KeySpec, KeyUsage, EncryptionAlgorithms, SigningAlgorithms);
    }
    public static _IGetPublicKeyResponse create_GetPublicKeyResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> PublicKey, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> KeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> EncryptionAlgorithms, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> SigningAlgorithms) {
      return create(KeyId, PublicKey, CustomerMasterKeySpec, KeySpec, KeyUsage, EncryptionAlgorithms, SigningAlgorithms);
    }
    public bool is_GetPublicKeyResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_PublicKey {
      get {
        return this._PublicKey;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec {
      get {
        return this._CustomerMasterKeySpec;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> dtor_KeySpec {
      get {
        return this._KeySpec;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> dtor_KeyUsage {
      get {
        return this._KeyUsage;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> dtor_EncryptionAlgorithms {
      get {
        return this._EncryptionAlgorithms;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> dtor_SigningAlgorithms {
      get {
        return this._SigningAlgorithms;
      }
    }
  }

  public interface _IGrantConstraints {
    bool is_GrantConstraints { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContextSubset { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContextEquals { get; }
    _IGrantConstraints DowncastClone();
  }
  public class GrantConstraints : _IGrantConstraints {
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _EncryptionContextSubset;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _EncryptionContextEquals;
    public GrantConstraints(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextSubset, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextEquals) {
      this._EncryptionContextSubset = EncryptionContextSubset;
      this._EncryptionContextEquals = EncryptionContextEquals;
    }
    public _IGrantConstraints DowncastClone() {
      if (this is _IGrantConstraints dt) { return dt; }
      return new GrantConstraints(_EncryptionContextSubset, _EncryptionContextEquals);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantConstraints;
      return oth != null && object.Equals(this._EncryptionContextSubset, oth._EncryptionContextSubset) && object.Equals(this._EncryptionContextEquals, oth._EncryptionContextEquals);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionContextSubset));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionContextEquals));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantConstraints.GrantConstraints";
      s += "(";
      s += Dafny.Helpers.ToString(this._EncryptionContextSubset);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptionContextEquals);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints theDefault = create(Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints>(software.amazon.cryptography.services.kms.internaldafny.types.GrantConstraints.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGrantConstraints create(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextSubset, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextEquals) {
      return new GrantConstraints(EncryptionContextSubset, EncryptionContextEquals);
    }
    public static _IGrantConstraints create_GrantConstraints(Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextSubset, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> EncryptionContextEquals) {
      return create(EncryptionContextSubset, EncryptionContextEquals);
    }
    public bool is_GrantConstraints { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContextSubset {
      get {
        return this._EncryptionContextSubset;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_EncryptionContextEquals {
      get {
        return this._EncryptionContextEquals;
      }
    }
  }

  public partial class GrantIdType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IGrantListEntry {
    bool is_GrantListEntry { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Name { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GranteePrincipal { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_RetiringPrincipal { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_IssuingAccount { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>> dtor_Operations { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> dtor_Constraints { get; }
    _IGrantListEntry DowncastClone();
  }
  public class GrantListEntry : _IGrantListEntry {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _GrantId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Name;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CreationDate;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _GranteePrincipal;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _RetiringPrincipal;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _IssuingAccount;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>> _Operations;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> _Constraints;
    public GrantListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId, Wrappers_Compile._IOption<Dafny.ISequence<char>> Name, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> IssuingAccount, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>> Operations, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> Constraints) {
      this._KeyId = KeyId;
      this._GrantId = GrantId;
      this._Name = Name;
      this._CreationDate = CreationDate;
      this._GranteePrincipal = GranteePrincipal;
      this._RetiringPrincipal = RetiringPrincipal;
      this._IssuingAccount = IssuingAccount;
      this._Operations = Operations;
      this._Constraints = Constraints;
    }
    public _IGrantListEntry DowncastClone() {
      if (this is _IGrantListEntry dt) { return dt; }
      return new GrantListEntry(_KeyId, _GrantId, _Name, _CreationDate, _GranteePrincipal, _RetiringPrincipal, _IssuingAccount, _Operations, _Constraints);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantListEntry;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._GrantId, oth._GrantId) && object.Equals(this._Name, oth._Name) && object.Equals(this._CreationDate, oth._CreationDate) && object.Equals(this._GranteePrincipal, oth._GranteePrincipal) && object.Equals(this._RetiringPrincipal, oth._RetiringPrincipal) && object.Equals(this._IssuingAccount, oth._IssuingAccount) && object.Equals(this._Operations, oth._Operations) && object.Equals(this._Constraints, oth._Constraints);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CreationDate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GranteePrincipal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._RetiringPrincipal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._IssuingAccount));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Operations));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Constraints));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantListEntry.GrantListEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CreationDate);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GranteePrincipal);
      s += ", ";
      s += Dafny.Helpers.ToString(this._RetiringPrincipal);
      s += ", ";
      s += Dafny.Helpers.ToString(this._IssuingAccount);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Operations);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Constraints);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>(software.amazon.cryptography.services.kms.internaldafny.types.GrantListEntry.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGrantListEntry create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId, Wrappers_Compile._IOption<Dafny.ISequence<char>> Name, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> IssuingAccount, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>> Operations, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> Constraints) {
      return new GrantListEntry(KeyId, GrantId, Name, CreationDate, GranteePrincipal, RetiringPrincipal, IssuingAccount, Operations, Constraints);
    }
    public static _IGrantListEntry create_GrantListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId, Wrappers_Compile._IOption<Dafny.ISequence<char>> Name, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> RetiringPrincipal, Wrappers_Compile._IOption<Dafny.ISequence<char>> IssuingAccount, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>> Operations, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> Constraints) {
      return create(KeyId, GrantId, Name, CreationDate, GranteePrincipal, RetiringPrincipal, IssuingAccount, Operations, Constraints);
    }
    public bool is_GrantListEntry { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId {
      get {
        return this._GrantId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Name {
      get {
        return this._Name;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate {
      get {
        return this._CreationDate;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GranteePrincipal {
      get {
        return this._GranteePrincipal;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_RetiringPrincipal {
      get {
        return this._RetiringPrincipal;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_IssuingAccount {
      get {
        return this._IssuingAccount;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>> dtor_Operations {
      get {
        return this._Operations;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IGrantConstraints> dtor_Constraints {
      get {
        return this._Constraints;
      }
    }
  }

  public partial class GrantNameType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IGrantOperation {
    bool is_Decrypt { get; }
    bool is_Encrypt { get; }
    bool is_GenerateDataKey { get; }
    bool is_GenerateDataKeyWithoutPlaintext { get; }
    bool is_ReEncryptFrom { get; }
    bool is_ReEncryptTo { get; }
    bool is_Sign { get; }
    bool is_Verify { get; }
    bool is_GetPublicKey { get; }
    bool is_CreateGrant { get; }
    bool is_RetireGrant { get; }
    bool is_DescribeKey { get; }
    bool is_GenerateDataKeyPair { get; }
    bool is_GenerateDataKeyPairWithoutPlaintext { get; }
    _IGrantOperation DowncastClone();
  }
  public abstract class GrantOperation : _IGrantOperation {
    public GrantOperation() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation theDefault = create_Decrypt();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation>(software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IGrantOperation> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGrantOperation create_Decrypt() {
      return new GrantOperation_Decrypt();
    }
    public static _IGrantOperation create_Encrypt() {
      return new GrantOperation_Encrypt();
    }
    public static _IGrantOperation create_GenerateDataKey() {
      return new GrantOperation_GenerateDataKey();
    }
    public static _IGrantOperation create_GenerateDataKeyWithoutPlaintext() {
      return new GrantOperation_GenerateDataKeyWithoutPlaintext();
    }
    public static _IGrantOperation create_ReEncryptFrom() {
      return new GrantOperation_ReEncryptFrom();
    }
    public static _IGrantOperation create_ReEncryptTo() {
      return new GrantOperation_ReEncryptTo();
    }
    public static _IGrantOperation create_Sign() {
      return new GrantOperation_Sign();
    }
    public static _IGrantOperation create_Verify() {
      return new GrantOperation_Verify();
    }
    public static _IGrantOperation create_GetPublicKey() {
      return new GrantOperation_GetPublicKey();
    }
    public static _IGrantOperation create_CreateGrant() {
      return new GrantOperation_CreateGrant();
    }
    public static _IGrantOperation create_RetireGrant() {
      return new GrantOperation_RetireGrant();
    }
    public static _IGrantOperation create_DescribeKey() {
      return new GrantOperation_DescribeKey();
    }
    public static _IGrantOperation create_GenerateDataKeyPair() {
      return new GrantOperation_GenerateDataKeyPair();
    }
    public static _IGrantOperation create_GenerateDataKeyPairWithoutPlaintext() {
      return new GrantOperation_GenerateDataKeyPairWithoutPlaintext();
    }
    public bool is_Decrypt { get { return this is GrantOperation_Decrypt; } }
    public bool is_Encrypt { get { return this is GrantOperation_Encrypt; } }
    public bool is_GenerateDataKey { get { return this is GrantOperation_GenerateDataKey; } }
    public bool is_GenerateDataKeyWithoutPlaintext { get { return this is GrantOperation_GenerateDataKeyWithoutPlaintext; } }
    public bool is_ReEncryptFrom { get { return this is GrantOperation_ReEncryptFrom; } }
    public bool is_ReEncryptTo { get { return this is GrantOperation_ReEncryptTo; } }
    public bool is_Sign { get { return this is GrantOperation_Sign; } }
    public bool is_Verify { get { return this is GrantOperation_Verify; } }
    public bool is_GetPublicKey { get { return this is GrantOperation_GetPublicKey; } }
    public bool is_CreateGrant { get { return this is GrantOperation_CreateGrant; } }
    public bool is_RetireGrant { get { return this is GrantOperation_RetireGrant; } }
    public bool is_DescribeKey { get { return this is GrantOperation_DescribeKey; } }
    public bool is_GenerateDataKeyPair { get { return this is GrantOperation_GenerateDataKeyPair; } }
    public bool is_GenerateDataKeyPairWithoutPlaintext { get { return this is GrantOperation_GenerateDataKeyPairWithoutPlaintext; } }
    public static System.Collections.Generic.IEnumerable<_IGrantOperation> AllSingletonConstructors {
      get {
        yield return GrantOperation.create_Decrypt();
        yield return GrantOperation.create_Encrypt();
        yield return GrantOperation.create_GenerateDataKey();
        yield return GrantOperation.create_GenerateDataKeyWithoutPlaintext();
        yield return GrantOperation.create_ReEncryptFrom();
        yield return GrantOperation.create_ReEncryptTo();
        yield return GrantOperation.create_Sign();
        yield return GrantOperation.create_Verify();
        yield return GrantOperation.create_GetPublicKey();
        yield return GrantOperation.create_CreateGrant();
        yield return GrantOperation.create_RetireGrant();
        yield return GrantOperation.create_DescribeKey();
        yield return GrantOperation.create_GenerateDataKeyPair();
        yield return GrantOperation.create_GenerateDataKeyPairWithoutPlaintext();
      }
    }
    public abstract _IGrantOperation DowncastClone();
  }
  public class GrantOperation_Decrypt : GrantOperation {
    public GrantOperation_Decrypt() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_Decrypt();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_Decrypt;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.Decrypt";
      return s;
    }
  }
  public class GrantOperation_Encrypt : GrantOperation {
    public GrantOperation_Encrypt() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_Encrypt();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_Encrypt;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.Encrypt";
      return s;
    }
  }
  public class GrantOperation_GenerateDataKey : GrantOperation {
    public GrantOperation_GenerateDataKey() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_GenerateDataKey();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_GenerateDataKey;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.GenerateDataKey";
      return s;
    }
  }
  public class GrantOperation_GenerateDataKeyWithoutPlaintext : GrantOperation {
    public GrantOperation_GenerateDataKeyWithoutPlaintext() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_GenerateDataKeyWithoutPlaintext();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_GenerateDataKeyWithoutPlaintext;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.GenerateDataKeyWithoutPlaintext";
      return s;
    }
  }
  public class GrantOperation_ReEncryptFrom : GrantOperation {
    public GrantOperation_ReEncryptFrom() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_ReEncryptFrom();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_ReEncryptFrom;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.ReEncryptFrom";
      return s;
    }
  }
  public class GrantOperation_ReEncryptTo : GrantOperation {
    public GrantOperation_ReEncryptTo() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_ReEncryptTo();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_ReEncryptTo;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.ReEncryptTo";
      return s;
    }
  }
  public class GrantOperation_Sign : GrantOperation {
    public GrantOperation_Sign() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_Sign();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_Sign;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.Sign";
      return s;
    }
  }
  public class GrantOperation_Verify : GrantOperation {
    public GrantOperation_Verify() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_Verify();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_Verify;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.Verify";
      return s;
    }
  }
  public class GrantOperation_GetPublicKey : GrantOperation {
    public GrantOperation_GetPublicKey() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_GetPublicKey();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_GetPublicKey;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.GetPublicKey";
      return s;
    }
  }
  public class GrantOperation_CreateGrant : GrantOperation {
    public GrantOperation_CreateGrant() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_CreateGrant();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_CreateGrant;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.CreateGrant";
      return s;
    }
  }
  public class GrantOperation_RetireGrant : GrantOperation {
    public GrantOperation_RetireGrant() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_RetireGrant();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_RetireGrant;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.RetireGrant";
      return s;
    }
  }
  public class GrantOperation_DescribeKey : GrantOperation {
    public GrantOperation_DescribeKey() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_DescribeKey();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_DescribeKey;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.DescribeKey";
      return s;
    }
  }
  public class GrantOperation_GenerateDataKeyPair : GrantOperation {
    public GrantOperation_GenerateDataKeyPair() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_GenerateDataKeyPair();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_GenerateDataKeyPair;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.GenerateDataKeyPair";
      return s;
    }
  }
  public class GrantOperation_GenerateDataKeyPairWithoutPlaintext : GrantOperation {
    public GrantOperation_GenerateDataKeyPairWithoutPlaintext() {
    }
    public override _IGrantOperation DowncastClone() {
      if (this is _IGrantOperation dt) { return dt; }
      return new GrantOperation_GenerateDataKeyPairWithoutPlaintext();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation_GenerateDataKeyPairWithoutPlaintext;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.GrantOperation.GenerateDataKeyPairWithoutPlaintext";
      return s;
    }
  }

  public partial class GrantTokenList {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<char>>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<char>>>(Dafny.Sequence<Dafny.ISequence<char>>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<char>>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class GrantTokenType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IImportKeyMaterialRequest {
    bool is_ImportKeyMaterialRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<byte> dtor_ImportToken { get; }
    Dafny.ISequence<byte> dtor_EncryptedKeyMaterial { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ValidTo { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> dtor_ExpirationModel { get; }
    _IImportKeyMaterialRequest DowncastClone();
  }
  public class ImportKeyMaterialRequest : _IImportKeyMaterialRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<byte> _ImportToken;
    public readonly Dafny.ISequence<byte> _EncryptedKeyMaterial;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _ValidTo;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> _ExpirationModel;
    public ImportKeyMaterialRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> ImportToken, Dafny.ISequence<byte> EncryptedKeyMaterial, Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> ExpirationModel) {
      this._KeyId = KeyId;
      this._ImportToken = ImportToken;
      this._EncryptedKeyMaterial = EncryptedKeyMaterial;
      this._ValidTo = ValidTo;
      this._ExpirationModel = ExpirationModel;
    }
    public _IImportKeyMaterialRequest DowncastClone() {
      if (this is _IImportKeyMaterialRequest dt) { return dt; }
      return new ImportKeyMaterialRequest(_KeyId, _ImportToken, _EncryptedKeyMaterial, _ValidTo, _ExpirationModel);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._ImportToken, oth._ImportToken) && object.Equals(this._EncryptedKeyMaterial, oth._EncryptedKeyMaterial) && object.Equals(this._ValidTo, oth._ValidTo) && object.Equals(this._ExpirationModel, oth._ExpirationModel);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ImportToken));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptedKeyMaterial));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ValidTo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ExpirationModel));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ImportKeyMaterialRequest.ImportKeyMaterialRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ImportToken);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptedKeyMaterial);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ValidTo);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ExpirationModel);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialRequest>(software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IImportKeyMaterialRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> ImportToken, Dafny.ISequence<byte> EncryptedKeyMaterial, Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> ExpirationModel) {
      return new ImportKeyMaterialRequest(KeyId, ImportToken, EncryptedKeyMaterial, ValidTo, ExpirationModel);
    }
    public static _IImportKeyMaterialRequest create_ImportKeyMaterialRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> ImportToken, Dafny.ISequence<byte> EncryptedKeyMaterial, Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> ExpirationModel) {
      return create(KeyId, ImportToken, EncryptedKeyMaterial, ValidTo, ExpirationModel);
    }
    public bool is_ImportKeyMaterialRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<byte> dtor_ImportToken {
      get {
        return this._ImportToken;
      }
    }
    public Dafny.ISequence<byte> dtor_EncryptedKeyMaterial {
      get {
        return this._EncryptedKeyMaterial;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ValidTo {
      get {
        return this._ValidTo;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> dtor_ExpirationModel {
      get {
        return this._ExpirationModel;
      }
    }
  }

  public interface _IImportKeyMaterialResponse {
    bool is_ImportKeyMaterialResponse { get; }
    _IImportKeyMaterialResponse DowncastClone();
  }
  public class ImportKeyMaterialResponse : _IImportKeyMaterialResponse {
    public ImportKeyMaterialResponse() {
    }
    public _IImportKeyMaterialResponse DowncastClone() {
      if (this is _IImportKeyMaterialResponse dt) { return dt; }
      return new ImportKeyMaterialResponse();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialResponse;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ImportKeyMaterialResponse.ImportKeyMaterialResponse";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialResponse theDefault = create();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialResponse>(software.amazon.cryptography.services.kms.internaldafny.types.ImportKeyMaterialResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IImportKeyMaterialResponse create() {
      return new ImportKeyMaterialResponse();
    }
    public static _IImportKeyMaterialResponse create_ImportKeyMaterialResponse() {
      return create();
    }
    public bool is_ImportKeyMaterialResponse { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IImportKeyMaterialResponse> AllSingletonConstructors {
      get {
        yield return ImportKeyMaterialResponse.create();
      }
    }
  }

  public partial class KeyIdType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IKeyListEntry {
    bool is_KeyListEntry { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyArn { get; }
    _IKeyListEntry DowncastClone();
  }
  public class KeyListEntry : _IKeyListEntry {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyArn;
    public KeyListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyArn) {
      this._KeyId = KeyId;
      this._KeyArn = KeyArn;
    }
    public _IKeyListEntry DowncastClone() {
      if (this is _IKeyListEntry dt) { return dt; }
      return new KeyListEntry(_KeyId, _KeyArn);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyListEntry;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._KeyArn, oth._KeyArn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyArn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyListEntry.KeyListEntry";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyArn);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IKeyListEntry theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IKeyListEntry Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyListEntry> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyListEntry>(software.amazon.cryptography.services.kms.internaldafny.types.KeyListEntry.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyListEntry> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyListEntry create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyArn) {
      return new KeyListEntry(KeyId, KeyArn);
    }
    public static _IKeyListEntry create_KeyListEntry(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyArn) {
      return create(KeyId, KeyArn);
    }
    public bool is_KeyListEntry { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyArn {
      get {
        return this._KeyArn;
      }
    }
  }

  public interface _IKeyManagerType {
    bool is_AWS { get; }
    bool is_CUSTOMER { get; }
    _IKeyManagerType DowncastClone();
  }
  public abstract class KeyManagerType : _IKeyManagerType {
    public KeyManagerType() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType theDefault = create_AWS();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType>(software.amazon.cryptography.services.kms.internaldafny.types.KeyManagerType.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyManagerType create_AWS() {
      return new KeyManagerType_AWS();
    }
    public static _IKeyManagerType create_CUSTOMER() {
      return new KeyManagerType_CUSTOMER();
    }
    public bool is_AWS { get { return this is KeyManagerType_AWS; } }
    public bool is_CUSTOMER { get { return this is KeyManagerType_CUSTOMER; } }
    public static System.Collections.Generic.IEnumerable<_IKeyManagerType> AllSingletonConstructors {
      get {
        yield return KeyManagerType.create_AWS();
        yield return KeyManagerType.create_CUSTOMER();
      }
    }
    public abstract _IKeyManagerType DowncastClone();
  }
  public class KeyManagerType_AWS : KeyManagerType {
    public KeyManagerType_AWS() {
    }
    public override _IKeyManagerType DowncastClone() {
      if (this is _IKeyManagerType dt) { return dt; }
      return new KeyManagerType_AWS();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyManagerType_AWS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyManagerType.AWS";
      return s;
    }
  }
  public class KeyManagerType_CUSTOMER : KeyManagerType {
    public KeyManagerType_CUSTOMER() {
    }
    public override _IKeyManagerType DowncastClone() {
      if (this is _IKeyManagerType dt) { return dt; }
      return new KeyManagerType_CUSTOMER();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyManagerType_CUSTOMER;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyManagerType.CUSTOMER";
      return s;
    }
  }

  public interface _IKeyMetadata {
    bool is_KeyMetadata { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AWSAccountId { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Arn { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate { get; }
    Wrappers_Compile._IOption<bool> dtor_Enabled { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> dtor_KeyUsage { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> dtor_KeyState { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_DeletionDate { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ValidTo { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> dtor_Origin { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> dtor_ExpirationModel { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType> dtor_KeyManager { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> dtor_KeySpec { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> dtor_EncryptionAlgorithms { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> dtor_SigningAlgorithms { get; }
    Wrappers_Compile._IOption<bool> dtor_MultiRegion { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration> dtor_MultiRegionConfiguration { get; }
    Wrappers_Compile._IOption<int> dtor_PendingDeletionWindowInDays { get; }
    _IKeyMetadata DowncastClone();
  }
  public class KeyMetadata : _IKeyMetadata {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _AWSAccountId;
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Arn;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CreationDate;
    public readonly Wrappers_Compile._IOption<bool> _Enabled;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Description;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> _KeyUsage;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> _KeyState;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _DeletionDate;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _ValidTo;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> _Origin;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CustomKeyStoreId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CloudHsmClusterId;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> _ExpirationModel;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType> _KeyManager;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> _CustomerMasterKeySpec;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> _KeySpec;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> _EncryptionAlgorithms;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> _SigningAlgorithms;
    public readonly Wrappers_Compile._IOption<bool> _MultiRegion;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration> _MultiRegionConfiguration;
    public readonly Wrappers_Compile._IOption<int> _PendingDeletionWindowInDays;
    public KeyMetadata(Wrappers_Compile._IOption<Dafny.ISequence<char>> AWSAccountId, Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<bool> Enabled, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> KeyState, Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> Origin, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> ExpirationModel, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType> KeyManager, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> KeySpec, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> EncryptionAlgorithms, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> SigningAlgorithms, Wrappers_Compile._IOption<bool> MultiRegion, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration> MultiRegionConfiguration, Wrappers_Compile._IOption<int> PendingDeletionWindowInDays) {
      this._AWSAccountId = AWSAccountId;
      this._KeyId = KeyId;
      this._Arn = Arn;
      this._CreationDate = CreationDate;
      this._Enabled = Enabled;
      this._Description = Description;
      this._KeyUsage = KeyUsage;
      this._KeyState = KeyState;
      this._DeletionDate = DeletionDate;
      this._ValidTo = ValidTo;
      this._Origin = Origin;
      this._CustomKeyStoreId = CustomKeyStoreId;
      this._CloudHsmClusterId = CloudHsmClusterId;
      this._ExpirationModel = ExpirationModel;
      this._KeyManager = KeyManager;
      this._CustomerMasterKeySpec = CustomerMasterKeySpec;
      this._KeySpec = KeySpec;
      this._EncryptionAlgorithms = EncryptionAlgorithms;
      this._SigningAlgorithms = SigningAlgorithms;
      this._MultiRegion = MultiRegion;
      this._MultiRegionConfiguration = MultiRegionConfiguration;
      this._PendingDeletionWindowInDays = PendingDeletionWindowInDays;
    }
    public _IKeyMetadata DowncastClone() {
      if (this is _IKeyMetadata dt) { return dt; }
      return new KeyMetadata(_AWSAccountId, _KeyId, _Arn, _CreationDate, _Enabled, _Description, _KeyUsage, _KeyState, _DeletionDate, _ValidTo, _Origin, _CustomKeyStoreId, _CloudHsmClusterId, _ExpirationModel, _KeyManager, _CustomerMasterKeySpec, _KeySpec, _EncryptionAlgorithms, _SigningAlgorithms, _MultiRegion, _MultiRegionConfiguration, _PendingDeletionWindowInDays);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyMetadata;
      return oth != null && object.Equals(this._AWSAccountId, oth._AWSAccountId) && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._Arn, oth._Arn) && object.Equals(this._CreationDate, oth._CreationDate) && object.Equals(this._Enabled, oth._Enabled) && object.Equals(this._Description, oth._Description) && object.Equals(this._KeyUsage, oth._KeyUsage) && object.Equals(this._KeyState, oth._KeyState) && object.Equals(this._DeletionDate, oth._DeletionDate) && object.Equals(this._ValidTo, oth._ValidTo) && object.Equals(this._Origin, oth._Origin) && object.Equals(this._CustomKeyStoreId, oth._CustomKeyStoreId) && object.Equals(this._CloudHsmClusterId, oth._CloudHsmClusterId) && object.Equals(this._ExpirationModel, oth._ExpirationModel) && object.Equals(this._KeyManager, oth._KeyManager) && object.Equals(this._CustomerMasterKeySpec, oth._CustomerMasterKeySpec) && object.Equals(this._KeySpec, oth._KeySpec) && object.Equals(this._EncryptionAlgorithms, oth._EncryptionAlgorithms) && object.Equals(this._SigningAlgorithms, oth._SigningAlgorithms) && object.Equals(this._MultiRegion, oth._MultiRegion) && object.Equals(this._MultiRegionConfiguration, oth._MultiRegionConfiguration) && object.Equals(this._PendingDeletionWindowInDays, oth._PendingDeletionWindowInDays);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._AWSAccountId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Arn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CreationDate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Enabled));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Description));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyUsage));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._DeletionDate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ValidTo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Origin));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CloudHsmClusterId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ExpirationModel));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyManager));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomerMasterKeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeySpec));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._EncryptionAlgorithms));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SigningAlgorithms));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._MultiRegion));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._MultiRegionConfiguration));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PendingDeletionWindowInDays));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyMetadata.KeyMetadata";
      s += "(";
      s += Dafny.Helpers.ToString(this._AWSAccountId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Arn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CreationDate);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Enabled);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Description);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyUsage);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._DeletionDate);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ValidTo);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Origin);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CloudHsmClusterId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ExpirationModel);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyManager);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CustomerMasterKeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeySpec);
      s += ", ";
      s += Dafny.Helpers.ToString(this._EncryptionAlgorithms);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SigningAlgorithms);
      s += ", ";
      s += Dafny.Helpers.ToString(this._MultiRegion);
      s += ", ";
      s += Dafny.Helpers.ToString(this._MultiRegionConfiguration);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PendingDeletionWindowInDays);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec>.Default(), Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>>.Default(), Wrappers_Compile.Option<bool>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration>.Default(), Wrappers_Compile.Option<int>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata>(software.amazon.cryptography.services.kms.internaldafny.types.KeyMetadata.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyMetadata create(Wrappers_Compile._IOption<Dafny.ISequence<char>> AWSAccountId, Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<bool> Enabled, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> KeyState, Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> Origin, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> ExpirationModel, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType> KeyManager, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> KeySpec, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> EncryptionAlgorithms, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> SigningAlgorithms, Wrappers_Compile._IOption<bool> MultiRegion, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration> MultiRegionConfiguration, Wrappers_Compile._IOption<int> PendingDeletionWindowInDays) {
      return new KeyMetadata(AWSAccountId, KeyId, Arn, CreationDate, Enabled, Description, KeyUsage, KeyState, DeletionDate, ValidTo, Origin, CustomKeyStoreId, CloudHsmClusterId, ExpirationModel, KeyManager, CustomerMasterKeySpec, KeySpec, EncryptionAlgorithms, SigningAlgorithms, MultiRegion, MultiRegionConfiguration, PendingDeletionWindowInDays);
    }
    public static _IKeyMetadata create_KeyMetadata(Wrappers_Compile._IOption<Dafny.ISequence<char>> AWSAccountId, Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn, Wrappers_Compile._IOption<Dafny.ISequence<char>> CreationDate, Wrappers_Compile._IOption<bool> Enabled, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> KeyUsage, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> KeyState, Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate, Wrappers_Compile._IOption<Dafny.ISequence<char>> ValidTo, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> Origin, Wrappers_Compile._IOption<Dafny.ISequence<char>> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> ExpirationModel, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType> KeyManager, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> CustomerMasterKeySpec, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> KeySpec, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> EncryptionAlgorithms, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> SigningAlgorithms, Wrappers_Compile._IOption<bool> MultiRegion, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration> MultiRegionConfiguration, Wrappers_Compile._IOption<int> PendingDeletionWindowInDays) {
      return create(AWSAccountId, KeyId, Arn, CreationDate, Enabled, Description, KeyUsage, KeyState, DeletionDate, ValidTo, Origin, CustomKeyStoreId, CloudHsmClusterId, ExpirationModel, KeyManager, CustomerMasterKeySpec, KeySpec, EncryptionAlgorithms, SigningAlgorithms, MultiRegion, MultiRegionConfiguration, PendingDeletionWindowInDays);
    }
    public bool is_KeyMetadata { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_AWSAccountId {
      get {
        return this._AWSAccountId;
      }
    }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Arn {
      get {
        return this._Arn;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CreationDate {
      get {
        return this._CreationDate;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Enabled {
      get {
        return this._Enabled;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description {
      get {
        return this._Description;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> dtor_KeyUsage {
      get {
        return this._KeyUsage;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> dtor_KeyState {
      get {
        return this._KeyState;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_DeletionDate {
      get {
        return this._DeletionDate;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ValidTo {
      get {
        return this._ValidTo;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> dtor_Origin {
      get {
        return this._Origin;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CustomKeyStoreId {
      get {
        return this._CustomKeyStoreId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId {
      get {
        return this._CloudHsmClusterId;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IExpirationModelType> dtor_ExpirationModel {
      get {
        return this._ExpirationModel;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyManagerType> dtor_KeyManager {
      get {
        return this._KeyManager;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ICustomerMasterKeySpec> dtor_CustomerMasterKeySpec {
      get {
        return this._CustomerMasterKeySpec;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> dtor_KeySpec {
      get {
        return this._KeySpec;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>> dtor_EncryptionAlgorithms {
      get {
        return this._EncryptionAlgorithms;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>> dtor_SigningAlgorithms {
      get {
        return this._SigningAlgorithms;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_MultiRegion {
      get {
        return this._MultiRegion;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration> dtor_MultiRegionConfiguration {
      get {
        return this._MultiRegionConfiguration;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_PendingDeletionWindowInDays {
      get {
        return this._PendingDeletionWindowInDays;
      }
    }
  }

  public interface _IKeySpec {
    bool is_RSA__2048 { get; }
    bool is_RSA__3072 { get; }
    bool is_RSA__4096 { get; }
    bool is_ECC__NIST__P256 { get; }
    bool is_ECC__NIST__P384 { get; }
    bool is_ECC__NIST__P521 { get; }
    bool is_ECC__SECG__P256K1 { get; }
    bool is_SYMMETRIC__DEFAULT { get; }
    _IKeySpec DowncastClone();
  }
  public abstract class KeySpec : _IKeySpec {
    public KeySpec() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec theDefault = create_RSA__2048();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec>(software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeySpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeySpec create_RSA__2048() {
      return new KeySpec_RSA__2048();
    }
    public static _IKeySpec create_RSA__3072() {
      return new KeySpec_RSA__3072();
    }
    public static _IKeySpec create_RSA__4096() {
      return new KeySpec_RSA__4096();
    }
    public static _IKeySpec create_ECC__NIST__P256() {
      return new KeySpec_ECC__NIST__P256();
    }
    public static _IKeySpec create_ECC__NIST__P384() {
      return new KeySpec_ECC__NIST__P384();
    }
    public static _IKeySpec create_ECC__NIST__P521() {
      return new KeySpec_ECC__NIST__P521();
    }
    public static _IKeySpec create_ECC__SECG__P256K1() {
      return new KeySpec_ECC__SECG__P256K1();
    }
    public static _IKeySpec create_SYMMETRIC__DEFAULT() {
      return new KeySpec_SYMMETRIC__DEFAULT();
    }
    public bool is_RSA__2048 { get { return this is KeySpec_RSA__2048; } }
    public bool is_RSA__3072 { get { return this is KeySpec_RSA__3072; } }
    public bool is_RSA__4096 { get { return this is KeySpec_RSA__4096; } }
    public bool is_ECC__NIST__P256 { get { return this is KeySpec_ECC__NIST__P256; } }
    public bool is_ECC__NIST__P384 { get { return this is KeySpec_ECC__NIST__P384; } }
    public bool is_ECC__NIST__P521 { get { return this is KeySpec_ECC__NIST__P521; } }
    public bool is_ECC__SECG__P256K1 { get { return this is KeySpec_ECC__SECG__P256K1; } }
    public bool is_SYMMETRIC__DEFAULT { get { return this is KeySpec_SYMMETRIC__DEFAULT; } }
    public static System.Collections.Generic.IEnumerable<_IKeySpec> AllSingletonConstructors {
      get {
        yield return KeySpec.create_RSA__2048();
        yield return KeySpec.create_RSA__3072();
        yield return KeySpec.create_RSA__4096();
        yield return KeySpec.create_ECC__NIST__P256();
        yield return KeySpec.create_ECC__NIST__P384();
        yield return KeySpec.create_ECC__NIST__P521();
        yield return KeySpec.create_ECC__SECG__P256K1();
        yield return KeySpec.create_SYMMETRIC__DEFAULT();
      }
    }
    public abstract _IKeySpec DowncastClone();
  }
  public class KeySpec_RSA__2048 : KeySpec {
    public KeySpec_RSA__2048() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_RSA__2048();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeySpec_RSA__2048;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeySpec.RSA_2048";
      return s;
    }
  }
  public class KeySpec_RSA__3072 : KeySpec {
    public KeySpec_RSA__3072() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_RSA__3072();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeySpec_RSA__3072;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeySpec.RSA_3072";
      return s;
    }
  }
  public class KeySpec_RSA__4096 : KeySpec {
    public KeySpec_RSA__4096() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_RSA__4096();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeySpec_RSA__4096;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeySpec.RSA_4096";
      return s;
    }
  }
  public class KeySpec_ECC__NIST__P256 : KeySpec {
    public KeySpec_ECC__NIST__P256() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_ECC__NIST__P256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeySpec_ECC__NIST__P256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeySpec.ECC_NIST_P256";
      return s;
    }
  }
  public class KeySpec_ECC__NIST__P384 : KeySpec {
    public KeySpec_ECC__NIST__P384() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_ECC__NIST__P384();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeySpec_ECC__NIST__P384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeySpec.ECC_NIST_P384";
      return s;
    }
  }
  public class KeySpec_ECC__NIST__P521 : KeySpec {
    public KeySpec_ECC__NIST__P521() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_ECC__NIST__P521();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeySpec_ECC__NIST__P521;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeySpec.ECC_NIST_P521";
      return s;
    }
  }
  public class KeySpec_ECC__SECG__P256K1 : KeySpec {
    public KeySpec_ECC__SECG__P256K1() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_ECC__SECG__P256K1();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeySpec_ECC__SECG__P256K1;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeySpec.ECC_SECG_P256K1";
      return s;
    }
  }
  public class KeySpec_SYMMETRIC__DEFAULT : KeySpec {
    public KeySpec_SYMMETRIC__DEFAULT() {
    }
    public override _IKeySpec DowncastClone() {
      if (this is _IKeySpec dt) { return dt; }
      return new KeySpec_SYMMETRIC__DEFAULT();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeySpec_SYMMETRIC__DEFAULT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeySpec.SYMMETRIC_DEFAULT";
      return s;
    }
  }

  public interface _IKeyState {
    bool is_Creating { get; }
    bool is_Enabled { get; }
    bool is_Disabled { get; }
    bool is_PendingDeletion { get; }
    bool is_PendingImport { get; }
    bool is_PendingReplicaDeletion { get; }
    bool is_Unavailable { get; }
    bool is_Updating { get; }
    _IKeyState DowncastClone();
  }
  public abstract class KeyState : _IKeyState {
    public KeyState() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IKeyState theDefault = create_Creating();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IKeyState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState>(software.amazon.cryptography.services.kms.internaldafny.types.KeyState.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyState create_Creating() {
      return new KeyState_Creating();
    }
    public static _IKeyState create_Enabled() {
      return new KeyState_Enabled();
    }
    public static _IKeyState create_Disabled() {
      return new KeyState_Disabled();
    }
    public static _IKeyState create_PendingDeletion() {
      return new KeyState_PendingDeletion();
    }
    public static _IKeyState create_PendingImport() {
      return new KeyState_PendingImport();
    }
    public static _IKeyState create_PendingReplicaDeletion() {
      return new KeyState_PendingReplicaDeletion();
    }
    public static _IKeyState create_Unavailable() {
      return new KeyState_Unavailable();
    }
    public static _IKeyState create_Updating() {
      return new KeyState_Updating();
    }
    public bool is_Creating { get { return this is KeyState_Creating; } }
    public bool is_Enabled { get { return this is KeyState_Enabled; } }
    public bool is_Disabled { get { return this is KeyState_Disabled; } }
    public bool is_PendingDeletion { get { return this is KeyState_PendingDeletion; } }
    public bool is_PendingImport { get { return this is KeyState_PendingImport; } }
    public bool is_PendingReplicaDeletion { get { return this is KeyState_PendingReplicaDeletion; } }
    public bool is_Unavailable { get { return this is KeyState_Unavailable; } }
    public bool is_Updating { get { return this is KeyState_Updating; } }
    public static System.Collections.Generic.IEnumerable<_IKeyState> AllSingletonConstructors {
      get {
        yield return KeyState.create_Creating();
        yield return KeyState.create_Enabled();
        yield return KeyState.create_Disabled();
        yield return KeyState.create_PendingDeletion();
        yield return KeyState.create_PendingImport();
        yield return KeyState.create_PendingReplicaDeletion();
        yield return KeyState.create_Unavailable();
        yield return KeyState.create_Updating();
      }
    }
    public abstract _IKeyState DowncastClone();
  }
  public class KeyState_Creating : KeyState {
    public KeyState_Creating() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_Creating();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyState_Creating;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyState.Creating";
      return s;
    }
  }
  public class KeyState_Enabled : KeyState {
    public KeyState_Enabled() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_Enabled();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyState_Enabled;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyState.Enabled";
      return s;
    }
  }
  public class KeyState_Disabled : KeyState {
    public KeyState_Disabled() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_Disabled();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyState_Disabled;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyState.Disabled";
      return s;
    }
  }
  public class KeyState_PendingDeletion : KeyState {
    public KeyState_PendingDeletion() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_PendingDeletion();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyState_PendingDeletion;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyState.PendingDeletion";
      return s;
    }
  }
  public class KeyState_PendingImport : KeyState {
    public KeyState_PendingImport() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_PendingImport();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyState_PendingImport;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyState.PendingImport";
      return s;
    }
  }
  public class KeyState_PendingReplicaDeletion : KeyState {
    public KeyState_PendingReplicaDeletion() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_PendingReplicaDeletion();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyState_PendingReplicaDeletion;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyState.PendingReplicaDeletion";
      return s;
    }
  }
  public class KeyState_Unavailable : KeyState {
    public KeyState_Unavailable() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_Unavailable();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyState_Unavailable;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyState.Unavailable";
      return s;
    }
  }
  public class KeyState_Updating : KeyState {
    public KeyState_Updating() {
    }
    public override _IKeyState DowncastClone() {
      if (this is _IKeyState dt) { return dt; }
      return new KeyState_Updating();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyState_Updating;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyState.Updating";
      return s;
    }
  }

  public partial class KeyStorePasswordType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IKeyUsageType {
    bool is_SIGN__VERIFY { get; }
    bool is_ENCRYPT__DECRYPT { get; }
    _IKeyUsageType DowncastClone();
  }
  public abstract class KeyUsageType : _IKeyUsageType {
    public KeyUsageType() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType theDefault = create_SIGN__VERIFY();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType>(software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IKeyUsageType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKeyUsageType create_SIGN__VERIFY() {
      return new KeyUsageType_SIGN__VERIFY();
    }
    public static _IKeyUsageType create_ENCRYPT__DECRYPT() {
      return new KeyUsageType_ENCRYPT__DECRYPT();
    }
    public bool is_SIGN__VERIFY { get { return this is KeyUsageType_SIGN__VERIFY; } }
    public bool is_ENCRYPT__DECRYPT { get { return this is KeyUsageType_ENCRYPT__DECRYPT; } }
    public static System.Collections.Generic.IEnumerable<_IKeyUsageType> AllSingletonConstructors {
      get {
        yield return KeyUsageType.create_SIGN__VERIFY();
        yield return KeyUsageType.create_ENCRYPT__DECRYPT();
      }
    }
    public abstract _IKeyUsageType DowncastClone();
  }
  public class KeyUsageType_SIGN__VERIFY : KeyUsageType {
    public KeyUsageType_SIGN__VERIFY() {
    }
    public override _IKeyUsageType DowncastClone() {
      if (this is _IKeyUsageType dt) { return dt; }
      return new KeyUsageType_SIGN__VERIFY();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType_SIGN__VERIFY;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyUsageType.SIGN_VERIFY";
      return s;
    }
  }
  public class KeyUsageType_ENCRYPT__DECRYPT : KeyUsageType {
    public KeyUsageType_ENCRYPT__DECRYPT() {
    }
    public override _IKeyUsageType DowncastClone() {
      if (this is _IKeyUsageType dt) { return dt; }
      return new KeyUsageType_ENCRYPT__DECRYPT();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType_ENCRYPT__DECRYPT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.KeyUsageType.ENCRYPT_DECRYPT";
      return s;
    }
  }

  public partial class LimitType {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IListAliasesRequest {
    bool is_ListAliasesRequest { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    _IListAliasesRequest DowncastClone();
  }
  public class ListAliasesRequest : _IListAliasesRequest {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<int> _Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Marker;
    public ListAliasesRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      this._KeyId = KeyId;
      this._Limit = Limit;
      this._Marker = Marker;
    }
    public _IListAliasesRequest DowncastClone() {
      if (this is _IListAliasesRequest dt) { return dt; }
      return new ListAliasesRequest(_KeyId, _Limit, _Marker);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._Limit, oth._Limit) && object.Equals(this._Marker, oth._Marker);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Marker));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ListAliasesRequest.ListAliasesRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Marker);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesRequest theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesRequest>(software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListAliasesRequest create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return new ListAliasesRequest(KeyId, Limit, Marker);
    }
    public static _IListAliasesRequest create_ListAliasesRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return create(KeyId, Limit, Marker);
    }
    public bool is_ListAliasesRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this._Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this._Marker;
      }
    }
  }

  public interface _IListAliasesResponse {
    bool is_ListAliasesResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>> dtor_Aliases { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker { get; }
    Wrappers_Compile._IOption<bool> dtor_Truncated { get; }
    _IListAliasesResponse DowncastClone();
  }
  public class ListAliasesResponse : _IListAliasesResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>> _Aliases;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _NextMarker;
    public readonly Wrappers_Compile._IOption<bool> _Truncated;
    public ListAliasesResponse(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>> Aliases, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      this._Aliases = Aliases;
      this._NextMarker = NextMarker;
      this._Truncated = Truncated;
    }
    public _IListAliasesResponse DowncastClone() {
      if (this is _IListAliasesResponse dt) { return dt; }
      return new ListAliasesResponse(_Aliases, _NextMarker, _Truncated);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesResponse;
      return oth != null && object.Equals(this._Aliases, oth._Aliases) && object.Equals(this._NextMarker, oth._NextMarker) && object.Equals(this._Truncated, oth._Truncated);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Aliases));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._NextMarker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Truncated));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ListAliasesResponse.ListAliasesResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._Aliases);
      s += ", ";
      s += Dafny.Helpers.ToString(this._NextMarker);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Truncated);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesResponse>(software.amazon.cryptography.services.kms.internaldafny.types.ListAliasesResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListAliasesResponse create(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>> Aliases, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return new ListAliasesResponse(Aliases, NextMarker, Truncated);
    }
    public static _IListAliasesResponse create_ListAliasesResponse(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>> Aliases, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return create(Aliases, NextMarker, Truncated);
    }
    public bool is_ListAliasesResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IAliasListEntry>> dtor_Aliases {
      get {
        return this._Aliases;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker {
      get {
        return this._NextMarker;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Truncated {
      get {
        return this._Truncated;
      }
    }
  }

  public interface _IListGrantsRequest {
    bool is_ListGrantsRequest { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GranteePrincipal { get; }
    _IListGrantsRequest DowncastClone();
  }
  public class ListGrantsRequest : _IListGrantsRequest {
    public readonly Wrappers_Compile._IOption<int> _Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Marker;
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _GrantId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _GranteePrincipal;
    public ListGrantsRequest(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker, Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal) {
      this._Limit = Limit;
      this._Marker = Marker;
      this._KeyId = KeyId;
      this._GrantId = GrantId;
      this._GranteePrincipal = GranteePrincipal;
    }
    public _IListGrantsRequest DowncastClone() {
      if (this is _IListGrantsRequest dt) { return dt; }
      return new ListGrantsRequest(_Limit, _Marker, _KeyId, _GrantId, _GranteePrincipal);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsRequest;
      return oth != null && object.Equals(this._Limit, oth._Limit) && object.Equals(this._Marker, oth._Marker) && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._GrantId, oth._GrantId) && object.Equals(this._GranteePrincipal, oth._GranteePrincipal);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Marker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GranteePrincipal));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ListGrantsRequest.ListGrantsRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Marker);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GranteePrincipal);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsRequest theDefault = create(Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsRequest>(software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListGrantsRequest create(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker, Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal) {
      return new ListGrantsRequest(Limit, Marker, KeyId, GrantId, GranteePrincipal);
    }
    public static _IListGrantsRequest create_ListGrantsRequest(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker, Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GranteePrincipal) {
      return create(Limit, Marker, KeyId, GrantId, GranteePrincipal);
    }
    public bool is_ListGrantsRequest { get { return true; } }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this._Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this._Marker;
      }
    }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId {
      get {
        return this._GrantId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GranteePrincipal {
      get {
        return this._GranteePrincipal;
      }
    }
  }

  public interface _IListGrantsResponse {
    bool is_ListGrantsResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>> dtor_Grants { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker { get; }
    Wrappers_Compile._IOption<bool> dtor_Truncated { get; }
    _IListGrantsResponse DowncastClone();
  }
  public class ListGrantsResponse : _IListGrantsResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>> _Grants;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _NextMarker;
    public readonly Wrappers_Compile._IOption<bool> _Truncated;
    public ListGrantsResponse(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>> Grants, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      this._Grants = Grants;
      this._NextMarker = NextMarker;
      this._Truncated = Truncated;
    }
    public _IListGrantsResponse DowncastClone() {
      if (this is _IListGrantsResponse dt) { return dt; }
      return new ListGrantsResponse(_Grants, _NextMarker, _Truncated);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsResponse;
      return oth != null && object.Equals(this._Grants, oth._Grants) && object.Equals(this._NextMarker, oth._NextMarker) && object.Equals(this._Truncated, oth._Truncated);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Grants));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._NextMarker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Truncated));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ListGrantsResponse.ListGrantsResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._Grants);
      s += ", ";
      s += Dafny.Helpers.ToString(this._NextMarker);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Truncated);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsResponse>(software.amazon.cryptography.services.kms.internaldafny.types.ListGrantsResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListGrantsResponse create(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>> Grants, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return new ListGrantsResponse(Grants, NextMarker, Truncated);
    }
    public static _IListGrantsResponse create_ListGrantsResponse(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>> Grants, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return create(Grants, NextMarker, Truncated);
    }
    public bool is_ListGrantsResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IGrantListEntry>> dtor_Grants {
      get {
        return this._Grants;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker {
      get {
        return this._NextMarker;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Truncated {
      get {
        return this._Truncated;
      }
    }
  }

  public interface _IListKeyPoliciesRequest {
    bool is_ListKeyPoliciesRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    _IListKeyPoliciesRequest DowncastClone();
  }
  public class ListKeyPoliciesRequest : _IListKeyPoliciesRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Wrappers_Compile._IOption<int> _Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Marker;
    public ListKeyPoliciesRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      this._KeyId = KeyId;
      this._Limit = Limit;
      this._Marker = Marker;
    }
    public _IListKeyPoliciesRequest DowncastClone() {
      if (this is _IListKeyPoliciesRequest dt) { return dt; }
      return new ListKeyPoliciesRequest(_KeyId, _Limit, _Marker);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._Limit, oth._Limit) && object.Equals(this._Marker, oth._Marker);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Marker));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ListKeyPoliciesRequest.ListKeyPoliciesRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Marker);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesRequest>(software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListKeyPoliciesRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return new ListKeyPoliciesRequest(KeyId, Limit, Marker);
    }
    public static _IListKeyPoliciesRequest create_ListKeyPoliciesRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return create(KeyId, Limit, Marker);
    }
    public bool is_ListKeyPoliciesRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this._Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this._Marker;
      }
    }
  }

  public interface _IListKeyPoliciesResponse {
    bool is_ListKeyPoliciesResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_PolicyNames { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker { get; }
    Wrappers_Compile._IOption<bool> dtor_Truncated { get; }
    _IListKeyPoliciesResponse DowncastClone();
  }
  public class ListKeyPoliciesResponse : _IListKeyPoliciesResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _PolicyNames;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _NextMarker;
    public readonly Wrappers_Compile._IOption<bool> _Truncated;
    public ListKeyPoliciesResponse(Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> PolicyNames, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      this._PolicyNames = PolicyNames;
      this._NextMarker = NextMarker;
      this._Truncated = Truncated;
    }
    public _IListKeyPoliciesResponse DowncastClone() {
      if (this is _IListKeyPoliciesResponse dt) { return dt; }
      return new ListKeyPoliciesResponse(_PolicyNames, _NextMarker, _Truncated);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesResponse;
      return oth != null && object.Equals(this._PolicyNames, oth._PolicyNames) && object.Equals(this._NextMarker, oth._NextMarker) && object.Equals(this._Truncated, oth._Truncated);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PolicyNames));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._NextMarker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Truncated));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ListKeyPoliciesResponse.ListKeyPoliciesResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._PolicyNames);
      s += ", ";
      s += Dafny.Helpers.ToString(this._NextMarker);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Truncated);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesResponse>(software.amazon.cryptography.services.kms.internaldafny.types.ListKeyPoliciesResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListKeyPoliciesResponse create(Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> PolicyNames, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return new ListKeyPoliciesResponse(PolicyNames, NextMarker, Truncated);
    }
    public static _IListKeyPoliciesResponse create_ListKeyPoliciesResponse(Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> PolicyNames, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return create(PolicyNames, NextMarker, Truncated);
    }
    public bool is_ListKeyPoliciesResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_PolicyNames {
      get {
        return this._PolicyNames;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker {
      get {
        return this._NextMarker;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Truncated {
      get {
        return this._Truncated;
      }
    }
  }

  public interface _IListKeysRequest {
    bool is_ListKeysRequest { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    _IListKeysRequest DowncastClone();
  }
  public class ListKeysRequest : _IListKeysRequest {
    public readonly Wrappers_Compile._IOption<int> _Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Marker;
    public ListKeysRequest(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      this._Limit = Limit;
      this._Marker = Marker;
    }
    public _IListKeysRequest DowncastClone() {
      if (this is _IListKeysRequest dt) { return dt; }
      return new ListKeysRequest(_Limit, _Marker);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ListKeysRequest;
      return oth != null && object.Equals(this._Limit, oth._Limit) && object.Equals(this._Marker, oth._Marker);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Marker));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ListKeysRequest.ListKeysRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Marker);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IListKeysRequest theDefault = create(Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IListKeysRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListKeysRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListKeysRequest>(software.amazon.cryptography.services.kms.internaldafny.types.ListKeysRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListKeysRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListKeysRequest create(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return new ListKeysRequest(Limit, Marker);
    }
    public static _IListKeysRequest create_ListKeysRequest(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return create(Limit, Marker);
    }
    public bool is_ListKeysRequest { get { return true; } }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this._Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this._Marker;
      }
    }
  }

  public interface _IListResourceTagsRequest {
    bool is_ListResourceTagsRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    _IListResourceTagsRequest DowncastClone();
  }
  public class ListResourceTagsRequest : _IListResourceTagsRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Wrappers_Compile._IOption<int> _Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Marker;
    public ListResourceTagsRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      this._KeyId = KeyId;
      this._Limit = Limit;
      this._Marker = Marker;
    }
    public _IListResourceTagsRequest DowncastClone() {
      if (this is _IListResourceTagsRequest dt) { return dt; }
      return new ListResourceTagsRequest(_KeyId, _Limit, _Marker);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._Limit, oth._Limit) && object.Equals(this._Marker, oth._Marker);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Marker));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ListResourceTagsRequest.ListResourceTagsRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Marker);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsRequest>(software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListResourceTagsRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return new ListResourceTagsRequest(KeyId, Limit, Marker);
    }
    public static _IListResourceTagsRequest create_ListResourceTagsRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker) {
      return create(KeyId, Limit, Marker);
    }
    public bool is_ListResourceTagsRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this._Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this._Marker;
      }
    }
  }

  public interface _IListResourceTagsResponse {
    bool is_ListResourceTagsResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> dtor_Tags { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker { get; }
    Wrappers_Compile._IOption<bool> dtor_Truncated { get; }
    _IListResourceTagsResponse DowncastClone();
  }
  public class ListResourceTagsResponse : _IListResourceTagsResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> _Tags;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _NextMarker;
    public readonly Wrappers_Compile._IOption<bool> _Truncated;
    public ListResourceTagsResponse(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> Tags, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      this._Tags = Tags;
      this._NextMarker = NextMarker;
      this._Truncated = Truncated;
    }
    public _IListResourceTagsResponse DowncastClone() {
      if (this is _IListResourceTagsResponse dt) { return dt; }
      return new ListResourceTagsResponse(_Tags, _NextMarker, _Truncated);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsResponse;
      return oth != null && object.Equals(this._Tags, oth._Tags) && object.Equals(this._NextMarker, oth._NextMarker) && object.Equals(this._Truncated, oth._Truncated);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Tags));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._NextMarker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Truncated));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ListResourceTagsResponse.ListResourceTagsResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._Tags);
      s += ", ";
      s += Dafny.Helpers.ToString(this._NextMarker);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Truncated);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsResponse>(software.amazon.cryptography.services.kms.internaldafny.types.ListResourceTagsResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListResourceTagsResponse create(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> Tags, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return new ListResourceTagsResponse(Tags, NextMarker, Truncated);
    }
    public static _IListResourceTagsResponse create_ListResourceTagsResponse(Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> Tags, Wrappers_Compile._IOption<Dafny.ISequence<char>> NextMarker, Wrappers_Compile._IOption<bool> Truncated) {
      return create(Tags, NextMarker, Truncated);
    }
    public bool is_ListResourceTagsResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> dtor_Tags {
      get {
        return this._Tags;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NextMarker {
      get {
        return this._NextMarker;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_Truncated {
      get {
        return this._Truncated;
      }
    }
  }

  public interface _IListRetirableGrantsRequest {
    bool is_ListRetirableGrantsRequest { get; }
    Wrappers_Compile._IOption<int> dtor_Limit { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker { get; }
    Dafny.ISequence<char> dtor_RetiringPrincipal { get; }
    _IListRetirableGrantsRequest DowncastClone();
  }
  public class ListRetirableGrantsRequest : _IListRetirableGrantsRequest {
    public readonly Wrappers_Compile._IOption<int> _Limit;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Marker;
    public readonly Dafny.ISequence<char> _RetiringPrincipal;
    public ListRetirableGrantsRequest(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker, Dafny.ISequence<char> RetiringPrincipal) {
      this._Limit = Limit;
      this._Marker = Marker;
      this._RetiringPrincipal = RetiringPrincipal;
    }
    public _IListRetirableGrantsRequest DowncastClone() {
      if (this is _IListRetirableGrantsRequest dt) { return dt; }
      return new ListRetirableGrantsRequest(_Limit, _Marker, _RetiringPrincipal);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ListRetirableGrantsRequest;
      return oth != null && object.Equals(this._Limit, oth._Limit) && object.Equals(this._Marker, oth._Marker) && object.Equals(this._RetiringPrincipal, oth._RetiringPrincipal);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Limit));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Marker));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._RetiringPrincipal));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ListRetirableGrantsRequest.ListRetirableGrantsRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._Limit);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Marker);
      s += ", ";
      s += Dafny.Helpers.ToString(this._RetiringPrincipal);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IListRetirableGrantsRequest theDefault = create(Wrappers_Compile.Option<int>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IListRetirableGrantsRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListRetirableGrantsRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListRetirableGrantsRequest>(software.amazon.cryptography.services.kms.internaldafny.types.ListRetirableGrantsRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IListRetirableGrantsRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IListRetirableGrantsRequest create(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker, Dafny.ISequence<char> RetiringPrincipal) {
      return new ListRetirableGrantsRequest(Limit, Marker, RetiringPrincipal);
    }
    public static _IListRetirableGrantsRequest create_ListRetirableGrantsRequest(Wrappers_Compile._IOption<int> Limit, Wrappers_Compile._IOption<Dafny.ISequence<char>> Marker, Dafny.ISequence<char> RetiringPrincipal) {
      return create(Limit, Marker, RetiringPrincipal);
    }
    public bool is_ListRetirableGrantsRequest { get { return true; } }
    public Wrappers_Compile._IOption<int> dtor_Limit {
      get {
        return this._Limit;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Marker {
      get {
        return this._Marker;
      }
    }
    public Dafny.ISequence<char> dtor_RetiringPrincipal {
      get {
        return this._RetiringPrincipal;
      }
    }
  }

  public partial class MarkerType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IMessageType {
    bool is_RAW { get; }
    bool is_DIGEST { get; }
    _IMessageType DowncastClone();
  }
  public abstract class MessageType : _IMessageType {
    public MessageType() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IMessageType theDefault = create_RAW();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IMessageType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType>(software.amazon.cryptography.services.kms.internaldafny.types.MessageType.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMessageType create_RAW() {
      return new MessageType_RAW();
    }
    public static _IMessageType create_DIGEST() {
      return new MessageType_DIGEST();
    }
    public bool is_RAW { get { return this is MessageType_RAW; } }
    public bool is_DIGEST { get { return this is MessageType_DIGEST; } }
    public static System.Collections.Generic.IEnumerable<_IMessageType> AllSingletonConstructors {
      get {
        yield return MessageType.create_RAW();
        yield return MessageType.create_DIGEST();
      }
    }
    public abstract _IMessageType DowncastClone();
  }
  public class MessageType_RAW : MessageType {
    public MessageType_RAW() {
    }
    public override _IMessageType DowncastClone() {
      if (this is _IMessageType dt) { return dt; }
      return new MessageType_RAW();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.MessageType_RAW;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.MessageType.RAW";
      return s;
    }
  }
  public class MessageType_DIGEST : MessageType {
    public MessageType_DIGEST() {
    }
    public override _IMessageType DowncastClone() {
      if (this is _IMessageType dt) { return dt; }
      return new MessageType_DIGEST();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.MessageType_DIGEST;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.MessageType.DIGEST";
      return s;
    }
  }

  public interface _IMultiRegionConfiguration {
    bool is_MultiRegionConfiguration { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType> dtor_MultiRegionKeyType { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> dtor_PrimaryKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>> dtor_ReplicaKeys { get; }
    _IMultiRegionConfiguration DowncastClone();
  }
  public class MultiRegionConfiguration : _IMultiRegionConfiguration {
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType> _MultiRegionKeyType;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> _PrimaryKey;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>> _ReplicaKeys;
    public MultiRegionConfiguration(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType> MultiRegionKeyType, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> PrimaryKey, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>> ReplicaKeys) {
      this._MultiRegionKeyType = MultiRegionKeyType;
      this._PrimaryKey = PrimaryKey;
      this._ReplicaKeys = ReplicaKeys;
    }
    public _IMultiRegionConfiguration DowncastClone() {
      if (this is _IMultiRegionConfiguration dt) { return dt; }
      return new MultiRegionConfiguration(_MultiRegionKeyType, _PrimaryKey, _ReplicaKeys);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionConfiguration;
      return oth != null && object.Equals(this._MultiRegionKeyType, oth._MultiRegionKeyType) && object.Equals(this._PrimaryKey, oth._PrimaryKey) && object.Equals(this._ReplicaKeys, oth._ReplicaKeys);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._MultiRegionKeyType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PrimaryKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ReplicaKeys));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.MultiRegionConfiguration.MultiRegionConfiguration";
      s += "(";
      s += Dafny.Helpers.ToString(this._MultiRegionKeyType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PrimaryKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ReplicaKeys);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration theDefault = create(Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>.Default(), Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration>(software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionConfiguration.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionConfiguration> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMultiRegionConfiguration create(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType> MultiRegionKeyType, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> PrimaryKey, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>> ReplicaKeys) {
      return new MultiRegionConfiguration(MultiRegionKeyType, PrimaryKey, ReplicaKeys);
    }
    public static _IMultiRegionConfiguration create_MultiRegionConfiguration(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType> MultiRegionKeyType, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> PrimaryKey, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>> ReplicaKeys) {
      return create(MultiRegionKeyType, PrimaryKey, ReplicaKeys);
    }
    public bool is_MultiRegionConfiguration { get { return true; } }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType> dtor_MultiRegionKeyType {
      get {
        return this._MultiRegionKeyType;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> dtor_PrimaryKey {
      get {
        return this._PrimaryKey;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>> dtor_ReplicaKeys {
      get {
        return this._ReplicaKeys;
      }
    }
  }

  public interface _IMultiRegionKey {
    bool is_MultiRegionKey { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Arn { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Region { get; }
    _IMultiRegionKey DowncastClone();
  }
  public class MultiRegionKey : _IMultiRegionKey {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Arn;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Region;
    public MultiRegionKey(Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn, Wrappers_Compile._IOption<Dafny.ISequence<char>> Region) {
      this._Arn = Arn;
      this._Region = Region;
    }
    public _IMultiRegionKey DowncastClone() {
      if (this is _IMultiRegionKey dt) { return dt; }
      return new MultiRegionKey(_Arn, _Region);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKey;
      return oth != null && object.Equals(this._Arn, oth._Arn) && object.Equals(this._Region, oth._Region);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Arn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Region));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.MultiRegionKey.MultiRegionKey";
      s += "(";
      s += Dafny.Helpers.ToString(this._Arn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Region);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey>(software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKey.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKey> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMultiRegionKey create(Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn, Wrappers_Compile._IOption<Dafny.ISequence<char>> Region) {
      return new MultiRegionKey(Arn, Region);
    }
    public static _IMultiRegionKey create_MultiRegionKey(Wrappers_Compile._IOption<Dafny.ISequence<char>> Arn, Wrappers_Compile._IOption<Dafny.ISequence<char>> Region) {
      return create(Arn, Region);
    }
    public bool is_MultiRegionKey { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Arn {
      get {
        return this._Arn;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Region {
      get {
        return this._Region;
      }
    }
  }

  public interface _IMultiRegionKeyType {
    bool is_PRIMARY { get; }
    bool is_REPLICA { get; }
    _IMultiRegionKeyType DowncastClone();
  }
  public abstract class MultiRegionKeyType : _IMultiRegionKeyType {
    public MultiRegionKeyType() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType theDefault = create_PRIMARY();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType>(software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKeyType.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IMultiRegionKeyType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMultiRegionKeyType create_PRIMARY() {
      return new MultiRegionKeyType_PRIMARY();
    }
    public static _IMultiRegionKeyType create_REPLICA() {
      return new MultiRegionKeyType_REPLICA();
    }
    public bool is_PRIMARY { get { return this is MultiRegionKeyType_PRIMARY; } }
    public bool is_REPLICA { get { return this is MultiRegionKeyType_REPLICA; } }
    public static System.Collections.Generic.IEnumerable<_IMultiRegionKeyType> AllSingletonConstructors {
      get {
        yield return MultiRegionKeyType.create_PRIMARY();
        yield return MultiRegionKeyType.create_REPLICA();
      }
    }
    public abstract _IMultiRegionKeyType DowncastClone();
  }
  public class MultiRegionKeyType_PRIMARY : MultiRegionKeyType {
    public MultiRegionKeyType_PRIMARY() {
    }
    public override _IMultiRegionKeyType DowncastClone() {
      if (this is _IMultiRegionKeyType dt) { return dt; }
      return new MultiRegionKeyType_PRIMARY();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKeyType_PRIMARY;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.MultiRegionKeyType.PRIMARY";
      return s;
    }
  }
  public class MultiRegionKeyType_REPLICA : MultiRegionKeyType {
    public MultiRegionKeyType_REPLICA() {
    }
    public override _IMultiRegionKeyType DowncastClone() {
      if (this is _IMultiRegionKeyType dt) { return dt; }
      return new MultiRegionKeyType_REPLICA();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.MultiRegionKeyType_REPLICA;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.MultiRegionKeyType.REPLICA";
      return s;
    }
  }

  public partial class NumberOfBytesType {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IOriginType {
    bool is_AWS__KMS { get; }
    bool is_EXTERNAL { get; }
    bool is_AWS__CLOUDHSM { get; }
    _IOriginType DowncastClone();
  }
  public abstract class OriginType : _IOriginType {
    public OriginType() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IOriginType theDefault = create_AWS__KMS();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IOriginType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType>(software.amazon.cryptography.services.kms.internaldafny.types.OriginType.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IOriginType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOriginType create_AWS__KMS() {
      return new OriginType_AWS__KMS();
    }
    public static _IOriginType create_EXTERNAL() {
      return new OriginType_EXTERNAL();
    }
    public static _IOriginType create_AWS__CLOUDHSM() {
      return new OriginType_AWS__CLOUDHSM();
    }
    public bool is_AWS__KMS { get { return this is OriginType_AWS__KMS; } }
    public bool is_EXTERNAL { get { return this is OriginType_EXTERNAL; } }
    public bool is_AWS__CLOUDHSM { get { return this is OriginType_AWS__CLOUDHSM; } }
    public static System.Collections.Generic.IEnumerable<_IOriginType> AllSingletonConstructors {
      get {
        yield return OriginType.create_AWS__KMS();
        yield return OriginType.create_EXTERNAL();
        yield return OriginType.create_AWS__CLOUDHSM();
      }
    }
    public abstract _IOriginType DowncastClone();
  }
  public class OriginType_AWS__KMS : OriginType {
    public OriginType_AWS__KMS() {
    }
    public override _IOriginType DowncastClone() {
      if (this is _IOriginType dt) { return dt; }
      return new OriginType_AWS__KMS();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.OriginType_AWS__KMS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.OriginType.AWS_KMS";
      return s;
    }
  }
  public class OriginType_EXTERNAL : OriginType {
    public OriginType_EXTERNAL() {
    }
    public override _IOriginType DowncastClone() {
      if (this is _IOriginType dt) { return dt; }
      return new OriginType_EXTERNAL();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.OriginType_EXTERNAL;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.OriginType.EXTERNAL";
      return s;
    }
  }
  public class OriginType_AWS__CLOUDHSM : OriginType {
    public OriginType_AWS__CLOUDHSM() {
    }
    public override _IOriginType DowncastClone() {
      if (this is _IOriginType dt) { return dt; }
      return new OriginType_AWS__CLOUDHSM();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.OriginType_AWS__CLOUDHSM;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.OriginType.AWS_CLOUDHSM";
      return s;
    }
  }

  public partial class PendingWindowInDaysType {
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class PlaintextType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Dafny.Sequence<byte>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class PolicyNameType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class PolicyType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class PrincipalIdType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class PublicKeyType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Dafny.Sequence<byte>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IPutKeyPolicyRequest {
    bool is_PutKeyPolicyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_PolicyName { get; }
    Dafny.ISequence<char> dtor_Policy { get; }
    Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck { get; }
    _IPutKeyPolicyRequest DowncastClone();
  }
  public class PutKeyPolicyRequest : _IPutKeyPolicyRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<char> _PolicyName;
    public readonly Dafny.ISequence<char> _Policy;
    public readonly Wrappers_Compile._IOption<bool> _BypassPolicyLockoutSafetyCheck;
    public PutKeyPolicyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PolicyName, Dafny.ISequence<char> Policy, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck) {
      this._KeyId = KeyId;
      this._PolicyName = PolicyName;
      this._Policy = Policy;
      this._BypassPolicyLockoutSafetyCheck = BypassPolicyLockoutSafetyCheck;
    }
    public _IPutKeyPolicyRequest DowncastClone() {
      if (this is _IPutKeyPolicyRequest dt) { return dt; }
      return new PutKeyPolicyRequest(_KeyId, _PolicyName, _Policy, _BypassPolicyLockoutSafetyCheck);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.PutKeyPolicyRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._PolicyName, oth._PolicyName) && object.Equals(this._Policy, oth._Policy) && object.Equals(this._BypassPolicyLockoutSafetyCheck, oth._BypassPolicyLockoutSafetyCheck);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PolicyName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Policy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._BypassPolicyLockoutSafetyCheck));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.PutKeyPolicyRequest.PutKeyPolicyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PolicyName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Policy);
      s += ", ";
      s += Dafny.Helpers.ToString(this._BypassPolicyLockoutSafetyCheck);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IPutKeyPolicyRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<bool>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IPutKeyPolicyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IPutKeyPolicyRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IPutKeyPolicyRequest>(software.amazon.cryptography.services.kms.internaldafny.types.PutKeyPolicyRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IPutKeyPolicyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPutKeyPolicyRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PolicyName, Dafny.ISequence<char> Policy, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck) {
      return new PutKeyPolicyRequest(KeyId, PolicyName, Policy, BypassPolicyLockoutSafetyCheck);
    }
    public static _IPutKeyPolicyRequest create_PutKeyPolicyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PolicyName, Dafny.ISequence<char> Policy, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck) {
      return create(KeyId, PolicyName, Policy, BypassPolicyLockoutSafetyCheck);
    }
    public bool is_PutKeyPolicyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_PolicyName {
      get {
        return this._PolicyName;
      }
    }
    public Dafny.ISequence<char> dtor_Policy {
      get {
        return this._Policy;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck {
      get {
        return this._BypassPolicyLockoutSafetyCheck;
      }
    }
  }

  public interface _IReEncryptRequest {
    bool is_ReEncryptRequest { get; }
    Dafny.ISequence<byte> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_SourceEncryptionContext { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_SourceKeyId { get; }
    Dafny.ISequence<char> dtor_DestinationKeyId { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_DestinationEncryptionContext { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_SourceEncryptionAlgorithm { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_DestinationEncryptionAlgorithm { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IReEncryptRequest DowncastClone();
  }
  public class ReEncryptRequest : _IReEncryptRequest {
    public readonly Dafny.ISequence<byte> _CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _SourceEncryptionContext;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _SourceKeyId;
    public readonly Dafny.ISequence<char> _DestinationKeyId;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _DestinationEncryptionContext;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _SourceEncryptionAlgorithm;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _DestinationEncryptionAlgorithm;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public ReEncryptRequest(Dafny.ISequence<byte> CiphertextBlob, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> SourceEncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId, Dafny.ISequence<char> DestinationKeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> DestinationEncryptionContext, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this._CiphertextBlob = CiphertextBlob;
      this._SourceEncryptionContext = SourceEncryptionContext;
      this._SourceKeyId = SourceKeyId;
      this._DestinationKeyId = DestinationKeyId;
      this._DestinationEncryptionContext = DestinationEncryptionContext;
      this._SourceEncryptionAlgorithm = SourceEncryptionAlgorithm;
      this._DestinationEncryptionAlgorithm = DestinationEncryptionAlgorithm;
      this._GrantTokens = GrantTokens;
    }
    public _IReEncryptRequest DowncastClone() {
      if (this is _IReEncryptRequest dt) { return dt; }
      return new ReEncryptRequest(_CiphertextBlob, _SourceEncryptionContext, _SourceKeyId, _DestinationKeyId, _DestinationEncryptionContext, _SourceEncryptionAlgorithm, _DestinationEncryptionAlgorithm, _GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptRequest;
      return oth != null && object.Equals(this._CiphertextBlob, oth._CiphertextBlob) && object.Equals(this._SourceEncryptionContext, oth._SourceEncryptionContext) && object.Equals(this._SourceKeyId, oth._SourceKeyId) && object.Equals(this._DestinationKeyId, oth._DestinationKeyId) && object.Equals(this._DestinationEncryptionContext, oth._DestinationEncryptionContext) && object.Equals(this._SourceEncryptionAlgorithm, oth._SourceEncryptionAlgorithm) && object.Equals(this._DestinationEncryptionAlgorithm, oth._DestinationEncryptionAlgorithm) && object.Equals(this._GrantTokens, oth._GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SourceEncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SourceKeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._DestinationKeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._DestinationEncryptionContext));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SourceEncryptionAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._DestinationEncryptionAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ReEncryptRequest.ReEncryptRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SourceEncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SourceKeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._DestinationKeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._DestinationEncryptionContext);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SourceEncryptionAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._DestinationEncryptionAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptRequest theDefault = create(Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptRequest>(software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IReEncryptRequest create(Dafny.ISequence<byte> CiphertextBlob, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> SourceEncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId, Dafny.ISequence<char> DestinationKeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> DestinationEncryptionContext, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new ReEncryptRequest(CiphertextBlob, SourceEncryptionContext, SourceKeyId, DestinationKeyId, DestinationEncryptionContext, SourceEncryptionAlgorithm, DestinationEncryptionAlgorithm, GrantTokens);
    }
    public static _IReEncryptRequest create_ReEncryptRequest(Dafny.ISequence<byte> CiphertextBlob, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> SourceEncryptionContext, Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId, Dafny.ISequence<char> DestinationKeyId, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> DestinationEncryptionContext, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return create(CiphertextBlob, SourceEncryptionContext, SourceKeyId, DestinationKeyId, DestinationEncryptionContext, SourceEncryptionAlgorithm, DestinationEncryptionAlgorithm, GrantTokens);
    }
    public bool is_ReEncryptRequest { get { return true; } }
    public Dafny.ISequence<byte> dtor_CiphertextBlob {
      get {
        return this._CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_SourceEncryptionContext {
      get {
        return this._SourceEncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_SourceKeyId {
      get {
        return this._SourceKeyId;
      }
    }
    public Dafny.ISequence<char> dtor_DestinationKeyId {
      get {
        return this._DestinationKeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_DestinationEncryptionContext {
      get {
        return this._DestinationEncryptionContext;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_SourceEncryptionAlgorithm {
      get {
        return this._SourceEncryptionAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_DestinationEncryptionAlgorithm {
      get {
        return this._DestinationEncryptionAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
  }

  public interface _IReEncryptResponse {
    bool is_ReEncryptResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_SourceKeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_SourceEncryptionAlgorithm { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_DestinationEncryptionAlgorithm { get; }
    _IReEncryptResponse DowncastClone();
  }
  public class ReEncryptResponse : _IReEncryptResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _CiphertextBlob;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _SourceKeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _SourceEncryptionAlgorithm;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _DestinationEncryptionAlgorithm;
    public ReEncryptResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm) {
      this._CiphertextBlob = CiphertextBlob;
      this._SourceKeyId = SourceKeyId;
      this._KeyId = KeyId;
      this._SourceEncryptionAlgorithm = SourceEncryptionAlgorithm;
      this._DestinationEncryptionAlgorithm = DestinationEncryptionAlgorithm;
    }
    public _IReEncryptResponse DowncastClone() {
      if (this is _IReEncryptResponse dt) { return dt; }
      return new ReEncryptResponse(_CiphertextBlob, _SourceKeyId, _KeyId, _SourceEncryptionAlgorithm, _DestinationEncryptionAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptResponse;
      return oth != null && object.Equals(this._CiphertextBlob, oth._CiphertextBlob) && object.Equals(this._SourceKeyId, oth._SourceKeyId) && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._SourceEncryptionAlgorithm, oth._SourceEncryptionAlgorithm) && object.Equals(this._DestinationEncryptionAlgorithm, oth._DestinationEncryptionAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CiphertextBlob));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SourceKeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SourceEncryptionAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._DestinationEncryptionAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ReEncryptResponse.ReEncryptResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._CiphertextBlob);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SourceKeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SourceEncryptionAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._DestinationEncryptionAlgorithm);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptResponse>(software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IReEncryptResponse create(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm) {
      return new ReEncryptResponse(CiphertextBlob, SourceKeyId, KeyId, SourceEncryptionAlgorithm, DestinationEncryptionAlgorithm);
    }
    public static _IReEncryptResponse create_ReEncryptResponse(Wrappers_Compile._IOption<Dafny.ISequence<byte>> CiphertextBlob, Wrappers_Compile._IOption<Dafny.ISequence<char>> SourceKeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> SourceEncryptionAlgorithm, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> DestinationEncryptionAlgorithm) {
      return create(CiphertextBlob, SourceKeyId, KeyId, SourceEncryptionAlgorithm, DestinationEncryptionAlgorithm);
    }
    public bool is_ReEncryptResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_CiphertextBlob {
      get {
        return this._CiphertextBlob;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_SourceKeyId {
      get {
        return this._SourceKeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_SourceEncryptionAlgorithm {
      get {
        return this._SourceEncryptionAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> dtor_DestinationEncryptionAlgorithm {
      get {
        return this._DestinationEncryptionAlgorithm;
      }
    }
  }

  public partial class RegionType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IReplicateKeyRequest {
    bool is_ReplicateKeyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_ReplicaRegion { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy { get; }
    Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> dtor_Tags { get; }
    _IReplicateKeyRequest DowncastClone();
  }
  public class ReplicateKeyRequest : _IReplicateKeyRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<char> _ReplicaRegion;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Policy;
    public readonly Wrappers_Compile._IOption<bool> _BypassPolicyLockoutSafetyCheck;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _Description;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> _Tags;
    public ReplicateKeyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> ReplicaRegion, Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> Tags) {
      this._KeyId = KeyId;
      this._ReplicaRegion = ReplicaRegion;
      this._Policy = Policy;
      this._BypassPolicyLockoutSafetyCheck = BypassPolicyLockoutSafetyCheck;
      this._Description = Description;
      this._Tags = Tags;
    }
    public _IReplicateKeyRequest DowncastClone() {
      if (this is _IReplicateKeyRequest dt) { return dt; }
      return new ReplicateKeyRequest(_KeyId, _ReplicaRegion, _Policy, _BypassPolicyLockoutSafetyCheck, _Description, _Tags);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._ReplicaRegion, oth._ReplicaRegion) && object.Equals(this._Policy, oth._Policy) && object.Equals(this._BypassPolicyLockoutSafetyCheck, oth._BypassPolicyLockoutSafetyCheck) && object.Equals(this._Description, oth._Description) && object.Equals(this._Tags, oth._Tags);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ReplicaRegion));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Policy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._BypassPolicyLockoutSafetyCheck));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Description));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Tags));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ReplicateKeyRequest.ReplicateKeyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ReplicaRegion);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Policy);
      s += ", ";
      s += Dafny.Helpers.ToString(this._BypassPolicyLockoutSafetyCheck);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Description);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Tags);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyRequest>(software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IReplicateKeyRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> ReplicaRegion, Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> Tags) {
      return new ReplicateKeyRequest(KeyId, ReplicaRegion, Policy, BypassPolicyLockoutSafetyCheck, Description, Tags);
    }
    public static _IReplicateKeyRequest create_ReplicateKeyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> ReplicaRegion, Wrappers_Compile._IOption<Dafny.ISequence<char>> Policy, Wrappers_Compile._IOption<bool> BypassPolicyLockoutSafetyCheck, Wrappers_Compile._IOption<Dafny.ISequence<char>> Description, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> Tags) {
      return create(KeyId, ReplicaRegion, Policy, BypassPolicyLockoutSafetyCheck, Description, Tags);
    }
    public bool is_ReplicateKeyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_ReplicaRegion {
      get {
        return this._ReplicaRegion;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Policy {
      get {
        return this._Policy;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_BypassPolicyLockoutSafetyCheck {
      get {
        return this._BypassPolicyLockoutSafetyCheck;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_Description {
      get {
        return this._Description;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> dtor_Tags {
      get {
        return this._Tags;
      }
    }
  }

  public interface _IReplicateKeyResponse {
    bool is_ReplicateKeyResponse { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> dtor_ReplicaKeyMetadata { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ReplicaPolicy { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> dtor_ReplicaTags { get; }
    _IReplicateKeyResponse DowncastClone();
  }
  public class ReplicateKeyResponse : _IReplicateKeyResponse {
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> _ReplicaKeyMetadata;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _ReplicaPolicy;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> _ReplicaTags;
    public ReplicateKeyResponse(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> ReplicaKeyMetadata, Wrappers_Compile._IOption<Dafny.ISequence<char>> ReplicaPolicy, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> ReplicaTags) {
      this._ReplicaKeyMetadata = ReplicaKeyMetadata;
      this._ReplicaPolicy = ReplicaPolicy;
      this._ReplicaTags = ReplicaTags;
    }
    public _IReplicateKeyResponse DowncastClone() {
      if (this is _IReplicateKeyResponse dt) { return dt; }
      return new ReplicateKeyResponse(_ReplicaKeyMetadata, _ReplicaPolicy, _ReplicaTags);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyResponse;
      return oth != null && object.Equals(this._ReplicaKeyMetadata, oth._ReplicaKeyMetadata) && object.Equals(this._ReplicaPolicy, oth._ReplicaPolicy) && object.Equals(this._ReplicaTags, oth._ReplicaTags);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ReplicaKeyMetadata));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ReplicaPolicy));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ReplicaTags));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ReplicateKeyResponse.ReplicateKeyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._ReplicaKeyMetadata);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ReplicaPolicy);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ReplicaTags);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyResponse theDefault = create(Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyResponse>(software.amazon.cryptography.services.kms.internaldafny.types.ReplicateKeyResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IReplicateKeyResponse create(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> ReplicaKeyMetadata, Wrappers_Compile._IOption<Dafny.ISequence<char>> ReplicaPolicy, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> ReplicaTags) {
      return new ReplicateKeyResponse(ReplicaKeyMetadata, ReplicaPolicy, ReplicaTags);
    }
    public static _IReplicateKeyResponse create_ReplicateKeyResponse(Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> ReplicaKeyMetadata, Wrappers_Compile._IOption<Dafny.ISequence<char>> ReplicaPolicy, Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> ReplicaTags) {
      return create(ReplicaKeyMetadata, ReplicaPolicy, ReplicaTags);
    }
    public bool is_ReplicateKeyResponse { get { return true; } }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyMetadata> dtor_ReplicaKeyMetadata {
      get {
        return this._ReplicaKeyMetadata;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_ReplicaPolicy {
      get {
        return this._ReplicaPolicy;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>> dtor_ReplicaTags {
      get {
        return this._ReplicaTags;
      }
    }
  }

  public interface _IRetireGrantRequest {
    bool is_RetireGrantRequest { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantToken { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId { get; }
    _IRetireGrantRequest DowncastClone();
  }
  public class RetireGrantRequest : _IRetireGrantRequest {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _GrantToken;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _GrantId;
    public RetireGrantRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId) {
      this._GrantToken = GrantToken;
      this._KeyId = KeyId;
      this._GrantId = GrantId;
    }
    public _IRetireGrantRequest DowncastClone() {
      if (this is _IRetireGrantRequest dt) { return dt; }
      return new RetireGrantRequest(_GrantToken, _KeyId, _GrantId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.RetireGrantRequest;
      return oth != null && object.Equals(this._GrantToken, oth._GrantToken) && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._GrantId, oth._GrantId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantToken));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.RetireGrantRequest.RetireGrantRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._GrantToken);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IRetireGrantRequest theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IRetireGrantRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IRetireGrantRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IRetireGrantRequest>(software.amazon.cryptography.services.kms.internaldafny.types.RetireGrantRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IRetireGrantRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRetireGrantRequest create(Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId) {
      return new RetireGrantRequest(GrantToken, KeyId, GrantId);
    }
    public static _IRetireGrantRequest create_RetireGrantRequest(Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantToken, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> GrantId) {
      return create(GrantToken, KeyId, GrantId);
    }
    public bool is_RetireGrantRequest { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantToken {
      get {
        return this._GrantToken;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_GrantId {
      get {
        return this._GrantId;
      }
    }
  }

  public interface _IRevokeGrantRequest {
    bool is_RevokeGrantRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_GrantId { get; }
    _IRevokeGrantRequest DowncastClone();
  }
  public class RevokeGrantRequest : _IRevokeGrantRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<char> _GrantId;
    public RevokeGrantRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> GrantId) {
      this._KeyId = KeyId;
      this._GrantId = GrantId;
    }
    public _IRevokeGrantRequest DowncastClone() {
      if (this is _IRevokeGrantRequest dt) { return dt; }
      return new RevokeGrantRequest(_KeyId, _GrantId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.RevokeGrantRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._GrantId, oth._GrantId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.RevokeGrantRequest.RevokeGrantRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IRevokeGrantRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IRevokeGrantRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IRevokeGrantRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IRevokeGrantRequest>(software.amazon.cryptography.services.kms.internaldafny.types.RevokeGrantRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IRevokeGrantRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRevokeGrantRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> GrantId) {
      return new RevokeGrantRequest(KeyId, GrantId);
    }
    public static _IRevokeGrantRequest create_RevokeGrantRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> GrantId) {
      return create(KeyId, GrantId);
    }
    public bool is_RevokeGrantRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_GrantId {
      get {
        return this._GrantId;
      }
    }
  }

  public interface _IScheduleKeyDeletionRequest {
    bool is_ScheduleKeyDeletionRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Wrappers_Compile._IOption<int> dtor_PendingWindowInDays { get; }
    _IScheduleKeyDeletionRequest DowncastClone();
  }
  public class ScheduleKeyDeletionRequest : _IScheduleKeyDeletionRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Wrappers_Compile._IOption<int> _PendingWindowInDays;
    public ScheduleKeyDeletionRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> PendingWindowInDays) {
      this._KeyId = KeyId;
      this._PendingWindowInDays = PendingWindowInDays;
    }
    public _IScheduleKeyDeletionRequest DowncastClone() {
      if (this is _IScheduleKeyDeletionRequest dt) { return dt; }
      return new ScheduleKeyDeletionRequest(_KeyId, _PendingWindowInDays);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._PendingWindowInDays, oth._PendingWindowInDays);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PendingWindowInDays));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ScheduleKeyDeletionRequest.ScheduleKeyDeletionRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PendingWindowInDays);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<int>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionRequest>(software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IScheduleKeyDeletionRequest create(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> PendingWindowInDays) {
      return new ScheduleKeyDeletionRequest(KeyId, PendingWindowInDays);
    }
    public static _IScheduleKeyDeletionRequest create_ScheduleKeyDeletionRequest(Dafny.ISequence<char> KeyId, Wrappers_Compile._IOption<int> PendingWindowInDays) {
      return create(KeyId, PendingWindowInDays);
    }
    public bool is_ScheduleKeyDeletionRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_PendingWindowInDays {
      get {
        return this._PendingWindowInDays;
      }
    }
  }

  public interface _IScheduleKeyDeletionResponse {
    bool is_ScheduleKeyDeletionResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_DeletionDate { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> dtor_KeyState { get; }
    Wrappers_Compile._IOption<int> dtor_PendingWindowInDays { get; }
    _IScheduleKeyDeletionResponse DowncastClone();
  }
  public class ScheduleKeyDeletionResponse : _IScheduleKeyDeletionResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _DeletionDate;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> _KeyState;
    public readonly Wrappers_Compile._IOption<int> _PendingWindowInDays;
    public ScheduleKeyDeletionResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> KeyState, Wrappers_Compile._IOption<int> PendingWindowInDays) {
      this._KeyId = KeyId;
      this._DeletionDate = DeletionDate;
      this._KeyState = KeyState;
      this._PendingWindowInDays = PendingWindowInDays;
    }
    public _IScheduleKeyDeletionResponse DowncastClone() {
      if (this is _IScheduleKeyDeletionResponse dt) { return dt; }
      return new ScheduleKeyDeletionResponse(_KeyId, _DeletionDate, _KeyState, _PendingWindowInDays);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionResponse;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._DeletionDate, oth._DeletionDate) && object.Equals(this._KeyState, oth._KeyState) && object.Equals(this._PendingWindowInDays, oth._PendingWindowInDays);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._DeletionDate));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyState));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PendingWindowInDays));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.ScheduleKeyDeletionResponse.ScheduleKeyDeletionResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._DeletionDate);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyState);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PendingWindowInDays);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState>.Default(), Wrappers_Compile.Option<int>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionResponse>(software.amazon.cryptography.services.kms.internaldafny.types.ScheduleKeyDeletionResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IScheduleKeyDeletionResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> KeyState, Wrappers_Compile._IOption<int> PendingWindowInDays) {
      return new ScheduleKeyDeletionResponse(KeyId, DeletionDate, KeyState, PendingWindowInDays);
    }
    public static _IScheduleKeyDeletionResponse create_ScheduleKeyDeletionResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<char>> DeletionDate, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> KeyState, Wrappers_Compile._IOption<int> PendingWindowInDays) {
      return create(KeyId, DeletionDate, KeyState, PendingWindowInDays);
    }
    public bool is_ScheduleKeyDeletionResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_DeletionDate {
      get {
        return this._DeletionDate;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IKeyState> dtor_KeyState {
      get {
        return this._KeyState;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_PendingWindowInDays {
      get {
        return this._PendingWindowInDays;
      }
    }
  }

  public interface _ISigningAlgorithmSpec {
    bool is_RSASSA__PSS__SHA__256 { get; }
    bool is_RSASSA__PSS__SHA__384 { get; }
    bool is_RSASSA__PSS__SHA__512 { get; }
    bool is_RSASSA__PKCS1__V1__5__SHA__256 { get; }
    bool is_RSASSA__PKCS1__V1__5__SHA__384 { get; }
    bool is_RSASSA__PKCS1__V1__5__SHA__512 { get; }
    bool is_ECDSA__SHA__256 { get; }
    bool is_ECDSA__SHA__384 { get; }
    bool is_ECDSA__SHA__512 { get; }
    _ISigningAlgorithmSpec DowncastClone();
  }
  public abstract class SigningAlgorithmSpec : _ISigningAlgorithmSpec {
    public SigningAlgorithmSpec() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec theDefault = create_RSASSA__PSS__SHA__256();
    public static software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>(software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PSS__SHA__256() {
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__256();
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PSS__SHA__384() {
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__384();
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PSS__SHA__512() {
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__512();
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PKCS1__V1__5__SHA__256() {
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256();
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PKCS1__V1__5__SHA__384() {
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384();
    }
    public static _ISigningAlgorithmSpec create_RSASSA__PKCS1__V1__5__SHA__512() {
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512();
    }
    public static _ISigningAlgorithmSpec create_ECDSA__SHA__256() {
      return new SigningAlgorithmSpec_ECDSA__SHA__256();
    }
    public static _ISigningAlgorithmSpec create_ECDSA__SHA__384() {
      return new SigningAlgorithmSpec_ECDSA__SHA__384();
    }
    public static _ISigningAlgorithmSpec create_ECDSA__SHA__512() {
      return new SigningAlgorithmSpec_ECDSA__SHA__512();
    }
    public bool is_RSASSA__PSS__SHA__256 { get { return this is SigningAlgorithmSpec_RSASSA__PSS__SHA__256; } }
    public bool is_RSASSA__PSS__SHA__384 { get { return this is SigningAlgorithmSpec_RSASSA__PSS__SHA__384; } }
    public bool is_RSASSA__PSS__SHA__512 { get { return this is SigningAlgorithmSpec_RSASSA__PSS__SHA__512; } }
    public bool is_RSASSA__PKCS1__V1__5__SHA__256 { get { return this is SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256; } }
    public bool is_RSASSA__PKCS1__V1__5__SHA__384 { get { return this is SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384; } }
    public bool is_RSASSA__PKCS1__V1__5__SHA__512 { get { return this is SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512; } }
    public bool is_ECDSA__SHA__256 { get { return this is SigningAlgorithmSpec_ECDSA__SHA__256; } }
    public bool is_ECDSA__SHA__384 { get { return this is SigningAlgorithmSpec_ECDSA__SHA__384; } }
    public bool is_ECDSA__SHA__512 { get { return this is SigningAlgorithmSpec_ECDSA__SHA__512; } }
    public static System.Collections.Generic.IEnumerable<_ISigningAlgorithmSpec> AllSingletonConstructors {
      get {
        yield return SigningAlgorithmSpec.create_RSASSA__PSS__SHA__256();
        yield return SigningAlgorithmSpec.create_RSASSA__PSS__SHA__384();
        yield return SigningAlgorithmSpec.create_RSASSA__PSS__SHA__512();
        yield return SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__256();
        yield return SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__384();
        yield return SigningAlgorithmSpec.create_RSASSA__PKCS1__V1__5__SHA__512();
        yield return SigningAlgorithmSpec.create_ECDSA__SHA__256();
        yield return SigningAlgorithmSpec.create_ECDSA__SHA__384();
        yield return SigningAlgorithmSpec.create_ECDSA__SHA__512();
      }
    }
    public abstract _ISigningAlgorithmSpec DowncastClone();
  }
  public class SigningAlgorithmSpec_RSASSA__PSS__SHA__256 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PSS__SHA__256() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec_RSASSA__PSS__SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.SigningAlgorithmSpec.RSASSA_PSS_SHA_256";
      return s;
    }
  }
  public class SigningAlgorithmSpec_RSASSA__PSS__SHA__384 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PSS__SHA__384() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__384();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec_RSASSA__PSS__SHA__384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.SigningAlgorithmSpec.RSASSA_PSS_SHA_384";
      return s;
    }
  }
  public class SigningAlgorithmSpec_RSASSA__PSS__SHA__512 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PSS__SHA__512() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PSS__SHA__512();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec_RSASSA__PSS__SHA__512;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.SigningAlgorithmSpec.RSASSA_PSS_SHA_512";
      return s;
    }
  }
  public class SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_256";
      return s;
    }
  }
  public class SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_384";
      return s;
    }
  }
  public class SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_512";
      return s;
    }
  }
  public class SigningAlgorithmSpec_ECDSA__SHA__256 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_ECDSA__SHA__256() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_ECDSA__SHA__256();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec_ECDSA__SHA__256;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.SigningAlgorithmSpec.ECDSA_SHA_256";
      return s;
    }
  }
  public class SigningAlgorithmSpec_ECDSA__SHA__384 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_ECDSA__SHA__384() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_ECDSA__SHA__384();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec_ECDSA__SHA__384;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.SigningAlgorithmSpec.ECDSA_SHA_384";
      return s;
    }
  }
  public class SigningAlgorithmSpec_ECDSA__SHA__512 : SigningAlgorithmSpec {
    public SigningAlgorithmSpec_ECDSA__SHA__512() {
    }
    public override _ISigningAlgorithmSpec DowncastClone() {
      if (this is _ISigningAlgorithmSpec dt) { return dt; }
      return new SigningAlgorithmSpec_ECDSA__SHA__512();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec_ECDSA__SHA__512;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.SigningAlgorithmSpec.ECDSA_SHA_512";
      return s;
    }
  }

  public interface _ISignRequest {
    bool is_SignRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<byte> dtor_Message { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> dtor_MessageType { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec dtor_SigningAlgorithm { get; }
    _ISignRequest DowncastClone();
  }
  public class SignRequest : _ISignRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<byte> _Message;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> _MessageType;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public readonly software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec _SigningAlgorithm;
    public SignRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Message, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> MessageType, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec SigningAlgorithm) {
      this._KeyId = KeyId;
      this._Message = Message;
      this._MessageType = MessageType;
      this._GrantTokens = GrantTokens;
      this._SigningAlgorithm = SigningAlgorithm;
    }
    public _ISignRequest DowncastClone() {
      if (this is _ISignRequest dt) { return dt; }
      return new SignRequest(_KeyId, _Message, _MessageType, _GrantTokens, _SigningAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.SignRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._Message, oth._Message) && object.Equals(this._MessageType, oth._MessageType) && object.Equals(this._GrantTokens, oth._GrantTokens) && object.Equals(this._SigningAlgorithm, oth._SigningAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Message));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._MessageType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SigningAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.SignRequest.SignRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Message);
      s += ", ";
      s += Dafny.Helpers.ToString(this._MessageType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SigningAlgorithm);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ISignRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._ISignRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ISignRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ISignRequest>(software.amazon.cryptography.services.kms.internaldafny.types.SignRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ISignRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISignRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Message, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> MessageType, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec SigningAlgorithm) {
      return new SignRequest(KeyId, Message, MessageType, GrantTokens, SigningAlgorithm);
    }
    public static _ISignRequest create_SignRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Message, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> MessageType, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens, software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec SigningAlgorithm) {
      return create(KeyId, Message, MessageType, GrantTokens, SigningAlgorithm);
    }
    public bool is_SignRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<byte> dtor_Message {
      get {
        return this._Message;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> dtor_MessageType {
      get {
        return this._MessageType;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
    public software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec dtor_SigningAlgorithm {
      get {
        return this._SigningAlgorithm;
      }
    }
  }

  public interface _ISignResponse {
    bool is_SignResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Signature { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> dtor_SigningAlgorithm { get; }
    _ISignResponse DowncastClone();
  }
  public class SignResponse : _ISignResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<byte>> _Signature;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> _SigningAlgorithm;
    public SignResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Signature, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> SigningAlgorithm) {
      this._KeyId = KeyId;
      this._Signature = Signature;
      this._SigningAlgorithm = SigningAlgorithm;
    }
    public _ISignResponse DowncastClone() {
      if (this is _ISignResponse dt) { return dt; }
      return new SignResponse(_KeyId, _Signature, _SigningAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.SignResponse;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._Signature, oth._Signature) && object.Equals(this._SigningAlgorithm, oth._SigningAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Signature));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SigningAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.SignResponse.SignResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Signature);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SigningAlgorithm);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ISignResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._ISignResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ISignResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ISignResponse>(software.amazon.cryptography.services.kms.internaldafny.types.SignResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ISignResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISignResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Signature, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> SigningAlgorithm) {
      return new SignResponse(KeyId, Signature, SigningAlgorithm);
    }
    public static _ISignResponse create_SignResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<Dafny.ISequence<byte>> Signature, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> SigningAlgorithm) {
      return create(KeyId, Signature, SigningAlgorithm);
    }
    public bool is_SignResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<byte>> dtor_Signature {
      get {
        return this._Signature;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> dtor_SigningAlgorithm {
      get {
        return this._SigningAlgorithm;
      }
    }
  }

  public interface _ITag {
    bool is_Tag { get; }
    Dafny.ISequence<char> dtor_TagKey { get; }
    Dafny.ISequence<char> dtor_TagValue { get; }
    _ITag DowncastClone();
  }
  public class Tag : _ITag {
    public readonly Dafny.ISequence<char> _TagKey;
    public readonly Dafny.ISequence<char> _TagValue;
    public Tag(Dafny.ISequence<char> TagKey, Dafny.ISequence<char> TagValue) {
      this._TagKey = TagKey;
      this._TagValue = TagValue;
    }
    public _ITag DowncastClone() {
      if (this is _ITag dt) { return dt; }
      return new Tag(_TagKey, _TagValue);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Tag;
      return oth != null && object.Equals(this._TagKey, oth._TagKey) && object.Equals(this._TagValue, oth._TagValue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._TagKey));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._TagValue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Tag.Tag";
      s += "(";
      s += Dafny.Helpers.ToString(this._TagKey);
      s += ", ";
      s += Dafny.Helpers.ToString(this._TagValue);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ITag theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._ITag Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ITag> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ITag>(software.amazon.cryptography.services.kms.internaldafny.types.Tag.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ITag> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITag create(Dafny.ISequence<char> TagKey, Dafny.ISequence<char> TagValue) {
      return new Tag(TagKey, TagValue);
    }
    public static _ITag create_Tag(Dafny.ISequence<char> TagKey, Dafny.ISequence<char> TagValue) {
      return create(TagKey, TagValue);
    }
    public bool is_Tag { get { return true; } }
    public Dafny.ISequence<char> dtor_TagKey {
      get {
        return this._TagKey;
      }
    }
    public Dafny.ISequence<char> dtor_TagValue {
      get {
        return this._TagValue;
      }
    }
  }

  public partial class TagKeyType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ITagResourceRequest {
    bool is_TagResourceRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag> dtor_Tags { get; }
    _ITagResourceRequest DowncastClone();
  }
  public class TagResourceRequest : _ITagResourceRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag> _Tags;
    public TagResourceRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag> Tags) {
      this._KeyId = KeyId;
      this._Tags = Tags;
    }
    public _ITagResourceRequest DowncastClone() {
      if (this is _ITagResourceRequest dt) { return dt; }
      return new TagResourceRequest(_KeyId, _Tags);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.TagResourceRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._Tags, oth._Tags);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Tags));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.TagResourceRequest.TagResourceRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Tags);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._ITagResourceRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._ITagResourceRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ITagResourceRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ITagResourceRequest>(software.amazon.cryptography.services.kms.internaldafny.types.TagResourceRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._ITagResourceRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITagResourceRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag> Tags) {
      return new TagResourceRequest(KeyId, Tags);
    }
    public static _ITagResourceRequest create_TagResourceRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag> Tags) {
      return create(KeyId, Tags);
    }
    public bool is_TagResourceRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<software.amazon.cryptography.services.kms.internaldafny.types._ITag> dtor_Tags {
      get {
        return this._Tags;
      }
    }
  }

  public partial class TagValueType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class IKMSClientCallHistory {
    public IKMSClientCallHistory() {
    }
  }

  public interface IKMSClient {
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> CancelKeyDeletion(software.amazon.cryptography.services.kms.internaldafny.types._ICancelKeyDeletionRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ConnectCustomKeyStore(software.amazon.cryptography.services.kms.internaldafny.types._IConnectCustomKeyStoreRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> CreateAlias(software.amazon.cryptography.services.kms.internaldafny.types._ICreateAliasRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> CreateCustomKeyStore(software.amazon.cryptography.services.kms.internaldafny.types._ICreateCustomKeyStoreRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> CreateGrant(software.amazon.cryptography.services.kms.internaldafny.types._ICreateGrantRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> CreateKey(software.amazon.cryptography.services.kms.internaldafny.types._ICreateKeyRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> Decrypt(software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> DeleteAlias(software.amazon.cryptography.services.kms.internaldafny.types._IDeleteAliasRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> DeleteCustomKeyStore(software.amazon.cryptography.services.kms.internaldafny.types._IDeleteCustomKeyStoreRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> DeleteImportedKeyMaterial(software.amazon.cryptography.services.kms.internaldafny.types._IDeleteImportedKeyMaterialRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> DescribeCustomKeyStores(software.amazon.cryptography.services.kms.internaldafny.types._IDescribeCustomKeyStoresRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> DescribeKey(software.amazon.cryptography.services.kms.internaldafny.types._IDescribeKeyRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> DisableKey(software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> DisableKeyRotation(software.amazon.cryptography.services.kms.internaldafny.types._IDisableKeyRotationRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> DisconnectCustomKeyStore(software.amazon.cryptography.services.kms.internaldafny.types._IDisconnectCustomKeyStoreRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> EnableKey(software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> EnableKeyRotation(software.amazon.cryptography.services.kms.internaldafny.types._IEnableKeyRotationRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> Encrypt(software.amazon.cryptography.services.kms.internaldafny.types._IEncryptRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GenerateDataKey(software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GenerateDataKeyPair(software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GenerateDataKeyPairWithoutPlaintext(software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyPairWithoutPlaintextRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GenerateDataKeyWithoutPlaintext(software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyWithoutPlaintextRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GenerateRandom(software.amazon.cryptography.services.kms.internaldafny.types._IGenerateRandomRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GetKeyPolicy(software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyPolicyRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GetKeyRotationStatus(software.amazon.cryptography.services.kms.internaldafny.types._IGetKeyRotationStatusRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GetParametersForImport(software.amazon.cryptography.services.kms.internaldafny.types._IGetParametersForImportRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> GetPublicKey(software.amazon.cryptography.services.kms.internaldafny.types._IGetPublicKeyRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ImportKeyMaterial(software.amazon.cryptography.services.kms.internaldafny.types._IImportKeyMaterialRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ListAliases(software.amazon.cryptography.services.kms.internaldafny.types._IListAliasesRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ListGrants(software.amazon.cryptography.services.kms.internaldafny.types._IListGrantsRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ListKeyPolicies(software.amazon.cryptography.services.kms.internaldafny.types._IListKeyPoliciesRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ListResourceTags(software.amazon.cryptography.services.kms.internaldafny.types._IListResourceTagsRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> PutKeyPolicy(software.amazon.cryptography.services.kms.internaldafny.types._IPutKeyPolicyRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ReEncrypt(software.amazon.cryptography.services.kms.internaldafny.types._IReEncryptRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ReplicateKey(software.amazon.cryptography.services.kms.internaldafny.types._IReplicateKeyRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> RetireGrant(software.amazon.cryptography.services.kms.internaldafny.types._IRetireGrantRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> RevokeGrant(software.amazon.cryptography.services.kms.internaldafny.types._IRevokeGrantRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> ScheduleKeyDeletion(software.amazon.cryptography.services.kms.internaldafny.types._IScheduleKeyDeletionRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._ISignResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> Sign(software.amazon.cryptography.services.kms.internaldafny.types._ISignRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> TagResource(software.amazon.cryptography.services.kms.internaldafny.types._ITagResourceRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> UntagResource(software.amazon.cryptography.services.kms.internaldafny.types._IUntagResourceRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> UpdateAlias(software.amazon.cryptography.services.kms.internaldafny.types._IUpdateAliasRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> UpdateCustomKeyStore(software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> UpdateKeyDescription(software.amazon.cryptography.services.kms.internaldafny.types._IUpdateKeyDescriptionRequest input);
    Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.services.kms.internaldafny.types._IError> UpdatePrimaryRegion(software.amazon.cryptography.services.kms.internaldafny.types._IUpdatePrimaryRegionRequest input);
    Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IVerifyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> Verify(software.amazon.cryptography.services.kms.internaldafny.types._IVerifyRequest input);
  }
  public class _Companion_IKMSClient {
  }

  public partial class TrustAnchorCertificateType {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IUntagResourceRequest {
    bool is_UntagResourceRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<Dafny.ISequence<char>> dtor_TagKeys { get; }
    _IUntagResourceRequest DowncastClone();
  }
  public class UntagResourceRequest : _IUntagResourceRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<Dafny.ISequence<char>> _TagKeys;
    public UntagResourceRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<Dafny.ISequence<char>> TagKeys) {
      this._KeyId = KeyId;
      this._TagKeys = TagKeys;
    }
    public _IUntagResourceRequest DowncastClone() {
      if (this is _IUntagResourceRequest dt) { return dt; }
      return new UntagResourceRequest(_KeyId, _TagKeys);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.UntagResourceRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._TagKeys, oth._TagKeys);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._TagKeys));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.UntagResourceRequest.UntagResourceRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._TagKeys);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IUntagResourceRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<Dafny.ISequence<char>>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IUntagResourceRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUntagResourceRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUntagResourceRequest>(software.amazon.cryptography.services.kms.internaldafny.types.UntagResourceRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUntagResourceRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUntagResourceRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<Dafny.ISequence<char>> TagKeys) {
      return new UntagResourceRequest(KeyId, TagKeys);
    }
    public static _IUntagResourceRequest create_UntagResourceRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<Dafny.ISequence<char>> TagKeys) {
      return create(KeyId, TagKeys);
    }
    public bool is_UntagResourceRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<char>> dtor_TagKeys {
      get {
        return this._TagKeys;
      }
    }
  }

  public interface _IUpdateAliasRequest {
    bool is_UpdateAliasRequest { get; }
    Dafny.ISequence<char> dtor_AliasName { get; }
    Dafny.ISequence<char> dtor_TargetKeyId { get; }
    _IUpdateAliasRequest DowncastClone();
  }
  public class UpdateAliasRequest : _IUpdateAliasRequest {
    public readonly Dafny.ISequence<char> _AliasName;
    public readonly Dafny.ISequence<char> _TargetKeyId;
    public UpdateAliasRequest(Dafny.ISequence<char> AliasName, Dafny.ISequence<char> TargetKeyId) {
      this._AliasName = AliasName;
      this._TargetKeyId = TargetKeyId;
    }
    public _IUpdateAliasRequest DowncastClone() {
      if (this is _IUpdateAliasRequest dt) { return dt; }
      return new UpdateAliasRequest(_AliasName, _TargetKeyId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.UpdateAliasRequest;
      return oth != null && object.Equals(this._AliasName, oth._AliasName) && object.Equals(this._TargetKeyId, oth._TargetKeyId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._AliasName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._TargetKeyId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.UpdateAliasRequest.UpdateAliasRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._AliasName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._TargetKeyId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IUpdateAliasRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IUpdateAliasRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateAliasRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateAliasRequest>(software.amazon.cryptography.services.kms.internaldafny.types.UpdateAliasRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateAliasRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUpdateAliasRequest create(Dafny.ISequence<char> AliasName, Dafny.ISequence<char> TargetKeyId) {
      return new UpdateAliasRequest(AliasName, TargetKeyId);
    }
    public static _IUpdateAliasRequest create_UpdateAliasRequest(Dafny.ISequence<char> AliasName, Dafny.ISequence<char> TargetKeyId) {
      return create(AliasName, TargetKeyId);
    }
    public bool is_UpdateAliasRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_AliasName {
      get {
        return this._AliasName;
      }
    }
    public Dafny.ISequence<char> dtor_TargetKeyId {
      get {
        return this._TargetKeyId;
      }
    }
  }

  public interface _IUpdateCustomKeyStoreRequest {
    bool is_UpdateCustomKeyStoreRequest { get; }
    Dafny.ISequence<char> dtor_CustomKeyStoreId { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NewCustomKeyStoreName { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyStorePassword { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId { get; }
    _IUpdateCustomKeyStoreRequest DowncastClone();
  }
  public class UpdateCustomKeyStoreRequest : _IUpdateCustomKeyStoreRequest {
    public readonly Dafny.ISequence<char> _CustomKeyStoreId;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _NewCustomKeyStoreName;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyStorePassword;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _CloudHsmClusterId;
    public UpdateCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> NewCustomKeyStoreName, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyStorePassword, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId) {
      this._CustomKeyStoreId = CustomKeyStoreId;
      this._NewCustomKeyStoreName = NewCustomKeyStoreName;
      this._KeyStorePassword = KeyStorePassword;
      this._CloudHsmClusterId = CloudHsmClusterId;
    }
    public _IUpdateCustomKeyStoreRequest DowncastClone() {
      if (this is _IUpdateCustomKeyStoreRequest dt) { return dt; }
      return new UpdateCustomKeyStoreRequest(_CustomKeyStoreId, _NewCustomKeyStoreName, _KeyStorePassword, _CloudHsmClusterId);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreRequest;
      return oth != null && object.Equals(this._CustomKeyStoreId, oth._CustomKeyStoreId) && object.Equals(this._NewCustomKeyStoreName, oth._NewCustomKeyStoreName) && object.Equals(this._KeyStorePassword, oth._KeyStorePassword) && object.Equals(this._CloudHsmClusterId, oth._CloudHsmClusterId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CustomKeyStoreId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._NewCustomKeyStoreName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyStorePassword));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._CloudHsmClusterId));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.UpdateCustomKeyStoreRequest.UpdateCustomKeyStoreRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._CustomKeyStoreId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._NewCustomKeyStoreName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._KeyStorePassword);
      s += ", ";
      s += Dafny.Helpers.ToString(this._CloudHsmClusterId);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreRequest theDefault = create(Dafny.Sequence<char>.Empty, Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreRequest>(software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUpdateCustomKeyStoreRequest create(Dafny.ISequence<char> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> NewCustomKeyStoreName, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyStorePassword, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId) {
      return new UpdateCustomKeyStoreRequest(CustomKeyStoreId, NewCustomKeyStoreName, KeyStorePassword, CloudHsmClusterId);
    }
    public static _IUpdateCustomKeyStoreRequest create_UpdateCustomKeyStoreRequest(Dafny.ISequence<char> CustomKeyStoreId, Wrappers_Compile._IOption<Dafny.ISequence<char>> NewCustomKeyStoreName, Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyStorePassword, Wrappers_Compile._IOption<Dafny.ISequence<char>> CloudHsmClusterId) {
      return create(CustomKeyStoreId, NewCustomKeyStoreName, KeyStorePassword, CloudHsmClusterId);
    }
    public bool is_UpdateCustomKeyStoreRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_CustomKeyStoreId {
      get {
        return this._CustomKeyStoreId;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_NewCustomKeyStoreName {
      get {
        return this._NewCustomKeyStoreName;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyStorePassword {
      get {
        return this._KeyStorePassword;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_CloudHsmClusterId {
      get {
        return this._CloudHsmClusterId;
      }
    }
  }

  public interface _IUpdateCustomKeyStoreResponse {
    bool is_UpdateCustomKeyStoreResponse { get; }
    _IUpdateCustomKeyStoreResponse DowncastClone();
  }
  public class UpdateCustomKeyStoreResponse : _IUpdateCustomKeyStoreResponse {
    public UpdateCustomKeyStoreResponse() {
    }
    public _IUpdateCustomKeyStoreResponse DowncastClone() {
      if (this is _IUpdateCustomKeyStoreResponse dt) { return dt; }
      return new UpdateCustomKeyStoreResponse();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreResponse;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.UpdateCustomKeyStoreResponse.UpdateCustomKeyStoreResponse";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreResponse theDefault = create();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreResponse>(software.amazon.cryptography.services.kms.internaldafny.types.UpdateCustomKeyStoreResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateCustomKeyStoreResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUpdateCustomKeyStoreResponse create() {
      return new UpdateCustomKeyStoreResponse();
    }
    public static _IUpdateCustomKeyStoreResponse create_UpdateCustomKeyStoreResponse() {
      return create();
    }
    public bool is_UpdateCustomKeyStoreResponse { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IUpdateCustomKeyStoreResponse> AllSingletonConstructors {
      get {
        yield return UpdateCustomKeyStoreResponse.create();
      }
    }
  }

  public interface _IUpdateKeyDescriptionRequest {
    bool is_UpdateKeyDescriptionRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_Description { get; }
    _IUpdateKeyDescriptionRequest DowncastClone();
  }
  public class UpdateKeyDescriptionRequest : _IUpdateKeyDescriptionRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<char> _Description;
    public UpdateKeyDescriptionRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> Description) {
      this._KeyId = KeyId;
      this._Description = Description;
    }
    public _IUpdateKeyDescriptionRequest DowncastClone() {
      if (this is _IUpdateKeyDescriptionRequest dt) { return dt; }
      return new UpdateKeyDescriptionRequest(_KeyId, _Description);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.UpdateKeyDescriptionRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._Description, oth._Description);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Description));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.UpdateKeyDescriptionRequest.UpdateKeyDescriptionRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Description);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IUpdateKeyDescriptionRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IUpdateKeyDescriptionRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateKeyDescriptionRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateKeyDescriptionRequest>(software.amazon.cryptography.services.kms.internaldafny.types.UpdateKeyDescriptionRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdateKeyDescriptionRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUpdateKeyDescriptionRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> Description) {
      return new UpdateKeyDescriptionRequest(KeyId, Description);
    }
    public static _IUpdateKeyDescriptionRequest create_UpdateKeyDescriptionRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> Description) {
      return create(KeyId, Description);
    }
    public bool is_UpdateKeyDescriptionRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_Description {
      get {
        return this._Description;
      }
    }
  }

  public interface _IUpdatePrimaryRegionRequest {
    bool is_UpdatePrimaryRegionRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<char> dtor_PrimaryRegion { get; }
    _IUpdatePrimaryRegionRequest DowncastClone();
  }
  public class UpdatePrimaryRegionRequest : _IUpdatePrimaryRegionRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<char> _PrimaryRegion;
    public UpdatePrimaryRegionRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PrimaryRegion) {
      this._KeyId = KeyId;
      this._PrimaryRegion = PrimaryRegion;
    }
    public _IUpdatePrimaryRegionRequest DowncastClone() {
      if (this is _IUpdatePrimaryRegionRequest dt) { return dt; }
      return new UpdatePrimaryRegionRequest(_KeyId, _PrimaryRegion);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.UpdatePrimaryRegionRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._PrimaryRegion, oth._PrimaryRegion);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._PrimaryRegion));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.UpdatePrimaryRegionRequest.UpdatePrimaryRegionRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._PrimaryRegion);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IUpdatePrimaryRegionRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty);
    public static software.amazon.cryptography.services.kms.internaldafny.types._IUpdatePrimaryRegionRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdatePrimaryRegionRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdatePrimaryRegionRequest>(software.amazon.cryptography.services.kms.internaldafny.types.UpdatePrimaryRegionRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IUpdatePrimaryRegionRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUpdatePrimaryRegionRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PrimaryRegion) {
      return new UpdatePrimaryRegionRequest(KeyId, PrimaryRegion);
    }
    public static _IUpdatePrimaryRegionRequest create_UpdatePrimaryRegionRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<char> PrimaryRegion) {
      return create(KeyId, PrimaryRegion);
    }
    public bool is_UpdatePrimaryRegionRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<char> dtor_PrimaryRegion {
      get {
        return this._PrimaryRegion;
      }
    }
  }

  public interface _IVerifyRequest {
    bool is_VerifyRequest { get; }
    Dafny.ISequence<char> dtor_KeyId { get; }
    Dafny.ISequence<byte> dtor_Message { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> dtor_MessageType { get; }
    Dafny.ISequence<byte> dtor_Signature { get; }
    software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec dtor_SigningAlgorithm { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens { get; }
    _IVerifyRequest DowncastClone();
  }
  public class VerifyRequest : _IVerifyRequest {
    public readonly Dafny.ISequence<char> _KeyId;
    public readonly Dafny.ISequence<byte> _Message;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> _MessageType;
    public readonly Dafny.ISequence<byte> _Signature;
    public readonly software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec _SigningAlgorithm;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _GrantTokens;
    public VerifyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Message, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> MessageType, Dafny.ISequence<byte> Signature, software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec SigningAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      this._KeyId = KeyId;
      this._Message = Message;
      this._MessageType = MessageType;
      this._Signature = Signature;
      this._SigningAlgorithm = SigningAlgorithm;
      this._GrantTokens = GrantTokens;
    }
    public _IVerifyRequest DowncastClone() {
      if (this is _IVerifyRequest dt) { return dt; }
      return new VerifyRequest(_KeyId, _Message, _MessageType, _Signature, _SigningAlgorithm, _GrantTokens);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.VerifyRequest;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._Message, oth._Message) && object.Equals(this._MessageType, oth._MessageType) && object.Equals(this._Signature, oth._Signature) && object.Equals(this._SigningAlgorithm, oth._SigningAlgorithm) && object.Equals(this._GrantTokens, oth._GrantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Message));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._MessageType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._Signature));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SigningAlgorithm));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._GrantTokens));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.VerifyRequest.VerifyRequest";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Message);
      s += ", ";
      s += Dafny.Helpers.ToString(this._MessageType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._Signature);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SigningAlgorithm);
      s += ", ";
      s += Dafny.Helpers.ToString(this._GrantTokens);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IVerifyRequest theDefault = create(Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType>.Default(), Dafny.Sequence<byte>.Empty, software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IVerifyRequest Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IVerifyRequest> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IVerifyRequest>(software.amazon.cryptography.services.kms.internaldafny.types.VerifyRequest.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IVerifyRequest> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IVerifyRequest create(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Message, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> MessageType, Dafny.ISequence<byte> Signature, software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec SigningAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return new VerifyRequest(KeyId, Message, MessageType, Signature, SigningAlgorithm, GrantTokens);
    }
    public static _IVerifyRequest create_VerifyRequest(Dafny.ISequence<char> KeyId, Dafny.ISequence<byte> Message, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> MessageType, Dafny.ISequence<byte> Signature, software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec SigningAlgorithm, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> GrantTokens) {
      return create(KeyId, Message, MessageType, Signature, SigningAlgorithm, GrantTokens);
    }
    public bool is_VerifyRequest { get { return true; } }
    public Dafny.ISequence<char> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Dafny.ISequence<byte> dtor_Message {
      get {
        return this._Message;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IMessageType> dtor_MessageType {
      get {
        return this._MessageType;
      }
    }
    public Dafny.ISequence<byte> dtor_Signature {
      get {
        return this._Signature;
      }
    }
    public software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec dtor_SigningAlgorithm {
      get {
        return this._SigningAlgorithm;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_GrantTokens {
      get {
        return this._GrantTokens;
      }
    }
  }

  public interface _IVerifyResponse {
    bool is_VerifyResponse { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId { get; }
    Wrappers_Compile._IOption<bool> dtor_SignatureValid { get; }
    Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> dtor_SigningAlgorithm { get; }
    _IVerifyResponse DowncastClone();
  }
  public class VerifyResponse : _IVerifyResponse {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _KeyId;
    public readonly Wrappers_Compile._IOption<bool> _SignatureValid;
    public readonly Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> _SigningAlgorithm;
    public VerifyResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<bool> SignatureValid, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> SigningAlgorithm) {
      this._KeyId = KeyId;
      this._SignatureValid = SignatureValid;
      this._SigningAlgorithm = SigningAlgorithm;
    }
    public _IVerifyResponse DowncastClone() {
      if (this is _IVerifyResponse dt) { return dt; }
      return new VerifyResponse(_KeyId, _SignatureValid, _SigningAlgorithm);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.VerifyResponse;
      return oth != null && object.Equals(this._KeyId, oth._KeyId) && object.Equals(this._SignatureValid, oth._SignatureValid) && object.Equals(this._SigningAlgorithm, oth._SigningAlgorithm);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._KeyId));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SignatureValid));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SigningAlgorithm));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.VerifyResponse.VerifyResponse";
      s += "(";
      s += Dafny.Helpers.ToString(this._KeyId);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SignatureValid);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SigningAlgorithm);
      s += ")";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IVerifyResponse theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<bool>.Default(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IVerifyResponse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IVerifyResponse> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IVerifyResponse>(software.amazon.cryptography.services.kms.internaldafny.types.VerifyResponse.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IVerifyResponse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IVerifyResponse create(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<bool> SignatureValid, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> SigningAlgorithm) {
      return new VerifyResponse(KeyId, SignatureValid, SigningAlgorithm);
    }
    public static _IVerifyResponse create_VerifyResponse(Wrappers_Compile._IOption<Dafny.ISequence<char>> KeyId, Wrappers_Compile._IOption<bool> SignatureValid, Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> SigningAlgorithm) {
      return create(KeyId, SignatureValid, SigningAlgorithm);
    }
    public bool is_VerifyResponse { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_KeyId {
      get {
        return this._KeyId;
      }
    }
    public Wrappers_Compile._IOption<bool> dtor_SignatureValid {
      get {
        return this._SignatureValid;
      }
    }
    public Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._ISigningAlgorithmSpec> dtor_SigningAlgorithm {
      get {
        return this._SigningAlgorithm;
      }
    }
  }

  public interface _IWrappingKeySpec {
    bool is_RSA__2048 { get; }
    _IWrappingKeySpec DowncastClone();
  }
  public class WrappingKeySpec : _IWrappingKeySpec {
    public WrappingKeySpec() {
    }
    public _IWrappingKeySpec DowncastClone() {
      if (this is _IWrappingKeySpec dt) { return dt; }
      return new WrappingKeySpec();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.WrappingKeySpec;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.WrappingKeySpec.RSA_2048";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec theDefault = create();
    public static software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec>(software.amazon.cryptography.services.kms.internaldafny.types.WrappingKeySpec.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IWrappingKeySpec> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IWrappingKeySpec create() {
      return new WrappingKeySpec();
    }
    public static _IWrappingKeySpec create_RSA__2048() {
      return create();
    }
    public bool is_RSA__2048 { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IWrappingKeySpec> AllSingletonConstructors {
      get {
        yield return WrappingKeySpec.create();
      }
    }
  }

  public interface _IError {
    bool is_AlreadyExistsException { get; }
    bool is_CloudHsmClusterInUseException { get; }
    bool is_CloudHsmClusterInvalidConfigurationException { get; }
    bool is_CloudHsmClusterNotActiveException { get; }
    bool is_CloudHsmClusterNotFoundException { get; }
    bool is_CloudHsmClusterNotRelatedException { get; }
    bool is_CustomKeyStoreHasCMKsException { get; }
    bool is_CustomKeyStoreInvalidStateException { get; }
    bool is_CustomKeyStoreNameInUseException { get; }
    bool is_CustomKeyStoreNotFoundException { get; }
    bool is_DependencyTimeoutException { get; }
    bool is_DisabledException { get; }
    bool is_ExpiredImportTokenException { get; }
    bool is_IncorrectKeyException { get; }
    bool is_IncorrectKeyMaterialException { get; }
    bool is_IncorrectTrustAnchorException { get; }
    bool is_InvalidAliasNameException { get; }
    bool is_InvalidArnException { get; }
    bool is_InvalidCiphertextException { get; }
    bool is_InvalidGrantIdException { get; }
    bool is_InvalidGrantTokenException { get; }
    bool is_InvalidImportTokenException { get; }
    bool is_InvalidKeyUsageException { get; }
    bool is_InvalidMarkerException { get; }
    bool is_KeyUnavailableException { get; }
    bool is_KMSInternalException { get; }
    bool is_KMSInvalidSignatureException { get; }
    bool is_KMSInvalidStateException { get; }
    bool is_LimitExceededException { get; }
    bool is_MalformedPolicyDocumentException { get; }
    bool is_NotFoundException { get; }
    bool is_TagException { get; }
    bool is_UnsupportedOperationException { get; }
    bool is_Opaque { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_message { get; }
    object dtor_obj { get; }
    _IError DowncastClone();
  }
  public abstract class Error : _IError {
    public Error() { }
    private static readonly software.amazon.cryptography.services.kms.internaldafny.types._IError theDefault = create_AlreadyExistsException(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static software.amazon.cryptography.services.kms.internaldafny.types._IError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IError> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IError>(software.amazon.cryptography.services.kms.internaldafny.types.Error.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IError create_AlreadyExistsException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_AlreadyExistsException(message);
    }
    public static _IError create_CloudHsmClusterInUseException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CloudHsmClusterInUseException(message);
    }
    public static _IError create_CloudHsmClusterInvalidConfigurationException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CloudHsmClusterInvalidConfigurationException(message);
    }
    public static _IError create_CloudHsmClusterNotActiveException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CloudHsmClusterNotActiveException(message);
    }
    public static _IError create_CloudHsmClusterNotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CloudHsmClusterNotFoundException(message);
    }
    public static _IError create_CloudHsmClusterNotRelatedException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CloudHsmClusterNotRelatedException(message);
    }
    public static _IError create_CustomKeyStoreHasCMKsException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CustomKeyStoreHasCMKsException(message);
    }
    public static _IError create_CustomKeyStoreInvalidStateException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CustomKeyStoreInvalidStateException(message);
    }
    public static _IError create_CustomKeyStoreNameInUseException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CustomKeyStoreNameInUseException(message);
    }
    public static _IError create_CustomKeyStoreNotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_CustomKeyStoreNotFoundException(message);
    }
    public static _IError create_DependencyTimeoutException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_DependencyTimeoutException(message);
    }
    public static _IError create_DisabledException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_DisabledException(message);
    }
    public static _IError create_ExpiredImportTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_ExpiredImportTokenException(message);
    }
    public static _IError create_IncorrectKeyException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_IncorrectKeyException(message);
    }
    public static _IError create_IncorrectKeyMaterialException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_IncorrectKeyMaterialException(message);
    }
    public static _IError create_IncorrectTrustAnchorException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_IncorrectTrustAnchorException(message);
    }
    public static _IError create_InvalidAliasNameException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidAliasNameException(message);
    }
    public static _IError create_InvalidArnException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidArnException(message);
    }
    public static _IError create_InvalidCiphertextException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidCiphertextException(message);
    }
    public static _IError create_InvalidGrantIdException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidGrantIdException(message);
    }
    public static _IError create_InvalidGrantTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidGrantTokenException(message);
    }
    public static _IError create_InvalidImportTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidImportTokenException(message);
    }
    public static _IError create_InvalidKeyUsageException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidKeyUsageException(message);
    }
    public static _IError create_InvalidMarkerException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_InvalidMarkerException(message);
    }
    public static _IError create_KeyUnavailableException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_KeyUnavailableException(message);
    }
    public static _IError create_KMSInternalException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_KMSInternalException(message);
    }
    public static _IError create_KMSInvalidSignatureException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_KMSInvalidSignatureException(message);
    }
    public static _IError create_KMSInvalidStateException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_KMSInvalidStateException(message);
    }
    public static _IError create_LimitExceededException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_LimitExceededException(message);
    }
    public static _IError create_MalformedPolicyDocumentException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_MalformedPolicyDocumentException(message);
    }
    public static _IError create_NotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_NotFoundException(message);
    }
    public static _IError create_TagException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_TagException(message);
    }
    public static _IError create_UnsupportedOperationException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      return new Error_UnsupportedOperationException(message);
    }
    public static _IError create_Opaque(object obj) {
      return new Error_Opaque(obj);
    }
    public bool is_AlreadyExistsException { get { return this is Error_AlreadyExistsException; } }
    public bool is_CloudHsmClusterInUseException { get { return this is Error_CloudHsmClusterInUseException; } }
    public bool is_CloudHsmClusterInvalidConfigurationException { get { return this is Error_CloudHsmClusterInvalidConfigurationException; } }
    public bool is_CloudHsmClusterNotActiveException { get { return this is Error_CloudHsmClusterNotActiveException; } }
    public bool is_CloudHsmClusterNotFoundException { get { return this is Error_CloudHsmClusterNotFoundException; } }
    public bool is_CloudHsmClusterNotRelatedException { get { return this is Error_CloudHsmClusterNotRelatedException; } }
    public bool is_CustomKeyStoreHasCMKsException { get { return this is Error_CustomKeyStoreHasCMKsException; } }
    public bool is_CustomKeyStoreInvalidStateException { get { return this is Error_CustomKeyStoreInvalidStateException; } }
    public bool is_CustomKeyStoreNameInUseException { get { return this is Error_CustomKeyStoreNameInUseException; } }
    public bool is_CustomKeyStoreNotFoundException { get { return this is Error_CustomKeyStoreNotFoundException; } }
    public bool is_DependencyTimeoutException { get { return this is Error_DependencyTimeoutException; } }
    public bool is_DisabledException { get { return this is Error_DisabledException; } }
    public bool is_ExpiredImportTokenException { get { return this is Error_ExpiredImportTokenException; } }
    public bool is_IncorrectKeyException { get { return this is Error_IncorrectKeyException; } }
    public bool is_IncorrectKeyMaterialException { get { return this is Error_IncorrectKeyMaterialException; } }
    public bool is_IncorrectTrustAnchorException { get { return this is Error_IncorrectTrustAnchorException; } }
    public bool is_InvalidAliasNameException { get { return this is Error_InvalidAliasNameException; } }
    public bool is_InvalidArnException { get { return this is Error_InvalidArnException; } }
    public bool is_InvalidCiphertextException { get { return this is Error_InvalidCiphertextException; } }
    public bool is_InvalidGrantIdException { get { return this is Error_InvalidGrantIdException; } }
    public bool is_InvalidGrantTokenException { get { return this is Error_InvalidGrantTokenException; } }
    public bool is_InvalidImportTokenException { get { return this is Error_InvalidImportTokenException; } }
    public bool is_InvalidKeyUsageException { get { return this is Error_InvalidKeyUsageException; } }
    public bool is_InvalidMarkerException { get { return this is Error_InvalidMarkerException; } }
    public bool is_KeyUnavailableException { get { return this is Error_KeyUnavailableException; } }
    public bool is_KMSInternalException { get { return this is Error_KMSInternalException; } }
    public bool is_KMSInvalidSignatureException { get { return this is Error_KMSInvalidSignatureException; } }
    public bool is_KMSInvalidStateException { get { return this is Error_KMSInvalidStateException; } }
    public bool is_LimitExceededException { get { return this is Error_LimitExceededException; } }
    public bool is_MalformedPolicyDocumentException { get { return this is Error_MalformedPolicyDocumentException; } }
    public bool is_NotFoundException { get { return this is Error_NotFoundException; } }
    public bool is_TagException { get { return this is Error_TagException; } }
    public bool is_UnsupportedOperationException { get { return this is Error_UnsupportedOperationException; } }
    public bool is_Opaque { get { return this is Error_Opaque; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_message {
      get {
        var d = this;
        if (d is Error_AlreadyExistsException) { return ((Error_AlreadyExistsException)d)._message; }
        if (d is Error_CloudHsmClusterInUseException) { return ((Error_CloudHsmClusterInUseException)d)._message; }
        if (d is Error_CloudHsmClusterInvalidConfigurationException) { return ((Error_CloudHsmClusterInvalidConfigurationException)d)._message; }
        if (d is Error_CloudHsmClusterNotActiveException) { return ((Error_CloudHsmClusterNotActiveException)d)._message; }
        if (d is Error_CloudHsmClusterNotFoundException) { return ((Error_CloudHsmClusterNotFoundException)d)._message; }
        if (d is Error_CloudHsmClusterNotRelatedException) { return ((Error_CloudHsmClusterNotRelatedException)d)._message; }
        if (d is Error_CustomKeyStoreHasCMKsException) { return ((Error_CustomKeyStoreHasCMKsException)d)._message; }
        if (d is Error_CustomKeyStoreInvalidStateException) { return ((Error_CustomKeyStoreInvalidStateException)d)._message; }
        if (d is Error_CustomKeyStoreNameInUseException) { return ((Error_CustomKeyStoreNameInUseException)d)._message; }
        if (d is Error_CustomKeyStoreNotFoundException) { return ((Error_CustomKeyStoreNotFoundException)d)._message; }
        if (d is Error_DependencyTimeoutException) { return ((Error_DependencyTimeoutException)d)._message; }
        if (d is Error_DisabledException) { return ((Error_DisabledException)d)._message; }
        if (d is Error_ExpiredImportTokenException) { return ((Error_ExpiredImportTokenException)d)._message; }
        if (d is Error_IncorrectKeyException) { return ((Error_IncorrectKeyException)d)._message; }
        if (d is Error_IncorrectKeyMaterialException) { return ((Error_IncorrectKeyMaterialException)d)._message; }
        if (d is Error_IncorrectTrustAnchorException) { return ((Error_IncorrectTrustAnchorException)d)._message; }
        if (d is Error_InvalidAliasNameException) { return ((Error_InvalidAliasNameException)d)._message; }
        if (d is Error_InvalidArnException) { return ((Error_InvalidArnException)d)._message; }
        if (d is Error_InvalidCiphertextException) { return ((Error_InvalidCiphertextException)d)._message; }
        if (d is Error_InvalidGrantIdException) { return ((Error_InvalidGrantIdException)d)._message; }
        if (d is Error_InvalidGrantTokenException) { return ((Error_InvalidGrantTokenException)d)._message; }
        if (d is Error_InvalidImportTokenException) { return ((Error_InvalidImportTokenException)d)._message; }
        if (d is Error_InvalidKeyUsageException) { return ((Error_InvalidKeyUsageException)d)._message; }
        if (d is Error_InvalidMarkerException) { return ((Error_InvalidMarkerException)d)._message; }
        if (d is Error_KeyUnavailableException) { return ((Error_KeyUnavailableException)d)._message; }
        if (d is Error_KMSInternalException) { return ((Error_KMSInternalException)d)._message; }
        if (d is Error_KMSInvalidSignatureException) { return ((Error_KMSInvalidSignatureException)d)._message; }
        if (d is Error_KMSInvalidStateException) { return ((Error_KMSInvalidStateException)d)._message; }
        if (d is Error_LimitExceededException) { return ((Error_LimitExceededException)d)._message; }
        if (d is Error_MalformedPolicyDocumentException) { return ((Error_MalformedPolicyDocumentException)d)._message; }
        if (d is Error_NotFoundException) { return ((Error_NotFoundException)d)._message; }
        if (d is Error_TagException) { return ((Error_TagException)d)._message; }
        return ((Error_UnsupportedOperationException)d)._message;
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
  public class Error_AlreadyExistsException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_AlreadyExistsException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_AlreadyExistsException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_AlreadyExistsException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.AlreadyExistsException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_CloudHsmClusterInUseException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_CloudHsmClusterInUseException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CloudHsmClusterInUseException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInUseException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.CloudHsmClusterInUseException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_CloudHsmClusterInvalidConfigurationException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_CloudHsmClusterInvalidConfigurationException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CloudHsmClusterInvalidConfigurationException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterInvalidConfigurationException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.CloudHsmClusterInvalidConfigurationException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_CloudHsmClusterNotActiveException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_CloudHsmClusterNotActiveException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CloudHsmClusterNotActiveException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotActiveException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.CloudHsmClusterNotActiveException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_CloudHsmClusterNotFoundException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_CloudHsmClusterNotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CloudHsmClusterNotFoundException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotFoundException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.CloudHsmClusterNotFoundException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_CloudHsmClusterNotRelatedException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_CloudHsmClusterNotRelatedException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CloudHsmClusterNotRelatedException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_CloudHsmClusterNotRelatedException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.CloudHsmClusterNotRelatedException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_CustomKeyStoreHasCMKsException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_CustomKeyStoreHasCMKsException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CustomKeyStoreHasCMKsException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreHasCMKsException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.CustomKeyStoreHasCMKsException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_CustomKeyStoreInvalidStateException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_CustomKeyStoreInvalidStateException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CustomKeyStoreInvalidStateException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreInvalidStateException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.CustomKeyStoreInvalidStateException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_CustomKeyStoreNameInUseException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_CustomKeyStoreNameInUseException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CustomKeyStoreNameInUseException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNameInUseException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.CustomKeyStoreNameInUseException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_CustomKeyStoreNotFoundException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_CustomKeyStoreNotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_CustomKeyStoreNotFoundException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_CustomKeyStoreNotFoundException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.CustomKeyStoreNotFoundException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_DependencyTimeoutException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_DependencyTimeoutException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_DependencyTimeoutException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_DependencyTimeoutException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.DependencyTimeoutException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_DisabledException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_DisabledException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_DisabledException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_DisabledException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.DisabledException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_ExpiredImportTokenException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_ExpiredImportTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_ExpiredImportTokenException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_ExpiredImportTokenException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.ExpiredImportTokenException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_IncorrectKeyException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_IncorrectKeyException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_IncorrectKeyException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.IncorrectKeyException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_IncorrectKeyMaterialException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_IncorrectKeyMaterialException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_IncorrectKeyMaterialException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectKeyMaterialException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.IncorrectKeyMaterialException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_IncorrectTrustAnchorException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_IncorrectTrustAnchorException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_IncorrectTrustAnchorException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_IncorrectTrustAnchorException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.IncorrectTrustAnchorException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidAliasNameException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_InvalidAliasNameException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidAliasNameException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidAliasNameException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.InvalidAliasNameException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidArnException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_InvalidArnException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidArnException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidArnException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.InvalidArnException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidCiphertextException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_InvalidCiphertextException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidCiphertextException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidCiphertextException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.InvalidCiphertextException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidGrantIdException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_InvalidGrantIdException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidGrantIdException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantIdException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.InvalidGrantIdException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidGrantTokenException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_InvalidGrantTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidGrantTokenException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidGrantTokenException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.InvalidGrantTokenException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidImportTokenException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_InvalidImportTokenException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidImportTokenException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidImportTokenException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 21;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.InvalidImportTokenException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidKeyUsageException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_InvalidKeyUsageException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidKeyUsageException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidKeyUsageException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 22;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.InvalidKeyUsageException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_InvalidMarkerException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_InvalidMarkerException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_InvalidMarkerException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_InvalidMarkerException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 23;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.InvalidMarkerException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_KeyUnavailableException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_KeyUnavailableException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_KeyUnavailableException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_KeyUnavailableException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.KeyUnavailableException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_KMSInternalException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_KMSInternalException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_KMSInternalException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInternalException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 25;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.KMSInternalException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_KMSInvalidSignatureException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_KMSInvalidSignatureException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_KMSInvalidSignatureException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidSignatureException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 26;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.KMSInvalidSignatureException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_KMSInvalidStateException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_KMSInvalidStateException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_KMSInvalidStateException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_KMSInvalidStateException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 27;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.KMSInvalidStateException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_LimitExceededException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_LimitExceededException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_LimitExceededException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_LimitExceededException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 28;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.LimitExceededException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_MalformedPolicyDocumentException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_MalformedPolicyDocumentException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_MalformedPolicyDocumentException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_MalformedPolicyDocumentException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 29;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.MalformedPolicyDocumentException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_NotFoundException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_NotFoundException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_NotFoundException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_NotFoundException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 30;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.NotFoundException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_TagException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_TagException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_TagException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_TagException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 31;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.TagException";
      s += "(";
      s += Dafny.Helpers.ToString(this._message);
      s += ")";
      return s;
    }
  }
  public class Error_UnsupportedOperationException : Error {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _message;
    public Error_UnsupportedOperationException(Wrappers_Compile._IOption<Dafny.ISequence<char>> message) {
      this._message = message;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_UnsupportedOperationException(_message);
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_UnsupportedOperationException;
      return oth != null && object.Equals(this._message, oth._message);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 32;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._message));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.UnsupportedOperationException";
      s += "(";
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
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.types.Error_Opaque;
      return oth != null && this._obj == oth._obj;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 33;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny.types_Compile.Error.Opaque";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ")";
      return s;
    }
  }

  public partial class OpaqueError {
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IError> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IError>(software.amazon.cryptography.services.kms.internaldafny.types.Error.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny.types._IError> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool IsValid__AliasNameType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(256)));
    }
    public static bool IsValid__ArnType(Dafny.ISequence<char> x) {
      return ((new BigInteger(20)) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(2048)));
    }
    public static bool IsValid__CiphertextType(Dafny.ISequence<byte> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(6144)));
    }
    public static bool IsValid__CloudHsmClusterIdType(Dafny.ISequence<char> x) {
      return ((new BigInteger(19)) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(24)));
    }
    public static bool IsValid__CustomKeyStoreIdType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(64)));
    }
    public static bool IsValid__CustomKeyStoreNameType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(256)));
    }
    public static bool IsValid__DescriptionType(Dafny.ISequence<char> x) {
      return ((new BigInteger((x).Count)).Sign != -1) && ((new BigInteger((x).Count)) <= (new BigInteger(8192)));
    }
    public static bool IsValid__GrantIdType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(128)));
    }
    public static bool IsValid__GrantNameType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(256)));
    }
    public static bool IsValid__GrantTokenList(Dafny.ISequence<Dafny.ISequence<char>> x) {
      return ((new BigInteger((x).Count)).Sign != -1) && ((new BigInteger((x).Count)) <= (new BigInteger(10)));
    }
    public static bool IsValid__GrantTokenType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(8192)));
    }
    public static bool IsValid__KeyIdType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(2048)));
    }
    public static bool IsValid__KeyStorePasswordType(Dafny.ISequence<char> x) {
      return ((new BigInteger(7)) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(32)));
    }
    public static bool IsValid__LimitType(int x) {
      return ((1) <= (x)) && ((x) <= (1000));
    }
    public static bool IsValid__MarkerType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(1024)));
    }
    public static bool IsValid__NumberOfBytesType(int x) {
      return ((1) <= (x)) && ((x) <= (1024));
    }
    public static bool IsValid__PendingWindowInDaysType(int x) {
      return ((1) <= (x)) && ((x) <= (365));
    }
    public static bool IsValid__PlaintextType(Dafny.ISequence<byte> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(4096)));
    }
    public static bool IsValid__PolicyNameType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(128)));
    }
    public static bool IsValid__PolicyType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(131072)));
    }
    public static bool IsValid__PrincipalIdType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(256)));
    }
    public static bool IsValid__PublicKeyType(Dafny.ISequence<byte> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(8192)));
    }
    public static bool IsValid__RegionType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(32)));
    }
    public static bool IsValid__TagKeyType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(128)));
    }
    public static bool IsValid__TagValueType(Dafny.ISequence<char> x) {
      return ((new BigInteger((x).Count)).Sign != -1) && ((new BigInteger((x).Count)) <= (new BigInteger(256)));
    }
    public static bool IsValid__TrustAnchorCertificateType(Dafny.ISequence<char> x) {
      return ((BigInteger.One) <= (new BigInteger((x).Count))) && ((new BigInteger((x).Count)) <= (new BigInteger(5000)));
    }
  }
} // end of namespace software.amazon.cryptography.services.kms.internaldafny.types
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
namespace software.amazon.cryptography.services.kms.internaldafny {

  public partial class __default {
    public static software.amazon.cryptography.services.kms.internaldafny._IKMSClientConfigType DefaultKMSClientConfigType() {
      return software.amazon.cryptography.services.kms.internaldafny.KMSClientConfigType.create();
    }
    public static Dafny.ISequence<char> DafnyUserAgentSuffix(Dafny.ISequence<char> runtime) {
      Dafny.ISequence<char> _0_version = Dafny.Sequence<char>.FromString("1.0.0");
      return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("AwsCryptographicMPL/"), runtime), Dafny.Sequence<char>.FromString("/")), _0_version);
    }
  }

  public interface _IKMSClientConfigType {
    bool is_KMSClientConfigType { get; }
    _IKMSClientConfigType DowncastClone();
  }
  public class KMSClientConfigType : _IKMSClientConfigType {
    public KMSClientConfigType() {
    }
    public _IKMSClientConfigType DowncastClone() {
      if (this is _IKMSClientConfigType dt) { return dt; }
      return new KMSClientConfigType();
    }
    public override bool Equals(object other) {
      var oth = other as software.amazon.cryptography.services.kms.internaldafny.KMSClientConfigType;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "software.amazon.cryptography.services.kms.internaldafny_Compile.KMSClientConfigType.KMSClientConfigType";
      return s;
    }
    private static readonly software.amazon.cryptography.services.kms.internaldafny._IKMSClientConfigType theDefault = create();
    public static software.amazon.cryptography.services.kms.internaldafny._IKMSClientConfigType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny._IKMSClientConfigType> _TYPE = new Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny._IKMSClientConfigType>(software.amazon.cryptography.services.kms.internaldafny.KMSClientConfigType.Default());
    public static Dafny.TypeDescriptor<software.amazon.cryptography.services.kms.internaldafny._IKMSClientConfigType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IKMSClientConfigType create() {
      return new KMSClientConfigType();
    }
    public static _IKMSClientConfigType create_KMSClientConfigType() {
      return create();
    }
    public bool is_KMSClientConfigType { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IKMSClientConfigType> AllSingletonConstructors {
      get {
        yield return KMSClientConfigType.create();
      }
    }
  }
} // end of namespace software.amazon.cryptography.services.kms.internaldafny
namespace Com_mAmazonaws_Compile {

} // end of namespace Com_mAmazonaws_Compile
namespace Com_Compile {

} // end of namespace Com_Compile
namespace _module {

} // end of namespace _module
