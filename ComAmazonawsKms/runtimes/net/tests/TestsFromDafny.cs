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
// Command Line Options: -stdin -noVerify -vcsCores:2 -compileTarget:cs -spillTargetCode:3 -runAllTests:1 -compile:0 -optimizeErasableDatatypeWrapper:0 -quantifierSyntax:3 -unicodeChar:0 -functionSyntax:3 -useRuntimeLib -out runtimes/net/tests/TestsFromDafny -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/src/Index.dfy -library:src/Index.dfy
// the_program

method {:verify false} {:main} _Test__Main_()










































module TestComAmazonawsKms {

  import Kms = Com.Amazonaws.Kms

  import opened UInt = StandardLibrary.UInt
  const keyId := ""arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f""
  const TEST_REGION := ""us-west-2""

  function method workAround(literal: seq<uint8>): (ret: Kms.Types.CiphertextType)
    requires Kms.Types.IsValid_CiphertextType(literal)
    decreases literal
  {
    literal
  }

  method {:test} BasicDecryptTests()
  {
    var CiphertextBlob: seq<uint8> := [1, 1, 1, 0, 120, 64, 243, 140, 39, 94, 49, 9, 116, 22, 193, 7, 41, 81, 80, 87, 25, 100, 173, 163, 239, 28, 33, 233, 76, 139, 160, 189, 188, 157, 15, 180, 20, 0, 0, 0, 98, 48, 96, 6, 9, 42, 134, 72, 134, 247, 13, 1, 7, 6, 160, 83, 48, 81, 2, 1, 0, 48, 76, 6, 9, 42, 134, 72, 134, 247, 13, 1, 7, 1, 48, 30, 6, 9, 96, 134, 72, 1, 101, 3, 4, 1, 46, 48, 17, 4, 12, 196, 249, 60, 7, 21, 231, 87, 70, 216, 12, 31, 13, 2, 1, 16, 128, 31, 222, 119, 162, 112, 88, 153, 39, 197, 21, 182, 116, 176, 120, 174, 107, 82, 182, 223, 160, 201, 15, 29, 3, 254, 3, 208, 72, 171, 64, 207, 175];
    BasicDecryptTest(input := Kms.Types.DecryptRequest(CiphertextBlob := workAround(CiphertextBlob), EncryptionContext := Kms.Wrappers.None, GrantTokens := Kms.Wrappers.None, KeyId := Kms.Wrappers.Some(keyId), EncryptionAlgorithm := Kms.Wrappers.None), expectedPlaintext := [165, 191, 67, 62], expectedKeyId := keyId);
  }

  method {:test} BasicGenerateTests()
  {
    BasicGenerateTest(input := Kms.Types.GenerateDataKeyRequest(KeyId := keyId, EncryptionContext := Kms.Wrappers.None, NumberOfBytes := Kms.Wrappers.Some(32 as Kms.Types.NumberOfBytesType), KeySpec := Kms.Wrappers.None, GrantTokens := Kms.Wrappers.None));
  }

  method {:test} BasicEncryptTests()
  {
    BasicEncryptTest(input := Kms.Types.EncryptRequest(KeyId := keyId, Plaintext := [97, 115, 100, 102], EncryptionContext := Kms.Wrappers.None, GrantTokens := Kms.Wrappers.None, EncryptionAlgorithm := Kms.Wrappers.None));
  }

  method BasicDecryptTest(nameonly input: Kms.Types.DecryptRequest, nameonly expectedPlaintext: Kms.Types.PlaintextType, nameonly expectedKeyId: Kms.Types.KeyIdType)
    decreases input, expectedPlaintext, expectedKeyId
  {
    var client :- expect Kms.KMSClient();
    var ret := client.Decrypt(input);
    print ret;
    expect ret.Success?, ""expectation violation""
    var DecryptResponse(KeyId, Plaintext, EncryptionAlgorithm) := ret.value;
    expect Plaintext.Some?, ""expectation violation""
    expect KeyId.Some?, ""expectation violation""
    expect Plaintext.value == expectedPlaintext, ""expectation violation""
    expect KeyId.value == expectedKeyId, ""expectation violation""
  }

  method BasicGenerateTest(nameonly input: Kms.Types.GenerateDataKeyRequest)
    requires input.NumberOfBytes.Some?
    decreases input
  {
    var client :- expect Kms.KMSClient();
    var ret := client.GenerateDataKey(input);
    expect ret.Success?, ""expectation violation""
    var GenerateDataKeyResponse(CiphertextBlob, Plaintext, KeyId) := ret.value;
    expect CiphertextBlob.Some?, ""expectation violation""
    expect Plaintext.Some?, ""expectation violation""
    expect KeyId.Some?, ""expectation violation""
    expect |Plaintext.value| == input.NumberOfBytes.value as nat, ""expectation violation""
    var decryptInput := Kms.Types.DecryptRequest(CiphertextBlob := CiphertextBlob.value, EncryptionContext := input.EncryptionContext, GrantTokens := input.GrantTokens, KeyId := Kms.Wrappers.Some(KeyId.value), EncryptionAlgorithm := Kms.Wrappers.None);
    BasicDecryptTest(input := decryptInput, expectedPlaintext := Plaintext.value, expectedKeyId := input.KeyId);
  }

  method BasicEncryptTest(nameonly input: Kms.Types.EncryptRequest)
    decreases input
  {
    var client :- expect Kms.KMSClient();
    var ret := client.Encrypt(input);
    expect ret.Success?, ""expectation violation""
    var EncryptResponse(CiphertextBlob, KeyId, EncryptionAlgorithm) := ret.value;
    expect CiphertextBlob.Some?, ""expectation violation""
    expect KeyId.Some?, ""expectation violation""
    var decryptInput := Kms.Types.DecryptRequest(CiphertextBlob := CiphertextBlob.value, EncryptionContext := input.EncryptionContext, GrantTokens := input.GrantTokens, KeyId := Kms.Wrappers.Some(KeyId.value), EncryptionAlgorithm := input.EncryptionAlgorithm);
    BasicDecryptTest(input := decryptInput, expectedPlaintext := input.Plaintext, expectedKeyId := input.KeyId);
  }

  method {:test} RegionMatchTest()
  {
    var client :- expect Kms.KMSClient();
    var region := Kms.RegionMatch(client, TEST_REGION);
    expect region.None? || region.value, ""expectation violation""
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
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System
namespace Com_mAmazonaws_Compile {

} // end of namespace Com_mAmazonaws_Compile
namespace Com_Compile {

} // end of namespace Com_Compile
namespace TestComAmazonawsKms_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> workAround(Dafny.ISequence<byte> literal) {
      return literal;
    }
    public static void BasicDecryptTests()
    {
      Dafny.ISequence<byte> _0_CiphertextBlob;
      _0_CiphertextBlob = Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(1), (byte)(1), (byte)(0), (byte)(120), (byte)(64), (byte)(243), (byte)(140), (byte)(39), (byte)(94), (byte)(49), (byte)(9), (byte)(116), (byte)(22), (byte)(193), (byte)(7), (byte)(41), (byte)(81), (byte)(80), (byte)(87), (byte)(25), (byte)(100), (byte)(173), (byte)(163), (byte)(239), (byte)(28), (byte)(33), (byte)(233), (byte)(76), (byte)(139), (byte)(160), (byte)(189), (byte)(188), (byte)(157), (byte)(15), (byte)(180), (byte)(20), (byte)(0), (byte)(0), (byte)(0), (byte)(98), (byte)(48), (byte)(96), (byte)(6), (byte)(9), (byte)(42), (byte)(134), (byte)(72), (byte)(134), (byte)(247), (byte)(13), (byte)(1), (byte)(7), (byte)(6), (byte)(160), (byte)(83), (byte)(48), (byte)(81), (byte)(2), (byte)(1), (byte)(0), (byte)(48), (byte)(76), (byte)(6), (byte)(9), (byte)(42), (byte)(134), (byte)(72), (byte)(134), (byte)(247), (byte)(13), (byte)(1), (byte)(7), (byte)(1), (byte)(48), (byte)(30), (byte)(6), (byte)(9), (byte)(96), (byte)(134), (byte)(72), (byte)(1), (byte)(101), (byte)(3), (byte)(4), (byte)(1), (byte)(46), (byte)(48), (byte)(17), (byte)(4), (byte)(12), (byte)(196), (byte)(249), (byte)(60), (byte)(7), (byte)(21), (byte)(231), (byte)(87), (byte)(70), (byte)(216), (byte)(12), (byte)(31), (byte)(13), (byte)(2), (byte)(1), (byte)(16), (byte)(128), (byte)(31), (byte)(222), (byte)(119), (byte)(162), (byte)(112), (byte)(88), (byte)(153), (byte)(39), (byte)(197), (byte)(21), (byte)(182), (byte)(116), (byte)(176), (byte)(120), (byte)(174), (byte)(107), (byte)(82), (byte)(182), (byte)(223), (byte)(160), (byte)(201), (byte)(15), (byte)(29), (byte)(3), (byte)(254), (byte)(3), (byte)(208), (byte)(72), (byte)(171), (byte)(64), (byte)(207), (byte)(175));
      TestComAmazonawsKms_Compile.__default.BasicDecryptTest(software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest.create(TestComAmazonawsKms_Compile.__default.workAround(_0_CiphertextBlob), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(TestComAmazonawsKms_Compile.__default.keyId), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_None()), Dafny.Sequence<byte>.FromElements((byte)(165), (byte)(191), (byte)(67), (byte)(62)), TestComAmazonawsKms_Compile.__default.keyId);
    }
    public static void BasicGenerateTests()
    {
      TestComAmazonawsKms_Compile.__default.BasicGenerateTest(software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyRequest.create(TestComAmazonawsKms_Compile.__default.keyId, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<int>.create_Some((int)(32)), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IDataKeySpec>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None()));
    }
    public static void BasicEncryptTests()
    {
      TestComAmazonawsKms_Compile.__default.BasicEncryptTest(software.amazon.cryptography.services.kms.internaldafny.types.EncryptRequest.create(TestComAmazonawsKms_Compile.__default.keyId, Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(115), (byte)(100), (byte)(102)), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_None()));
    }
    public static void BasicDecryptTest(software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest input, Dafny.ISequence<byte> expectedPlaintext, Dafny.ISequence<char> expectedKeyId)
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _1_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _2_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out0;
      _out0 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _2_valueOrError0 = _out0;
      if (!(!((_2_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(88,15): " + _2_valueOrError0);}
      _1_client = (_2_valueOrError0).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> _3_ret;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out1;
      _out1 = (_1_client).Decrypt(input);
      _3_ret = _out1;
      Dafny.Helpers.Print((_3_ret));
      if (!((_3_ret).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(94,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.services.kms.internaldafny.types._IDecryptResponse _let_tmp_rhs0 = (_3_ret).dtor_value;
      Wrappers_Compile._IOption<Dafny.ISequence<char>> _4_KeyId = _let_tmp_rhs0.dtor_KeyId;
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _5_Plaintext = _let_tmp_rhs0.dtor_Plaintext;
      Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _6_EncryptionAlgorithm = _let_tmp_rhs0.dtor_EncryptionAlgorithm;
      if (!((_5_Plaintext).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(98,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_4_KeyId).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(99,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((_5_Plaintext).dtor_value).Equals(expectedPlaintext))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(100,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(((_4_KeyId).dtor_value).Equals(expectedKeyId))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(101,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void BasicGenerateTest(software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyRequest input)
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _7_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _8_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out2;
      _out2 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _8_valueOrError0 = _out2;
      if (!(!((_8_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(109,15): " + _8_valueOrError0);}
      _7_client = (_8_valueOrError0).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> _9_ret;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out3;
      _out3 = (_7_client).GenerateDataKey(input);
      _9_ret = _out3;
      if (!((_9_ret).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(113,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.services.kms.internaldafny.types._IGenerateDataKeyResponse _let_tmp_rhs1 = (_9_ret).dtor_value;
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _10_CiphertextBlob = _let_tmp_rhs1.dtor_CiphertextBlob;
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _11_Plaintext = _let_tmp_rhs1.dtor_Plaintext;
      Wrappers_Compile._IOption<Dafny.ISequence<char>> _12_KeyId = _let_tmp_rhs1.dtor_KeyId;
      if (!((_10_CiphertextBlob).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(117,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_11_Plaintext).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(118,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_12_KeyId).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(119,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((new BigInteger(((_11_Plaintext).dtor_value).Count)) == (new BigInteger(((input).dtor_NumberOfBytes).dtor_value)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(120,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest _13_decryptInput;
      _13_decryptInput = software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest.create((_10_CiphertextBlob).dtor_value, (input).dtor_EncryptionContext, (input).dtor_GrantTokens, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some((_12_KeyId).dtor_value), Wrappers_Compile.Option<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec>.create_None());
      TestComAmazonawsKms_Compile.__default.BasicDecryptTest(_13_decryptInput, (_11_Plaintext).dtor_value, (input).dtor_KeyId);
    }
    public static void BasicEncryptTest(software.amazon.cryptography.services.kms.internaldafny.types._IEncryptRequest input)
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _14_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _15_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out4;
      _out4 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _15_valueOrError0 = _out4;
      if (!(!((_15_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(141,15): " + _15_valueOrError0);}
      _14_client = (_15_valueOrError0).Extract();
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> _16_ret;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out5;
      _out5 = (_14_client).Encrypt(input);
      _16_ret = _out5;
      if (!((_16_ret).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(145,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.services.kms.internaldafny.types._IEncryptResponse _let_tmp_rhs2 = (_16_ret).dtor_value;
      Wrappers_Compile._IOption<Dafny.ISequence<byte>> _17_CiphertextBlob = _let_tmp_rhs2.dtor_CiphertextBlob;
      Wrappers_Compile._IOption<Dafny.ISequence<char>> _18_KeyId = _let_tmp_rhs2.dtor_KeyId;
      Wrappers_Compile._IOption<software.amazon.cryptography.services.kms.internaldafny.types._IEncryptionAlgorithmSpec> _19_EncryptionAlgorithm = _let_tmp_rhs2.dtor_EncryptionAlgorithm;
      if (!((_17_CiphertextBlob).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(149,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_18_KeyId).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(150,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.services.kms.internaldafny.types._IDecryptRequest _20_decryptInput;
      _20_decryptInput = software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest.create((_17_CiphertextBlob).dtor_value, (input).dtor_EncryptionContext, (input).dtor_GrantTokens, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some((_18_KeyId).dtor_value), (input).dtor_EncryptionAlgorithm);
      TestComAmazonawsKms_Compile.__default.BasicDecryptTest(_20_decryptInput, (input).dtor_Plaintext, (input).dtor_KeyId);
    }
    public static void RegionMatchTest()
    {
      software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient _21_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _22_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient, software.amazon.cryptography.services.kms.internaldafny.types._IError> _out6;
      _out6 = software.amazon.cryptography.services.kms.internaldafny.__default.KMSClient();
      _22_valueOrError0 = _out6;
      if (!(!((_22_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(170,15): " + _22_valueOrError0);}
      _21_client = (_22_valueOrError0).Extract();
      Wrappers_Compile._IOption<bool> _23_region;
      _23_region = software.amazon.cryptography.services.kms.internaldafny.__default.RegionMatch(_21_client, TestComAmazonawsKms_Compile.__default.TEST__REGION);
      if (!(((_23_region).is_None) || ((_23_region).dtor_value))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsKms/test/TestComAmazonawsKms.dfy(172,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static Dafny.ISequence<char> keyId { get {
      return Dafny.Sequence<char>.FromString("arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f");
    } }
    public static Dafny.ISequence<char> TEST__REGION { get {
      return Dafny.Sequence<char>.FromString("us-west-2");
    } }
  }
} // end of namespace TestComAmazonawsKms_Compile
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
      bool _24_success;
      _24_success = true;
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestComAmazonawsKms.BasicDecryptTests: ")));
      try {
        {
          TestComAmazonawsKms_Compile.__default.BasicDecryptTests();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _25_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_25_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _24_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestComAmazonawsKms.BasicGenerateTests: ")));
      try {
        {
          TestComAmazonawsKms_Compile.__default.BasicGenerateTests();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _26_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_26_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _24_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestComAmazonawsKms.BasicEncryptTests: ")));
      try {
        {
          TestComAmazonawsKms_Compile.__default.BasicEncryptTests();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _27_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_27_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _24_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestComAmazonawsKms.RegionMatchTest: ")));
      try {
        {
          TestComAmazonawsKms_Compile.__default.RegionMatchTest();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _28_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_28_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _24_success = false;
        }
      }
      if (!(_24_success)) {
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
