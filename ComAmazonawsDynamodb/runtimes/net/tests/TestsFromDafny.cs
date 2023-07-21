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










































module TestComAmazonawsDynamoDB {

  import DDB = Com.Amazonaws.Dynamodb

  import opened UInt = StandardLibrary.UInt

  import opened Wrappers
  const tableNameTest: DDB.Types.TableName := ""KeyStoreTestTable""
  const secIndex: DDB.Types.IndexName := ""Active-Keys""

  method {:test} BasicPutGetQuery()
  {
    var client :- expect DDB.DynamoDBClient();
    var item: DDB.Types.AttributeMap := map[""branch-key-id"" := DDB.Types.AttributeValue.S(""ddb-client-test""), ""type"" := DDB.Types.AttributeValue.S(""ddb-client-test""), ""status"" := DDB.Types.AttributeValue.S(""ACTIVE"")];
    var putInput := DDB.Types.PutItemInput(Item := item, TableName := tableNameTest, Expected := None, ReturnValues := None, ReturnConsumedCapacity := None, ReturnItemCollectionMetrics := None, ConditionalOperator := None, ConditionExpression := None, ExpressionAttributeNames := None, ExpressionAttributeValues := None);
    var putRet := client.PutItem(putInput);
    expect putRet.Success?, ""expectation violation""
    var Key2Get: DDB.Types.Key := map[""branch-key-id"" := DDB.Types.AttributeValue.S(""ddb-client-test""), ""type"" := DDB.Types.AttributeValue.S(""ddb-client-test"")];
    var getInput := DDB.Types.GetItemInput(TableName := tableNameTest, Key := Key2Get, AttributesToGet := None, ConsistentRead := None, ReturnConsumedCapacity := None, ProjectionExpression := None, ExpressionAttributeNames := None);
    var getRet := client.GetItem(getInput);
    expect getRet.Success?, ""expectation violation""
    var itemOutput := getRet.value;
    expect itemOutput.Item.Some?, ""expectation violation""
    var gotItem := itemOutput.Item.value;
    expect gotItem == item, ""expectation violation""
    var attributeNameMap := map[""#status"" := ""status"", ""#branchKeyId"" := ""branch-key-id""];
    var attributeValueMap: DDB.Types.AttributeMap := map["":status"" := DDB.Types.AttributeValue.S(""ACTIVE""), "":branchKeyId"" := DDB.Types.AttributeValue.S(""ddb-client-test"")];
    var queryInput := DDB.Types.QueryInput(TableName := tableNameTest, IndexName := DDB.Wrappers.Some(secIndex), Select := DDB.Wrappers.None, AttributesToGet := DDB.Wrappers.None, Limit := DDB.Wrappers.None, ConsistentRead := DDB.Wrappers.None, KeyConditions := DDB.Wrappers.None, QueryFilter := DDB.Wrappers.None, ConditionalOperator := DDB.Wrappers.None, ScanIndexForward := DDB.Wrappers.None, ExclusiveStartKey := DDB.Wrappers.None, ReturnConsumedCapacity := DDB.Wrappers.None, ProjectionExpression := DDB.Wrappers.None, FilterExpression := DDB.Wrappers.None, KeyConditionExpression := DDB.Wrappers.Some(""#status = :status and #branchKeyId = :branchKeyId""), ExpressionAttributeNames := DDB.Wrappers.Some(attributeNameMap), ExpressionAttributeValues := DDB.Wrappers.Some(attributeValueMap));
    var queryRet := client.Query(queryInput);
    expect queryRet.Success?, ""expectation violation""
    var queryOutput := queryRet.value;
    expect queryOutput.Items.Some?, ""expectation violation""
    var queryItem := queryOutput.Items.value;
    expect |queryItem| == 1, ""expectation violation""
    var queriedItem := queryItem[0];
    expect item == queriedItem, ""expectation violation""
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
namespace TestComAmazonawsDynamoDB_Compile {

  public partial class __default {
    public static void BasicPutGetQuery()
    {
      software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient _0_client;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _1_valueOrError0 = default(Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError>);
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out0;
      _out0 = software.amazon.cryptography.services.dynamodb.internaldafny.__default.DynamoDBClient();
      _1_valueOrError0 = _out0;
      if (!(!((_1_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsDynamodb/test/TestComAmazonawsDynamodb.dfy(20,15): " + _1_valueOrError0);}
      _0_client = (_1_valueOrError0).Extract();
      Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue> _2_item;
      _2_item = Dafny.Map<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>.FromElements(new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Dafny.Sequence<char>.FromString("branch-key-id"), software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(Dafny.Sequence<char>.FromString("ddb-client-test"))), new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Dafny.Sequence<char>.FromString("type"), software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(Dafny.Sequence<char>.FromString("ddb-client-test"))), new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Dafny.Sequence<char>.FromString("status"), software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(Dafny.Sequence<char>.FromString("ACTIVE"))));
      software.amazon.cryptography.services.dynamodb.internaldafny.types._IPutItemInput _3_putInput;
      _3_putInput = software.amazon.cryptography.services.dynamodb.internaldafny.types.PutItemInput.create(TestComAmazonawsDynamoDB_Compile.__default.tableNameTest, _2_item, Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IExpectedAttributeValue>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnValue>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnConsumedCapacity>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnItemCollectionMetrics>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IConditionalOperator>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>>.create_None());
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IPutItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _4_putRet;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IPutItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out1;
      _out1 = (_0_client).PutItem(_3_putInput);
      _4_putRet = _out1;
      if (!((_4_putRet).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsDynamodb/test/TestComAmazonawsDynamodb.dfy(44,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue> _5_Key2Get;
      _5_Key2Get = Dafny.Map<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>.FromElements(new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Dafny.Sequence<char>.FromString("branch-key-id"), software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(Dafny.Sequence<char>.FromString("ddb-client-test"))), new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Dafny.Sequence<char>.FromString("type"), software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(Dafny.Sequence<char>.FromString("ddb-client-test"))));
      software.amazon.cryptography.services.dynamodb.internaldafny.types._IGetItemInput _6_getInput;
      _6_getInput = software.amazon.cryptography.services.dynamodb.internaldafny.types.GetItemInput.create(TestComAmazonawsDynamoDB_Compile.__default.tableNameTest, _5_Key2Get, Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<bool>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnConsumedCapacity>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.create_None());
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IGetItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _7_getRet;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IGetItemOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out2;
      _out2 = (_0_client).GetItem(_6_getInput);
      _7_getRet = _out2;
      if (!((_7_getRet).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsDynamodb/test/TestComAmazonawsDynamodb.dfy(63,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.services.dynamodb.internaldafny.types._IGetItemOutput _8_itemOutput;
      _8_itemOutput = (_7_getRet).dtor_value;
      if (!(((_8_itemOutput).dtor_Item).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsDynamodb/test/TestComAmazonawsDynamodb.dfy(66,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue> _9_gotItem;
      _9_gotItem = ((_8_itemOutput).dtor_Item).dtor_value;
      if (!((_9_gotItem).Equals(_2_item))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsDynamodb/test/TestComAmazonawsDynamodb.dfy(68,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>> _10_attributeNameMap;
      _10_attributeNameMap = Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.FromElements(new Dafny.Pair<Dafny.ISequence<char>, Dafny.ISequence<char>>(Dafny.Sequence<char>.FromString("#status"), Dafny.Sequence<char>.FromString("status")), new Dafny.Pair<Dafny.ISequence<char>, Dafny.ISequence<char>>(Dafny.Sequence<char>.FromString("#branchKeyId"), Dafny.Sequence<char>.FromString("branch-key-id")));
      Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue> _11_attributeValueMap;
      _11_attributeValueMap = Dafny.Map<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>.FromElements(new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Dafny.Sequence<char>.FromString(":status"), software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(Dafny.Sequence<char>.FromString("ACTIVE"))), new Dafny.Pair<Dafny.ISequence<char>, software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>(Dafny.Sequence<char>.FromString(":branchKeyId"), software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.create_S(Dafny.Sequence<char>.FromString("ddb-client-test"))));
      software.amazon.cryptography.services.dynamodb.internaldafny.types._IQueryInput _12_queryInput;
      _12_queryInput = software.amazon.cryptography.services.dynamodb.internaldafny.types.QueryInput.create(TestComAmazonawsDynamoDB_Compile.__default.tableNameTest, Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(TestComAmazonawsDynamoDB_Compile.__default.secIndex), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._ISelect>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None(), Wrappers_Compile.Option<int>.create_None(), Wrappers_Compile.Option<bool>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._ICondition>>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._ICondition>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IConditionalOperator>.create_None(), Wrappers_Compile.Option<bool>.create_None(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>>.create_None(), Wrappers_Compile.Option<software.amazon.cryptography.services.dynamodb.internaldafny.types._IReturnConsumedCapacity>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None(), Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(Dafny.Sequence<char>.FromString("#status = :status and #branchKeyId = :branchKeyId")), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.create_Some(_10_attributeNameMap), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>>.create_Some(_11_attributeValueMap));
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IQueryOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _13_queryRet;
      Wrappers_Compile._IResult<software.amazon.cryptography.services.dynamodb.internaldafny.types._IQueryOutput, software.amazon.cryptography.services.dynamodb.internaldafny.types._IError> _out3;
      _out3 = (_0_client).Query(_12_queryInput);
      _13_queryRet = _out3;
      if (!((_13_queryRet).is_Success)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsDynamodb/test/TestComAmazonawsDynamodb.dfy(103,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      software.amazon.cryptography.services.dynamodb.internaldafny.types._IQueryOutput _14_queryOutput;
      _14_queryOutput = (_13_queryRet).dtor_value;
      if (!(((_14_queryOutput).dtor_Items).is_Some)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsDynamodb/test/TestComAmazonawsDynamodb.dfy(106,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue>> _15_queryItem;
      _15_queryItem = ((_14_queryOutput).dtor_Items).dtor_value;
      if (!((new BigInteger((_15_queryItem).Count)) == (BigInteger.One))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsDynamodb/test/TestComAmazonawsDynamodb.dfy(108,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.IMap<Dafny.ISequence<char>,software.amazon.cryptography.services.dynamodb.internaldafny.types._IAttributeValue> _16_queriedItem;
      _16_queriedItem = (_15_queryItem).Select(BigInteger.Zero);
      if (!((_2_item).Equals(_16_queriedItem))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/ComAmazonawsDynamodb/test/TestComAmazonawsDynamodb.dfy(110,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static Dafny.ISequence<char> tableNameTest { get {
      return Dafny.Sequence<char>.FromString("KeyStoreTestTable");
    } }
    public static Dafny.ISequence<char> secIndex { get {
      return Dafny.Sequence<char>.FromString("Active-Keys");
    } }
  }
} // end of namespace TestComAmazonawsDynamoDB_Compile
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
      bool _17_success;
      _17_success = true;
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestComAmazonawsDynamoDB.BasicPutGetQuery: ")));
      try {
        {
          TestComAmazonawsDynamoDB_Compile.__default.BasicPutGetQuery();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _18_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_18_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _17_success = false;
        }
      }
      if (!(_17_success)) {
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
