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
// Command Line Options: -stdin -noVerify -vcsCores:2 -compileTarget:cs -spillTargetCode:3 -runAllTests:1 -compile:0 -optimizeErasableDatatypeWrapper:0 -quantifierSyntax:3 -unicodeChar:0 -functionSyntax:3 -useRuntimeLib -out runtimes/net/tests/TestsFromDafny -library:/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-dafny/StandardLibrary/src/Index.dfy -library:dafny/KeyVectors/src/Index.dfy -library:dafny/TestVectorsAwsCryptographicMaterialProviders/src/Index.dfy
// the_program

method {:verify false} {:main} _Test__Main_()












































































































































module TestWrappedMaterialProvidersMain {

  import WrappedMaterialProvidersMain

  import TestManifests

  import CompleteVectors
  method {:test} ASDF()
  {
    CompleteVectors.WriteStuff();
  }

  method {:test} TestVectors()
  {
    WrappedMaterialProvidersMain.EncryptTestVectors();
    TestManifests.StartEncrypt(""dafny/TestVectorsAwsCryptographicMaterialProviders/test/test.json"", ""dafny/TestVectorsAwsCryptographicMaterialProviders/test/keys.json"");
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

module Com {

  module Amazonaws {

    
      }
}

module Aws {

  module Cryptography {

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
namespace Aws_mCryptography_Compile {

} // end of namespace Aws_mCryptography_Compile
namespace Aws_Compile {

} // end of namespace Aws_Compile
namespace Com_mAmazonaws_Compile {

} // end of namespace Com_mAmazonaws_Compile
namespace Com_Compile {

} // end of namespace Com_Compile
namespace TestWrappedMaterialProvidersMain_Compile {

  public partial class __default {
    public static void ASDF()
    {
      CompleteVectors_Compile.__default.WriteStuff();
    }
    public static void TestVectors()
    {
      WrappedMaterialProvidersMain_Compile.__default.EncryptTestVectors();
      TestManifests_Compile.__default.StartEncrypt(Dafny.Sequence<char>.FromString("dafny/TestVectorsAwsCryptographicMaterialProviders/test/test.json"), Dafny.Sequence<char>.FromString("dafny/TestVectorsAwsCryptographicMaterialProviders/test/keys.json"));
    }
  }
} // end of namespace TestWrappedMaterialProvidersMain_Compile
namespace _module {

  public partial class __default {
    public static void __Test____Main__(Dafny.ISequence<Dafny.ISequence<char>> __noArgsParameter)
    {
      bool _0_success;
      _0_success = true;
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestWrappedMaterialProvidersMain.ASDF: ")));
      try {
        {
          TestWrappedMaterialProvidersMain_Compile.__default.ASDF();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _1_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_1_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _0_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestWrappedMaterialProvidersMain.TestVectors: ")));
      try {
        {
          TestWrappedMaterialProvidersMain_Compile.__default.TestVectors();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _2_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_2_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _0_success = false;
        }
      }
      if (!(_0_success)) {
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
