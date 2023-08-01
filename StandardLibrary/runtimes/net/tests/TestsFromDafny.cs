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
// Command Line Options: -stdin -noVerify -vcsCores:2 -compileTarget:cs -spillTargetCode:3 -runAllTests:1 -compile:0 -optimizeErasableDatatypeWrapper:0 -quantifierSyntax:3 -unicodeChar:0 -functionSyntax:3 -useRuntimeLib -out runtimes/net/tests/TestsFromDafny -library:src/Index.dfy
// the_program

method {:verify false} {:main} _Test__Main_()







































module TestUUID {

  import opened UUID

  import opened UInt = StandardLibrary.UInt
  const uuid := ""92382658-b7a0-4d97-9c49-cee4e672a3b3""
  const byteUuid: seq<uint8> := [146, 56, 38, 88, 183, 160, 77, 151, 156, 73, 206, 228, 230, 114, 163, 179]
  const wrongByteUuid: seq<uint8> := [146, 56, 38, 88, 183, 160, 77, 151, 156, 73, 206, 228, 230, 114, 163, 178]

  method {:test} TestFromBytesSuccess()
  {
    var fromBytes :- expect UUID.FromByteArray(byteUuid);
    expect fromBytes == uuid, ""expectation violation""
  }

  method {:test} TestFromBytesFailure()
  {
    var fromBytes :- expect UUID.FromByteArray(wrongByteUuid);
    expect fromBytes != uuid, ""expectation violation""
  }

  method {:test} TestToBytesSuccess()
  {
    var toBytes :- expect UUID.ToByteArray(uuid);
    expect toBytes == byteUuid, ""expectation violation""
  }

  method {:test} TestToBytesFailure()
  {
    var toBytes :- expect UUID.ToByteArray(uuid);
    expect toBytes != wrongByteUuid, ""expectation violation""
  }

  method {:test} TestRoundTripStringConversion()
  {
    var stringToBytes :- expect UUID.ToByteArray(uuid);
    expect |stringToBytes| == 16, ""expectation violation""
    var bytesToString :- expect UUID.FromByteArray(stringToBytes);
    expect bytesToString == uuid, ""expectation violation""
  }

  method {:test} TestRoundTripByteConversion()
  {
    var bytesToString :- expect UUID.FromByteArray(byteUuid);
    var stringToBytes :- expect UUID.ToByteArray(bytesToString);
    expect |stringToBytes| == 16, ""expectation violation""
    expect stringToBytes == byteUuid, ""expectation violation""
  }

  method {:test} TestGenerateAndConversion()
  {
    var uuidString :- expect UUID.GenerateUUID();
    var uuidBytes :- expect UUID.ToByteArray(uuidString);
    var bytesToString :- expect UUID.FromByteArray(uuidBytes);
    var stringToBytes :- expect UUID.ToByteArray(bytesToString);
    expect |stringToBytes| == 16, ""expectation violation""
    expect stringToBytes == uuidBytes, ""expectation violation""
    var uuidStringToBytes :- expect UUID.ToByteArray(uuidString);
    expect |uuidStringToBytes| == 16, ""expectation violation""
    var uuidBytesToString :- expect UUID.FromByteArray(uuidStringToBytes);
    expect uuidBytesToString == uuidString, ""expectation violation""
  }
}

module TestCallMany {

  import opened StandardLibrary

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened BoundedInts

  import ConcurrentCall
  class MyCallee extends ConcurrentCall.Callee {
    var count: uint32

    constructor ()
      ensures ValidState()
    {
      count := 0;
      Modifies := {this};
    }

    predicate ValidState()
      reads this
      decreases {this}
    {
      this in Modifies
    }

    method call(nameonly serialPos: uint32, nameonly concurrentPos: uint32)
      requires ValidState()
      modifies Modifies
      ensures ValidState()
      decreases serialPos, concurrentPos
    {
      if count < UINT32_MAX {
        count := count + 1;
      }
    }
  }

  method {:test} TestBasic()
  {
    var c := new MyCallee();
    ConcurrentCall.ConcurrentCall(callee := c, serialIters := 2, concurrentIters := 3);
    expect c.count == 6, ""expectation violation""
  }
}

module FloatCompareTest {

  import opened Wrappers

  import opened FloatCompare
  const NEGATIVE_TWO := [""-2"", ""-2."", ""-2.0"", ""-2e0"", ""-2.e0"", ""-2.0e0"", ""-2.0e+0"", ""-2.0e-0"", ""-.2e1"", ""-0.2e1"", ""-0.2e+1"", ""-0.02e2"", ""-20e-1"", ""-20.e-1"", ""-200.0e-2""]
  const NEGATIVE_ONE := [""-1"", ""-1."", ""-1.0"", ""-1e0"", ""-1.e0"", ""-1.0e0"", ""-1.0e+0"", ""-1.0e-0"", ""-.1e1"", ""-0.1e1"", ""-0.1e+1"", ""-0.01e2"", ""-10e-1"", ""-10.e-1"", ""-100.0e-2""]
  const ZERO := [""0"", ""+0"", ""-0"", ""0."", ""+0."", ""-0."", ""00"", ""+00"", ""-00"", ""0.0"", ""+0.0"", ""-0.0"", ""00.00"", ""+00.00"", ""-00.00"", "".0"", ""+.0"", ""-.0"", ""0e0"", ""+0e0"", ""+0e+0"", ""+0e-0"", ""-0e0"", ""-0e+0"", ""-0e-0"", ""0e-99"", ""+0e-99"", ""-0e-99"", ""0e99"", ""+0e99"", ""-0e99"", ""0e+99"", ""+0e+99"", ""-0e+99""]
  const ONE := [""1"", ""1."", ""1.0"", ""1e0"", ""1.e0"", ""1.0e0"", ""1.0e+0"", ""1.0e-0"", "".1e1"", ""0.1e1"", ""0.1e+1"", ""0.01e2"", ""10e-1"", ""10.e-1"", ""100.0e-2"", ""+1"", ""+1."", ""+1.0"", ""+1e0"", ""+1.e0"", ""+1.0e0"", ""+1.0e+0"", ""+1.0e-0"", ""+.1e1"", ""+0.1e1"", ""+0.1e+1"", ""+0.01e2"", ""+10e-1"", ""+10.e-1"", ""+100.0e-2""]
  const TWO := [""2"", ""2."", ""2.0"", ""2e0"", ""2.e0"", ""2.0e0"", ""2.0e+0"", ""2.0e-0"", "".2e1"", ""0.2e1"", ""0.2e+1"", ""0.02e2"", ""20e-1"", ""20.e-1"", ""200.0e-2"", ""+2"", ""+2."", ""+2.0"", ""+2e0"", ""+2.e0"", ""+2.0e0"", ""+2.0e+0"", ""+2.0e-0"", ""+.2e1"", ""+0.2e1"", ""+0.2e+1"", ""+0.02e2"", ""+20e-1"", ""+20.e-1"", ""+200.0e-2""]

  method TestCompareFloat(x: string, y: string, ret: CompareType)
    ensures CompareFloat(x, y) == ret
    ensures CompareFloat(y, x) == -ret
    decreases x, y, ret
  {
    if CompareFloat(x, y) != ret {
      print ""CompareFloat("", x, "", "", y, "") was "", CompareFloat(x, y), "" but should have been "", ret, ""\n"";
    }
    if CompareFloat(y, x) != -ret {
      print ""CompareFloat("", y, "", "", x, "") was "", CompareFloat(y, x), "" but should have been "", -ret, ""\n"";
    }
    expect CompareFloat(x, y) == ret, ""expectation violation""
    expect CompareFloat(y, x) == -ret, ""expectation violation""
  }

  method {:test} TestOneTwoZeroMatrix()
  {
    for i: int := 0 to |NEGATIVE_TWO| {
      var negativeTwo := NEGATIVE_TWO[i];
      for j: int := i to |NEGATIVE_TWO| {
        TestCompareFloat(NEGATIVE_TWO[j], negativeTwo, Equal);
      }
      for j: int := 0 to |NEGATIVE_ONE| {
        TestCompareFloat(NEGATIVE_ONE[j], negativeTwo, Greater);
      }
      for j: int := 0 to |ZERO| {
        TestCompareFloat(ZERO[j], negativeTwo, Greater);
      }
      for j: int := 0 to |ONE| {
        TestCompareFloat(ONE[j], negativeTwo, Greater);
      }
      for j: int := 0 to |TWO| {
        TestCompareFloat(TWO[j], negativeTwo, Greater);
      }
    }
    for i: int := 0 to |NEGATIVE_ONE| {
      var negativeOne := NEGATIVE_ONE[i];
      for j: int := i to |NEGATIVE_ONE| {
        TestCompareFloat(NEGATIVE_ONE[j], negativeOne, Equal);
      }
      for j: int := 0 to |ZERO| {
        TestCompareFloat(ZERO[j], negativeOne, Greater);
      }
      for j: int := 0 to |ONE| {
        TestCompareFloat(ONE[j], negativeOne, Greater);
      }
      for j: int := 0 to |TWO| {
        TestCompareFloat(TWO[j], negativeOne, Greater);
      }
    }
    for i: int := 0 to |ZERO| {
      var zero := ZERO[i];
      for j: int := i to |ZERO| {
        TestCompareFloat(ZERO[j], zero, Equal);
      }
      for j: int := 0 to |ONE| {
        TestCompareFloat(ONE[j], zero, Greater);
      }
      for j: int := 0 to |TWO| {
        TestCompareFloat(TWO[j], zero, Greater);
      }
    }
    for i: int := 0 to |ONE| {
      var one := ONE[i];
      for j: int := i to |ONE| {
        TestCompareFloat(ONE[j], one, Equal);
      }
      for j: int := 0 to |TWO| {
        TestCompareFloat(TWO[j], one, Greater);
      }
    }
    for i: int := 0 to |TWO| {
      var two := TWO[i];
      for j: int := i to |TWO| {
        TestCompareFloat(TWO[j], two, Equal);
      }
    }
  }

  method {:test} SimpleTests()
  {
    TestCompareFloat(""1"", ""1"", Equal);
    TestCompareFloat(""2"", ""1"", Greater);
    TestCompareFloat(""1.1"", ""1.2"", Less);
    TestCompareFloat(""1.2"", ""1.2"", Equal);
    TestCompareFloat(""1.35"", ""1.357"", Less);
    TestCompareFloat(""1.35e2"", ""13.5e1"", Equal);
    TestCompareFloat(""1.351e2"", ""13.5e1"", Greater);
    TestCompareFloat(""1.35e-1"", ""13.5e-2"", Equal);
    TestCompareFloat(""1"", ""-2"", Greater);
    TestCompareFloat(""1.2e7"", ""2.3e2"", Greater);
    TestCompareFloat(""-1.2e7"", ""2.3e2"", Less);
    TestCompareFloat(""1.2e7"", ""-2.3e2"", Greater);
    TestCompareFloat(""-1.2e7"", ""-2.3e2"", Less);
  }

  method {:test} SignTests()
  {
    TestCompareFloat(""+1"", ""1"", Equal);
    TestCompareFloat(""+1e+0"", ""1"", Equal);
    TestCompareFloat(""+1e-0"", ""1"", Equal);
    TestCompareFloat(""-1"", ""1"", Less);
    TestCompareFloat(""-1"", ""+1"", Less);
    TestCompareFloat(""1"", ""-1"", Greater);
    TestCompareFloat(""+1"", ""-1"", Greater);
  }

  method {:test} ExponentTests()
  {
    TestCompareFloat(""2e0"", ""2e0"", Equal);
    TestCompareFloat(""1e0"", ""2e0"", Less);
    TestCompareFloat(""3e0"", ""2e0"", Greater);
    TestCompareFloat(""1e-5"", ""1e5"", Less);
    TestCompareFloat(""1e5"", ""1e-5"", Greater);
    TestCompareFloat(""1e5"", ""1e6"", Less);
    TestCompareFloat(""1e5"", ""1e4"", Greater);
    TestCompareFloat(""1e-5"", ""1e-4"", Less);
    TestCompareFloat(""1e-5"", ""1e-6"", Greater);
    TestCompareFloat(""-1e5"", ""-1e-5"", Less);
    TestCompareFloat(""-1e-5"", ""-1e5"", Greater);
    TestCompareFloat(""-1e5"", ""-1e4"", Less);
    TestCompareFloat(""-1e5"", ""-1e6"", Greater);
    TestCompareFloat(""-1e-5"", ""-1e-6"", Less);
    TestCompareFloat(""-1e-5"", ""-1e-4"", Greater);
    TestCompareFloat(""2"", ""2e0"", Equal);
    TestCompareFloat(""1"", ""2e0"", Less);
    TestCompareFloat(""3"", ""2e0"", Greater);
    TestCompareFloat(""20"", ""2e1"", Equal);
    TestCompareFloat(""19"", ""2e1"", Less);
    TestCompareFloat(""21"", ""2e1"", Greater);
    TestCompareFloat(""-20"", ""-2e1"", Equal);
    TestCompareFloat(""-21"", ""-2e1"", Less);
    TestCompareFloat(""-19"", ""-2e1"", Greater);
    TestCompareFloat(""0.2"", ""2e-1"", Equal);
    TestCompareFloat(""0.02"", ""2e-2"", Equal);
    TestCompareFloat(""0.02"", "".2e-1"", Equal);
    TestCompareFloat("".1"", ""2e-1"", Less);
    TestCompareFloat("".3"", ""2e-1"", Greater);
    TestCompareFloat(""-0.2"", ""-2e-1"", Equal);
    TestCompareFloat(""-0.02"", ""-2e-2"", Equal);
    TestCompareFloat(""-0.02"", ""-.2e-1"", Equal);
    TestCompareFloat(""-.3"", ""-2e-1"", Less);
    TestCompareFloat(""-.1"", ""-2e-1"", Greater);
  }

  method {:test} ZeroTests()
  {
    TestCompareFloat(""-0"", ""0"", Equal);
    TestCompareFloat(""+0"", ""0"", Equal);
    TestCompareFloat(""00"", ""0"", Equal);
    TestCompareFloat(""0.0"", ""0"", Equal);
    TestCompareFloat(""0"", ""000"", Equal);
    TestCompareFloat(""0"", "".000"", Equal);
    TestCompareFloat(""0.0"", ""000.00000"", Equal);
    TestCompareFloat(""0"", ""000.000e0"", Equal);
    TestCompareFloat(""0"", ""0e+0"", Equal);
    TestCompareFloat(""0"", ""0e-0"", Equal);
    TestCompareFloat(""0"", ""0e99"", Equal);
    TestCompareFloat(""0"", ""0e-99"", Equal);
    TestCompareFloat(""0e+99"", ""0e-99"", Equal);
    TestCompareFloat(""+0e+99"", ""-0e-99"", Equal);
    TestCompareFloat(""-0e+99"", ""-0e-99"", Equal);
    TestCompareFloat(""-0e+99"", ""+0e-99"", Equal);
    TestCompareFloat(""01"", ""1"", Equal);
    TestCompareFloat(""1"", ""001"", Equal);
    TestCompareFloat(""1.0"", ""001.00000"", Equal);
  }

  method {:test} ExtremeNumTest()
  {
    TestCompareFloat(""123456789.01234567890123456789012345678"", ""123456789.01234567890123456789012345678"", Equal);
    TestCompareFloat(""1234567890123456789012345678901234567800000000000000000000000000000"", ""1234567890123456789012345678901234567800000000000000000000000000000"", Equal);
    TestCompareFloat("".000000000000000000000000012345678901234567890123456789012345678"", ""0.000000000000000000000000012345678901234567890123456789012345678"", Equal);
    TestCompareFloat(""123456789.01234567890123456789012345676"", ""123456789.01234567890123456789012345678"", Less);
    TestCompareFloat(""123456789.01234567890123456789012345675"", ""123456789.01234567890123456789012345676"", Less);
    TestCompareFloat(""123456789.01234567890123456789012345679"", ""123456789.01234567890123456789012345678"", Greater);
    TestCompareFloat(""123456789.01234567890123456789012345677"", ""123456789.01234567890123456789012345676"", Greater);
    TestCompareFloat(""-123456789.01234567890123456789012345678"", ""123456789.01234567890123456789012345678"", Less);
    TestCompareFloat(""123456789.01234567890123456789012345678"", ""-123456789.01234567890123456789012345678"", Greater);
    TestCompareFloat(""0000000000000000000000000012345.67e121"", ""123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Equal);
    TestCompareFloat(""12345.67e121"", ""123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Equal);
    TestCompareFloat(""0.00000001e133"", ""100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Equal);
    TestCompareFloat(""0.00000001e-122"", ""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Equal);
    TestCompareFloat(""1234567e-136"", ""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001234567"", Equal);
    TestCompareFloat(""0000000000000000000000000012345.66e121"", ""123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Less);
    TestCompareFloat(""0000000000000000000000000012345.68e121"", ""123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Greater);
    TestCompareFloat(""12345.67e120"", ""12345.67e121"", Less);
    TestCompareFloat(""12345.67e122"", ""12345.67e121"", Greater);
    TestCompareFloat(""-12345.67e122"", ""-12345.67e121"", Less);
    TestCompareFloat(""-12345.67e120"", ""-12345.67e121"", Greater);
    TestCompareFloat(""12345.67e120"", ""123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Less);
    TestCompareFloat(""12345.67e122"", ""123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Greater);
    TestCompareFloat(""-12345.67e122"", ""-123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Less);
    TestCompareFloat(""-12345.67e120"", ""-123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Greater);
    TestCompareFloat(""0.00000001e-123"", ""0.00000001e-122"", Less);
    TestCompareFloat(""0.00000001e-121"", ""0.00000001e-122"", Greater);
    TestCompareFloat(""-0.00000001e-121"", ""-0.00000001e-122"", Less);
    TestCompareFloat(""-0.00000001e-123"", ""-0.00000001e-122"", Greater);
    TestCompareFloat(""0.00000001e-123"", ""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Less);
    TestCompareFloat(""0.00000001e-121"", ""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Greater);
    TestCompareFloat(""-0.00000001e-121"", ""-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Less);
    TestCompareFloat(""-0.00000001e-123"", ""-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Greater);
    TestCompareFloat(""9.9999999999999999999999999999999999999E+125"", ""999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Equal);
    TestCompareFloat("".99999999999999999999999999999999999999E+126"", ""999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Equal);
    TestCompareFloat(""999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", ""999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Equal);
    TestCompareFloat(""9.9999999999999999999999999999999999999E+124"", ""999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Less);
    TestCompareFloat(""9.9999999999999999999999999999999999999E+126"", ""999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Greater);
    TestCompareFloat(""999999999999999999999999999999999999989999999999999999999999999999999999999999999999999999999999999999999999999999999999999999"", ""999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Less);
    TestCompareFloat(""999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", ""999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Greater);
    TestCompareFloat(""1E-130"", ""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Equal);
    TestCompareFloat(""10E-131"", ""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Equal);
    TestCompareFloat(""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", ""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Equal);
    TestCompareFloat(""1E-131"", ""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Less);
    TestCompareFloat(""1E-129"", ""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Greater);
    TestCompareFloat(""0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009"", ""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Less);
    TestCompareFloat(""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"", ""0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Greater);
    TestCompareFloat(""-9.9999999999999999999999999999999999999E+125"", ""-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Equal);
    TestCompareFloat(""-.99999999999999999999999999999999999999E+126"", ""-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Equal);
    TestCompareFloat(""-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", ""-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Equal);
    TestCompareFloat(""-9.9999999999999999999999999999999999999E+126"", ""-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Less);
    TestCompareFloat(""-9.9999999999999999999999999999999999999E+124"", ""-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Greater);
    TestCompareFloat(""-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", ""-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Less);
    TestCompareFloat(""-99999999999999999999999999999999999998999999999999999999999999999999999999999999999999999999999999999999999999999999999999999"", ""-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"", Greater);
    TestCompareFloat(""-1E-130"", ""-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Equal);
    TestCompareFloat(""-10E-131"", ""-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Equal);
    TestCompareFloat(""-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", ""-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Equal);
    TestCompareFloat(""-1E-129"", ""-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Less);
    TestCompareFloat(""-1E-131"", ""-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Greater);
    TestCompareFloat(""-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"", ""-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Less);
    TestCompareFloat(""-0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009"", ""-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"", Greater);
  }

  method {:test} InvalidTests()
  {
    TestCompareFloat(""a"", ""0"", Equal);
    TestCompareFloat(""a"", ""b"", Equal);
  }
}

module TestSeqReaderReadElements {

  import opened StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import opened SortedSets
  predicate method UInt8Greater(x: uint8, y: uint8)
    decreases x, y
  {
    y < x
  }

  method {:test} TestSetToOrderedSequenceEmpty()
  {
    var output := ComputeSetToOrderedSequence({}, UInt8Less);
    var expected := [];
    expect output == expected, ""expectation violation""
  }

  method {:test} TestSetToOrderedSequenceOneItem()
  {
    var a := {[0]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0]];
    expect output == expected, ""expectation violation""
  }

  method {:test} TestSetToOrderedSequenceSimple()
  {
    var a := {[0, 2], [0, 1]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0, 1], [0, 2]];
    expect output == expected, ""expectation violation""
  }

  method {:test} TestSetToOrderedSequencePrefix()
  {
    var a := {[0, 1, 2], [0, 1]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0, 1], [0, 1, 2]];
    expect output == expected, ""expectation violation""
  }

  method {:test} TestSetToOrderedSequenceComplex()
  {
    var a := {[0, 1, 2], [1, 1, 2], [0, 1]};
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected := [[0, 1], [0, 1, 2], [1, 1, 2]];
    expect output == expected, ""expectation violation""
  }

  method {:test} TestSetToOrderedSequenceComplexReverse()
  {
    var a := {[0, 1, 2], [1, 1, 2], [0, 1]};
    var output := ComputeSetToOrderedSequence(a, UInt8Greater);
    var expected := [[1, 1, 2], [0, 1], [0, 1, 2]];
    expect output == expected, ""expectation violation""
  }

  method {:test} TestSetSequence()
  {
    var a := {[0, 1, 2], [1, 1, 2], [0, 1]};
    var output := ComputeSetToSequence(a);
    expect multiset(output) == multiset(a), ""expectation violation""
  }

  method {:test} TestSetToOrderedSequenceManyItems()
  {
    var a := set x: uint16 {:trigger UInt16ToSeq(x)} | 0 <= x < 65535 :: UInt16ToSeq(x);
    var output := ComputeSetToOrderedSequence(a, UInt8Less);
    var expected: seq<seq<uint8>> := seq(65535, (i: int) requires 0 <= i < 65535 => UInt16ToSeq(i as uint16));
    expect output == expected, ""expectation violation""
  }
}

module {:options ""-functionSyntax:4""} Sets {

  import opened Functions

  import opened Relations
  lemma LemmaSubset<T>(x: set<T>, y: set<T>)
    requires forall e: T {:trigger e in y} :: e in x ==> e in y
    ensures x <= y
    decreases x, y
  {
  }

  lemma LemmaSubsetSize<T>(x: set<T>, y: set<T>)
    ensures x < y ==> |x| < |y|
    ensures x <= y ==> |x| <= |y|
    decreases x, y
  {
  }

  lemma LemmaSubsetEquality<T>(x: set<T>, y: set<T>)
    requires x <= y
    requires |x| == |y|
    ensures x == y
    decreases x, y
  {
  }

  lemma LemmaSingletonSize<T>(x: set<T>, e: T)
    requires x == {e}
    ensures |x| == 1
    decreases x
  {
  }

  lemma LemmaSingletonEquality<T>(x: set<T>, a: T, b: T)
    requires |x| == 1
    requires a in x
    requires b in x
    ensures a == b
    decreases x
  {
  }

  predicate IsSingleton<T>(s: set<T>)
    decreases s
  {
    (exists x: T {:trigger x in s} :: 
      x in s) &&
    forall x: T, y: T {:trigger y in s, x in s} | x in s && y in s :: 
      x == y
  }

  lemma LemmaIsSingleton<T>(s: set<T>)
    ensures |s| == 1 <==> IsSingleton(s)
    decreases s
  {
  }

  function ExtractFromNonEmptySet<T>(s: set<T>): (x: T)
    requires |s| != 0
    ensures x in s
    decreases s
  {
    ghost var x: T :| x in s;
    x
  }

  function method ExtractFromSingleton<T>(s: set<T>): (x: T)
    requires |s| == 1
    ensures s == {x}
    decreases s
  {
    LemmaIsSingleton(s);
    var x: T :| x in s;
    x
  }

  lemma LemmaMapSize<X(!new), Y>(xs: set<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    requires forall x: X {:trigger f(x)} :: x in xs <==> f(x) in ys
    requires forall y: Y {:trigger y in ys} :: y in ys ==> exists x: X {:trigger f(x)} {:trigger x in xs} :: x in xs && y == f(x)
    ensures |xs| == |ys|
    decreases xs, ys
  {
  }

  function method {:opaque} {:fuel 0, 0} Map<X(!new), Y>(xs: set<X>, f: X --> Y): (ys: set<Y>)
    requires forall x: X {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    reads set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    ensures forall x: X {:trigger f(x)} :: x in xs <==> f(x) in ys
    ensures |xs| == |ys|
    decreases set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj, xs
  {
    var ys: set<Y> := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs :: f(x);
    LemmaMapSize(xs, ys, f);
    ys
  }

  lemma LemmaFilterSize<X>(xs: set<X>, ys: set<X>, f: X ~> bool)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    requires forall y: X {:trigger f(y)} {:trigger y in xs} :: (y in ys ==> y in xs) && (y in ys ==> f(y))
    ensures |ys| <= |xs|
    decreases xs, ys
  {
  }

  function method {:opaque} {:fuel 0, 0} Filter<X(!new)>(xs: set<X>, f: X ~> bool): (ys: set<X>)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    reads set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    ensures forall y: X {:trigger f(y)} {:trigger y in xs} :: y in ys <==> y in xs && f(y)
    ensures |ys| <= |xs|
    decreases set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj, xs
  {
    var ys: set<X> := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs && f(x);
    LemmaFilterSize(xs, ys, f);
    ys
  }

  lemma LemmaUnionSize<X>(xs: set<X>, ys: set<X>)
    ensures |xs + ys| >= |xs|
    ensures |xs + ys| >= |ys|
    decreases xs, ys
  {
  }

  function method {:opaque} {:fuel 0, 0} SetRange(a: int, b: int): (s: set<int>)
    requires a <= b
    ensures forall i: int {:trigger i in s} :: a <= i < b <==> i in s
    ensures |s| == b - a
    decreases b - a
  {
    if a == b then
      {}
    else
      {a} + SetRange(a + 1, b)
  }

  function method {:opaque} {:fuel 0, 0} SetRangeZeroBound(n: int): (s: set<int>)
    requires n >= 0
    ensures forall i: int {:trigger i in s} :: 0 <= i < n <==> i in s
    ensures |s| == n
    decreases n
  {
    SetRange(0, n)
  }

  lemma LemmaBoundedSetSize(x: set<int>, a: int, b: int)
    requires forall i: int {:trigger i in x} :: (i in x ==> a <= i) && (i in x ==> i < b)
    requires a <= b
    ensures |x| <= b - a
    decreases x, a, b
  {
  }

  lemma LemmaGreatestImpliesMaximal<T(!new)>(R: (T, T) -> bool, max: T, s: set<T>)
    requires PreOrdering(R)
    ensures IsGreatest(R, max, s) ==> IsMaximal(R, max, s)
    decreases s
  {
  }

  lemma LemmaLeastImpliesMinimal<T(!new)>(R: (T, T) -> bool, min: T, s: set<T>)
    requires PreOrdering(R)
    ensures IsLeast(R, min, s) ==> IsMinimal(R, min, s)
    decreases s
  {
  }

  lemma LemmaMaximalEquivalentGreatest<T(!new)>(R: (T, T) -> bool, max: T, s: set<T>)
    requires TotalOrdering(R)
    ensures IsGreatest(R, max, s) <==> IsMaximal(R, max, s)
    decreases s
  {
  }

  lemma LemmaMinimalEquivalentLeast<T(!new)>(R: (T, T) -> bool, min: T, s: set<T>)
    requires TotalOrdering(R)
    ensures IsLeast(R, min, s) <==> IsMinimal(R, min, s)
    decreases s
  {
  }

  lemma LemmaLeastIsUnique<T(!new)>(R: (T, T) -> bool, s: set<T>)
    requires PartialOrdering(R)
    ensures forall min: T, min': T {:trigger IsLeast(R, min', s), IsLeast(R, min, s)} | IsLeast(R, min, s) && IsLeast(R, min', s) :: min == min'
    decreases s
  {
  }

  lemma LemmaGreatestIsUnique<T(!new)>(R: (T, T) -> bool, s: set<T>)
    requires PartialOrdering(R)
    ensures forall max: T, max': T {:trigger IsGreatest(R, max', s), IsGreatest(R, max, s)} | IsGreatest(R, max, s) && IsGreatest(R, max', s) :: max == max'
    decreases s
  {
  }

  lemma LemmaMinimalIsUnique<T(!new)>(R: (T, T) -> bool, s: set<T>)
    requires TotalOrdering(R)
    ensures forall min: T, min': T {:trigger IsMinimal(R, min', s), IsMinimal(R, min, s)} | IsMinimal(R, min, s) && IsMinimal(R, min', s) :: min == min'
    decreases s
  {
  }

  lemma LemmaMaximalIsUnique<T(!new)>(R: (T, T) -> bool, s: set<T>)
    requires TotalOrdering(R)
    ensures forall max: T, max': T {:trigger IsMaximal(R, max', s), IsMaximal(R, max, s)} | IsMaximal(R, max, s) && IsMaximal(R, max', s) :: max == max'
    decreases s
  {
  }

  lemma LemmaFindUniqueMinimal<T(!new)>(R: (T, T) -> bool, s: set<T>) returns (min: T)
    requires |s| > 0 && TotalOrdering(R)
    ensures IsMinimal(R, min, s) && forall min': T {:trigger IsMinimal(R, min', s)} | IsMinimal(R, min', s) :: min == min'
    decreases s
  {
  }

  lemma LemmaFindUniqueMaximal<T(!new)>(R: (T, T) -> bool, s: set<T>) returns (max: T)
    requires |s| > 0 && TotalOrdering(R)
    ensures IsMaximal(R, max, s) && forall max': T {:trigger IsMaximal(R, max', s)} | IsMaximal(R, max', s) :: max == max'
    decreases s
  {
  }
}

module TestHexStrings {

  import opened HexStrings
  method {:test} BasicTests()
  {
    expect ToHexString([1, 2, 255]) == ""0102ff"", ""expectation violation""
    expect FromHexString(""0102ff"") == [1, 2, 255], ""expectation violation""
  }
}

module TestTime {

  import Time
  method {:test} TestNonDecreasing()
  {
    var t1 := Time.GetCurrent();
    var t2 := Time.GetCurrent();
    expect t2 >= t1, ""expectation violation""
  }

  method {:test} TestPositiveValues()
  {
    var t1 := Time.GetCurrent();
    var t2 := Time.GetCurrent();
    expect t2 - t1 >= 0, ""expectation violation""
  }
}

module TestUTF8 {

  import opened UInt = StandardLibrary.UInt

  import opened UTF8
  method {:test} TestEncodeHappyCase()
  {
    var unicodeString := ""abc\u0306\u01FD\u03B2"";
    var expectedBytes := [97, 98, 99, 204, 134, 199, 189, 206, 178];
    var encoded :- expect UTF8.Encode(unicodeString);
    expect expectedBytes == encoded, ""expectation violation""
  }

  method {:test} TestEncodeInvalidUnicode()
  {
    var invalidUnicode := ""abc\uD800"";
    var encoded := UTF8.Encode(invalidUnicode);
    expect encoded.Failure?, ""expectation violation""
  }

  method {:test} TestDecodeHappyCase()
  {
    var unicodeBytes := [97, 98, 99, 204, 134, 199, 189, 206, 178];
    assert UTF8.Uses2Bytes([199, 189, 206, 178]);
    assert [199, 189, 206, 178] == unicodeBytes[5 .. 9];
    assert UTF8.ValidUTF8Range(unicodeBytes, 7, 9);
    assert UTF8.ValidUTF8Range(unicodeBytes, 0, 9);
    var expectedString := ""abc\u0306\u01FD\u03B2"";
    var decoded :- expect UTF8.Decode(unicodeBytes);
    expect expectedString == decoded, ""expectation violation""
  }

  method {:test} TestDecodeInvalidUnicode()
  {
    var invalidUnicode := [97, 98, 99, 237, 160, 128];
    expect !ValidUTF8Seq(invalidUnicode), ""expectation violation""
    expect UTF8.Decode(invalidUnicode).Failure?, ""expectation violation""
  }

  method {:test} Test1Byte()
  {
    var decoded := ""\u0000"";
    var encoded :- expect UTF8.Encode(decoded);
    expect [0] == encoded, ""expectation violation""
    expect Uses1Byte(encoded), ""expectation violation""
    var redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""\u0020"";
    encoded :- expect UTF8.Encode(decoded);
    expect [32] == encoded, ""expectation violation""
    expect Uses1Byte(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""$"";
    encoded :- expect UTF8.Encode(decoded);
    expect [36] == encoded, ""expectation violation""
    expect Uses1Byte(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""0"";
    encoded :- expect UTF8.Encode(decoded);
    expect [48] == encoded, ""expectation violation""
    expect Uses1Byte(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""A"";
    encoded :- expect UTF8.Encode(decoded);
    expect [65] == encoded, ""expectation violation""
    expect Uses1Byte(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""a"";
    encoded :- expect UTF8.Encode(decoded);
    expect [97] == encoded, ""expectation violation""
    expect Uses1Byte(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
  }

  method {:test} Test2Bytes()
  {
    var decoded := ""\u00A3"";
    var encoded :- expect UTF8.Encode(decoded);
    expect [194, 163] == encoded, ""expectation violation""
    expect Uses2Bytes(encoded), ""expectation violation""
    var redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""\u00A9"";
    encoded :- expect UTF8.Encode(decoded);
    expect [194, 169] == encoded, ""expectation violation""
    expect Uses2Bytes(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""\u00AE"";
    encoded :- expect UTF8.Encode(decoded);
    expect [194, 174] == encoded, ""expectation violation""
    expect Uses2Bytes(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""\u03C0"";
    encoded :- expect UTF8.Encode(decoded);
    expect [207, 128] == encoded, ""expectation violation""
    expect Uses2Bytes(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
  }

  method {:test} Test3Bytes()
  {
    var decoded := ""\u2386"";
    var encoded :- expect UTF8.Encode(decoded);
    expect [226, 142, 134] == encoded, ""expectation violation""
    expect Uses3Bytes(encoded), ""expectation violation""
    var redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""\u2387"";
    encoded :- expect UTF8.Encode(decoded);
    expect [226, 142, 135] == encoded, ""expectation violation""
    expect Uses3Bytes(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""\u231B"";
    encoded :- expect UTF8.Encode(decoded);
    expect [226, 140, 155] == encoded, ""expectation violation""
    expect Uses3Bytes(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""\u1D78"";
    encoded :- expect UTF8.Encode(decoded);
    expect [225, 181, 184] == encoded, ""expectation violation""
    expect Uses3Bytes(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""\u732B"";
    encoded :- expect UTF8.Encode(decoded);
    expect [231, 140, 171] == encoded, ""expectation violation""
    expect Uses3Bytes(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
  }

  method {:test} Test4Bytes()
  {
    var decoded := ""\uD808\uDC00"";
    var encoded :- expect UTF8.Encode(decoded);
    expect [240, 146, 128, 128] == encoded, ""expectation violation""
    expect Uses4Bytes(encoded), ""expectation violation""
    var redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
    decoded := ""\uD835\uDFC1"";
    encoded :- expect UTF8.Encode(decoded);
    expect [240, 157, 159, 129] == encoded, ""expectation violation""
    expect Uses4Bytes(encoded), ""expectation violation""
    redecoded :- expect UTF8.Decode(encoded);
    expect decoded == redecoded, ""expectation violation""
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
namespace TestUUID_Compile {

  public partial class __default {
    public static void TestFromBytesSuccess()
    {
      Dafny.ISequence<char> _0_fromBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _1_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _1_valueOrError0 = UUID.__default.FromByteArray(TestUUID_Compile.__default.byteUuid);
      if (!(!((_1_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(23,18): " + _1_valueOrError0);}
      _0_fromBytes = (_1_valueOrError0).Extract();
      if (!((_0_fromBytes).Equals(TestUUID_Compile.__default.uuid))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(24,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestFromBytesFailure()
    {
      Dafny.ISequence<char> _2_fromBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _3_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _3_valueOrError0 = UUID.__default.FromByteArray(TestUUID_Compile.__default.wrongByteUuid);
      if (!(!((_3_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(28,18): " + _3_valueOrError0);}
      _2_fromBytes = (_3_valueOrError0).Extract();
      if (!(!(_2_fromBytes).Equals(TestUUID_Compile.__default.uuid))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(29,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestToBytesSuccess()
    {
      Dafny.ISequence<byte> _4_toBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _5_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      _5_valueOrError0 = UUID.__default.ToByteArray(TestUUID_Compile.__default.uuid);
      if (!(!((_5_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(33,16): " + _5_valueOrError0);}
      _4_toBytes = (_5_valueOrError0).Extract();
      if (!((_4_toBytes).Equals(TestUUID_Compile.__default.byteUuid))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(34,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestToBytesFailure()
    {
      Dafny.ISequence<byte> _6_toBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _7_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      _7_valueOrError0 = UUID.__default.ToByteArray(TestUUID_Compile.__default.uuid);
      if (!(!((_7_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(38,16): " + _7_valueOrError0);}
      _6_toBytes = (_7_valueOrError0).Extract();
      if (!(!(_6_toBytes).Equals(TestUUID_Compile.__default.wrongByteUuid))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(39,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestRoundTripStringConversion()
    {
      Dafny.ISequence<byte> _8_stringToBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _9_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      _9_valueOrError0 = UUID.__default.ToByteArray(TestUUID_Compile.__default.uuid);
      if (!(!((_9_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(43,22): " + _9_valueOrError0);}
      _8_stringToBytes = (_9_valueOrError0).Extract();
      if (!((new BigInteger((_8_stringToBytes).Count)) == (new BigInteger(16)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(44,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<char> _10_bytesToString;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _11_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _11_valueOrError1 = UUID.__default.FromByteArray(_8_stringToBytes);
      if (!(!((_11_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(45,22): " + _11_valueOrError1);}
      _10_bytesToString = (_11_valueOrError1).Extract();
      if (!((_10_bytesToString).Equals(TestUUID_Compile.__default.uuid))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(46,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestRoundTripByteConversion()
    {
      Dafny.ISequence<char> _12_bytesToString;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _13_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _13_valueOrError0 = UUID.__default.FromByteArray(TestUUID_Compile.__default.byteUuid);
      if (!(!((_13_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(50,22): " + _13_valueOrError0);}
      _12_bytesToString = (_13_valueOrError0).Extract();
      Dafny.ISequence<byte> _14_stringToBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _15_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      _15_valueOrError1 = UUID.__default.ToByteArray(_12_bytesToString);
      if (!(!((_15_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(51,22): " + _15_valueOrError1);}
      _14_stringToBytes = (_15_valueOrError1).Extract();
      if (!((new BigInteger((_14_stringToBytes).Count)) == (new BigInteger(16)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(52,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_14_stringToBytes).Equals(TestUUID_Compile.__default.byteUuid))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(53,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestGenerateAndConversion()
    {
      Dafny.ISequence<char> _16_uuidString;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _17_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _out0;
      _out0 = UUID.__default.GenerateUUID();
      _17_valueOrError0 = _out0;
      if (!(!((_17_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(57,19): " + _17_valueOrError0);}
      _16_uuidString = (_17_valueOrError0).Extract();
      Dafny.ISequence<byte> _18_uuidBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _19_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      _19_valueOrError1 = UUID.__default.ToByteArray(_16_uuidString);
      if (!(!((_19_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(58,18): " + _19_valueOrError1);}
      _18_uuidBytes = (_19_valueOrError1).Extract();
      Dafny.ISequence<char> _20_bytesToString;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _21_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _21_valueOrError2 = UUID.__default.FromByteArray(_18_uuidBytes);
      if (!(!((_21_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(60,22): " + _21_valueOrError2);}
      _20_bytesToString = (_21_valueOrError2).Extract();
      Dafny.ISequence<byte> _22_stringToBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _23_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      _23_valueOrError3 = UUID.__default.ToByteArray(_20_bytesToString);
      if (!(!((_23_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(61,22): " + _23_valueOrError3);}
      _22_stringToBytes = (_23_valueOrError3).Extract();
      if (!((new BigInteger((_22_stringToBytes).Count)) == (new BigInteger(16)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(62,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((_22_stringToBytes).Equals(_18_uuidBytes))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(63,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<byte> _24_uuidStringToBytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _25_valueOrError4 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      _25_valueOrError4 = UUID.__default.ToByteArray(_16_uuidString);
      if (!(!((_25_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(65,26): " + _25_valueOrError4);}
      _24_uuidStringToBytes = (_25_valueOrError4).Extract();
      if (!((new BigInteger((_24_uuidStringToBytes).Count)) == (new BigInteger(16)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(66,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<char> _26_uuidBytesToString;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _27_valueOrError5 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _27_valueOrError5 = UUID.__default.FromByteArray(_24_uuidStringToBytes);
      if (!(!((_27_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(67,26): " + _27_valueOrError5);}
      _26_uuidBytesToString = (_27_valueOrError5).Extract();
      if (!((_26_uuidBytesToString).Equals(_16_uuidString))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UUID.dfy(68,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static Dafny.ISequence<byte> byteUuid { get {
      return Dafny.Sequence<byte>.FromElements((byte)(146), (byte)(56), (byte)(38), (byte)(88), (byte)(183), (byte)(160), (byte)(77), (byte)(151), (byte)(156), (byte)(73), (byte)(206), (byte)(228), (byte)(230), (byte)(114), (byte)(163), (byte)(179));
    } }
    public static Dafny.ISequence<char> uuid { get {
      return Dafny.Sequence<char>.FromString("92382658-b7a0-4d97-9c49-cee4e672a3b3");
    } }
    public static Dafny.ISequence<byte> wrongByteUuid { get {
      return Dafny.Sequence<byte>.FromElements((byte)(146), (byte)(56), (byte)(38), (byte)(88), (byte)(183), (byte)(160), (byte)(77), (byte)(151), (byte)(156), (byte)(73), (byte)(206), (byte)(228), (byte)(230), (byte)(114), (byte)(163), (byte)(178));
    } }
  }
} // end of namespace TestUUID_Compile
namespace TestCallMany_Compile {

  public partial class MyCallee : ConcurrentCall.Callee {
    public MyCallee() {
      this.count = 0;
    }
    public uint count {get; set;}
    public void __ctor()
    {
      (this).count = 0U;
    }
    public void call(uint serialPos, uint concurrentPos)
    {
      if ((this.count) < (BoundedInts_Compile.__default.UINT32__MAX)) {
        (this).count = (this.count) + (1U);
      }
    }
  }

  public partial class __default {
    public static void TestBasic()
    {
      TestCallMany_Compile.MyCallee _28_c;
      TestCallMany_Compile.MyCallee _nw0 = new TestCallMany_Compile.MyCallee();
      _nw0.__ctor();
      _28_c = _nw0;
      ConcurrentCall.__default.ConcurrentCall(_28_c, 2U, 3U);
      if (!((_28_c.count) == (6U))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/ConcurrentCall.dfy(43,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestCallMany_Compile
namespace FloatCompareTest_Compile {

  public partial class __default {
    public static void TestCompareFloat(Dafny.ISequence<char> x, Dafny.ISequence<char> y, sbyte ret)
    {
      if ((FloatCompare_Compile.__default.CompareFloat(x, y)) != (ret)) {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("CompareFloat(")));
        Dafny.Helpers.Print((x));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(", ")));
        Dafny.Helpers.Print((y));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(") was ")));
        Dafny.Helpers.Print((FloatCompare_Compile.__default.CompareFloat(x, y)));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(" but should have been ")));
        Dafny.Helpers.Print((ret));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
      }
      if ((FloatCompare_Compile.__default.CompareFloat(y, x)) != ((sbyte)(((sbyte)(0)) - (ret)))) {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("CompareFloat(")));
        Dafny.Helpers.Print((y));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(", ")));
        Dafny.Helpers.Print((x));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(") was ")));
        Dafny.Helpers.Print((FloatCompare_Compile.__default.CompareFloat(y, x)));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(" but should have been ")));
        Dafny.Helpers.Print(((sbyte)(((sbyte)(0)) - (ret))));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
      }
      if (!((FloatCompare_Compile.__default.CompareFloat(x, y)) == (ret))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/FloatCompare.dfy(165,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((FloatCompare_Compile.__default.CompareFloat(y, x)) == ((sbyte)(((sbyte)(0)) - (ret))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/FloatCompare.dfy(166,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestOneTwoZeroMatrix()
    {
      BigInteger _hi0 = new BigInteger((FloatCompareTest_Compile.__default.NEGATIVE__TWO).Count);
      for (BigInteger _29_i = BigInteger.Zero; _29_i < _hi0; _29_i++) {
        Dafny.ISequence<char> _30_negativeTwo;
        _30_negativeTwo = (FloatCompareTest_Compile.__default.NEGATIVE__TWO).Select(_29_i);
        BigInteger _hi1 = new BigInteger((FloatCompareTest_Compile.__default.NEGATIVE__TWO).Count);
        for (BigInteger _31_j = _29_i; _31_j < _hi1; _31_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.NEGATIVE__TWO).Select(_31_j), _30_negativeTwo, FloatCompare_Compile.__default.Equal);
        }
        BigInteger _hi2 = new BigInteger((FloatCompareTest_Compile.__default.NEGATIVE__ONE).Count);
        for (BigInteger _32_j = BigInteger.Zero; _32_j < _hi2; _32_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.NEGATIVE__ONE).Select(_32_j), _30_negativeTwo, FloatCompare_Compile.__default.Greater);
        }
        BigInteger _hi3 = new BigInteger((FloatCompareTest_Compile.__default.ZERO).Count);
        for (BigInteger _33_j = BigInteger.Zero; _33_j < _hi3; _33_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.ZERO).Select(_33_j), _30_negativeTwo, FloatCompare_Compile.__default.Greater);
        }
        BigInteger _hi4 = new BigInteger((FloatCompareTest_Compile.__default.ONE).Count);
        for (BigInteger _34_j = BigInteger.Zero; _34_j < _hi4; _34_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.ONE).Select(_34_j), _30_negativeTwo, FloatCompare_Compile.__default.Greater);
        }
        BigInteger _hi5 = new BigInteger((FloatCompareTest_Compile.__default.TWO).Count);
        for (BigInteger _35_j = BigInteger.Zero; _35_j < _hi5; _35_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.TWO).Select(_35_j), _30_negativeTwo, FloatCompare_Compile.__default.Greater);
        }
      }
      BigInteger _hi6 = new BigInteger((FloatCompareTest_Compile.__default.NEGATIVE__ONE).Count);
      for (BigInteger _36_i = BigInteger.Zero; _36_i < _hi6; _36_i++) {
        Dafny.ISequence<char> _37_negativeOne;
        _37_negativeOne = (FloatCompareTest_Compile.__default.NEGATIVE__ONE).Select(_36_i);
        BigInteger _hi7 = new BigInteger((FloatCompareTest_Compile.__default.NEGATIVE__ONE).Count);
        for (BigInteger _38_j = _36_i; _38_j < _hi7; _38_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.NEGATIVE__ONE).Select(_38_j), _37_negativeOne, FloatCompare_Compile.__default.Equal);
        }
        BigInteger _hi8 = new BigInteger((FloatCompareTest_Compile.__default.ZERO).Count);
        for (BigInteger _39_j = BigInteger.Zero; _39_j < _hi8; _39_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.ZERO).Select(_39_j), _37_negativeOne, FloatCompare_Compile.__default.Greater);
        }
        BigInteger _hi9 = new BigInteger((FloatCompareTest_Compile.__default.ONE).Count);
        for (BigInteger _40_j = BigInteger.Zero; _40_j < _hi9; _40_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.ONE).Select(_40_j), _37_negativeOne, FloatCompare_Compile.__default.Greater);
        }
        BigInteger _hi10 = new BigInteger((FloatCompareTest_Compile.__default.TWO).Count);
        for (BigInteger _41_j = BigInteger.Zero; _41_j < _hi10; _41_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.TWO).Select(_41_j), _37_negativeOne, FloatCompare_Compile.__default.Greater);
        }
      }
      BigInteger _hi11 = new BigInteger((FloatCompareTest_Compile.__default.ZERO).Count);
      for (BigInteger _42_i = BigInteger.Zero; _42_i < _hi11; _42_i++) {
        Dafny.ISequence<char> _43_zero;
        _43_zero = (FloatCompareTest_Compile.__default.ZERO).Select(_42_i);
        BigInteger _hi12 = new BigInteger((FloatCompareTest_Compile.__default.ZERO).Count);
        for (BigInteger _44_j = _42_i; _44_j < _hi12; _44_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.ZERO).Select(_44_j), _43_zero, FloatCompare_Compile.__default.Equal);
        }
        BigInteger _hi13 = new BigInteger((FloatCompareTest_Compile.__default.ONE).Count);
        for (BigInteger _45_j = BigInteger.Zero; _45_j < _hi13; _45_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.ONE).Select(_45_j), _43_zero, FloatCompare_Compile.__default.Greater);
        }
        BigInteger _hi14 = new BigInteger((FloatCompareTest_Compile.__default.TWO).Count);
        for (BigInteger _46_j = BigInteger.Zero; _46_j < _hi14; _46_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.TWO).Select(_46_j), _43_zero, FloatCompare_Compile.__default.Greater);
        }
      }
      BigInteger _hi15 = new BigInteger((FloatCompareTest_Compile.__default.ONE).Count);
      for (BigInteger _47_i = BigInteger.Zero; _47_i < _hi15; _47_i++) {
        Dafny.ISequence<char> _48_one;
        _48_one = (FloatCompareTest_Compile.__default.ONE).Select(_47_i);
        BigInteger _hi16 = new BigInteger((FloatCompareTest_Compile.__default.ONE).Count);
        for (BigInteger _49_j = _47_i; _49_j < _hi16; _49_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.ONE).Select(_49_j), _48_one, FloatCompare_Compile.__default.Equal);
        }
        BigInteger _hi17 = new BigInteger((FloatCompareTest_Compile.__default.TWO).Count);
        for (BigInteger _50_j = BigInteger.Zero; _50_j < _hi17; _50_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.TWO).Select(_50_j), _48_one, FloatCompare_Compile.__default.Greater);
        }
      }
      BigInteger _hi18 = new BigInteger((FloatCompareTest_Compile.__default.TWO).Count);
      for (BigInteger _51_i = BigInteger.Zero; _51_i < _hi18; _51_i++) {
        Dafny.ISequence<char> _52_two;
        _52_two = (FloatCompareTest_Compile.__default.TWO).Select(_51_i);
        BigInteger _hi19 = new BigInteger((FloatCompareTest_Compile.__default.TWO).Count);
        for (BigInteger _53_j = _51_i; _53_j < _hi19; _53_j++) {
          FloatCompareTest_Compile.__default.TestCompareFloat((FloatCompareTest_Compile.__default.TWO).Select(_53_j), _52_two, FloatCompare_Compile.__default.Equal);
        }
      }
    }
    public static void SimpleTests()
    {
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1"), Dafny.Sequence<char>.FromString("1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("2"), Dafny.Sequence<char>.FromString("1"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1.1"), Dafny.Sequence<char>.FromString("1.2"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1.2"), Dafny.Sequence<char>.FromString("1.2"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1.35"), Dafny.Sequence<char>.FromString("1.357"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1.35e2"), Dafny.Sequence<char>.FromString("13.5e1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1.351e2"), Dafny.Sequence<char>.FromString("13.5e1"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1.35e-1"), Dafny.Sequence<char>.FromString("13.5e-2"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1"), Dafny.Sequence<char>.FromString("-2"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1.2e7"), Dafny.Sequence<char>.FromString("2.3e2"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1.2e7"), Dafny.Sequence<char>.FromString("2.3e2"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1.2e7"), Dafny.Sequence<char>.FromString("-2.3e2"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1.2e7"), Dafny.Sequence<char>.FromString("-2.3e2"), FloatCompare_Compile.__default.Less);
    }
    public static void SignTests()
    {
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("+1"), Dafny.Sequence<char>.FromString("1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("+1e+0"), Dafny.Sequence<char>.FromString("1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("+1e-0"), Dafny.Sequence<char>.FromString("1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1"), Dafny.Sequence<char>.FromString("1"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1"), Dafny.Sequence<char>.FromString("+1"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1"), Dafny.Sequence<char>.FromString("-1"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("+1"), Dafny.Sequence<char>.FromString("-1"), FloatCompare_Compile.__default.Greater);
    }
    public static void ExponentTests()
    {
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("2e0"), Dafny.Sequence<char>.FromString("2e0"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1e0"), Dafny.Sequence<char>.FromString("2e0"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("3e0"), Dafny.Sequence<char>.FromString("2e0"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1e-5"), Dafny.Sequence<char>.FromString("1e5"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1e5"), Dafny.Sequence<char>.FromString("1e-5"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1e5"), Dafny.Sequence<char>.FromString("1e6"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1e5"), Dafny.Sequence<char>.FromString("1e4"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1e-5"), Dafny.Sequence<char>.FromString("1e-4"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1e-5"), Dafny.Sequence<char>.FromString("1e-6"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1e5"), Dafny.Sequence<char>.FromString("-1e-5"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1e-5"), Dafny.Sequence<char>.FromString("-1e5"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1e5"), Dafny.Sequence<char>.FromString("-1e4"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1e5"), Dafny.Sequence<char>.FromString("-1e6"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1e-5"), Dafny.Sequence<char>.FromString("-1e-6"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1e-5"), Dafny.Sequence<char>.FromString("-1e-4"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("2"), Dafny.Sequence<char>.FromString("2e0"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1"), Dafny.Sequence<char>.FromString("2e0"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("3"), Dafny.Sequence<char>.FromString("2e0"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("20"), Dafny.Sequence<char>.FromString("2e1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("19"), Dafny.Sequence<char>.FromString("2e1"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("21"), Dafny.Sequence<char>.FromString("2e1"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-20"), Dafny.Sequence<char>.FromString("-2e1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-21"), Dafny.Sequence<char>.FromString("-2e1"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-19"), Dafny.Sequence<char>.FromString("-2e1"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.2"), Dafny.Sequence<char>.FromString("2e-1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.02"), Dafny.Sequence<char>.FromString("2e-2"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.02"), Dafny.Sequence<char>.FromString(".2e-1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString(".1"), Dafny.Sequence<char>.FromString("2e-1"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString(".3"), Dafny.Sequence<char>.FromString("2e-1"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0.2"), Dafny.Sequence<char>.FromString("-2e-1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0.02"), Dafny.Sequence<char>.FromString("-2e-2"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0.02"), Dafny.Sequence<char>.FromString("-.2e-1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-.3"), Dafny.Sequence<char>.FromString("-2e-1"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-.1"), Dafny.Sequence<char>.FromString("-2e-1"), FloatCompare_Compile.__default.Greater);
    }
    public static void ZeroTests()
    {
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0"), Dafny.Sequence<char>.FromString("0"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("+0"), Dafny.Sequence<char>.FromString("0"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("00"), Dafny.Sequence<char>.FromString("0"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.0"), Dafny.Sequence<char>.FromString("0"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0"), Dafny.Sequence<char>.FromString("000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0"), Dafny.Sequence<char>.FromString(".000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.0"), Dafny.Sequence<char>.FromString("000.00000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0"), Dafny.Sequence<char>.FromString("000.000e0"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0"), Dafny.Sequence<char>.FromString("0e+0"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0"), Dafny.Sequence<char>.FromString("0e-0"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0"), Dafny.Sequence<char>.FromString("0e99"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0"), Dafny.Sequence<char>.FromString("0e-99"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0e+99"), Dafny.Sequence<char>.FromString("0e-99"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("+0e+99"), Dafny.Sequence<char>.FromString("-0e-99"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0e+99"), Dafny.Sequence<char>.FromString("-0e-99"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0e+99"), Dafny.Sequence<char>.FromString("+0e-99"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("01"), Dafny.Sequence<char>.FromString("1"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1"), Dafny.Sequence<char>.FromString("001"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1.0"), Dafny.Sequence<char>.FromString("001.00000"), FloatCompare_Compile.__default.Equal);
    }
    public static void ExtremeNumTest()
    {
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345678"), Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345678"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1234567890123456789012345678901234567800000000000000000000000000000"), Dafny.Sequence<char>.FromString("1234567890123456789012345678901234567800000000000000000000000000000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString(".000000000000000000000000012345678901234567890123456789012345678"), Dafny.Sequence<char>.FromString("0.000000000000000000000000012345678901234567890123456789012345678"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345676"), Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345678"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345675"), Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345676"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345679"), Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345678"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345677"), Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345676"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-123456789.01234567890123456789012345678"), Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345678"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("123456789.01234567890123456789012345678"), Dafny.Sequence<char>.FromString("-123456789.01234567890123456789012345678"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0000000000000000000000000012345.67e121"), Dafny.Sequence<char>.FromString("123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("12345.67e121"), Dafny.Sequence<char>.FromString("123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.00000001e133"), Dafny.Sequence<char>.FromString("100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.00000001e-122"), Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1234567e-136"), Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001234567"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0000000000000000000000000012345.66e121"), Dafny.Sequence<char>.FromString("123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0000000000000000000000000012345.68e121"), Dafny.Sequence<char>.FromString("123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("12345.67e120"), Dafny.Sequence<char>.FromString("12345.67e121"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("12345.67e122"), Dafny.Sequence<char>.FromString("12345.67e121"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-12345.67e122"), Dafny.Sequence<char>.FromString("-12345.67e121"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-12345.67e120"), Dafny.Sequence<char>.FromString("-12345.67e121"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("12345.67e120"), Dafny.Sequence<char>.FromString("123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("12345.67e122"), Dafny.Sequence<char>.FromString("123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-12345.67e122"), Dafny.Sequence<char>.FromString("-123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-12345.67e120"), Dafny.Sequence<char>.FromString("-123456700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.00000001e-123"), Dafny.Sequence<char>.FromString("0.00000001e-122"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.00000001e-121"), Dafny.Sequence<char>.FromString("0.00000001e-122"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0.00000001e-121"), Dafny.Sequence<char>.FromString("-0.00000001e-122"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0.00000001e-123"), Dafny.Sequence<char>.FromString("-0.00000001e-122"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.00000001e-123"), Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.00000001e-121"), Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0.00000001e-121"), Dafny.Sequence<char>.FromString("-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0.00000001e-123"), Dafny.Sequence<char>.FromString("-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("9.9999999999999999999999999999999999999E+125"), Dafny.Sequence<char>.FromString("999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString(".99999999999999999999999999999999999999E+126"), Dafny.Sequence<char>.FromString("999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), Dafny.Sequence<char>.FromString("999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("9.9999999999999999999999999999999999999E+124"), Dafny.Sequence<char>.FromString("999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("9.9999999999999999999999999999999999999E+126"), Dafny.Sequence<char>.FromString("999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("999999999999999999999999999999999999989999999999999999999999999999999999999999999999999999999999999999999999999999999999999999"), Dafny.Sequence<char>.FromString("999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), Dafny.Sequence<char>.FromString("999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1E-130"), Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("10E-131"), Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1E-131"), Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("1E-129"), Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009"), Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"), Dafny.Sequence<char>.FromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-9.9999999999999999999999999999999999999E+125"), Dafny.Sequence<char>.FromString("-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-.99999999999999999999999999999999999999E+126"), Dafny.Sequence<char>.FromString("-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), Dafny.Sequence<char>.FromString("-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-9.9999999999999999999999999999999999999E+126"), Dafny.Sequence<char>.FromString("-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-9.9999999999999999999999999999999999999E+124"), Dafny.Sequence<char>.FromString("-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), Dafny.Sequence<char>.FromString("-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-99999999999999999999999999999999999998999999999999999999999999999999999999999999999999999999999999999999999999999999999999999"), Dafny.Sequence<char>.FromString("-999999999999999999999999999999999999990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1E-130"), Dafny.Sequence<char>.FromString("-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-10E-131"), Dafny.Sequence<char>.FromString("-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), Dafny.Sequence<char>.FromString("-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1E-129"), Dafny.Sequence<char>.FromString("-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-1E-131"), Dafny.Sequence<char>.FromString("-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Greater);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002"), Dafny.Sequence<char>.FromString("-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Less);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("-0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009"), Dafny.Sequence<char>.FromString("-0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"), FloatCompare_Compile.__default.Greater);
    }
    public static void InvalidTests()
    {
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("a"), Dafny.Sequence<char>.FromString("0"), FloatCompare_Compile.__default.Equal);
      FloatCompareTest_Compile.__default.TestCompareFloat(Dafny.Sequence<char>.FromString("a"), Dafny.Sequence<char>.FromString("b"), FloatCompare_Compile.__default.Equal);
    }
    public static Dafny.ISequence<Dafny.ISequence<char>> NEGATIVE__TWO { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("-2"), Dafny.Sequence<char>.FromString("-2."), Dafny.Sequence<char>.FromString("-2.0"), Dafny.Sequence<char>.FromString("-2e0"), Dafny.Sequence<char>.FromString("-2.e0"), Dafny.Sequence<char>.FromString("-2.0e0"), Dafny.Sequence<char>.FromString("-2.0e+0"), Dafny.Sequence<char>.FromString("-2.0e-0"), Dafny.Sequence<char>.FromString("-.2e1"), Dafny.Sequence<char>.FromString("-0.2e1"), Dafny.Sequence<char>.FromString("-0.2e+1"), Dafny.Sequence<char>.FromString("-0.02e2"), Dafny.Sequence<char>.FromString("-20e-1"), Dafny.Sequence<char>.FromString("-20.e-1"), Dafny.Sequence<char>.FromString("-200.0e-2"));
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> NEGATIVE__ONE { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("-1"), Dafny.Sequence<char>.FromString("-1."), Dafny.Sequence<char>.FromString("-1.0"), Dafny.Sequence<char>.FromString("-1e0"), Dafny.Sequence<char>.FromString("-1.e0"), Dafny.Sequence<char>.FromString("-1.0e0"), Dafny.Sequence<char>.FromString("-1.0e+0"), Dafny.Sequence<char>.FromString("-1.0e-0"), Dafny.Sequence<char>.FromString("-.1e1"), Dafny.Sequence<char>.FromString("-0.1e1"), Dafny.Sequence<char>.FromString("-0.1e+1"), Dafny.Sequence<char>.FromString("-0.01e2"), Dafny.Sequence<char>.FromString("-10e-1"), Dafny.Sequence<char>.FromString("-10.e-1"), Dafny.Sequence<char>.FromString("-100.0e-2"));
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> ZERO { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("0"), Dafny.Sequence<char>.FromString("+0"), Dafny.Sequence<char>.FromString("-0"), Dafny.Sequence<char>.FromString("0."), Dafny.Sequence<char>.FromString("+0."), Dafny.Sequence<char>.FromString("-0."), Dafny.Sequence<char>.FromString("00"), Dafny.Sequence<char>.FromString("+00"), Dafny.Sequence<char>.FromString("-00"), Dafny.Sequence<char>.FromString("0.0"), Dafny.Sequence<char>.FromString("+0.0"), Dafny.Sequence<char>.FromString("-0.0"), Dafny.Sequence<char>.FromString("00.00"), Dafny.Sequence<char>.FromString("+00.00"), Dafny.Sequence<char>.FromString("-00.00"), Dafny.Sequence<char>.FromString(".0"), Dafny.Sequence<char>.FromString("+.0"), Dafny.Sequence<char>.FromString("-.0"), Dafny.Sequence<char>.FromString("0e0"), Dafny.Sequence<char>.FromString("+0e0"), Dafny.Sequence<char>.FromString("+0e+0"), Dafny.Sequence<char>.FromString("+0e-0"), Dafny.Sequence<char>.FromString("-0e0"), Dafny.Sequence<char>.FromString("-0e+0"), Dafny.Sequence<char>.FromString("-0e-0"), Dafny.Sequence<char>.FromString("0e-99"), Dafny.Sequence<char>.FromString("+0e-99"), Dafny.Sequence<char>.FromString("-0e-99"), Dafny.Sequence<char>.FromString("0e99"), Dafny.Sequence<char>.FromString("+0e99"), Dafny.Sequence<char>.FromString("-0e99"), Dafny.Sequence<char>.FromString("0e+99"), Dafny.Sequence<char>.FromString("+0e+99"), Dafny.Sequence<char>.FromString("-0e+99"));
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> ONE { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("1"), Dafny.Sequence<char>.FromString("1."), Dafny.Sequence<char>.FromString("1.0"), Dafny.Sequence<char>.FromString("1e0"), Dafny.Sequence<char>.FromString("1.e0"), Dafny.Sequence<char>.FromString("1.0e0"), Dafny.Sequence<char>.FromString("1.0e+0"), Dafny.Sequence<char>.FromString("1.0e-0"), Dafny.Sequence<char>.FromString(".1e1"), Dafny.Sequence<char>.FromString("0.1e1"), Dafny.Sequence<char>.FromString("0.1e+1"), Dafny.Sequence<char>.FromString("0.01e2"), Dafny.Sequence<char>.FromString("10e-1"), Dafny.Sequence<char>.FromString("10.e-1"), Dafny.Sequence<char>.FromString("100.0e-2"), Dafny.Sequence<char>.FromString("+1"), Dafny.Sequence<char>.FromString("+1."), Dafny.Sequence<char>.FromString("+1.0"), Dafny.Sequence<char>.FromString("+1e0"), Dafny.Sequence<char>.FromString("+1.e0"), Dafny.Sequence<char>.FromString("+1.0e0"), Dafny.Sequence<char>.FromString("+1.0e+0"), Dafny.Sequence<char>.FromString("+1.0e-0"), Dafny.Sequence<char>.FromString("+.1e1"), Dafny.Sequence<char>.FromString("+0.1e1"), Dafny.Sequence<char>.FromString("+0.1e+1"), Dafny.Sequence<char>.FromString("+0.01e2"), Dafny.Sequence<char>.FromString("+10e-1"), Dafny.Sequence<char>.FromString("+10.e-1"), Dafny.Sequence<char>.FromString("+100.0e-2"));
    } }
    public static Dafny.ISequence<Dafny.ISequence<char>> TWO { get {
      return Dafny.Sequence<Dafny.ISequence<char>>.FromElements(Dafny.Sequence<char>.FromString("2"), Dafny.Sequence<char>.FromString("2."), Dafny.Sequence<char>.FromString("2.0"), Dafny.Sequence<char>.FromString("2e0"), Dafny.Sequence<char>.FromString("2.e0"), Dafny.Sequence<char>.FromString("2.0e0"), Dafny.Sequence<char>.FromString("2.0e+0"), Dafny.Sequence<char>.FromString("2.0e-0"), Dafny.Sequence<char>.FromString(".2e1"), Dafny.Sequence<char>.FromString("0.2e1"), Dafny.Sequence<char>.FromString("0.2e+1"), Dafny.Sequence<char>.FromString("0.02e2"), Dafny.Sequence<char>.FromString("20e-1"), Dafny.Sequence<char>.FromString("20.e-1"), Dafny.Sequence<char>.FromString("200.0e-2"), Dafny.Sequence<char>.FromString("+2"), Dafny.Sequence<char>.FromString("+2."), Dafny.Sequence<char>.FromString("+2.0"), Dafny.Sequence<char>.FromString("+2e0"), Dafny.Sequence<char>.FromString("+2.e0"), Dafny.Sequence<char>.FromString("+2.0e0"), Dafny.Sequence<char>.FromString("+2.0e+0"), Dafny.Sequence<char>.FromString("+2.0e-0"), Dafny.Sequence<char>.FromString("+.2e1"), Dafny.Sequence<char>.FromString("+0.2e1"), Dafny.Sequence<char>.FromString("+0.2e+1"), Dafny.Sequence<char>.FromString("+0.02e2"), Dafny.Sequence<char>.FromString("+20e-1"), Dafny.Sequence<char>.FromString("+20.e-1"), Dafny.Sequence<char>.FromString("+200.0e-2"));
    } }
  }
} // end of namespace FloatCompareTest_Compile
namespace TestSeqReaderReadElements_Compile {

  public partial class __default {
    public static bool UInt8Greater(byte x, byte y)
    {
      return (y) < (x);
    }
    public static void TestSetToOrderedSequenceEmpty()
    {
      Dafny.ISequence<Dafny.ISequence<byte>> _54_output;
      Dafny.ISequence<Dafny.ISequence<byte>> _out1;
      _out1 = SortedSets.__default.SetToOrderedSequence<byte>(Dafny.Set<Dafny.ISequence<byte>>.FromElements(), StandardLibrary_mUInt_Compile.__default.UInt8Less);
      _54_output = _out1;
      Dafny.ISequence<Dafny.ISequence<byte>> _55_expected;
      _55_expected = Dafny.Sequence<Dafny.ISequence<byte>>.FromElements();
      if (!((_54_output).Equals(_55_expected))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/Sets.dfy(21,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestSetToOrderedSequenceOneItem()
    {
      Dafny.ISet<Dafny.ISequence<byte>> _56_a;
      _56_a = Dafny.Set<Dafny.ISequence<byte>>.FromElements(Dafny.Sequence<byte>.FromElements((byte)(0)));
      Dafny.ISequence<Dafny.ISequence<byte>> _57_output;
      Dafny.ISequence<Dafny.ISequence<byte>> _out2;
      _out2 = SortedSets.__default.SetToOrderedSequence<byte>(_56_a, StandardLibrary_mUInt_Compile.__default.UInt8Less);
      _57_output = _out2;
      Dafny.ISequence<Dafny.ISequence<byte>> _58_expected;
      _58_expected = Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(Dafny.Sequence<byte>.FromElements((byte)(0)));
      if (!((_57_output).Equals(_58_expected))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/Sets.dfy(28,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestSetToOrderedSequenceSimple()
    {
      Dafny.ISet<Dafny.ISequence<byte>> _59_a;
      _59_a = Dafny.Set<Dafny.ISequence<byte>>.FromElements(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(2)), Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1)));
      Dafny.ISequence<Dafny.ISequence<byte>> _60_output;
      Dafny.ISequence<Dafny.ISequence<byte>> _out3;
      _out3 = SortedSets.__default.SetToOrderedSequence<byte>(_59_a, StandardLibrary_mUInt_Compile.__default.UInt8Less);
      _60_output = _out3;
      Dafny.ISequence<Dafny.ISequence<byte>> _61_expected;
      _61_expected = Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1)), Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(2)));
      if (!((_60_output).Equals(_61_expected))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/Sets.dfy(35,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestSetToOrderedSequencePrefix()
    {
      Dafny.ISet<Dafny.ISequence<byte>> _62_a;
      _62_a = Dafny.Set<Dafny.ISequence<byte>>.FromElements(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1), (byte)(2)), Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1)));
      Dafny.ISequence<Dafny.ISequence<byte>> _63_output;
      Dafny.ISequence<Dafny.ISequence<byte>> _out4;
      _out4 = SortedSets.__default.SetToOrderedSequence<byte>(_62_a, StandardLibrary_mUInt_Compile.__default.UInt8Less);
      _63_output = _out4;
      Dafny.ISequence<Dafny.ISequence<byte>> _64_expected;
      _64_expected = Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1)), Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1), (byte)(2)));
      if (!((_63_output).Equals(_64_expected))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/Sets.dfy(42,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestSetToOrderedSequenceComplex()
    {
      Dafny.ISet<Dafny.ISequence<byte>> _65_a;
      _65_a = Dafny.Set<Dafny.ISequence<byte>>.FromElements(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1), (byte)(2)), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(1), (byte)(2)), Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1)));
      Dafny.ISequence<Dafny.ISequence<byte>> _66_output;
      Dafny.ISequence<Dafny.ISequence<byte>> _out5;
      _out5 = SortedSets.__default.SetToOrderedSequence<byte>(_65_a, StandardLibrary_mUInt_Compile.__default.UInt8Less);
      _66_output = _out5;
      Dafny.ISequence<Dafny.ISequence<byte>> _67_expected;
      _67_expected = Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1)), Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1), (byte)(2)), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(1), (byte)(2)));
      if (!((_66_output).Equals(_67_expected))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/Sets.dfy(49,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestSetToOrderedSequenceComplexReverse()
    {
      Dafny.ISet<Dafny.ISequence<byte>> _68_a;
      _68_a = Dafny.Set<Dafny.ISequence<byte>>.FromElements(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1), (byte)(2)), Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(1), (byte)(2)), Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1)));
      Dafny.ISequence<Dafny.ISequence<byte>> _69_output;
      Dafny.ISequence<Dafny.ISequence<byte>> _out6;
      _out6 = SortedSets.__default.SetToOrderedSequence<byte>(_68_a, TestSeqReaderReadElements_Compile.__default.UInt8Greater);
      _69_output = _out6;
      Dafny.ISequence<Dafny.ISequence<byte>> _70_expected;
      _70_expected = Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(1), (byte)(2)), Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1)), Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(1), (byte)(2)));
      if (!((_69_output).Equals(_70_expected))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/Sets.dfy(56,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestSetSequence()
    {
      Dafny.ISet<Dafny.ISequence<BigInteger>> _71_a;
      _71_a = Dafny.Set<Dafny.ISequence<BigInteger>>.FromElements(Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.One, new BigInteger(2)), Dafny.Sequence<BigInteger>.FromElements(BigInteger.One, BigInteger.One, new BigInteger(2)), Dafny.Sequence<BigInteger>.FromElements(BigInteger.Zero, BigInteger.One));
      Dafny.ISequence<Dafny.ISequence<BigInteger>> _72_output;
      _72_output = SortedSets.__default.SetToSequence<Dafny.ISequence<BigInteger>>(_71_a);
      if (!((Dafny.MultiSet<Dafny.ISequence<BigInteger>>.FromSeq(_72_output)).Equals(Dafny.MultiSet<Dafny.ISequence<BigInteger>>.FromSet(_71_a)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/Sets.dfy(62,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestSetToOrderedSequenceManyItems()
    {
      Dafny.ISet<Dafny.ISequence<byte>> _73_a;
      _73_a = ((System.Func<Dafny.ISet<Dafny.ISequence<byte>>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.ISequence<byte>>();
        foreach (ushort _compr_0 in BoundedInts_Compile.uint16.IntegerRange(BigInteger.Zero, BoundedInts_Compile.__default.TWO__TO__THE__16)) {
          ushort _74_x = (ushort)_compr_0;
          if ((((ushort)(0)) <= (_74_x)) && ((_74_x) < ((ushort)(65535)))) {
            _coll0.Add(StandardLibrary_mUInt_Compile.__default.UInt16ToSeq(_74_x));
          }
        }
        return Dafny.Set<Dafny.ISequence<byte>>.FromCollection(_coll0);
      }))();
      Dafny.ISequence<Dafny.ISequence<byte>> _75_output;
      Dafny.ISequence<Dafny.ISequence<byte>> _out7;
      _out7 = SortedSets.__default.SetToOrderedSequence<byte>(_73_a, StandardLibrary_mUInt_Compile.__default.UInt8Less);
      _75_output = _out7;
      Dafny.ISequence<Dafny.ISequence<byte>> _76_expected;
      _76_expected = ((System.Func<Dafny.ISequence<Dafny.ISequence<byte>>>) (() => {
        BigInteger dim0 = new BigInteger(65535);
        var arr0 = new Dafny.ISequence<byte>[Dafny.Helpers.ToIntChecked(dim0, "array size exceeds memory limit")];
        for (int i0 = 0; i0 < dim0; i0++) {
          var _77_i = (BigInteger) i0;
          arr0[(int)(_77_i)] = StandardLibrary_mUInt_Compile.__default.UInt16ToSeq((ushort)(_77_i));
        }
        return Dafny.Sequence<Dafny.ISequence<byte>>.FromArray(arr0);
      }))();
      if (!((_75_output).Equals(_76_expected))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/Sets.dfy(69,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestSeqReaderReadElements_Compile
namespace Sets_Compile {

  public partial class __default {
    public static __T ExtractFromSingleton<__T>(Dafny.ISet<__T> s) {
      return Dafny.Helpers.Let<int, __T>(0, _let_dummy_0 =>  {
        __T _78_x = default(__T);
        foreach (__T _assign_such_that_0 in (s).Elements) {
          _78_x = (__T)_assign_such_that_0;
          if ((s).Contains(_78_x)) {
            goto after__ASSIGN_SUCH_THAT_0;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 120)");
      after__ASSIGN_SUCH_THAT_0: ;
        return _78_x;
      }
      );
    }
    public static Dafny.ISet<__Y> Map<__X, __Y>(Dafny.ISet<__X> xs, Func<__X, __Y> f)
    {
      Dafny.ISet<__Y> _79_ys = Dafny.Helpers.Id<Func<Dafny.ISet<__X>, Func<__X, __Y>, Dafny.ISet<__Y>>>((_80_xs, _81_f) => ((System.Func<Dafny.ISet<__Y>>)(() => {
        var _coll1 = new System.Collections.Generic.List<__Y>();
        foreach (__X _compr_1 in (_80_xs).Elements) {
          __X _82_x = (__X)_compr_1;
          if ((_80_xs).Contains(_82_x)) {
            _coll1.Add(Dafny.Helpers.Id<Func<__X, __Y>>(_81_f)(_82_x));
          }
        }
        return Dafny.Set<__Y>.FromCollection(_coll1);
      }))())(xs, f);
      return _79_ys;
    }
    public static Dafny.ISet<__X> Filter<__X>(Dafny.ISet<__X> xs, Func<__X, bool> f)
    {
      Dafny.ISet<__X> _83_ys = Dafny.Helpers.Id<Func<Dafny.ISet<__X>, Func<__X, bool>, Dafny.ISet<__X>>>((_84_xs, _85_f) => ((System.Func<Dafny.ISet<__X>>)(() => {
        var _coll2 = new System.Collections.Generic.List<__X>();
        foreach (__X _compr_2 in (_84_xs).Elements) {
          __X _86_x = (__X)_compr_2;
          if (((_84_xs).Contains(_86_x)) && (Dafny.Helpers.Id<Func<__X, bool>>(_85_f)(_86_x))) {
            _coll2.Add(_86_x);
          }
        }
        return Dafny.Set<__X>.FromCollection(_coll2);
      }))())(xs, f);
      return _83_ys;
    }
    public static Dafny.ISet<BigInteger> SetRange(BigInteger a, BigInteger b)
    {
      Dafny.ISet<BigInteger> _87___accumulator = Dafny.Set<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((a) == (b)) {
        return Dafny.Set<BigInteger>.Union(Dafny.Set<BigInteger>.FromElements(), _87___accumulator);
      } else {
        _87___accumulator = Dafny.Set<BigInteger>.Union(_87___accumulator, Dafny.Set<BigInteger>.FromElements(a));
        BigInteger _in0 = (a) + (BigInteger.One);
        BigInteger _in1 = b;
        a = _in0;
        b = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISet<BigInteger> SetRangeZeroBound(BigInteger n) {
      return Sets_Compile.__default.SetRange(BigInteger.Zero, n);
    }
  }
} // end of namespace Sets_Compile
namespace TestHexStrings_Compile {

  public partial class __default {
    public static void BasicTests()
    {
      if (!((HexStrings_Compile.__default.ToHexString(Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(2), (byte)(255)))).Equals(Dafny.Sequence<char>.FromString("0102ff")))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/HexStrings.dfy(11,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((HexStrings_Compile.__default.FromHexString(Dafny.Sequence<char>.FromString("0102ff"))).Equals(Dafny.Sequence<byte>.FromElements((byte)(1), (byte)(2), (byte)(255))))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/HexStrings.dfy(12,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestHexStrings_Compile
namespace TestTime_Compile {

  public partial class __default {
    public static void TestNonDecreasing()
    {
      long _88_t1;
      long _out8;
      _out8 = Time.__default.CurrentRelativeTime();
      _88_t1 = _out8;
      long _89_t2;
      long _out9;
      _out9 = Time.__default.CurrentRelativeTime();
      _89_t2 = _out9;
      if (!((_89_t2) >= (_88_t1))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/Time.dfy(13,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestPositiveValues()
    {
      long _90_t1;
      long _out10;
      _out10 = Time.__default.CurrentRelativeTime();
      _90_t1 = _out10;
      long _91_t2;
      long _out11;
      _out11 = Time.__default.CurrentRelativeTime();
      _91_t2 = _out11;
      if (!(((_91_t2) - (_90_t1)) >= (0L))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/Time.dfy(19,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestTime_Compile
namespace TestUTF8_Compile {

  public partial class __default {
    public static void TestEncodeHappyCase()
    {
      Dafny.ISequence<char> _92_unicodeString;
      _92_unicodeString = Dafny.Sequence<char>.FromString("abc\u0306\u01FD\u03B2");
      Dafny.ISequence<byte> _93_expectedBytes;
      _93_expectedBytes = Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(98), (byte)(99), (byte)(204), (byte)(134), (byte)(199), (byte)(189), (byte)(206), (byte)(178));
      Dafny.ISequence<byte> _94_encoded;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _95_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _95_valueOrError0 = UTF8.__default.Encode(_92_unicodeString);
      if (!(!((_95_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(14,16): " + _95_valueOrError0);}
      _94_encoded = (_95_valueOrError0).Extract();
      if (!((_93_expectedBytes).Equals(_94_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(15,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestEncodeInvalidUnicode()
    {
      Dafny.ISequence<char> _96_invalidUnicode;
      _96_invalidUnicode = Dafny.Sequence<char>.FromString("abc\uD800");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _97_encoded;
      _97_encoded = UTF8.__default.Encode(_96_invalidUnicode);
      if (!((_97_encoded).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(22,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestDecodeHappyCase()
    {
      Dafny.ISequence<byte> _98_unicodeBytes;
      _98_unicodeBytes = Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(98), (byte)(99), (byte)(204), (byte)(134), (byte)(199), (byte)(189), (byte)(206), (byte)(178));
      Dafny.ISequence<char> _99_expectedString;
      _99_expectedString = Dafny.Sequence<char>.FromString("abc\u0306\u01FD\u03B2");
      Dafny.ISequence<char> _100_decoded;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _101_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _101_valueOrError0 = UTF8.__default.Decode(_98_unicodeBytes);
      if (!(!((_101_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(32,16): " + _101_valueOrError0);}
      _100_decoded = (_101_valueOrError0).Extract();
      if (!((_99_expectedString).Equals(_100_decoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(33,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void TestDecodeInvalidUnicode()
    {
      Dafny.ISequence<byte> _102_invalidUnicode;
      _102_invalidUnicode = Dafny.Sequence<byte>.FromElements((byte)(97), (byte)(98), (byte)(99), (byte)(237), (byte)(160), (byte)(128));
      if (!(!(UTF8.__default.ValidUTF8Seq(_102_invalidUnicode)))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(39,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((UTF8.__default.Decode(_102_invalidUnicode)).is_Failure)) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(40,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void Test1Byte()
    {
      Dafny.ISequence<char> _103_decoded;
      _103_decoded = Dafny.Sequence<char>.FromString("\u0000");
      Dafny.ISequence<byte> _104_encoded;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _105_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _105_valueOrError0 = UTF8.__default.Encode(_103_decoded);
      if (!(!((_105_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(46,16): " + _105_valueOrError0);}
      _104_encoded = (_105_valueOrError0).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(0))).Equals(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(47,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses1Byte(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(48,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<char> _106_redecoded;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _107_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _107_valueOrError1 = UTF8.__default.Decode(_104_encoded);
      if (!(!((_107_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(49,18): " + _107_valueOrError1);}
      _106_redecoded = (_107_valueOrError1).Extract();
      if (!((_103_decoded).Equals(_106_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(50,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _103_decoded = Dafny.Sequence<char>.FromString("\u0020");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _108_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _108_valueOrError2 = UTF8.__default.Encode(_103_decoded);
      if (!(!((_108_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(54,12): " + _108_valueOrError2);}
      _104_encoded = (_108_valueOrError2).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(32))).Equals(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(55,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses1Byte(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(56,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _109_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _109_valueOrError3 = UTF8.__default.Decode(_104_encoded);
      if (!(!((_109_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(57,14): " + _109_valueOrError3);}
      _106_redecoded = (_109_valueOrError3).Extract();
      if (!((_103_decoded).Equals(_106_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(58,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _103_decoded = Dafny.Sequence<char>.FromString("$");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _110_valueOrError4 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _110_valueOrError4 = UTF8.__default.Encode(_103_decoded);
      if (!(!((_110_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(61,12): " + _110_valueOrError4);}
      _104_encoded = (_110_valueOrError4).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(36))).Equals(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(62,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses1Byte(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(63,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _111_valueOrError5 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _111_valueOrError5 = UTF8.__default.Decode(_104_encoded);
      if (!(!((_111_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(64,14): " + _111_valueOrError5);}
      _106_redecoded = (_111_valueOrError5).Extract();
      if (!((_103_decoded).Equals(_106_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(65,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _103_decoded = Dafny.Sequence<char>.FromString("0");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _112_valueOrError6 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _112_valueOrError6 = UTF8.__default.Encode(_103_decoded);
      if (!(!((_112_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(68,12): " + _112_valueOrError6);}
      _104_encoded = (_112_valueOrError6).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(48))).Equals(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(69,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses1Byte(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(70,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _113_valueOrError7 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _113_valueOrError7 = UTF8.__default.Decode(_104_encoded);
      if (!(!((_113_valueOrError7).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(71,14): " + _113_valueOrError7);}
      _106_redecoded = (_113_valueOrError7).Extract();
      if (!((_103_decoded).Equals(_106_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(72,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _103_decoded = Dafny.Sequence<char>.FromString("A");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _114_valueOrError8 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _114_valueOrError8 = UTF8.__default.Encode(_103_decoded);
      if (!(!((_114_valueOrError8).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(75,12): " + _114_valueOrError8);}
      _104_encoded = (_114_valueOrError8).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(65))).Equals(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(76,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses1Byte(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(77,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _115_valueOrError9 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _115_valueOrError9 = UTF8.__default.Decode(_104_encoded);
      if (!(!((_115_valueOrError9).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(78,14): " + _115_valueOrError9);}
      _106_redecoded = (_115_valueOrError9).Extract();
      if (!((_103_decoded).Equals(_106_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(79,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _103_decoded = Dafny.Sequence<char>.FromString("a");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _116_valueOrError10 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _116_valueOrError10 = UTF8.__default.Encode(_103_decoded);
      if (!(!((_116_valueOrError10).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(82,12): " + _116_valueOrError10);}
      _104_encoded = (_116_valueOrError10).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(97))).Equals(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(83,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses1Byte(_104_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(84,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _117_valueOrError11 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _117_valueOrError11 = UTF8.__default.Decode(_104_encoded);
      if (!(!((_117_valueOrError11).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(85,14): " + _117_valueOrError11);}
      _106_redecoded = (_117_valueOrError11).Extract();
      if (!((_103_decoded).Equals(_106_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(86,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void Test2Bytes()
    {
      Dafny.ISequence<char> _118_decoded;
      _118_decoded = Dafny.Sequence<char>.FromString("\u00A3");
      Dafny.ISequence<byte> _119_encoded;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _120_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _120_valueOrError0 = UTF8.__default.Encode(_118_decoded);
      if (!(!((_120_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(92,16): " + _120_valueOrError0);}
      _119_encoded = (_120_valueOrError0).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(194), (byte)(163))).Equals(_119_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(93,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses2Bytes(_119_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(94,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<char> _121_redecoded;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _122_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _122_valueOrError1 = UTF8.__default.Decode(_119_encoded);
      if (!(!((_122_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(95,18): " + _122_valueOrError1);}
      _121_redecoded = (_122_valueOrError1).Extract();
      if (!((_118_decoded).Equals(_121_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(96,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _118_decoded = Dafny.Sequence<char>.FromString("\u00A9");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _123_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _123_valueOrError2 = UTF8.__default.Encode(_118_decoded);
      if (!(!((_123_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(100,12): " + _123_valueOrError2);}
      _119_encoded = (_123_valueOrError2).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(194), (byte)(169))).Equals(_119_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(101,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses2Bytes(_119_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(102,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _124_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _124_valueOrError3 = UTF8.__default.Decode(_119_encoded);
      if (!(!((_124_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(103,14): " + _124_valueOrError3);}
      _121_redecoded = (_124_valueOrError3).Extract();
      if (!((_118_decoded).Equals(_121_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(104,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _118_decoded = Dafny.Sequence<char>.FromString("\u00AE");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _125_valueOrError4 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _125_valueOrError4 = UTF8.__default.Encode(_118_decoded);
      if (!(!((_125_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(108,12): " + _125_valueOrError4);}
      _119_encoded = (_125_valueOrError4).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(194), (byte)(174))).Equals(_119_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(109,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses2Bytes(_119_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(110,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _126_valueOrError5 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _126_valueOrError5 = UTF8.__default.Decode(_119_encoded);
      if (!(!((_126_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(111,14): " + _126_valueOrError5);}
      _121_redecoded = (_126_valueOrError5).Extract();
      if (!((_118_decoded).Equals(_121_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(112,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _118_decoded = Dafny.Sequence<char>.FromString("\u03C0");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _127_valueOrError6 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _127_valueOrError6 = UTF8.__default.Encode(_118_decoded);
      if (!(!((_127_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(116,12): " + _127_valueOrError6);}
      _119_encoded = (_127_valueOrError6).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(207), (byte)(128))).Equals(_119_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(117,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses2Bytes(_119_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(118,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _128_valueOrError7 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _128_valueOrError7 = UTF8.__default.Decode(_119_encoded);
      if (!(!((_128_valueOrError7).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(119,14): " + _128_valueOrError7);}
      _121_redecoded = (_128_valueOrError7).Extract();
      if (!((_118_decoded).Equals(_121_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(120,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void Test3Bytes()
    {
      Dafny.ISequence<char> _129_decoded;
      _129_decoded = Dafny.Sequence<char>.FromString("\u2386");
      Dafny.ISequence<byte> _130_encoded;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _131_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _131_valueOrError0 = UTF8.__default.Encode(_129_decoded);
      if (!(!((_131_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(126,16): " + _131_valueOrError0);}
      _130_encoded = (_131_valueOrError0).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(226), (byte)(142), (byte)(134))).Equals(_130_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(127,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses3Bytes(_130_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(128,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<char> _132_redecoded;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _133_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _133_valueOrError1 = UTF8.__default.Decode(_130_encoded);
      if (!(!((_133_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(129,18): " + _133_valueOrError1);}
      _132_redecoded = (_133_valueOrError1).Extract();
      if (!((_129_decoded).Equals(_132_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(130,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _129_decoded = Dafny.Sequence<char>.FromString("\u2387");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _134_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _134_valueOrError2 = UTF8.__default.Encode(_129_decoded);
      if (!(!((_134_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(134,12): " + _134_valueOrError2);}
      _130_encoded = (_134_valueOrError2).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(226), (byte)(142), (byte)(135))).Equals(_130_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(135,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses3Bytes(_130_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(136,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _135_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _135_valueOrError3 = UTF8.__default.Decode(_130_encoded);
      if (!(!((_135_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(137,14): " + _135_valueOrError3);}
      _132_redecoded = (_135_valueOrError3).Extract();
      if (!((_129_decoded).Equals(_132_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(138,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _129_decoded = Dafny.Sequence<char>.FromString("\u231B");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _136_valueOrError4 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _136_valueOrError4 = UTF8.__default.Encode(_129_decoded);
      if (!(!((_136_valueOrError4).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(142,12): " + _136_valueOrError4);}
      _130_encoded = (_136_valueOrError4).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(226), (byte)(140), (byte)(155))).Equals(_130_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(143,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses3Bytes(_130_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(144,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _137_valueOrError5 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _137_valueOrError5 = UTF8.__default.Decode(_130_encoded);
      if (!(!((_137_valueOrError5).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(145,14): " + _137_valueOrError5);}
      _132_redecoded = (_137_valueOrError5).Extract();
      if (!((_129_decoded).Equals(_132_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(146,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _129_decoded = Dafny.Sequence<char>.FromString("\u1D78");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _138_valueOrError6 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _138_valueOrError6 = UTF8.__default.Encode(_129_decoded);
      if (!(!((_138_valueOrError6).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(150,12): " + _138_valueOrError6);}
      _130_encoded = (_138_valueOrError6).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(225), (byte)(181), (byte)(184))).Equals(_130_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(151,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses3Bytes(_130_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(152,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _139_valueOrError7 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _139_valueOrError7 = UTF8.__default.Decode(_130_encoded);
      if (!(!((_139_valueOrError7).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(153,14): " + _139_valueOrError7);}
      _132_redecoded = (_139_valueOrError7).Extract();
      if (!((_129_decoded).Equals(_132_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(154,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _129_decoded = Dafny.Sequence<char>.FromString("\u732B");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _140_valueOrError8 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _140_valueOrError8 = UTF8.__default.Encode(_129_decoded);
      if (!(!((_140_valueOrError8).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(158,12): " + _140_valueOrError8);}
      _130_encoded = (_140_valueOrError8).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(231), (byte)(140), (byte)(171))).Equals(_130_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(159,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses3Bytes(_130_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(160,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _141_valueOrError9 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _141_valueOrError9 = UTF8.__default.Decode(_130_encoded);
      if (!(!((_141_valueOrError9).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(161,14): " + _141_valueOrError9);}
      _132_redecoded = (_141_valueOrError9).Extract();
      if (!((_129_decoded).Equals(_132_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(162,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static void Test4Bytes()
    {
      Dafny.ISequence<char> _142_decoded;
      _142_decoded = Dafny.Sequence<char>.FromString("\uD808\uDC00");
      Dafny.ISequence<byte> _143_encoded;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _144_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _144_valueOrError0 = UTF8.__default.Encode(_142_decoded);
      if (!(!((_144_valueOrError0).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(168,16): " + _144_valueOrError0);}
      _143_encoded = (_144_valueOrError0).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(240), (byte)(146), (byte)(128), (byte)(128))).Equals(_143_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(169,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses4Bytes(_143_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(170,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Dafny.ISequence<char> _145_redecoded;
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _146_valueOrError1 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _146_valueOrError1 = UTF8.__default.Decode(_143_encoded);
      if (!(!((_146_valueOrError1).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(171,18): " + _146_valueOrError1);}
      _145_redecoded = (_146_valueOrError1).Extract();
      if (!((_142_decoded).Equals(_145_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(172,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      _142_decoded = Dafny.Sequence<char>.FromString("\uD835\uDFC1");
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _147_valueOrError2 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(UTF8.ValidUTF8Bytes.Default());
      _147_valueOrError2 = UTF8.__default.Encode(_142_decoded);
      if (!(!((_147_valueOrError2).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(176,12): " + _147_valueOrError2);}
      _143_encoded = (_147_valueOrError2).Extract();
      if (!((Dafny.Sequence<byte>.FromElements((byte)(240), (byte)(157), (byte)(159), (byte)(129))).Equals(_143_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(177,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!(UTF8.__default.Uses4Bytes(_143_encoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(178,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      Wrappers_Compile._IResult<Dafny.ISequence<char>, Dafny.ISequence<char>> _148_valueOrError3 = Wrappers_Compile.Result<Dafny.ISequence<char>, Dafny.ISequence<char>>.Default(Dafny.Sequence<char>.Empty);
      _148_valueOrError3 = UTF8.__default.Decode(_143_encoded);
      if (!(!((_148_valueOrError3).IsFailure()))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(179,14): " + _148_valueOrError3);}
      _145_redecoded = (_148_valueOrError3).Extract();
      if (!((_142_decoded).Equals(_145_redecoded))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/StandardLibrary/test/UTF8.dfy(180,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
  }
} // end of namespace TestUTF8_Compile
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
      bool _149_success;
      _149_success = true;
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUUID.TestFromBytesSuccess: ")));
      try {
        {
          TestUUID_Compile.__default.TestFromBytesSuccess();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _150_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_150_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUUID.TestFromBytesFailure: ")));
      try {
        {
          TestUUID_Compile.__default.TestFromBytesFailure();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _151_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_151_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUUID.TestToBytesSuccess: ")));
      try {
        {
          TestUUID_Compile.__default.TestToBytesSuccess();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUUID.TestToBytesFailure: ")));
      try {
        {
          TestUUID_Compile.__default.TestToBytesFailure();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUUID.TestRoundTripStringConversion: ")));
      try {
        {
          TestUUID_Compile.__default.TestRoundTripStringConversion();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUUID.TestRoundTripByteConversion: ")));
      try {
        {
          TestUUID_Compile.__default.TestRoundTripByteConversion();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUUID.TestGenerateAndConversion: ")));
      try {
        {
          TestUUID_Compile.__default.TestGenerateAndConversion();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestCallMany.TestBasic: ")));
      try {
        {
          TestCallMany_Compile.__default.TestBasic();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FloatCompareTest.TestOneTwoZeroMatrix: ")));
      try {
        {
          FloatCompareTest_Compile.__default.TestOneTwoZeroMatrix();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FloatCompareTest.SimpleTests: ")));
      try {
        {
          FloatCompareTest_Compile.__default.SimpleTests();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FloatCompareTest.SignTests: ")));
      try {
        {
          FloatCompareTest_Compile.__default.SignTests();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FloatCompareTest.ExponentTests: ")));
      try {
        {
          FloatCompareTest_Compile.__default.ExponentTests();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FloatCompareTest.ZeroTests: ")));
      try {
        {
          FloatCompareTest_Compile.__default.ZeroTests();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FloatCompareTest.ExtremeNumTest: ")));
      try {
        {
          FloatCompareTest_Compile.__default.ExtremeNumTest();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FloatCompareTest.InvalidTests: ")));
      try {
        {
          FloatCompareTest_Compile.__default.InvalidTests();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSeqReaderReadElements.TestSetToOrderedSequenceEmpty: ")));
      try {
        {
          TestSeqReaderReadElements_Compile.__default.TestSetToOrderedSequenceEmpty();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSeqReaderReadElements.TestSetToOrderedSequenceOneItem: ")));
      try {
        {
          TestSeqReaderReadElements_Compile.__default.TestSetToOrderedSequenceOneItem();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSeqReaderReadElements.TestSetToOrderedSequenceSimple: ")));
      try {
        {
          TestSeqReaderReadElements_Compile.__default.TestSetToOrderedSequenceSimple();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSeqReaderReadElements.TestSetToOrderedSequencePrefix: ")));
      try {
        {
          TestSeqReaderReadElements_Compile.__default.TestSetToOrderedSequencePrefix();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSeqReaderReadElements.TestSetToOrderedSequenceComplex: ")));
      try {
        {
          TestSeqReaderReadElements_Compile.__default.TestSetToOrderedSequenceComplex();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSeqReaderReadElements.TestSetToOrderedSequenceComplexReverse: ")));
      try {
        {
          TestSeqReaderReadElements_Compile.__default.TestSetToOrderedSequenceComplexReverse();
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
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSeqReaderReadElements.TestSetSequence: ")));
      try {
        {
          TestSeqReaderReadElements_Compile.__default.TestSetSequence();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _171_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_171_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestSeqReaderReadElements.TestSetToOrderedSequenceManyItems: ")));
      try {
        {
          TestSeqReaderReadElements_Compile.__default.TestSetToOrderedSequenceManyItems();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _172_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_172_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestHexStrings.BasicTests: ")));
      try {
        {
          TestHexStrings_Compile.__default.BasicTests();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _173_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_173_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestTime.TestNonDecreasing: ")));
      try {
        {
          TestTime_Compile.__default.TestNonDecreasing();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _174_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_174_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestTime.TestPositiveValues: ")));
      try {
        {
          TestTime_Compile.__default.TestPositiveValues();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _175_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_175_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUTF8.TestEncodeHappyCase: ")));
      try {
        {
          TestUTF8_Compile.__default.TestEncodeHappyCase();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _176_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_176_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUTF8.TestEncodeInvalidUnicode: ")));
      try {
        {
          TestUTF8_Compile.__default.TestEncodeInvalidUnicode();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _177_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_177_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUTF8.TestDecodeHappyCase: ")));
      try {
        {
          TestUTF8_Compile.__default.TestDecodeHappyCase();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _178_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_178_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUTF8.TestDecodeInvalidUnicode: ")));
      try {
        {
          TestUTF8_Compile.__default.TestDecodeInvalidUnicode();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _179_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_179_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUTF8.Test1Byte: ")));
      try {
        {
          TestUTF8_Compile.__default.Test1Byte();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _180_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_180_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUTF8.Test2Bytes: ")));
      try {
        {
          TestUTF8_Compile.__default.Test2Bytes();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _181_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_181_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUTF8.Test3Bytes: ")));
      try {
        {
          TestUTF8_Compile.__default.Test3Bytes();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _182_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_182_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"TestUTF8.Test4Bytes: ")));
      try {
        {
          TestUTF8_Compile.__default.Test4Bytes();
          {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"PASSED
")));
          }
        }
      }
      catch (Dafny.HaltException e) {
        var _183_haltMessage = Dafny.Sequence<char>.FromString(e.Message);
        {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"FAILED
	")));
          Dafny.Helpers.Print((_183_haltMessage));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(@"
")));
          _149_success = false;
        }
      }
      if (!(_149_success)) {
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
