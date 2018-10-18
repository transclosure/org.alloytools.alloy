package amalgam.examples;

import kodkod.ast.*;
import kodkod.ast.SubstituteVisitor;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.ast.operator.FormulaOperator;
import kodkod.instance.*;

import java.util.*;

public class RoomHeat implements KodkodExample {

    Relation x0 = Relation.unary("Int/min");
    Relation x1 = Relation.unary("Int/zero");
    Relation x2 = Relation.unary("Int/max");
    Relation x3 = Relation.nary("Int/next", 2);
    Relation x4 = Relation.unary("seq/Int");
    Relation x5 = Relation.unary("String");
    Relation x6 = Relation.unary("this/Config");
    Relation x7 = Relation.unary("this/Time");
    Relation x8 = Relation.unary("ordering/Ord");
    Relation x9 = Relation.unary("boolean/True");
    Relation x10 = Relation.unary("boolean/False");
    Relation x11 = Relation.unary("this/Config.T");
    Relation x12 = Relation.nary("this/Time.temp", 2);
    Relation x13 = Relation.nary("this/Time.heat", 2);
    Relation x14 = Relation.unary("ordering/Ord.First");
    Relation x15 = Relation.nary("ordering/Ord.Next", 2);
    Relation x16 = Relation.unary("");
    List<String> atomlist = Arrays.asList(
            "-1", "-10", "-100", "-101", "-102",
            "-103", "-104", "-105", "-106", "-107", "-108",
            "-109", "-11", "-110", "-111", "-112", "-113",
            "-114", "-115", "-116", "-117", "-118", "-119",
            "-12", "-120", "-121", "-122", "-123", "-124",
            "-125", "-126", "-127", "-128", "-13", "-14",
            "-15", "-16", "-17", "-18", "-19", "-2",
            "-20", "-21", "-22", "-23", "-24", "-25",
            "-26", "-27", "-28", "-29", "-3", "-30",
            "-31", "-32", "-33", "-34", "-35", "-36",
            "-37", "-38", "-39", "-4", "-40", "-41",
            "-42", "-43", "-44", "-45", "-46", "-47",
            "-48", "-49", "-5", "-50", "-51", "-52",
            "-53", "-54", "-55", "-56", "-57", "-58",
            "-59", "-6", "-60", "-61", "-62", "-63",
            "-64", "-65", "-66", "-67", "-68", "-69",
            "-7", "-70", "-71", "-72", "-73", "-74",
            "-75", "-76", "-77", "-78", "-79", "-8",
            "-80", "-81", "-82", "-83", "-84", "-85",
            "-86", "-87", "-88", "-89", "-9", "-90",
            "-91", "-92", "-93", "-94", "-95", "-96",
            "-97", "-98", "-99", "0", "1", "10",
            "100", "101", "102", "103", "104", "105",
            "106", "107", "108", "109", "11", "110",
            "111", "112", "113", "114", "115", "116",
            "117", "118", "119", "12", "120", "121",
            "122", "123", "124", "125", "126", "127",
            "13", "14", "15", "16", "17", "18",
            "19", "2", "20", "21", "22", "23",
            "24", "25", "26", "27", "28", "29",
            "3", "30", "31", "32", "33", "34",
            "35", "36", "37", "38", "39", "4",
            "40", "41", "42", "43", "44", "45",
            "46", "47", "48", "49", "5", "50",
            "51", "52", "53", "54", "55", "56",
            "57", "58", "59", "6", "60", "61",
            "62", "63", "64", "65", "66", "67",
            "68", "69", "7", "70", "71", "72",
            "73", "74", "75", "76", "77", "78",
            "79", "8", "80", "81", "82", "83",
            "84", "85", "86", "87", "88", "89",
            "9", "90", "91", "92", "93", "94",
            "95", "96", "97", "98", "99", "Config$0",
            "Time$0", "Time$1", "Time$10", "Time$2", "Time$3", "Time$4",
            "Time$5", "Time$6", "Time$7", "Time$8", "Time$9", "boolean/False$0",
            "boolean/True$0", "ordering/Ord$0"
    );
    Universe universe = new Universe(atomlist);
    TupleFactory factory = universe.factory();
    Bounds bounds = new Bounds(universe);

    // phis
    Formula x155, x73, x49, x39, x29;
    // univars, expressions
    Variable x152, x137, x69, x48, x38, x28;
    Expression x153, x138, x70;

    /*
      ==================================================
        kodkod formula:
      ==================================================
        no (boolean/True & boolean/False) &&
        one (this/Config . (this/Config -> this/Config.T)) &&
        (this/Config . (this/Config -> this/Config.T)) in ints &&
        (all synth_revised_restricted_this: this/Time |
          one (synth_revised_restricted_this . this/Time.temp) &&
          (synth_revised_restricted_this . this/Time.temp) in ints) &&
        (this/Time.temp . univ) in this/Time &&
        (all synth_revised_restricted_this: this/Time |
          one (synth_revised_restricted_this . this/Time.heat) &&
          (synth_revised_restricted_this . this/Time.heat) in (boolean/True +
          boolean/False)) &&
        (this/Time.heat . univ) in this/Time &&
        (all synth_revised_restricted_this: this/Time |
          int[synth_revised_restricted_this . this/Time.temp] > 0) &&
        (ordering/Ord . (ordering/Ord -> ordering/Ord.First)) in this/Time &&
        (ordering/Ord . (ordering/Ord -> ordering/Ord.Next)) in (this/Time ->
        this/Time) &&
        ord[ordering/Ord.Next, this/Time, ordering/Ord.First, ] &&
        int[ordering/Ord.First . this/Time.temp] = 66 &&
        (ordering/Ord.First . this/Time.heat) = boolean/False &&
        (all synth_revised_restricted_t: this/Time - this/Time - (ordering/Ord.Next .
         this/Time) |
          ((synth_revised_restricted_t . this/Time.heat) = boolean/True =>
           ((int[synth_revised_restricted_t . this/Time.temp] < int[this/Config.T] =>
             (((synth_revised_restricted_t . ordering/Ord.Next) . this/Time.heat) =
              boolean/True &&
              ((synth_revised_restricted_t . ordering/Ord.Next) . this/Time.temp) =
              Int[int[synth_revised_restricted_t . this/Time.temp] + 1])) &&
            (!(int[synth_revised_restricted_t . this/Time.temp] < int[this/Config.T]
               ) =>
             (((synth_revised_restricted_t . ordering/Ord.Next) . this/Time.heat) =
              boolean/False &&
              ((synth_revised_restricted_t . ordering/Ord.Next) . this/Time.temp) =
              (synth_revised_restricted_t . this/Time.temp))))) &&
          (!((synth_revised_restricted_t . this/Time.heat) = boolean/True) =>
           ((int[synth_revised_restricted_t . this/Time.temp] >= int[this/Config.T] =>
             (((synth_revised_restricted_t . ordering/Ord.Next) . this/Time.heat) =
              boolean/False &&
              ((synth_revised_restricted_t . ordering/Ord.Next) . this/Time.temp) =
              Int[int[synth_revised_restricted_t . this/Time.temp] - 1])) &&
            (!(int[synth_revised_restricted_t . this/Time.temp] >= int[this/Config.T
               ]) =>
             (((synth_revised_restricted_t . ordering/Ord.Next) . this/Time.heat) =
              boolean/True &&
              ((synth_revised_restricted_t . ordering/Ord.Next) . this/Time.temp) =
              (synth_revised_restricted_t . this/Time.temp)))))) &&
        (some eventuallyalwayscomfy2_t: this/Time - this/Time - (ordering/Ord.Next .
         this/Time) |
          int[eventuallyalwayscomfy2_t . this/Time.temp] <= 75 &&
          int[eventuallyalwayscomfy2_t . this/Time.temp] >= 70 &&
          (all eventuallyalwayscomfy2_st: eventuallyalwayscomfy2_t . ^
           ordering/Ord.Next |
            int[eventuallyalwayscomfy2_st . this/Time.temp] <= 75 &&
            int[eventuallyalwayscomfy2_st . this/Time.temp] >= 70) &&
          (some eventuallyalwayscomfy2_c: eventuallyalwayscomfy2_t . ^
           ordering/Ord.Next |
            !(eventuallyalwayscomfy2_c = (this/Time - (ordering/Ord.Next . this/Time
              ))) &&
            int[eventuallyalwayscomfy2_c . this/Time.temp] = int[(this/Time - (
            ordering/Ord.Next . this/Time)) . this/Time.temp] &&
            (eventuallyalwayscomfy2_c . this/Time.heat) = ((this/Time - (
            ordering/Ord.Next . this/Time)) . this/Time.heat))) &&
        no ({restrictedTemp_i: ints | int[restrictedTemp_i] <= 0} & (this/Time .
        this/Time.temp)) &&
        Int/min = Int/min &&
        Int/zero = Int/zero &&
        Int/max = Int/max &&
        Int/next = Int/next &&
        seq/Int = seq/Int &&
        String = String &&
        this/Config = this/Config &&
        this/Time = this/Time &&
        ordering/Ord = ordering/Ord &&
        boolean/True = boolean/True &&
        boolean/False = boolean/False &&
        this/Config.T = this/Config.T &&
        this/Time.temp = this/Time.temp &&
        this/Time.heat = this/Time.heat &&
        ordering/Ord.First = ordering/Ord.First &&
        ordering/Ord.Next = ordering/Ord.Next &&
         =
      ==================================================
    */
    public RoomHeat() {

    }
    private TupleSet x3u() {
        TupleSet x3_upper = factory.noneOf(2);
        x3_upper.add(factory.tuple("-128").product(factory.tuple("-127")));
        x3_upper.add(factory.tuple("-127").product(factory.tuple("-126")));
        x3_upper.add(factory.tuple("-126").product(factory.tuple("-125")));
        x3_upper.add(factory.tuple("-125").product(factory.tuple("-124")));
        x3_upper.add(factory.tuple("-124").product(factory.tuple("-123")));
        x3_upper.add(factory.tuple("-123").product(factory.tuple("-122")));
        x3_upper.add(factory.tuple("-122").product(factory.tuple("-121")));
        x3_upper.add(factory.tuple("-121").product(factory.tuple("-120")));
        x3_upper.add(factory.tuple("-120").product(factory.tuple("-119")));
        x3_upper.add(factory.tuple("-119").product(factory.tuple("-118")));
        x3_upper.add(factory.tuple("-118").product(factory.tuple("-117")));
        x3_upper.add(factory.tuple("-117").product(factory.tuple("-116")));
        x3_upper.add(factory.tuple("-116").product(factory.tuple("-115")));
        x3_upper.add(factory.tuple("-115").product(factory.tuple("-114")));
        x3_upper.add(factory.tuple("-114").product(factory.tuple("-113")));
        x3_upper.add(factory.tuple("-113").product(factory.tuple("-112")));
        x3_upper.add(factory.tuple("-112").product(factory.tuple("-111")));
        x3_upper.add(factory.tuple("-111").product(factory.tuple("-110")));
        x3_upper.add(factory.tuple("-110").product(factory.tuple("-109")));
        x3_upper.add(factory.tuple("-109").product(factory.tuple("-108")));
        x3_upper.add(factory.tuple("-108").product(factory.tuple("-107")));
        x3_upper.add(factory.tuple("-107").product(factory.tuple("-106")));
        x3_upper.add(factory.tuple("-106").product(factory.tuple("-105")));
        x3_upper.add(factory.tuple("-105").product(factory.tuple("-104")));
        x3_upper.add(factory.tuple("-104").product(factory.tuple("-103")));
        x3_upper.add(factory.tuple("-103").product(factory.tuple("-102")));
        x3_upper.add(factory.tuple("-102").product(factory.tuple("-101")));
        x3_upper.add(factory.tuple("-101").product(factory.tuple("-100")));
        x3_upper.add(factory.tuple("-100").product(factory.tuple("-99")));
        x3_upper.add(factory.tuple("-99").product(factory.tuple("-98")));
        x3_upper.add(factory.tuple("-98").product(factory.tuple("-97")));
        x3_upper.add(factory.tuple("-97").product(factory.tuple("-96")));
        x3_upper.add(factory.tuple("-96").product(factory.tuple("-95")));
        x3_upper.add(factory.tuple("-95").product(factory.tuple("-94")));
        x3_upper.add(factory.tuple("-94").product(factory.tuple("-93")));
        x3_upper.add(factory.tuple("-93").product(factory.tuple("-92")));
        x3_upper.add(factory.tuple("-92").product(factory.tuple("-91")));
        x3_upper.add(factory.tuple("-91").product(factory.tuple("-90")));
        x3_upper.add(factory.tuple("-90").product(factory.tuple("-89")));
        x3_upper.add(factory.tuple("-89").product(factory.tuple("-88")));
        x3_upper.add(factory.tuple("-88").product(factory.tuple("-87")));
        x3_upper.add(factory.tuple("-87").product(factory.tuple("-86")));
        x3_upper.add(factory.tuple("-86").product(factory.tuple("-85")));
        x3_upper.add(factory.tuple("-85").product(factory.tuple("-84")));
        x3_upper.add(factory.tuple("-84").product(factory.tuple("-83")));
        x3_upper.add(factory.tuple("-83").product(factory.tuple("-82")));
        x3_upper.add(factory.tuple("-82").product(factory.tuple("-81")));
        x3_upper.add(factory.tuple("-81").product(factory.tuple("-80")));
        x3_upper.add(factory.tuple("-80").product(factory.tuple("-79")));
        x3_upper.add(factory.tuple("-79").product(factory.tuple("-78")));
        x3_upper.add(factory.tuple("-78").product(factory.tuple("-77")));
        x3_upper.add(factory.tuple("-77").product(factory.tuple("-76")));
        x3_upper.add(factory.tuple("-76").product(factory.tuple("-75")));
        x3_upper.add(factory.tuple("-75").product(factory.tuple("-74")));
        x3_upper.add(factory.tuple("-74").product(factory.tuple("-73")));
        x3_upper.add(factory.tuple("-73").product(factory.tuple("-72")));
        x3_upper.add(factory.tuple("-72").product(factory.tuple("-71")));
        x3_upper.add(factory.tuple("-71").product(factory.tuple("-70")));
        x3_upper.add(factory.tuple("-70").product(factory.tuple("-69")));
        x3_upper.add(factory.tuple("-69").product(factory.tuple("-68")));
        x3_upper.add(factory.tuple("-68").product(factory.tuple("-67")));
        x3_upper.add(factory.tuple("-67").product(factory.tuple("-66")));
        x3_upper.add(factory.tuple("-66").product(factory.tuple("-65")));
        x3_upper.add(factory.tuple("-65").product(factory.tuple("-64")));
        x3_upper.add(factory.tuple("-64").product(factory.tuple("-63")));
        x3_upper.add(factory.tuple("-63").product(factory.tuple("-62")));
        x3_upper.add(factory.tuple("-62").product(factory.tuple("-61")));
        x3_upper.add(factory.tuple("-61").product(factory.tuple("-60")));
        x3_upper.add(factory.tuple("-60").product(factory.tuple("-59")));
        x3_upper.add(factory.tuple("-59").product(factory.tuple("-58")));
        x3_upper.add(factory.tuple("-58").product(factory.tuple("-57")));
        x3_upper.add(factory.tuple("-57").product(factory.tuple("-56")));
        x3_upper.add(factory.tuple("-56").product(factory.tuple("-55")));
        x3_upper.add(factory.tuple("-55").product(factory.tuple("-54")));
        x3_upper.add(factory.tuple("-54").product(factory.tuple("-53")));
        x3_upper.add(factory.tuple("-53").product(factory.tuple("-52")));
        x3_upper.add(factory.tuple("-52").product(factory.tuple("-51")));
        x3_upper.add(factory.tuple("-51").product(factory.tuple("-50")));
        x3_upper.add(factory.tuple("-50").product(factory.tuple("-49")));
        x3_upper.add(factory.tuple("-49").product(factory.tuple("-48")));
        x3_upper.add(factory.tuple("-48").product(factory.tuple("-47")));
        x3_upper.add(factory.tuple("-47").product(factory.tuple("-46")));
        x3_upper.add(factory.tuple("-46").product(factory.tuple("-45")));
        x3_upper.add(factory.tuple("-45").product(factory.tuple("-44")));
        x3_upper.add(factory.tuple("-44").product(factory.tuple("-43")));
        x3_upper.add(factory.tuple("-43").product(factory.tuple("-42")));
        x3_upper.add(factory.tuple("-42").product(factory.tuple("-41")));
        x3_upper.add(factory.tuple("-41").product(factory.tuple("-40")));
        x3_upper.add(factory.tuple("-40").product(factory.tuple("-39")));
        x3_upper.add(factory.tuple("-39").product(factory.tuple("-38")));
        x3_upper.add(factory.tuple("-38").product(factory.tuple("-37")));
        x3_upper.add(factory.tuple("-37").product(factory.tuple("-36")));
        x3_upper.add(factory.tuple("-36").product(factory.tuple("-35")));
        x3_upper.add(factory.tuple("-35").product(factory.tuple("-34")));
        x3_upper.add(factory.tuple("-34").product(factory.tuple("-33")));
        x3_upper.add(factory.tuple("-33").product(factory.tuple("-32")));
        x3_upper.add(factory.tuple("-32").product(factory.tuple("-31")));
        x3_upper.add(factory.tuple("-31").product(factory.tuple("-30")));
        x3_upper.add(factory.tuple("-30").product(factory.tuple("-29")));
        x3_upper.add(factory.tuple("-29").product(factory.tuple("-28")));
        x3_upper.add(factory.tuple("-28").product(factory.tuple("-27")));
        x3_upper.add(factory.tuple("-27").product(factory.tuple("-26")));
        x3_upper.add(factory.tuple("-26").product(factory.tuple("-25")));
        x3_upper.add(factory.tuple("-25").product(factory.tuple("-24")));
        x3_upper.add(factory.tuple("-24").product(factory.tuple("-23")));
        x3_upper.add(factory.tuple("-23").product(factory.tuple("-22")));
        x3_upper.add(factory.tuple("-22").product(factory.tuple("-21")));
        x3_upper.add(factory.tuple("-21").product(factory.tuple("-20")));
        x3_upper.add(factory.tuple("-20").product(factory.tuple("-19")));
        x3_upper.add(factory.tuple("-19").product(factory.tuple("-18")));
        x3_upper.add(factory.tuple("-18").product(factory.tuple("-17")));
        x3_upper.add(factory.tuple("-17").product(factory.tuple("-16")));
        x3_upper.add(factory.tuple("-16").product(factory.tuple("-15")));
        x3_upper.add(factory.tuple("-15").product(factory.tuple("-14")));
        x3_upper.add(factory.tuple("-14").product(factory.tuple("-13")));
        x3_upper.add(factory.tuple("-13").product(factory.tuple("-12")));
        x3_upper.add(factory.tuple("-12").product(factory.tuple("-11")));
        x3_upper.add(factory.tuple("-11").product(factory.tuple("-10")));
        x3_upper.add(factory.tuple("-10").product(factory.tuple("-9")));
        x3_upper.add(factory.tuple("-9").product(factory.tuple("-8")));
        x3_upper.add(factory.tuple("-8").product(factory.tuple("-7")));
        x3_upper.add(factory.tuple("-7").product(factory.tuple("-6")));
        x3_upper.add(factory.tuple("-6").product(factory.tuple("-5")));
        x3_upper.add(factory.tuple("-5").product(factory.tuple("-4")));
        x3_upper.add(factory.tuple("-4").product(factory.tuple("-3")));
        x3_upper.add(factory.tuple("-3").product(factory.tuple("-2")));
        x3_upper.add(factory.tuple("-2").product(factory.tuple("-1")));
        x3_upper.add(factory.tuple("-1").product(factory.tuple("0")));
        x3_upper.add(factory.tuple("0").product(factory.tuple("1")));
        x3_upper.add(factory.tuple("1").product(factory.tuple("2")));
        x3_upper.add(factory.tuple("2").product(factory.tuple("3")));
        x3_upper.add(factory.tuple("3").product(factory.tuple("4")));
        x3_upper.add(factory.tuple("4").product(factory.tuple("5")));
        x3_upper.add(factory.tuple("5").product(factory.tuple("6")));
        x3_upper.add(factory.tuple("6").product(factory.tuple("7")));
        x3_upper.add(factory.tuple("7").product(factory.tuple("8")));
        x3_upper.add(factory.tuple("8").product(factory.tuple("9")));
        x3_upper.add(factory.tuple("9").product(factory.tuple("10")));
        x3_upper.add(factory.tuple("10").product(factory.tuple("11")));
        x3_upper.add(factory.tuple("11").product(factory.tuple("12")));
        x3_upper.add(factory.tuple("12").product(factory.tuple("13")));
        x3_upper.add(factory.tuple("13").product(factory.tuple("14")));
        x3_upper.add(factory.tuple("14").product(factory.tuple("15")));
        x3_upper.add(factory.tuple("15").product(factory.tuple("16")));
        x3_upper.add(factory.tuple("16").product(factory.tuple("17")));
        x3_upper.add(factory.tuple("17").product(factory.tuple("18")));
        x3_upper.add(factory.tuple("18").product(factory.tuple("19")));
        x3_upper.add(factory.tuple("19").product(factory.tuple("20")));
        x3_upper.add(factory.tuple("20").product(factory.tuple("21")));
        x3_upper.add(factory.tuple("21").product(factory.tuple("22")));
        x3_upper.add(factory.tuple("22").product(factory.tuple("23")));
        x3_upper.add(factory.tuple("23").product(factory.tuple("24")));
        x3_upper.add(factory.tuple("24").product(factory.tuple("25")));
        x3_upper.add(factory.tuple("25").product(factory.tuple("26")));
        x3_upper.add(factory.tuple("26").product(factory.tuple("27")));
        x3_upper.add(factory.tuple("27").product(factory.tuple("28")));
        x3_upper.add(factory.tuple("28").product(factory.tuple("29")));
        x3_upper.add(factory.tuple("29").product(factory.tuple("30")));
        x3_upper.add(factory.tuple("30").product(factory.tuple("31")));
        x3_upper.add(factory.tuple("31").product(factory.tuple("32")));
        x3_upper.add(factory.tuple("32").product(factory.tuple("33")));
        x3_upper.add(factory.tuple("33").product(factory.tuple("34")));
        x3_upper.add(factory.tuple("34").product(factory.tuple("35")));
        x3_upper.add(factory.tuple("35").product(factory.tuple("36")));
        x3_upper.add(factory.tuple("36").product(factory.tuple("37")));
        x3_upper.add(factory.tuple("37").product(factory.tuple("38")));
        x3_upper.add(factory.tuple("38").product(factory.tuple("39")));
        x3_upper.add(factory.tuple("39").product(factory.tuple("40")));
        x3_upper.add(factory.tuple("40").product(factory.tuple("41")));
        x3_upper.add(factory.tuple("41").product(factory.tuple("42")));
        x3_upper.add(factory.tuple("42").product(factory.tuple("43")));
        x3_upper.add(factory.tuple("43").product(factory.tuple("44")));
        x3_upper.add(factory.tuple("44").product(factory.tuple("45")));
        x3_upper.add(factory.tuple("45").product(factory.tuple("46")));
        x3_upper.add(factory.tuple("46").product(factory.tuple("47")));
        x3_upper.add(factory.tuple("47").product(factory.tuple("48")));
        x3_upper.add(factory.tuple("48").product(factory.tuple("49")));
        x3_upper.add(factory.tuple("49").product(factory.tuple("50")));
        x3_upper.add(factory.tuple("50").product(factory.tuple("51")));
        x3_upper.add(factory.tuple("51").product(factory.tuple("52")));
        x3_upper.add(factory.tuple("52").product(factory.tuple("53")));
        x3_upper.add(factory.tuple("53").product(factory.tuple("54")));
        x3_upper.add(factory.tuple("54").product(factory.tuple("55")));
        x3_upper.add(factory.tuple("55").product(factory.tuple("56")));
        x3_upper.add(factory.tuple("56").product(factory.tuple("57")));
        x3_upper.add(factory.tuple("57").product(factory.tuple("58")));
        x3_upper.add(factory.tuple("58").product(factory.tuple("59")));
        x3_upper.add(factory.tuple("59").product(factory.tuple("60")));
        x3_upper.add(factory.tuple("60").product(factory.tuple("61")));
        x3_upper.add(factory.tuple("61").product(factory.tuple("62")));
        x3_upper.add(factory.tuple("62").product(factory.tuple("63")));
        x3_upper.add(factory.tuple("63").product(factory.tuple("64")));
        x3_upper.add(factory.tuple("64").product(factory.tuple("65")));
        x3_upper.add(factory.tuple("65").product(factory.tuple("66")));
        x3_upper.add(factory.tuple("66").product(factory.tuple("67")));
        x3_upper.add(factory.tuple("67").product(factory.tuple("68")));
        x3_upper.add(factory.tuple("68").product(factory.tuple("69")));
        x3_upper.add(factory.tuple("69").product(factory.tuple("70")));
        x3_upper.add(factory.tuple("70").product(factory.tuple("71")));
        x3_upper.add(factory.tuple("71").product(factory.tuple("72")));
        x3_upper.add(factory.tuple("72").product(factory.tuple("73")));
        x3_upper.add(factory.tuple("73").product(factory.tuple("74")));
        x3_upper.add(factory.tuple("74").product(factory.tuple("75")));
        x3_upper.add(factory.tuple("75").product(factory.tuple("76")));
        x3_upper.add(factory.tuple("76").product(factory.tuple("77")));
        x3_upper.add(factory.tuple("77").product(factory.tuple("78")));
        x3_upper.add(factory.tuple("78").product(factory.tuple("79")));
        x3_upper.add(factory.tuple("79").product(factory.tuple("80")));
        x3_upper.add(factory.tuple("80").product(factory.tuple("81")));
        x3_upper.add(factory.tuple("81").product(factory.tuple("82")));
        x3_upper.add(factory.tuple("82").product(factory.tuple("83")));
        x3_upper.add(factory.tuple("83").product(factory.tuple("84")));
        x3_upper.add(factory.tuple("84").product(factory.tuple("85")));
        x3_upper.add(factory.tuple("85").product(factory.tuple("86")));
        x3_upper.add(factory.tuple("86").product(factory.tuple("87")));
        x3_upper.add(factory.tuple("87").product(factory.tuple("88")));
        x3_upper.add(factory.tuple("88").product(factory.tuple("89")));
        x3_upper.add(factory.tuple("89").product(factory.tuple("90")));
        x3_upper.add(factory.tuple("90").product(factory.tuple("91")));
        x3_upper.add(factory.tuple("91").product(factory.tuple("92")));
        x3_upper.add(factory.tuple("92").product(factory.tuple("93")));
        x3_upper.add(factory.tuple("93").product(factory.tuple("94")));
        x3_upper.add(factory.tuple("94").product(factory.tuple("95")));
        x3_upper.add(factory.tuple("95").product(factory.tuple("96")));
        x3_upper.add(factory.tuple("96").product(factory.tuple("97")));
        x3_upper.add(factory.tuple("97").product(factory.tuple("98")));
        x3_upper.add(factory.tuple("98").product(factory.tuple("99")));
        x3_upper.add(factory.tuple("99").product(factory.tuple("100")));
        x3_upper.add(factory.tuple("100").product(factory.tuple("101")));
        x3_upper.add(factory.tuple("101").product(factory.tuple("102")));
        x3_upper.add(factory.tuple("102").product(factory.tuple("103")));
        x3_upper.add(factory.tuple("103").product(factory.tuple("104")));
        x3_upper.add(factory.tuple("104").product(factory.tuple("105")));
        x3_upper.add(factory.tuple("105").product(factory.tuple("106")));
        x3_upper.add(factory.tuple("106").product(factory.tuple("107")));
        x3_upper.add(factory.tuple("107").product(factory.tuple("108")));
        x3_upper.add(factory.tuple("108").product(factory.tuple("109")));
        x3_upper.add(factory.tuple("109").product(factory.tuple("110")));
        x3_upper.add(factory.tuple("110").product(factory.tuple("111")));
        x3_upper.add(factory.tuple("111").product(factory.tuple("112")));
        x3_upper.add(factory.tuple("112").product(factory.tuple("113")));
        x3_upper.add(factory.tuple("113").product(factory.tuple("114")));
        x3_upper.add(factory.tuple("114").product(factory.tuple("115")));
        x3_upper.add(factory.tuple("115").product(factory.tuple("116")));
        x3_upper.add(factory.tuple("116").product(factory.tuple("117")));
        x3_upper.add(factory.tuple("117").product(factory.tuple("118")));
        x3_upper.add(factory.tuple("118").product(factory.tuple("119")));
        x3_upper.add(factory.tuple("119").product(factory.tuple("120")));
        x3_upper.add(factory.tuple("120").product(factory.tuple("121")));
        x3_upper.add(factory.tuple("121").product(factory.tuple("122")));
        x3_upper.add(factory.tuple("122").product(factory.tuple("123")));
        x3_upper.add(factory.tuple("123").product(factory.tuple("124")));
        x3_upper.add(factory.tuple("124").product(factory.tuple("125")));
        x3_upper.add(factory.tuple("125").product(factory.tuple("126")));
        x3_upper.add(factory.tuple("126").product(factory.tuple("127")));
        return x3_upper;
    }
    private TupleSet x11u() {
        TupleSet x11_upper = factory.noneOf(1);
        x11_upper.add(factory.tuple("-128"));
        x11_upper.add(factory.tuple("-127"));
        x11_upper.add(factory.tuple("-126"));
        x11_upper.add(factory.tuple("-125"));
        x11_upper.add(factory.tuple("-124"));
        x11_upper.add(factory.tuple("-123"));
        x11_upper.add(factory.tuple("-122"));
        x11_upper.add(factory.tuple("-121"));
        x11_upper.add(factory.tuple("-120"));
        x11_upper.add(factory.tuple("-119"));
        x11_upper.add(factory.tuple("-118"));
        x11_upper.add(factory.tuple("-117"));
        x11_upper.add(factory.tuple("-116"));
        x11_upper.add(factory.tuple("-115"));
        x11_upper.add(factory.tuple("-114"));
        x11_upper.add(factory.tuple("-113"));
        x11_upper.add(factory.tuple("-112"));
        x11_upper.add(factory.tuple("-111"));
        x11_upper.add(factory.tuple("-110"));
        x11_upper.add(factory.tuple("-109"));
        x11_upper.add(factory.tuple("-108"));
        x11_upper.add(factory.tuple("-107"));
        x11_upper.add(factory.tuple("-106"));
        x11_upper.add(factory.tuple("-105"));
        x11_upper.add(factory.tuple("-104"));
        x11_upper.add(factory.tuple("-103"));
        x11_upper.add(factory.tuple("-102"));
        x11_upper.add(factory.tuple("-101"));
        x11_upper.add(factory.tuple("-100"));
        x11_upper.add(factory.tuple("-99"));
        x11_upper.add(factory.tuple("-98"));
        x11_upper.add(factory.tuple("-97"));
        x11_upper.add(factory.tuple("-96"));
        x11_upper.add(factory.tuple("-95"));
        x11_upper.add(factory.tuple("-94"));
        x11_upper.add(factory.tuple("-93"));
        x11_upper.add(factory.tuple("-92"));
        x11_upper.add(factory.tuple("-91"));
        x11_upper.add(factory.tuple("-90"));
        x11_upper.add(factory.tuple("-89"));
        x11_upper.add(factory.tuple("-88"));
        x11_upper.add(factory.tuple("-87"));
        x11_upper.add(factory.tuple("-86"));
        x11_upper.add(factory.tuple("-85"));
        x11_upper.add(factory.tuple("-84"));
        x11_upper.add(factory.tuple("-83"));
        x11_upper.add(factory.tuple("-82"));
        x11_upper.add(factory.tuple("-81"));
        x11_upper.add(factory.tuple("-80"));
        x11_upper.add(factory.tuple("-79"));
        x11_upper.add(factory.tuple("-78"));
        x11_upper.add(factory.tuple("-77"));
        x11_upper.add(factory.tuple("-76"));
        x11_upper.add(factory.tuple("-75"));
        x11_upper.add(factory.tuple("-74"));
        x11_upper.add(factory.tuple("-73"));
        x11_upper.add(factory.tuple("-72"));
        x11_upper.add(factory.tuple("-71"));
        x11_upper.add(factory.tuple("-70"));
        x11_upper.add(factory.tuple("-69"));
        x11_upper.add(factory.tuple("-68"));
        x11_upper.add(factory.tuple("-67"));
        x11_upper.add(factory.tuple("-66"));
        x11_upper.add(factory.tuple("-65"));
        x11_upper.add(factory.tuple("-64"));
        x11_upper.add(factory.tuple("-63"));
        x11_upper.add(factory.tuple("-62"));
        x11_upper.add(factory.tuple("-61"));
        x11_upper.add(factory.tuple("-60"));
        x11_upper.add(factory.tuple("-59"));
        x11_upper.add(factory.tuple("-58"));
        x11_upper.add(factory.tuple("-57"));
        x11_upper.add(factory.tuple("-56"));
        x11_upper.add(factory.tuple("-55"));
        x11_upper.add(factory.tuple("-54"));
        x11_upper.add(factory.tuple("-53"));
        x11_upper.add(factory.tuple("-52"));
        x11_upper.add(factory.tuple("-51"));
        x11_upper.add(factory.tuple("-50"));
        x11_upper.add(factory.tuple("-49"));
        x11_upper.add(factory.tuple("-48"));
        x11_upper.add(factory.tuple("-47"));
        x11_upper.add(factory.tuple("-46"));
        x11_upper.add(factory.tuple("-45"));
        x11_upper.add(factory.tuple("-44"));
        x11_upper.add(factory.tuple("-43"));
        x11_upper.add(factory.tuple("-42"));
        x11_upper.add(factory.tuple("-41"));
        x11_upper.add(factory.tuple("-40"));
        x11_upper.add(factory.tuple("-39"));
        x11_upper.add(factory.tuple("-38"));
        x11_upper.add(factory.tuple("-37"));
        x11_upper.add(factory.tuple("-36"));
        x11_upper.add(factory.tuple("-35"));
        x11_upper.add(factory.tuple("-34"));
        x11_upper.add(factory.tuple("-33"));
        x11_upper.add(factory.tuple("-32"));
        x11_upper.add(factory.tuple("-31"));
        x11_upper.add(factory.tuple("-30"));
        x11_upper.add(factory.tuple("-29"));
        x11_upper.add(factory.tuple("-28"));
        x11_upper.add(factory.tuple("-27"));
        x11_upper.add(factory.tuple("-26"));
        x11_upper.add(factory.tuple("-25"));
        x11_upper.add(factory.tuple("-24"));
        x11_upper.add(factory.tuple("-23"));
        x11_upper.add(factory.tuple("-22"));
        x11_upper.add(factory.tuple("-21"));
        x11_upper.add(factory.tuple("-20"));
        x11_upper.add(factory.tuple("-19"));
        x11_upper.add(factory.tuple("-18"));
        x11_upper.add(factory.tuple("-17"));
        x11_upper.add(factory.tuple("-16"));
        x11_upper.add(factory.tuple("-15"));
        x11_upper.add(factory.tuple("-14"));
        x11_upper.add(factory.tuple("-13"));
        x11_upper.add(factory.tuple("-12"));
        x11_upper.add(factory.tuple("-11"));
        x11_upper.add(factory.tuple("-10"));
        x11_upper.add(factory.tuple("-9"));
        x11_upper.add(factory.tuple("-8"));
        x11_upper.add(factory.tuple("-7"));
        x11_upper.add(factory.tuple("-6"));
        x11_upper.add(factory.tuple("-5"));
        x11_upper.add(factory.tuple("-4"));
        x11_upper.add(factory.tuple("-3"));
        x11_upper.add(factory.tuple("-2"));
        x11_upper.add(factory.tuple("-1"));
        x11_upper.add(factory.tuple("0"));
        x11_upper.add(factory.tuple("1"));
        x11_upper.add(factory.tuple("2"));
        x11_upper.add(factory.tuple("3"));
        x11_upper.add(factory.tuple("4"));
        x11_upper.add(factory.tuple("5"));
        x11_upper.add(factory.tuple("6"));
        x11_upper.add(factory.tuple("7"));
        x11_upper.add(factory.tuple("8"));
        x11_upper.add(factory.tuple("9"));
        x11_upper.add(factory.tuple("10"));
        x11_upper.add(factory.tuple("11"));
        x11_upper.add(factory.tuple("12"));
        x11_upper.add(factory.tuple("13"));
        x11_upper.add(factory.tuple("14"));
        x11_upper.add(factory.tuple("15"));
        x11_upper.add(factory.tuple("16"));
        x11_upper.add(factory.tuple("17"));
        x11_upper.add(factory.tuple("18"));
        x11_upper.add(factory.tuple("19"));
        x11_upper.add(factory.tuple("20"));
        x11_upper.add(factory.tuple("21"));
        x11_upper.add(factory.tuple("22"));
        x11_upper.add(factory.tuple("23"));
        x11_upper.add(factory.tuple("24"));
        x11_upper.add(factory.tuple("25"));
        x11_upper.add(factory.tuple("26"));
        x11_upper.add(factory.tuple("27"));
        x11_upper.add(factory.tuple("28"));
        x11_upper.add(factory.tuple("29"));
        x11_upper.add(factory.tuple("30"));
        x11_upper.add(factory.tuple("31"));
        x11_upper.add(factory.tuple("32"));
        x11_upper.add(factory.tuple("33"));
        x11_upper.add(factory.tuple("34"));
        x11_upper.add(factory.tuple("35"));
        x11_upper.add(factory.tuple("36"));
        x11_upper.add(factory.tuple("37"));
        x11_upper.add(factory.tuple("38"));
        x11_upper.add(factory.tuple("39"));
        x11_upper.add(factory.tuple("40"));
        x11_upper.add(factory.tuple("41"));
        x11_upper.add(factory.tuple("42"));
        x11_upper.add(factory.tuple("43"));
        x11_upper.add(factory.tuple("44"));
        x11_upper.add(factory.tuple("45"));
        x11_upper.add(factory.tuple("46"));
        x11_upper.add(factory.tuple("47"));
        x11_upper.add(factory.tuple("48"));
        x11_upper.add(factory.tuple("49"));
        x11_upper.add(factory.tuple("50"));
        x11_upper.add(factory.tuple("51"));
        x11_upper.add(factory.tuple("52"));
        x11_upper.add(factory.tuple("53"));
        x11_upper.add(factory.tuple("54"));
        x11_upper.add(factory.tuple("55"));
        x11_upper.add(factory.tuple("56"));
        x11_upper.add(factory.tuple("57"));
        x11_upper.add(factory.tuple("58"));
        x11_upper.add(factory.tuple("59"));
        x11_upper.add(factory.tuple("60"));
        x11_upper.add(factory.tuple("61"));
        x11_upper.add(factory.tuple("62"));
        x11_upper.add(factory.tuple("63"));
        x11_upper.add(factory.tuple("64"));
        x11_upper.add(factory.tuple("65"));
        x11_upper.add(factory.tuple("66"));
        x11_upper.add(factory.tuple("67"));
        x11_upper.add(factory.tuple("68"));
        x11_upper.add(factory.tuple("69"));
        x11_upper.add(factory.tuple("70"));
        x11_upper.add(factory.tuple("71"));
        x11_upper.add(factory.tuple("72"));
        x11_upper.add(factory.tuple("73"));
        x11_upper.add(factory.tuple("74"));
        x11_upper.add(factory.tuple("75"));
        x11_upper.add(factory.tuple("76"));
        x11_upper.add(factory.tuple("77"));
        x11_upper.add(factory.tuple("78"));
        x11_upper.add(factory.tuple("79"));
        x11_upper.add(factory.tuple("80"));
        x11_upper.add(factory.tuple("81"));
        x11_upper.add(factory.tuple("82"));
        x11_upper.add(factory.tuple("83"));
        x11_upper.add(factory.tuple("84"));
        x11_upper.add(factory.tuple("85"));
        x11_upper.add(factory.tuple("86"));
        x11_upper.add(factory.tuple("87"));
        x11_upper.add(factory.tuple("88"));
        x11_upper.add(factory.tuple("89"));
        x11_upper.add(factory.tuple("90"));
        x11_upper.add(factory.tuple("91"));
        x11_upper.add(factory.tuple("92"));
        x11_upper.add(factory.tuple("93"));
        x11_upper.add(factory.tuple("94"));
        x11_upper.add(factory.tuple("95"));
        x11_upper.add(factory.tuple("96"));
        x11_upper.add(factory.tuple("97"));
        x11_upper.add(factory.tuple("98"));
        x11_upper.add(factory.tuple("99"));
        x11_upper.add(factory.tuple("100"));
        x11_upper.add(factory.tuple("101"));
        x11_upper.add(factory.tuple("102"));
        x11_upper.add(factory.tuple("103"));
        x11_upper.add(factory.tuple("104"));
        x11_upper.add(factory.tuple("105"));
        x11_upper.add(factory.tuple("106"));
        x11_upper.add(factory.tuple("107"));
        x11_upper.add(factory.tuple("108"));
        x11_upper.add(factory.tuple("109"));
        x11_upper.add(factory.tuple("110"));
        x11_upper.add(factory.tuple("111"));
        x11_upper.add(factory.tuple("112"));
        x11_upper.add(factory.tuple("113"));
        x11_upper.add(factory.tuple("114"));
        x11_upper.add(factory.tuple("115"));
        x11_upper.add(factory.tuple("116"));
        x11_upper.add(factory.tuple("117"));
        x11_upper.add(factory.tuple("118"));
        x11_upper.add(factory.tuple("119"));
        x11_upper.add(factory.tuple("120"));
        x11_upper.add(factory.tuple("121"));
        x11_upper.add(factory.tuple("122"));
        x11_upper.add(factory.tuple("123"));
        x11_upper.add(factory.tuple("124"));
        x11_upper.add(factory.tuple("125"));
        x11_upper.add(factory.tuple("126"));
        x11_upper.add(factory.tuple("127"));
        return x11_upper;
    }
    private TupleSet x12u() {
        TupleSet x12_upper = factory.noneOf(2);
        for(int i=0; i<=10; i++) {
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-128")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-127")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-126")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-125")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-124")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-123")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-122")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-121")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-120")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-119")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-118")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-117")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-116")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-115")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-114")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-113")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-112")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-111")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-110")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-109")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-108")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-107")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-106")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-105")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-104")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-103")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-102")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-101")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-100")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-99")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-98")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-97")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-96")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-95")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-94")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-93")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-92")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-91")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-90")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-89")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-88")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-87")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-86")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-85")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-84")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-83")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-82")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-81")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-80")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-79")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-78")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-77")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-76")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-75")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-74")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-73")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-72")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-71")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-70")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-69")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-68")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-67")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-66")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-65")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-64")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-63")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-62")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-61")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-60")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-59")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-58")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-57")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-56")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-55")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-54")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-53")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-52")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-51")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-50")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-49")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-48")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-47")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-46")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-45")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-44")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-43")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-42")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-41")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-40")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-39")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-38")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-37")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-36")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-35")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-34")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-33")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-32")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-31")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-30")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-29")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-28")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-27")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-26")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-25")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-24")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-23")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-22")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-21")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-20")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-19")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-18")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-17")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-16")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-15")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-14")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-13")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-12")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-11")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-10")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-9")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-8")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-7")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-6")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-5")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-4")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-3")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-2")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("-1")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("0")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("1")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("2")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("3")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("4")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("5")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("6")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("7")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("8")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("9")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("10")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("11")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("12")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("13")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("14")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("15")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("16")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("17")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("18")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("19")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("20")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("21")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("22")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("23")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("24")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("25")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("26")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("27")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("28")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("29")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("30")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("31")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("32")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("33")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("34")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("35")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("36")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("37")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("38")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("39")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("40")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("41")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("42")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("43")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("44")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("45")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("46")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("47")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("48")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("49")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("50")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("51")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("52")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("53")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("54")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("55")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("56")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("57")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("58")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("59")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("60")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("61")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("62")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("63")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("64")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("65")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("66")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("67")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("68")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("69")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("70")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("71")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("72")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("73")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("74")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("75")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("76")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("77")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("78")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("79")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("80")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("81")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("82")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("83")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("84")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("85")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("86")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("87")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("88")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("89")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("90")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("91")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("92")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("93")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("94")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("95")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("96")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("97")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("98")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("99")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("100")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("101")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("102")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("103")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("104")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("105")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("106")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("107")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("108")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("109")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("110")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("111")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("112")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("113")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("114")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("115")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("116")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("117")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("118")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("119")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("120")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("121")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("122")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("123")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("124")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("125")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("126")));
            x12_upper.add(factory.tuple("Time$"+i).product(factory.tuple("127")));
        }
        return x12_upper;
    }
    @Override
    public Bounds bounds(int n) {

        TupleSet x0_upper = factory.noneOf(1);
        x0_upper.add(factory.tuple("-128"));
        bounds.boundExactly(x0, x0_upper);

        TupleSet x1_upper = factory.noneOf(1);
        x1_upper.add(factory.tuple("0"));
        bounds.boundExactly(x1, x1_upper);

        TupleSet x2_upper = factory.noneOf(1);
        x2_upper.add(factory.tuple("127"));
        bounds.boundExactly(x2, x2_upper);

        bounds.boundExactly(x3, x3u());

        TupleSet x4_upper = factory.noneOf(1);
        x4_upper.add(factory.tuple("0"));
        x4_upper.add(factory.tuple("1"));
        x4_upper.add(factory.tuple("2"));
        x4_upper.add(factory.tuple("3"));
        bounds.boundExactly(x4, x4_upper);

        TupleSet x5_upper = factory.noneOf(1);
        bounds.boundExactly(x5, x5_upper);

        TupleSet x6_upper = factory.noneOf(1);
        x6_upper.add(factory.tuple("Config$0"));
        bounds.boundExactly(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("Time$0"));
        x7_upper.add(factory.tuple("Time$1"));
        x7_upper.add(factory.tuple("Time$2"));
        x7_upper.add(factory.tuple("Time$3"));
        x7_upper.add(factory.tuple("Time$4"));
        x7_upper.add(factory.tuple("Time$5"));
        x7_upper.add(factory.tuple("Time$6"));
        x7_upper.add(factory.tuple("Time$7"));
        x7_upper.add(factory.tuple("Time$8"));
        x7_upper.add(factory.tuple("Time$9"));
        x7_upper.add(factory.tuple("Time$10"));
        bounds.boundExactly(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(1);
        x8_upper.add(factory.tuple("ordering/Ord$0"));
        bounds.boundExactly(x8, x8_upper);

        TupleSet x9_upper = factory.noneOf(1);
        x9_upper.add(factory.tuple("boolean/True$0"));
        bounds.boundExactly(x9, x9_upper);

        TupleSet x10_upper = factory.noneOf(1);
        x10_upper.add(factory.tuple("boolean/False$0"));
        bounds.boundExactly(x10, x10_upper);

        bounds.bound(x11, x11u());

        bounds.bound(x12, x12u());

        TupleSet x13_upper = factory.noneOf(2);
        x13_upper.add(factory.tuple("Time$0").product(factory.tuple("boolean/True$0")));
        x13_upper.add(factory.tuple("Time$0").product(factory.tuple("boolean/False$0")));
        x13_upper.add(factory.tuple("Time$1").product(factory.tuple("boolean/True$0")));
        x13_upper.add(factory.tuple("Time$1").product(factory.tuple("boolean/False$0")));
        x13_upper.add(factory.tuple("Time$2").product(factory.tuple("boolean/True$0")));
        x13_upper.add(factory.tuple("Time$2").product(factory.tuple("boolean/False$0")));
        x13_upper.add(factory.tuple("Time$3").product(factory.tuple("boolean/True$0")));
        x13_upper.add(factory.tuple("Time$3").product(factory.tuple("boolean/False$0")));
        x13_upper.add(factory.tuple("Time$4").product(factory.tuple("boolean/True$0")));
        x13_upper.add(factory.tuple("Time$4").product(factory.tuple("boolean/False$0")));
        x13_upper.add(factory.tuple("Time$5").product(factory.tuple("boolean/True$0")));
        x13_upper.add(factory.tuple("Time$5").product(factory.tuple("boolean/False$0")));
        x13_upper.add(factory.tuple("Time$6").product(factory.tuple("boolean/True$0")));
        x13_upper.add(factory.tuple("Time$6").product(factory.tuple("boolean/False$0")));
        x13_upper.add(factory.tuple("Time$7").product(factory.tuple("boolean/True$0")));
        x13_upper.add(factory.tuple("Time$7").product(factory.tuple("boolean/False$0")));
        x13_upper.add(factory.tuple("Time$8").product(factory.tuple("boolean/True$0")));
        x13_upper.add(factory.tuple("Time$8").product(factory.tuple("boolean/False$0")));
        x13_upper.add(factory.tuple("Time$9").product(factory.tuple("boolean/True$0")));
        x13_upper.add(factory.tuple("Time$9").product(factory.tuple("boolean/False$0")));
        x13_upper.add(factory.tuple("Time$10").product(factory.tuple("boolean/True$0")));
        x13_upper.add(factory.tuple("Time$10").product(factory.tuple("boolean/False$0")));
        bounds.bound(x13, x13_upper);

        // FIXME naive cegis has trouble with first/ordering in this space, giving some help
        TupleSet x14_upper = factory.noneOf(1);
        x14_upper.add(factory.tuple("Time$0"));
        //x14_upper.add(factory.tuple("Time$1"));
        //x14_upper.add(factory.tuple("Time$2"));
        //x14_upper.add(factory.tuple("Time$3"));
        //x14_upper.add(factory.tuple("Time$4"));
        //x14_upper.add(factory.tuple("Time$5"));
        //x14_upper.add(factory.tuple("Time$6"));
        //x14_upper.add(factory.tuple("Time$7"));
        //x14_upper.add(factory.tuple("Time$8"));
        //x14_upper.add(factory.tuple("Time$9"));
        //x14_upper.add(factory.tuple("Time$10"));
        bounds.boundExactly(x14, x14_upper);

        TupleSet x15_upper = factory.noneOf(2);
        //x15_upper.add(factory.tuple("Time$0").product(factory.tuple("Time$0")));
        x15_upper.add(factory.tuple("Time$0").product(factory.tuple("Time$1")));
        //x15_upper.add(factory.tuple("Time$0").product(factory.tuple("Time$2")));
        //x15_upper.add(factory.tuple("Time$0").product(factory.tuple("Time$3")));
        //x15_upper.add(factory.tuple("Time$0").product(factory.tuple("Time$4")));
        //x15_upper.add(factory.tuple("Time$0").product(factory.tuple("Time$5")));
        //x15_upper.add(factory.tuple("Time$0").product(factory.tuple("Time$6")));
        //x15_upper.add(factory.tuple("Time$0").product(factory.tuple("Time$7")));
        //x15_upper.add(factory.tuple("Time$0").product(factory.tuple("Time$8")));
        //x15_upper.add(factory.tuple("Time$0").product(factory.tuple("Time$9")));
        //x15_upper.add(factory.tuple("Time$0").product(factory.tuple("Time$10")));
        //x15_upper.add(factory.tuple("Time$1").product(factory.tuple("Time$0")));
        //x15_upper.add(factory.tuple("Time$1").product(factory.tuple("Time$1")));
        x15_upper.add(factory.tuple("Time$1").product(factory.tuple("Time$2")));
        //x15_upper.add(factory.tuple("Time$1").product(factory.tuple("Time$3")));
        //x15_upper.add(factory.tuple("Time$1").product(factory.tuple("Time$4")));
        //x15_upper.add(factory.tuple("Time$1").product(factory.tuple("Time$5")));
        //x15_upper.add(factory.tuple("Time$1").product(factory.tuple("Time$6")));
        //x15_upper.add(factory.tuple("Time$1").product(factory.tuple("Time$7")));
        //x15_upper.add(factory.tuple("Time$1").product(factory.tuple("Time$8")));
        //x15_upper.add(factory.tuple("Time$1").product(factory.tuple("Time$9")));
        //x15_upper.add(factory.tuple("Time$1").product(factory.tuple("Time$10")));
        //x15_upper.add(factory.tuple("Time$2").product(factory.tuple("Time$0")));
        //x15_upper.add(factory.tuple("Time$2").product(factory.tuple("Time$1")));
        //x15_upper.add(factory.tuple("Time$2").product(factory.tuple("Time$2")));
        x15_upper.add(factory.tuple("Time$2").product(factory.tuple("Time$3")));
        //x15_upper.add(factory.tuple("Time$2").product(factory.tuple("Time$4")));
        //x15_upper.add(factory.tuple("Time$2").product(factory.tuple("Time$5")));
        //x15_upper.add(factory.tuple("Time$2").product(factory.tuple("Time$6")));
        //x15_upper.add(factory.tuple("Time$2").product(factory.tuple("Time$7")));
        //x15_upper.add(factory.tuple("Time$2").product(factory.tuple("Time$8")));
        //x15_upper.add(factory.tuple("Time$2").product(factory.tuple("Time$9")));
        //x15_upper.add(factory.tuple("Time$2").product(factory.tuple("Time$10")));
        //x15_upper.add(factory.tuple("Time$3").product(factory.tuple("Time$0")));
        //x15_upper.add(factory.tuple("Time$3").product(factory.tuple("Time$1")));
        //x15_upper.add(factory.tuple("Time$3").product(factory.tuple("Time$2")));
        //x15_upper.add(factory.tuple("Time$3").product(factory.tuple("Time$3")));
        x15_upper.add(factory.tuple("Time$3").product(factory.tuple("Time$4")));
        //x15_upper.add(factory.tuple("Time$3").product(factory.tuple("Time$5")));
        //x15_upper.add(factory.tuple("Time$3").product(factory.tuple("Time$6")));
        //x15_upper.add(factory.tuple("Time$3").product(factory.tuple("Time$7")));
        //x15_upper.add(factory.tuple("Time$3").product(factory.tuple("Time$8")));
        //x15_upper.add(factory.tuple("Time$3").product(factory.tuple("Time$9")));
        //x15_upper.add(factory.tuple("Time$3").product(factory.tuple("Time$10")));
        //x15_upper.add(factory.tuple("Time$4").product(factory.tuple("Time$0")));
        //x15_upper.add(factory.tuple("Time$4").product(factory.tuple("Time$1")));
        //x15_upper.add(factory.tuple("Time$4").product(factory.tuple("Time$2")));
        //x15_upper.add(factory.tuple("Time$4").product(factory.tuple("Time$3")));
        //x15_upper.add(factory.tuple("Time$4").product(factory.tuple("Time$4")));
        x15_upper.add(factory.tuple("Time$4").product(factory.tuple("Time$5")));
        //x15_upper.add(factory.tuple("Time$4").product(factory.tuple("Time$6")));
        //x15_upper.add(factory.tuple("Time$4").product(factory.tuple("Time$7")));
        //x15_upper.add(factory.tuple("Time$4").product(factory.tuple("Time$8")));
        //x15_upper.add(factory.tuple("Time$4").product(factory.tuple("Time$9")));
        //x15_upper.add(factory.tuple("Time$4").product(factory.tuple("Time$10")));
        //x15_upper.add(factory.tuple("Time$5").product(factory.tuple("Time$0")));
        //x15_upper.add(factory.tuple("Time$5").product(factory.tuple("Time$1")));
        //x15_upper.add(factory.tuple("Time$5").product(factory.tuple("Time$2")));
        //x15_upper.add(factory.tuple("Time$5").product(factory.tuple("Time$3")));
        //x15_upper.add(factory.tuple("Time$5").product(factory.tuple("Time$4")));
        //x15_upper.add(factory.tuple("Time$5").product(factory.tuple("Time$5")));
        x15_upper.add(factory.tuple("Time$5").product(factory.tuple("Time$6")));
        //x15_upper.add(factory.tuple("Time$5").product(factory.tuple("Time$7")));
        //x15_upper.add(factory.tuple("Time$5").product(factory.tuple("Time$8")));
        //x15_upper.add(factory.tuple("Time$5").product(factory.tuple("Time$9")));
        //x15_upper.add(factory.tuple("Time$5").product(factory.tuple("Time$10")));
        //x15_upper.add(factory.tuple("Time$6").product(factory.tuple("Time$0")));
        //x15_upper.add(factory.tuple("Time$6").product(factory.tuple("Time$1")));
        //x15_upper.add(factory.tuple("Time$6").product(factory.tuple("Time$2")));
        //x15_upper.add(factory.tuple("Time$6").product(factory.tuple("Time$3")));
        //x15_upper.add(factory.tuple("Time$6").product(factory.tuple("Time$4")));
        //x15_upper.add(factory.tuple("Time$6").product(factory.tuple("Time$5")));
        //x15_upper.add(factory.tuple("Time$6").product(factory.tuple("Time$6")));
        x15_upper.add(factory.tuple("Time$6").product(factory.tuple("Time$7")));
        //x15_upper.add(factory.tuple("Time$6").product(factory.tuple("Time$8")));
        //x15_upper.add(factory.tuple("Time$6").product(factory.tuple("Time$9")));
        //x15_upper.add(factory.tuple("Time$6").product(factory.tuple("Time$10")));
        //x15_upper.add(factory.tuple("Time$7").product(factory.tuple("Time$0")));
        //x15_upper.add(factory.tuple("Time$7").product(factory.tuple("Time$1")));
        //x15_upper.add(factory.tuple("Time$7").product(factory.tuple("Time$2")));
        //x15_upper.add(factory.tuple("Time$7").product(factory.tuple("Time$3")));
        //x15_upper.add(factory.tuple("Time$7").product(factory.tuple("Time$4")));
        //x15_upper.add(factory.tuple("Time$7").product(factory.tuple("Time$5")));
        //x15_upper.add(factory.tuple("Time$7").product(factory.tuple("Time$6")));
        //x15_upper.add(factory.tuple("Time$7").product(factory.tuple("Time$7")));
        x15_upper.add(factory.tuple("Time$7").product(factory.tuple("Time$8")));
        //x15_upper.add(factory.tuple("Time$7").product(factory.tuple("Time$9")));
        //x15_upper.add(factory.tuple("Time$7").product(factory.tuple("Time$10")));
        //x15_upper.add(factory.tuple("Time$8").product(factory.tuple("Time$0")));
        //x15_upper.add(factory.tuple("Time$8").product(factory.tuple("Time$1")));
        //x15_upper.add(factory.tuple("Time$8").product(factory.tuple("Time$2")));
        //x15_upper.add(factory.tuple("Time$8").product(factory.tuple("Time$3")));
        //x15_upper.add(factory.tuple("Time$8").product(factory.tuple("Time$4")));
        //x15_upper.add(factory.tuple("Time$8").product(factory.tuple("Time$5")));
        //x15_upper.add(factory.tuple("Time$8").product(factory.tuple("Time$6")));
        //x15_upper.add(factory.tuple("Time$8").product(factory.tuple("Time$7")));
        //x15_upper.add(factory.tuple("Time$8").product(factory.tuple("Time$8")));
        x15_upper.add(factory.tuple("Time$8").product(factory.tuple("Time$9")));
        //x15_upper.add(factory.tuple("Time$8").product(factory.tuple("Time$10")));
        //x15_upper.add(factory.tuple("Time$9").product(factory.tuple("Time$0")));
        //x15_upper.add(factory.tuple("Time$9").product(factory.tuple("Time$1")));
        //x15_upper.add(factory.tuple("Time$9").product(factory.tuple("Time$2")));
        //x15_upper.add(factory.tuple("Time$9").product(factory.tuple("Time$3")));
        //x15_upper.add(factory.tuple("Time$9").product(factory.tuple("Time$4")));
        //x15_upper.add(factory.tuple("Time$9").product(factory.tuple("Time$5")));
        //x15_upper.add(factory.tuple("Time$9").product(factory.tuple("Time$6")));
        //x15_upper.add(factory.tuple("Time$9").product(factory.tuple("Time$7")));
        //x15_upper.add(factory.tuple("Time$9").product(factory.tuple("Time$8")));
        //x15_upper.add(factory.tuple("Time$9").product(factory.tuple("Time$9")));
        x15_upper.add(factory.tuple("Time$9").product(factory.tuple("Time$10")));
        //x15_upper.add(factory.tuple("Time$10").product(factory.tuple("Time$0")));
        //x15_upper.add(factory.tuple("Time$10").product(factory.tuple("Time$1")));
        //x15_upper.add(factory.tuple("Time$10").product(factory.tuple("Time$2")));
        //x15_upper.add(factory.tuple("Time$10").product(factory.tuple("Time$3")));
        //x15_upper.add(factory.tuple("Time$10").product(factory.tuple("Time$4")));
        //x15_upper.add(factory.tuple("Time$10").product(factory.tuple("Time$5")));
        //x15_upper.add(factory.tuple("Time$10").product(factory.tuple("Time$6")));
        //x15_upper.add(factory.tuple("Time$10").product(factory.tuple("Time$7")));
        //x15_upper.add(factory.tuple("Time$10").product(factory.tuple("Time$8")));
        //x15_upper.add(factory.tuple("Time$10").product(factory.tuple("Time$9")));
        //x15_upper.add(factory.tuple("Time$10").product(factory.tuple("Time$10")));
        bounds.boundExactly(x15, x15_upper);

        TupleSet x16_upper = factory.noneOf(1);
        x16_upper.add(factory.tuple("Time$0"));
        x16_upper.add(factory.tuple("Time$1"));
        x16_upper.add(factory.tuple("Time$2"));
        x16_upper.add(factory.tuple("Time$3"));
        x16_upper.add(factory.tuple("Time$4"));
        x16_upper.add(factory.tuple("Time$5"));
        x16_upper.add(factory.tuple("Time$6"));
        x16_upper.add(factory.tuple("Time$7"));
        x16_upper.add(factory.tuple("Time$8"));
        x16_upper.add(factory.tuple("Time$9"));
        x16_upper.add(factory.tuple("Time$10"));
        bounds.bound(x16, x16_upper);

        bounds.boundExactly(-128,factory.range(factory.tuple("-128"),factory.tuple("-128")));
        bounds.boundExactly(-127,factory.range(factory.tuple("-127"),factory.tuple("-127")));
        bounds.boundExactly(-126,factory.range(factory.tuple("-126"),factory.tuple("-126")));
        bounds.boundExactly(-125,factory.range(factory.tuple("-125"),factory.tuple("-125")));
        bounds.boundExactly(-124,factory.range(factory.tuple("-124"),factory.tuple("-124")));
        bounds.boundExactly(-123,factory.range(factory.tuple("-123"),factory.tuple("-123")));
        bounds.boundExactly(-122,factory.range(factory.tuple("-122"),factory.tuple("-122")));
        bounds.boundExactly(-121,factory.range(factory.tuple("-121"),factory.tuple("-121")));
        bounds.boundExactly(-120,factory.range(factory.tuple("-120"),factory.tuple("-120")));
        bounds.boundExactly(-119,factory.range(factory.tuple("-119"),factory.tuple("-119")));
        bounds.boundExactly(-118,factory.range(factory.tuple("-118"),factory.tuple("-118")));
        bounds.boundExactly(-117,factory.range(factory.tuple("-117"),factory.tuple("-117")));
        bounds.boundExactly(-116,factory.range(factory.tuple("-116"),factory.tuple("-116")));
        bounds.boundExactly(-115,factory.range(factory.tuple("-115"),factory.tuple("-115")));
        bounds.boundExactly(-114,factory.range(factory.tuple("-114"),factory.tuple("-114")));
        bounds.boundExactly(-113,factory.range(factory.tuple("-113"),factory.tuple("-113")));
        bounds.boundExactly(-112,factory.range(factory.tuple("-112"),factory.tuple("-112")));
        bounds.boundExactly(-111,factory.range(factory.tuple("-111"),factory.tuple("-111")));
        bounds.boundExactly(-110,factory.range(factory.tuple("-110"),factory.tuple("-110")));
        bounds.boundExactly(-109,factory.range(factory.tuple("-109"),factory.tuple("-109")));
        bounds.boundExactly(-108,factory.range(factory.tuple("-108"),factory.tuple("-108")));
        bounds.boundExactly(-107,factory.range(factory.tuple("-107"),factory.tuple("-107")));
        bounds.boundExactly(-106,factory.range(factory.tuple("-106"),factory.tuple("-106")));
        bounds.boundExactly(-105,factory.range(factory.tuple("-105"),factory.tuple("-105")));
        bounds.boundExactly(-104,factory.range(factory.tuple("-104"),factory.tuple("-104")));
        bounds.boundExactly(-103,factory.range(factory.tuple("-103"),factory.tuple("-103")));
        bounds.boundExactly(-102,factory.range(factory.tuple("-102"),factory.tuple("-102")));
        bounds.boundExactly(-101,factory.range(factory.tuple("-101"),factory.tuple("-101")));
        bounds.boundExactly(-100,factory.range(factory.tuple("-100"),factory.tuple("-100")));
        bounds.boundExactly(-99,factory.range(factory.tuple("-99"),factory.tuple("-99")));
        bounds.boundExactly(-98,factory.range(factory.tuple("-98"),factory.tuple("-98")));
        bounds.boundExactly(-97,factory.range(factory.tuple("-97"),factory.tuple("-97")));
        bounds.boundExactly(-96,factory.range(factory.tuple("-96"),factory.tuple("-96")));
        bounds.boundExactly(-95,factory.range(factory.tuple("-95"),factory.tuple("-95")));
        bounds.boundExactly(-94,factory.range(factory.tuple("-94"),factory.tuple("-94")));
        bounds.boundExactly(-93,factory.range(factory.tuple("-93"),factory.tuple("-93")));
        bounds.boundExactly(-92,factory.range(factory.tuple("-92"),factory.tuple("-92")));
        bounds.boundExactly(-91,factory.range(factory.tuple("-91"),factory.tuple("-91")));
        bounds.boundExactly(-90,factory.range(factory.tuple("-90"),factory.tuple("-90")));
        bounds.boundExactly(-89,factory.range(factory.tuple("-89"),factory.tuple("-89")));
        bounds.boundExactly(-88,factory.range(factory.tuple("-88"),factory.tuple("-88")));
        bounds.boundExactly(-87,factory.range(factory.tuple("-87"),factory.tuple("-87")));
        bounds.boundExactly(-86,factory.range(factory.tuple("-86"),factory.tuple("-86")));
        bounds.boundExactly(-85,factory.range(factory.tuple("-85"),factory.tuple("-85")));
        bounds.boundExactly(-84,factory.range(factory.tuple("-84"),factory.tuple("-84")));
        bounds.boundExactly(-83,factory.range(factory.tuple("-83"),factory.tuple("-83")));
        bounds.boundExactly(-82,factory.range(factory.tuple("-82"),factory.tuple("-82")));
        bounds.boundExactly(-81,factory.range(factory.tuple("-81"),factory.tuple("-81")));
        bounds.boundExactly(-80,factory.range(factory.tuple("-80"),factory.tuple("-80")));
        bounds.boundExactly(-79,factory.range(factory.tuple("-79"),factory.tuple("-79")));
        bounds.boundExactly(-78,factory.range(factory.tuple("-78"),factory.tuple("-78")));
        bounds.boundExactly(-77,factory.range(factory.tuple("-77"),factory.tuple("-77")));
        bounds.boundExactly(-76,factory.range(factory.tuple("-76"),factory.tuple("-76")));
        bounds.boundExactly(-75,factory.range(factory.tuple("-75"),factory.tuple("-75")));
        bounds.boundExactly(-74,factory.range(factory.tuple("-74"),factory.tuple("-74")));
        bounds.boundExactly(-73,factory.range(factory.tuple("-73"),factory.tuple("-73")));
        bounds.boundExactly(-72,factory.range(factory.tuple("-72"),factory.tuple("-72")));
        bounds.boundExactly(-71,factory.range(factory.tuple("-71"),factory.tuple("-71")));
        bounds.boundExactly(-70,factory.range(factory.tuple("-70"),factory.tuple("-70")));
        bounds.boundExactly(-69,factory.range(factory.tuple("-69"),factory.tuple("-69")));
        bounds.boundExactly(-68,factory.range(factory.tuple("-68"),factory.tuple("-68")));
        bounds.boundExactly(-67,factory.range(factory.tuple("-67"),factory.tuple("-67")));
        bounds.boundExactly(-66,factory.range(factory.tuple("-66"),factory.tuple("-66")));
        bounds.boundExactly(-65,factory.range(factory.tuple("-65"),factory.tuple("-65")));
        bounds.boundExactly(-64,factory.range(factory.tuple("-64"),factory.tuple("-64")));
        bounds.boundExactly(-63,factory.range(factory.tuple("-63"),factory.tuple("-63")));
        bounds.boundExactly(-62,factory.range(factory.tuple("-62"),factory.tuple("-62")));
        bounds.boundExactly(-61,factory.range(factory.tuple("-61"),factory.tuple("-61")));
        bounds.boundExactly(-60,factory.range(factory.tuple("-60"),factory.tuple("-60")));
        bounds.boundExactly(-59,factory.range(factory.tuple("-59"),factory.tuple("-59")));
        bounds.boundExactly(-58,factory.range(factory.tuple("-58"),factory.tuple("-58")));
        bounds.boundExactly(-57,factory.range(factory.tuple("-57"),factory.tuple("-57")));
        bounds.boundExactly(-56,factory.range(factory.tuple("-56"),factory.tuple("-56")));
        bounds.boundExactly(-55,factory.range(factory.tuple("-55"),factory.tuple("-55")));
        bounds.boundExactly(-54,factory.range(factory.tuple("-54"),factory.tuple("-54")));
        bounds.boundExactly(-53,factory.range(factory.tuple("-53"),factory.tuple("-53")));
        bounds.boundExactly(-52,factory.range(factory.tuple("-52"),factory.tuple("-52")));
        bounds.boundExactly(-51,factory.range(factory.tuple("-51"),factory.tuple("-51")));
        bounds.boundExactly(-50,factory.range(factory.tuple("-50"),factory.tuple("-50")));
        bounds.boundExactly(-49,factory.range(factory.tuple("-49"),factory.tuple("-49")));
        bounds.boundExactly(-48,factory.range(factory.tuple("-48"),factory.tuple("-48")));
        bounds.boundExactly(-47,factory.range(factory.tuple("-47"),factory.tuple("-47")));
        bounds.boundExactly(-46,factory.range(factory.tuple("-46"),factory.tuple("-46")));
        bounds.boundExactly(-45,factory.range(factory.tuple("-45"),factory.tuple("-45")));
        bounds.boundExactly(-44,factory.range(factory.tuple("-44"),factory.tuple("-44")));
        bounds.boundExactly(-43,factory.range(factory.tuple("-43"),factory.tuple("-43")));
        bounds.boundExactly(-42,factory.range(factory.tuple("-42"),factory.tuple("-42")));
        bounds.boundExactly(-41,factory.range(factory.tuple("-41"),factory.tuple("-41")));
        bounds.boundExactly(-40,factory.range(factory.tuple("-40"),factory.tuple("-40")));
        bounds.boundExactly(-39,factory.range(factory.tuple("-39"),factory.tuple("-39")));
        bounds.boundExactly(-38,factory.range(factory.tuple("-38"),factory.tuple("-38")));
        bounds.boundExactly(-37,factory.range(factory.tuple("-37"),factory.tuple("-37")));
        bounds.boundExactly(-36,factory.range(factory.tuple("-36"),factory.tuple("-36")));
        bounds.boundExactly(-35,factory.range(factory.tuple("-35"),factory.tuple("-35")));
        bounds.boundExactly(-34,factory.range(factory.tuple("-34"),factory.tuple("-34")));
        bounds.boundExactly(-33,factory.range(factory.tuple("-33"),factory.tuple("-33")));
        bounds.boundExactly(-32,factory.range(factory.tuple("-32"),factory.tuple("-32")));
        bounds.boundExactly(-31,factory.range(factory.tuple("-31"),factory.tuple("-31")));
        bounds.boundExactly(-30,factory.range(factory.tuple("-30"),factory.tuple("-30")));
        bounds.boundExactly(-29,factory.range(factory.tuple("-29"),factory.tuple("-29")));
        bounds.boundExactly(-28,factory.range(factory.tuple("-28"),factory.tuple("-28")));
        bounds.boundExactly(-27,factory.range(factory.tuple("-27"),factory.tuple("-27")));
        bounds.boundExactly(-26,factory.range(factory.tuple("-26"),factory.tuple("-26")));
        bounds.boundExactly(-25,factory.range(factory.tuple("-25"),factory.tuple("-25")));
        bounds.boundExactly(-24,factory.range(factory.tuple("-24"),factory.tuple("-24")));
        bounds.boundExactly(-23,factory.range(factory.tuple("-23"),factory.tuple("-23")));
        bounds.boundExactly(-22,factory.range(factory.tuple("-22"),factory.tuple("-22")));
        bounds.boundExactly(-21,factory.range(factory.tuple("-21"),factory.tuple("-21")));
        bounds.boundExactly(-20,factory.range(factory.tuple("-20"),factory.tuple("-20")));
        bounds.boundExactly(-19,factory.range(factory.tuple("-19"),factory.tuple("-19")));
        bounds.boundExactly(-18,factory.range(factory.tuple("-18"),factory.tuple("-18")));
        bounds.boundExactly(-17,factory.range(factory.tuple("-17"),factory.tuple("-17")));
        bounds.boundExactly(-16,factory.range(factory.tuple("-16"),factory.tuple("-16")));
        bounds.boundExactly(-15,factory.range(factory.tuple("-15"),factory.tuple("-15")));
        bounds.boundExactly(-14,factory.range(factory.tuple("-14"),factory.tuple("-14")));
        bounds.boundExactly(-13,factory.range(factory.tuple("-13"),factory.tuple("-13")));
        bounds.boundExactly(-12,factory.range(factory.tuple("-12"),factory.tuple("-12")));
        bounds.boundExactly(-11,factory.range(factory.tuple("-11"),factory.tuple("-11")));
        bounds.boundExactly(-10,factory.range(factory.tuple("-10"),factory.tuple("-10")));
        bounds.boundExactly(-9,factory.range(factory.tuple("-9"),factory.tuple("-9")));
        bounds.boundExactly(-8,factory.range(factory.tuple("-8"),factory.tuple("-8")));
        bounds.boundExactly(-7,factory.range(factory.tuple("-7"),factory.tuple("-7")));
        bounds.boundExactly(-6,factory.range(factory.tuple("-6"),factory.tuple("-6")));
        bounds.boundExactly(-5,factory.range(factory.tuple("-5"),factory.tuple("-5")));
        bounds.boundExactly(-4,factory.range(factory.tuple("-4"),factory.tuple("-4")));
        bounds.boundExactly(-3,factory.range(factory.tuple("-3"),factory.tuple("-3")));
        bounds.boundExactly(-2,factory.range(factory.tuple("-2"),factory.tuple("-2")));
        bounds.boundExactly(-1,factory.range(factory.tuple("-1"),factory.tuple("-1")));
        bounds.boundExactly(0,factory.range(factory.tuple("0"),factory.tuple("0")));
        bounds.boundExactly(1,factory.range(factory.tuple("1"),factory.tuple("1")));
        bounds.boundExactly(2,factory.range(factory.tuple("2"),factory.tuple("2")));
        bounds.boundExactly(3,factory.range(factory.tuple("3"),factory.tuple("3")));
        bounds.boundExactly(4,factory.range(factory.tuple("4"),factory.tuple("4")));
        bounds.boundExactly(5,factory.range(factory.tuple("5"),factory.tuple("5")));
        bounds.boundExactly(6,factory.range(factory.tuple("6"),factory.tuple("6")));
        bounds.boundExactly(7,factory.range(factory.tuple("7"),factory.tuple("7")));
        bounds.boundExactly(8,factory.range(factory.tuple("8"),factory.tuple("8")));
        bounds.boundExactly(9,factory.range(factory.tuple("9"),factory.tuple("9")));
        bounds.boundExactly(10,factory.range(factory.tuple("10"),factory.tuple("10")));
        bounds.boundExactly(11,factory.range(factory.tuple("11"),factory.tuple("11")));
        bounds.boundExactly(12,factory.range(factory.tuple("12"),factory.tuple("12")));
        bounds.boundExactly(13,factory.range(factory.tuple("13"),factory.tuple("13")));
        bounds.boundExactly(14,factory.range(factory.tuple("14"),factory.tuple("14")));
        bounds.boundExactly(15,factory.range(factory.tuple("15"),factory.tuple("15")));
        bounds.boundExactly(16,factory.range(factory.tuple("16"),factory.tuple("16")));
        bounds.boundExactly(17,factory.range(factory.tuple("17"),factory.tuple("17")));
        bounds.boundExactly(18,factory.range(factory.tuple("18"),factory.tuple("18")));
        bounds.boundExactly(19,factory.range(factory.tuple("19"),factory.tuple("19")));
        bounds.boundExactly(20,factory.range(factory.tuple("20"),factory.tuple("20")));
        bounds.boundExactly(21,factory.range(factory.tuple("21"),factory.tuple("21")));
        bounds.boundExactly(22,factory.range(factory.tuple("22"),factory.tuple("22")));
        bounds.boundExactly(23,factory.range(factory.tuple("23"),factory.tuple("23")));
        bounds.boundExactly(24,factory.range(factory.tuple("24"),factory.tuple("24")));
        bounds.boundExactly(25,factory.range(factory.tuple("25"),factory.tuple("25")));
        bounds.boundExactly(26,factory.range(factory.tuple("26"),factory.tuple("26")));
        bounds.boundExactly(27,factory.range(factory.tuple("27"),factory.tuple("27")));
        bounds.boundExactly(28,factory.range(factory.tuple("28"),factory.tuple("28")));
        bounds.boundExactly(29,factory.range(factory.tuple("29"),factory.tuple("29")));
        bounds.boundExactly(30,factory.range(factory.tuple("30"),factory.tuple("30")));
        bounds.boundExactly(31,factory.range(factory.tuple("31"),factory.tuple("31")));
        bounds.boundExactly(32,factory.range(factory.tuple("32"),factory.tuple("32")));
        bounds.boundExactly(33,factory.range(factory.tuple("33"),factory.tuple("33")));
        bounds.boundExactly(34,factory.range(factory.tuple("34"),factory.tuple("34")));
        bounds.boundExactly(35,factory.range(factory.tuple("35"),factory.tuple("35")));
        bounds.boundExactly(36,factory.range(factory.tuple("36"),factory.tuple("36")));
        bounds.boundExactly(37,factory.range(factory.tuple("37"),factory.tuple("37")));
        bounds.boundExactly(38,factory.range(factory.tuple("38"),factory.tuple("38")));
        bounds.boundExactly(39,factory.range(factory.tuple("39"),factory.tuple("39")));
        bounds.boundExactly(40,factory.range(factory.tuple("40"),factory.tuple("40")));
        bounds.boundExactly(41,factory.range(factory.tuple("41"),factory.tuple("41")));
        bounds.boundExactly(42,factory.range(factory.tuple("42"),factory.tuple("42")));
        bounds.boundExactly(43,factory.range(factory.tuple("43"),factory.tuple("43")));
        bounds.boundExactly(44,factory.range(factory.tuple("44"),factory.tuple("44")));
        bounds.boundExactly(45,factory.range(factory.tuple("45"),factory.tuple("45")));
        bounds.boundExactly(46,factory.range(factory.tuple("46"),factory.tuple("46")));
        bounds.boundExactly(47,factory.range(factory.tuple("47"),factory.tuple("47")));
        bounds.boundExactly(48,factory.range(factory.tuple("48"),factory.tuple("48")));
        bounds.boundExactly(49,factory.range(factory.tuple("49"),factory.tuple("49")));
        bounds.boundExactly(50,factory.range(factory.tuple("50"),factory.tuple("50")));
        bounds.boundExactly(51,factory.range(factory.tuple("51"),factory.tuple("51")));
        bounds.boundExactly(52,factory.range(factory.tuple("52"),factory.tuple("52")));
        bounds.boundExactly(53,factory.range(factory.tuple("53"),factory.tuple("53")));
        bounds.boundExactly(54,factory.range(factory.tuple("54"),factory.tuple("54")));
        bounds.boundExactly(55,factory.range(factory.tuple("55"),factory.tuple("55")));
        bounds.boundExactly(56,factory.range(factory.tuple("56"),factory.tuple("56")));
        bounds.boundExactly(57,factory.range(factory.tuple("57"),factory.tuple("57")));
        bounds.boundExactly(58,factory.range(factory.tuple("58"),factory.tuple("58")));
        bounds.boundExactly(59,factory.range(factory.tuple("59"),factory.tuple("59")));
        bounds.boundExactly(60,factory.range(factory.tuple("60"),factory.tuple("60")));
        bounds.boundExactly(61,factory.range(factory.tuple("61"),factory.tuple("61")));
        bounds.boundExactly(62,factory.range(factory.tuple("62"),factory.tuple("62")));
        bounds.boundExactly(63,factory.range(factory.tuple("63"),factory.tuple("63")));
        bounds.boundExactly(64,factory.range(factory.tuple("64"),factory.tuple("64")));
        bounds.boundExactly(65,factory.range(factory.tuple("65"),factory.tuple("65")));
        bounds.boundExactly(66,factory.range(factory.tuple("66"),factory.tuple("66")));
        bounds.boundExactly(67,factory.range(factory.tuple("67"),factory.tuple("67")));
        bounds.boundExactly(68,factory.range(factory.tuple("68"),factory.tuple("68")));
        bounds.boundExactly(69,factory.range(factory.tuple("69"),factory.tuple("69")));
        bounds.boundExactly(70,factory.range(factory.tuple("70"),factory.tuple("70")));
        bounds.boundExactly(71,factory.range(factory.tuple("71"),factory.tuple("71")));
        bounds.boundExactly(72,factory.range(factory.tuple("72"),factory.tuple("72")));
        bounds.boundExactly(73,factory.range(factory.tuple("73"),factory.tuple("73")));
        bounds.boundExactly(74,factory.range(factory.tuple("74"),factory.tuple("74")));
        bounds.boundExactly(75,factory.range(factory.tuple("75"),factory.tuple("75")));
        bounds.boundExactly(76,factory.range(factory.tuple("76"),factory.tuple("76")));
        bounds.boundExactly(77,factory.range(factory.tuple("77"),factory.tuple("77")));
        bounds.boundExactly(78,factory.range(factory.tuple("78"),factory.tuple("78")));
        bounds.boundExactly(79,factory.range(factory.tuple("79"),factory.tuple("79")));
        bounds.boundExactly(80,factory.range(factory.tuple("80"),factory.tuple("80")));
        bounds.boundExactly(81,factory.range(factory.tuple("81"),factory.tuple("81")));
        bounds.boundExactly(82,factory.range(factory.tuple("82"),factory.tuple("82")));
        bounds.boundExactly(83,factory.range(factory.tuple("83"),factory.tuple("83")));
        bounds.boundExactly(84,factory.range(factory.tuple("84"),factory.tuple("84")));
        bounds.boundExactly(85,factory.range(factory.tuple("85"),factory.tuple("85")));
        bounds.boundExactly(86,factory.range(factory.tuple("86"),factory.tuple("86")));
        bounds.boundExactly(87,factory.range(factory.tuple("87"),factory.tuple("87")));
        bounds.boundExactly(88,factory.range(factory.tuple("88"),factory.tuple("88")));
        bounds.boundExactly(89,factory.range(factory.tuple("89"),factory.tuple("89")));
        bounds.boundExactly(90,factory.range(factory.tuple("90"),factory.tuple("90")));
        bounds.boundExactly(91,factory.range(factory.tuple("91"),factory.tuple("91")));
        bounds.boundExactly(92,factory.range(factory.tuple("92"),factory.tuple("92")));
        bounds.boundExactly(93,factory.range(factory.tuple("93"),factory.tuple("93")));
        bounds.boundExactly(94,factory.range(factory.tuple("94"),factory.tuple("94")));
        bounds.boundExactly(95,factory.range(factory.tuple("95"),factory.tuple("95")));
        bounds.boundExactly(96,factory.range(factory.tuple("96"),factory.tuple("96")));
        bounds.boundExactly(97,factory.range(factory.tuple("97"),factory.tuple("97")));
        bounds.boundExactly(98,factory.range(factory.tuple("98"),factory.tuple("98")));
        bounds.boundExactly(99,factory.range(factory.tuple("99"),factory.tuple("99")));
        bounds.boundExactly(100,factory.range(factory.tuple("100"),factory.tuple("100")));
        bounds.boundExactly(101,factory.range(factory.tuple("101"),factory.tuple("101")));
        bounds.boundExactly(102,factory.range(factory.tuple("102"),factory.tuple("102")));
        bounds.boundExactly(103,factory.range(factory.tuple("103"),factory.tuple("103")));
        bounds.boundExactly(104,factory.range(factory.tuple("104"),factory.tuple("104")));
        bounds.boundExactly(105,factory.range(factory.tuple("105"),factory.tuple("105")));
        bounds.boundExactly(106,factory.range(factory.tuple("106"),factory.tuple("106")));
        bounds.boundExactly(107,factory.range(factory.tuple("107"),factory.tuple("107")));
        bounds.boundExactly(108,factory.range(factory.tuple("108"),factory.tuple("108")));
        bounds.boundExactly(109,factory.range(factory.tuple("109"),factory.tuple("109")));
        bounds.boundExactly(110,factory.range(factory.tuple("110"),factory.tuple("110")));
        bounds.boundExactly(111,factory.range(factory.tuple("111"),factory.tuple("111")));
        bounds.boundExactly(112,factory.range(factory.tuple("112"),factory.tuple("112")));
        bounds.boundExactly(113,factory.range(factory.tuple("113"),factory.tuple("113")));
        bounds.boundExactly(114,factory.range(factory.tuple("114"),factory.tuple("114")));
        bounds.boundExactly(115,factory.range(factory.tuple("115"),factory.tuple("115")));
        bounds.boundExactly(116,factory.range(factory.tuple("116"),factory.tuple("116")));
        bounds.boundExactly(117,factory.range(factory.tuple("117"),factory.tuple("117")));
        bounds.boundExactly(118,factory.range(factory.tuple("118"),factory.tuple("118")));
        bounds.boundExactly(119,factory.range(factory.tuple("119"),factory.tuple("119")));
        bounds.boundExactly(120,factory.range(factory.tuple("120"),factory.tuple("120")));
        bounds.boundExactly(121,factory.range(factory.tuple("121"),factory.tuple("121")));
        bounds.boundExactly(122,factory.range(factory.tuple("122"),factory.tuple("122")));
        bounds.boundExactly(123,factory.range(factory.tuple("123"),factory.tuple("123")));
        bounds.boundExactly(124,factory.range(factory.tuple("124"),factory.tuple("124")));
        bounds.boundExactly(125,factory.range(factory.tuple("125"),factory.tuple("125")));
        bounds.boundExactly(126,factory.range(factory.tuple("126"),factory.tuple("126")));
        bounds.boundExactly(127,factory.range(factory.tuple("127"),factory.tuple("127")));

        // Add constant symbols
        for(String a: atomlist) {
            Relation ra = Relation.unary(a);
            bounds.boundExactly(ra, factory.setOf(factory.tuple(a)));
        }

        return bounds;
    }
    @Override
    public Formula verifyformula() {
        Expression x19=x9.intersection(x10);
        Formula x18=x19.no();
        Expression x23=x6.product(x11);
        Expression x22=x6.join(x23);
        Formula x21=x22.one();
        Formula x24=x22.in(Expression.INTS);
        Formula x20=x21.and(x24);
        x28=Variable.unary("synth_revised_restricted_this");
        Decls x27=x28.oneOf(x7);
        Expression x31=x28.join(x12);
        Formula x30=x31.one();
        Formula x32=x31.in(Expression.INTS);
        x29=x30.and(x32);
        Formula x26=x29.forAll(x27);
        Expression x34=x12.join(Expression.UNIV);
        Formula x33=x34.in(x7);
        x38=Variable.unary("synth_revised_restricted_this");
        Decls x37=x38.oneOf(x7);
        Expression x41=x38.join(x13);
        Formula x40=x41.one();
        Expression x43=x9.union(x10);
        Formula x42=x41.in(x43);
        x39=x40.and(x42);
        Formula x36=x39.forAll(x37);
        Expression x45=x13.join(Expression.UNIV);
        Formula x44=x45.in(x7);
        x48=Variable.unary("synth_revised_restricted_this");
        Decls x47=x48.oneOf(x7);
        Expression x51=x48.join(x12);
        IntExpression x50=x51.sum();
        IntExpression x52=IntConstant.constant(0);
        x49=x50.gt(x52);
        Formula x46=x49.forAll(x47);
        Expression x55=x8.product(x14);
        Expression x54=x8.join(x55);
        Formula x53=x54.in(x7);
        Expression x58=x8.product(x15);
        Expression x57=x8.join(x58);
        Expression x59=x7.product(x7);
        Formula x56=x57.in(x59);
        Formula x60=x15.totalOrder(x7,x14,x16);
        Expression x63=x14.join(x12);
        IntExpression x62=x63.sum();
        IntExpression x64=IntConstant.constant(66);
        Formula x61=x62.eq(x64);
        Expression x66=x14.join(x13);
        Formula x65=x66.eq(x10);
        x69=Variable.unary("synth_revised_restricted_t");
        Expression x72=x15.join(x7);
        Expression x71=x7.difference(x72);
        x70=x7.difference(x71);
        Decls x68=x69.oneOf(x70);
        Expression x76=x69.join(x13);
        Formula x75=x76.eq(x9);
        Expression x81=x69.join(x12);
        IntExpression x80=x81.sum();
        IntExpression x82=x11.sum();
        Formula x79=x80.lt(x82);
        Expression x86=x69.join(x15);
        Expression x85=x86.join(x13);
        Formula x84=x85.eq(x9);
        Expression x89=x69.join(x15);
        Expression x88=x89.join(x12);
        Expression x93=x69.join(x12);
        IntExpression x92=x93.sum();
        IntExpression x94=IntConstant.constant(1);
        IntExpression x91=x92.plus(x94);
        Expression x90=x91.toExpression();
        Formula x87=x88.eq(x90);
        Formula x83=x84.and(x87);
        Formula x78=x79.implies(x83);
        Formula x96=x79.not();
        Expression x100=x69.join(x15);
        Expression x99=x100.join(x13);
        Formula x98=x99.eq(x10);
        Expression x103=x69.join(x15);
        Expression x102=x103.join(x12);
        Expression x104=x69.join(x12);
        Formula x101=x102.eq(x104);
        Formula x97=x98.and(x101);
        Formula x95=x96.implies(x97);
        Formula x77=x78.and(x95);
        Formula x74=x75.implies(x77);
        Formula x106=x75.not();
        Expression x111=x69.join(x12);
        IntExpression x110=x111.sum();
        IntExpression x112=x11.sum();
        Formula x109=x110.gte(x112);
        Expression x116=x69.join(x15);
        Expression x115=x116.join(x13);
        Formula x114=x115.eq(x10);
        Expression x119=x69.join(x15);
        Expression x118=x119.join(x12);
        Expression x123=x69.join(x12);
        IntExpression x122=x123.sum();
        IntExpression x124=IntConstant.constant(1);
        IntExpression x121=x122.minus(x124);
        Expression x120=x121.toExpression();
        Formula x117=x118.eq(x120);
        Formula x113=x114.and(x117);
        Formula x108=x109.implies(x113);
        Formula x126=x109.not();
        Expression x130=x69.join(x15);
        Expression x129=x130.join(x13);
        Formula x128=x129.eq(x9);
        Expression x133=x69.join(x15);
        Expression x132=x133.join(x12);
        Expression x134=x69.join(x12);
        Formula x131=x132.eq(x134);
        Formula x127=x128.and(x131);
        Formula x125=x126.implies(x127);
        Formula x107=x108.and(x125);
        Formula x105=x106.implies(x107);
        x73=x74.and(x105);
        Formula x67=x73.forAll(x68);
        x137=Variable.unary("eventuallyalwayscomfy2_t");
        x138=x7.difference(x71);
        Decls x136=x137.oneOf(x138);
        Expression x144=x137.join(x12);
        IntExpression x143=x144.sum();
        IntExpression x145=IntConstant.constant(75);
        Formula x142=x143.lte(x145);
        Expression x148=x137.join(x12);
        IntExpression x147=x148.sum();
        IntExpression x149=IntConstant.constant(70);
        Formula x146=x147.gte(x149);
        Formula x141=x142.and(x146);
        x152=Variable.unary("eventuallyalwayscomfy2_st");
        Expression x154=x15.closure();
        x153=x137.join(x154);
        Decls x151=x152.oneOf(x153);
        Expression x158=x152.join(x12);
        IntExpression x157=x158.sum();
        IntExpression x159=IntConstant.constant(75);
        Formula x156=x157.lte(x159);
        Expression x162=x152.join(x12);
        IntExpression x161=x162.sum();
        IntExpression x163=IntConstant.constant(70);
        Formula x160=x161.gte(x163);
        x155=x156.and(x160);
        Formula x150=x155.forAll(x151);
        Formula x140=x141.and(x150);
        Variable x166=Variable.unary("eventuallyalwayscomfy2_c");
        Expression x168=x15.closure();
        Expression x167=x137.join(x168);
        Decls x165=x166.oneOf(x167);
        Formula x172=x166.eq(x71);
        Formula x171=x172.not();
        Expression x175=x166.join(x12);
        IntExpression x174=x175.sum();
        Expression x177=x71.join(x12);
        IntExpression x176=x177.sum();
        Formula x173=x174.eq(x176);
        Formula x170=x171.and(x173);
        Expression x179=x166.join(x13);
        Expression x180=x71.join(x13);
        Formula x178=x179.eq(x180);
        Formula x169=x170.and(x178);
        Formula x164=x169.forSome(x165);
        Formula x139=x140.and(x164);
        Formula x135=x139.forSome(x136);
        Variable x185=Variable.unary("restrictedTemp_i");
        Decls x184=x185.oneOf(Expression.INTS);
        IntExpression x187=x185.sum();
        IntExpression x188=IntConstant.constant(0);
        Formula x186=x187.lte(x188);
        Expression x183=x186.comprehension(x184);
        Expression x189=x7.join(x12);
        Expression x182=x183.intersection(x189);
        Formula x181=x182.no();
        Formula x190=x0.eq(x0);
        Formula x191=x1.eq(x1);
        Formula x192=x2.eq(x2);
        Formula x193=x3.eq(x3);
        Formula x194=x4.eq(x4);
        Formula x195=x5.eq(x5);
        Formula x196=x6.eq(x6);
        Formula x197=x7.eq(x7);
        Formula x198=x8.eq(x8);
        Formula x199=x9.eq(x9);
        Formula x200=x10.eq(x10);
        Formula x201=x11.eq(x11);
        Formula x202=x12.eq(x12);
        Formula x203=x13.eq(x13);
        Formula x204=x14.eq(x14);
        Formula x205=x15.eq(x15);
        Formula x206=x16.eq(x16);
        return Formula.compose(FormulaOperator.AND,
                x18,
                x20,
                x26,
                x33,
                x36,
                x44,
                x46,
                x53,
                x56,
                x60,
                x61,
                x65,
                x67,
                x135,
                x181,
                x190,
                x191,
                x192,
                x193,
                x194,
                x195,
                x196,
                x197,
                x198,
                x199,
                x200,
                x201,
                x202,
                x203,
                x204,
                x205,
                x206);
    }

    // CEGIS
    @Override
    public Formula synthformula() {
        List<Formula> formulas = new ArrayList<>();
        formulas.add(bounds.findRelByName("this/Config.T").one());
        Variable t = Variable.unary("t");
        formulas.add(t.join(bounds.findRelByName("this/Time.temp")).one().forAll(t.oneOf(bounds.findRelByName("this/Time"))));
        formulas.add(t.join(bounds.findRelByName("this/Time.heat")).one().forAll(t.oneOf(bounds.findRelByName("this/Time"))));
        return Formula.and(formulas);
    }

    // TN note: there is some code duplication here; I didn't want to clobber existing code in a quick test hack
    @Override
    public Collection<SynthGoal> goals() {
        final List<SynthGoal> results = new ArrayList<>();
        final List<Formula> formulas = new ArrayList<>();
        final Map<Variable, Expression> univars = new HashMap<>();
        // phi,var,expr
        // 155,152,153
        univars.put(x152,x153);
        univars.put(x137,x138);
        formulas.add(x155);
        results.add(new RoomHeatGoal(univars, Formula.and(formulas)));
        formulas.clear();
        univars.clear();
        // 73,69,70
        univars.put(x69,x70);
        formulas.add(x73);
        results.add(new RoomHeatGoal(univars, Formula.and(formulas)));
        formulas.clear();
        univars.clear();
        // 49,48,7
        univars.put(x48,x7);
        formulas.add(x49);
        results.add(new RoomHeatGoal(univars, Formula.and(formulas)));
        formulas.clear();
        univars.clear();
        // 39,38,7
        //univars.put(x38,x7);
        //formulas.add(x39);
        //results.add(new RoomHeatGoal(univars, Formula.and(formulas)));
        //formulas.clear();
        //univars.clear();
        // 29,28,7
        univars.put(x28,x7);
        formulas.add(x29);
        results.add(new RoomHeatGoal(univars, Formula.and(formulas)));
        formulas.clear();
        univars.clear();
        //
        return results;
    }

    @Override
    public Bounds restrict(Bounds verifybounds, Instance synth, boolean onlySkeleton) {
        Bounds restricted = verifybounds.clone();
        restricted.boundExactly(verifybounds.findRelByName("this/Config.T"), synth.tuples("this/Config.T"));
        restricted.boundExactly(verifybounds.findRelByName("this/Time.heat"), synth.tuples("this/Time.heat"));
        restricted.boundExactly(verifybounds.findRelByName("this/Time.temp"), synth.tuples("this/Time.temp"));
        return restricted;
    }
    @Override
    public Bounds refine(Bounds synthbounds, Instance synth, Instance verify)  {
        throw new UnsupportedOperationException();
    }

    // Target-oriented
    @Override
    public Bounds target(Bounds bounds) { throw new UnsupportedOperationException(); }
}

// FIXME class same across specs, make the interface an abstract class?
class RoomHeatGoal implements KodkodExample.SynthGoal {
    Map<Variable, Expression> freevars;
    Formula unboundformula;
    Formula boundformula;

    RoomHeatGoal(Map<Variable, Expression> freevars, Formula unboundformula) {
        this.freevars = new HashMap(freevars);
        this.unboundformula = unboundformula;
        this.boundformula = unboundformula;
        for(Variable v : freevars.keySet()) {
            this.boundformula = this.boundformula().forAll(v.oneOf(freevars.get(v)));
        }
    }
    public Map<Variable, Expression> freevars() { return freevars; }
    public Formula unboundformula() { return unboundformula; }
    public Formula boundformula() { return boundformula; }

    public Formula instantiateWithCE(Instance ce, Bounds b) {
        // Need to produce phi(ce).
        Formula f = unboundformula;
        System.out.println("instantiateWithCE: "+freevars);
        for(Variable v : freevars.keySet()) {
            Relation skolemRel = ce.findRelationByName("$"+v);
            TupleSet relTuples = ce.relationTuples().get(skolemRel);
            String constStr = "";
            // TODO: hack! assume that the name of the relation and the name of the atom are the same Java string
            for(Tuple t : relTuples) {
                constStr = t.atom(0).toString();
                break;
            }
            f = f.accept(new SubstituteVisitor(v, b.findRelByName(constStr)));
        }
        return f;
    }

}