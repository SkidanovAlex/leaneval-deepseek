import Submission.CDT.FinalStep

/-!
# The final linear algebra of the eliminated equation

... (docstring)
-/

open Classical

noncomputable section
namespace Submission.CDT

open Polynomial

namespace FrobeniusApply

open Submission.CDT.Elim14C
open Submission.CDT.ElimOpC

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 8000000

/-! ## The integral ansatz factor -/

/-- The integral form `72·y²(y−4)²(y+1/72) = y²(y−4)²(72y+1)` of the ansatz
factor `Pz`. -/
def PzI : Polynomial ℂ := y ^ 2 * (y - 4) ^ 2 * (72 * y + 1)

lemma Pz_mul_72 : Polynomial.C (72 : ℂ) * Pz = PzI := by
  have hstep : (72 : Polynomial ℂ) * Pz = PzI := by
    calc (72 : Polynomial ℂ) * Pz
        = (Polynomial.X - Polynomial.C (0 : ℂ)) ^ 2 * (Polynomial.X - Polynomial.C (4 : ℂ)) ^ 2
            * ((72 : Polynomial ℂ) * (Polynomial.X - Polynomial.C a72)) := by
          unfold Pz; ring
      _ = (Polynomial.X - Polynomial.C (0 : ℂ)) ^ 2 * (Polynomial.X - Polynomial.C (4 : ℂ)) ^ 2
            * (72 * Polynomial.X + 1) := by rw [mul_X_sub_C_a72]
      _ = PzI := by
          unfold PzI y
          simp only [Polynomial.C_0, map_ofNat Polynomial.C]
          ring
  rw [← map_ofNat Polynomial.C 72] at hstep
  rw [map_ofNat Polynomial.C 72]
  exact hstep

lemma C72_mul_C72inv : Polynomial.C (72 : ℂ) * Polynomial.C ((72 : ℂ)⁻¹) = 1 := by
  rw [← Polynomial.C_mul, mul_inv_cancel₀ (by norm_num : (72 : ℂ) ≠ 0), Polynomial.C_1]

lemma C72inv_mul_C72 : Polynomial.C ((72 : ℂ)⁻¹) * Polynomial.C (72 : ℂ) = 1 := by
  rw [mul_comm]; exact C72_mul_C72inv

lemma Pz_eq_inv72_smul (k : ℕ) : Pz * y ^ k = Polynomial.C ((72 : ℂ)⁻¹) * (PzI * y ^ k) := by
  rw [show Pz = Polynomial.C ((72 : ℂ)⁻¹) * PzI from by
    rw [← Pz_mul_72, ← mul_assoc, C72inv_mul_C72, one_mul]]
  ring

lemma mul72_dnum (k j : ℕ) :
    Polynomial.C (72 : ℂ) * dnum (Pz * y ^ k) cub j = dnum (PzI * y ^ k) cub j := by
  conv_lhs => rw [Pz_eq_inv72_smul k, dnum_smul]
  rw [← mul_assoc, C72_mul_C72inv, one_mul]

/-- `cub.derivative = cubP`. -/
lemma cub_dv : cub.derivative = cubP := cubP_eq_derivative.symm

/-- The chain rule bookkeeping for an explicit polynomial in `y`. -/
macro "dersimp" : tactic => `(tactic|
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.derivative_C,
    Polynomial.derivative_intCast, Polynomial.derivative_natCast, Polynomial.derivative_ofNat,
    Polynomial.derivative_one, Polynomial.derivative_zero, mul_zero, zero_mul, add_zero, zero_add,
    mul_one, one_mul, map_ofNat Polynomial.C, Polynomial.C_eq_natCast, Polynomial.C_eq_intCast,
    map_zero, map_add, map_mul, map_pow, Nat.reduceSub, pow_one])

/-! ## The explicit cascade numerators -/


/-- `dnum (PzI · y^0) cub 0`. -/
def Ct00 : Polynomial ℂ :=
  ((16 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((1144 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((-575 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((72 : ℤ) : Polynomial ℂ) * (y ^ 5)

/-- `dnum (PzI · y^0) cub 1`. -/
def Ct01 : Polynomial ℂ :=
  ((-32 : ℤ) : Polynomial ℂ) * (y) + ((-1544 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((272284 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((-345782 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((174284 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-109152 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((20736 : ℤ) : Polynomial ℂ) * (y ^ 7)

/-- `dnum (PzI · y^0) cub 2`. -/
def Ct02 : Polynomial ℂ :=
  ((32 : ℤ) : Polynomial ℂ) * (1) + ((6864 : ℤ) : Polynomial ℂ) * (y) + ((-828564 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((33158944 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((-48367980 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((-55275240 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((26657672 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((13770432 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((-7589376 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((2985984 : ℤ) : Polynomial ℂ) * (y ^ 9)

/-- `dnum (PzI · y^0) cub 3`. -/
def Ct03 : Polynomial ℂ :=
  ((-18192 : ℤ) : Polynomial ℂ) * (1) + ((60648 : ℤ) : Polynomial ℂ) * (y) + ((2439288 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((-218774640 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((7540320576 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((-53656017408 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((37421789184 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((38398897152 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((-17700712704 : ℤ) : Polynomial ℂ) * (y ^ 8)

/-- `dnum (PzI · y^0) cub 4`. -/
def Ct04 : Polynomial ℂ :=
  ((8525976 : ℤ) : Polynomial ℂ) * (1) + ((-44103360 : ℤ) : Polynomial ℂ) * (y) + ((163881120 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((-2656382400 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((131314981920 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((-2592732414720 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-19761801707520 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((76950997401600 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((-36002496798720 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((-27647205949440 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((10195610517504 : ℤ) : Polynomial ℂ) * (y ^ 10)

/-- `dnum (PzI · y^1) cub 0`. -/
def Ct10 : Polynomial ℂ :=
  ((16 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((1144 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((-575 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((72 : ℤ) : Polynomial ℂ) * (y ^ 6)

/-- `dnum (PzI · y^1) cub 1`. -/
def Ct11 : Polynomial ℂ :=
  ((-48 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((-800 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((405899 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((-550968 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((417666 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((-200736 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((31104 : ℤ) : Polynomial ℂ) * (y ^ 8)

/-- `dnum (PzI · y^1) cub 2`. -/
def Ct12 : Polynomial ℂ :=
  ((96 : ℤ) : Polynomial ℂ) * (y) + ((2400 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((-1729708 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((98477052 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((-197203068 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((148862688 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((-141254184 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((95491008 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((-44084736 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((8957952 : ℤ) : Polynomial ℂ) * (y ^ 10)

/-- `dnum (PzI · y^1) cub 3`. -/
def Ct13 : Polynomial ℂ :=
  ((-96 : ℤ) : Polynomial ℂ) * (1) + ((-27456 : ℤ) : Polynomial ℂ) * (y) + ((4964484 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((-392847600 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((11970815148 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((-21910231776 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-41276080896 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((46153064256 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((9660786576 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((-13920173568 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((9783576576 : ℤ) : Polynomial ℂ) * (y ^ 10) + ((-4371480576 : ℤ) : Polynomial ℂ) * (y ^ 11) + ((1289945088 : ℤ) : Polynomial ℂ) * (y ^ 12)

/-- `dnum (PzI · y^1) cub 4`. -/
def Ct14 : Polynomial ℂ :=
  ((72768 : ℤ) : Polynomial ℂ) * (1) + ((-303240 : ℤ) : Polynomial ℂ) * (y) + ((-16356960 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((2150248800 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((-137234734080 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((4013137417632 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-31873750421760 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((28275048345600 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((45978380559360 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((-41540944435200 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((3108506609664 : ℤ) : Polynomial ℂ) * (y ^ 10)

/-- `dnum (PzI · y^2) cub 0`. -/
def Ct20 : Polynomial ℂ :=
  ((16 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((1144 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-575 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((72 : ℤ) : Polynomial ℂ) * (y ^ 7)

/-- `dnum (PzI · y^2) cub 1`. -/
def Ct21 : Polynomial ℂ :=
  ((-64 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((-56 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((539514 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-756154 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((661048 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((-292320 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((41472 : ℤ) : Polynomial ℂ) * (y ^ 9)

/-- `dnum (PzI · y^2) cub 2`. -/
def Ct22 : Polynomial ℂ :=
  ((192 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((-7328 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((-2718594 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((195552528 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-427336604 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((499168440 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((-449279376 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((272098944 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((-109486080 : ℤ) : Polynomial ℂ) * (y ^ 10) + ((17915904 : ℤ) : Polynomial ℂ) * (y ^ 11)

/-- `dnum (PzI · y^2) cub 3`. -/
def Ct23 : Polynomial ℂ :=
  ((-384 : ℤ) : Polynomial ℂ) * (y) + ((-672 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((10968072 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((-1301432316 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((48057410688 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-128956540800 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((126563482560 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((-143812859088 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((159604570176 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((-125524560384 : ℤ) : Polynomial ℂ) * (y ^ 10) + ((70341820416 : ℤ) : Polynomial ℂ) * (y ^ 11) + ((-26694696960 : ℤ) : Polynomial ℂ) * (y ^ 12) + ((5159780352 : ℤ) : Polynomial ℂ) * (y ^ 13)

/-- `dnum (PzI · y^2) cub 4`. -/
def Ct24 : Polynomial ℂ :=
  ((384 : ℤ) : Polynomial ℂ) * (1) + ((137280 : ℤ) : Polynomial ℂ) * (y) + ((-33073560 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((3911613120 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((-233595561840 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((5795200114464 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-12231425666880 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((-33953290229760 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((57543085502400 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((4296234564480 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((-26280699503232 : ℤ) : Polynomial ℂ) * (y ^ 10) + ((20101498444800 : ℤ) : Polynomial ℂ) * (y ^ 11) + ((-14860903956480 : ℤ) : Polynomial ℂ) * (y ^ 12) + ((8377476710400 : ℤ) : Polynomial ℂ) * (y ^ 13) + ((-3147466014720 : ℤ) : Polynomial ℂ) * (y ^ 14) + ((743008370688 : ℤ) : Polynomial ℂ) * (y ^ 15)


/-- `72·POLYq (y^0)`, the integral form of the cascade numerator. -/
def INTQ0 : Polynomial ℂ :=
  ∑ j ∈ Finset.range 5, Acoef j * dnum (PzI * y ^ 0) cub j

/-- `72·POLYq (y^1)`, the integral form of the cascade numerator. -/
def INTQ1 : Polynomial ℂ :=
  ∑ j ∈ Finset.range 5, Acoef j * dnum (PzI * y ^ 1) cub j

/-- `72·POLYq (y^2)`, the integral form of the cascade numerator. -/
def INTQ2 : Polynomial ℂ :=
  ∑ j ∈ Finset.range 5, Acoef j * dnum (PzI * y ^ 2) cub j

/-- The remainder of `Dv · INTQ0` modulo `cub^5`. -/
def RR0 : Polynomial ℂ :=
  ((43038535184254860089263920 : ℤ) : Polynomial ℂ) * (1) + ((-25433184897388440008617627296 : ℤ) : Polynomial ℂ) * (y) + ((6042765005003801115152886668256 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((-725193269837721980599296658639104 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((44606225946475463091899512300977024 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((-1202667971641757009717770896563453184 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((6619488403819329447568040934973926144 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((-21528590071976857248398525758303162368 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((48004688189798573382592164206273403648 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((-78707545114167652219866293045672544768 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((97531348854577506780290457174308384256 : ℤ) : Polynomial ℂ) * (y ^ 10) + ((-90718862026905122118621158152147415040 : ℤ) : Polynomial ℂ) * (y ^ 11) + ((62067440323704903380842968246542893056 : ℤ) : Polynomial ℂ) * (y ^ 12) + ((-28384118881642971382548949096927592448 : ℤ) : Polynomial ℂ) * (y ^ 13) + ((7444978289662562753502410246599999488 : ℤ) : Polynomial ℂ) * (y ^ 14)

/-- The quotient of `Dv · INTQ0` by `cub^5`. -/
def SS0 : Polynomial ℂ :=
  ((43038535184254860089263920 : ℤ) : Polynomial ℂ) * (1) + ((-40449138678072555951914496 : ℤ) : Polynomial ℂ) * (y) + ((-39132334298098709211626496 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((2333318551125363940884480 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((14117776972935916485279744 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((306856747889593598214144 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-4098727317350291543949312 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((1539294331473605198610432 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((-238431488041031055704064 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((15828299617255676706816 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((-303256405652583481344 : ℤ) : Polynomial ℂ) * (y ^ 10)

/-- The remainder of `Dv · INTQ1` modulo `cub^5`. -/
def RR1 : Polynomial ℂ :=
  ((39729018640533377369396787 : ℤ) : Polynomial ℂ) * (1) + ((-23425580984069814251089703274 : ℤ) : Polynomial ℂ) * (y) + ((5547512661970853369465141918526 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((-662187390675667385012830730769552 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((40312183373645956992421314948647352 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((-1057632304418532418515760279290501072 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((4734604103998393527257188870168249008 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((-13826411938495578459320861372014152960 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((26840524595313352008038437908147373488 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((-39327286467214571053580901162653616288 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((42057469511403173522409363439483367136 : ℤ) : Polynomial ℂ) * (y ^ 10) + ((-34014999878957126692457974775469742848 : ℤ) : Polynomial ℂ) * (y ^ 11) + ((18730668500633349180214182638546909184 : ℤ) : Polynomial ℂ) * (y ^ 12) + ((-6848266487453759981937138815336693760 : ℤ) : Polynomial ℂ) * (y ^ 13) + ((824988536512851690958001124621680640 : ℤ) : Polynomial ℂ) * (y ^ 14)

/-- The quotient of `Dv · INTQ1` by `cub^5`. -/
def SS1 : Polynomial ℂ :=
  ((39729018640533377369396787 : ℤ) : Polynomial ℂ) * (1) + ((14540013844878396854401056 : ℤ) : Polynomial ℂ) * (y) + ((-11986739261201500902120384 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((-10297705822794600863496192 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((1766261378932574324944896 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((3155482309783951107293184 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-694496742071165971070976 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((-326180663219210172235776 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((144265343211890358091776 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((-19540909143633225056256 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((884497849820035153920 : ℤ) : Polynomial ℂ) * (y ^ 10)

/-- The remainder of `Dv · INTQ2` modulo `cub^5`. -/
def RR2 : Polynomial ℂ :=
  ((-9815972204153093338634041 : ℤ) : Polynomial ℂ) * (1) + ((5791180335787088547112501502 : ℤ) : Polynomial ℂ) * (y) + ((-1372615666800845439275096889338 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((164076161138414004703588671978416 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((-10015832977304126990495115758706216 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((264705316276811349541435097786539376 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((-1258616485748666112295874032548766224 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((3806496876405078415485350865697130240 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((-7759576528161806180448668415152425744 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((11868294362568318487732638528468952544 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((-13488372440902529657543776298542993568 : ℤ) : Polynomial ℂ) * (y ^ 10) + ((11614518619022645458311399043055710464 : ℤ) : Polynomial ℂ) * (y ^ 11) + ((-7117454110297113965214809464203896832 : ℤ) : Polynomial ℂ) * (y ^ 12) + ((2941424575304657483067805766934282240 : ℤ) : Polynomial ℂ) * (y ^ 13) + ((-594245973664129002997861428827258880 : ℤ) : Polynomial ℂ) * (y ^ 14)

/-- The quotient of `Dv · INTQ2` by `cub^5`. -/
def SS2 : Polynomial ℂ :=
  ((-9815972204153093338634041 : ℤ) : Polynomial ℂ) * (1) + ((-243264663236522681582688 : ℤ) : Polynomial ℂ) * (y) + ((4519798655115750739958592 : ℤ) : Polynomial ℂ) * (y ^ 2) + ((1740426749288655600347136 : ℤ) : Polynomial ℂ) * (y ^ 3) + ((-1164006377227899412107264 : ℤ) : Polynomial ℂ) * (y ^ 4) + ((-599585561619865426132992 : ℤ) : Polynomial ℂ) * (y ^ 5) + ((331578787286016435290112 : ℤ) : Polynomial ℂ) * (y ^ 6) + ((10693369571644593930240 : ℤ) : Polynomial ℂ) * (y ^ 7) + ((-28644628828932362207232 : ℤ) : Polynomial ℂ) * (y ^ 8) + ((5413915921137946066944 : ℤ) : Polynomial ℂ) * (y ^ 9) + ((-319168007183737552896 : ℤ) : Polynomial ℂ) * (y ^ 10)

/-- `Dv = 72·78364164096`, as a constant polynomial. -/
def Dv : Polynomial ℂ := 5642219814912

section Cascade

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_00 : dnum (PzI * y ^ 0) cub 0 = Ct00 := by
  simp only [dnum]
  unfold PzI Ct00
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_01 : dnum (PzI * y ^ 0) cub 1 = Ct01 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct01 cubP cub y
  dersimp
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_02 : dnum (PzI * y ^ 0) cub 2 = Ct02 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct02 cubP cub y
  dersimp
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_03 : dnum (PzI * y ^ 0) cub 3 = Ct03 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct03 cubP cub y
  dersimp
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_04 : dnum (PzI * y ^ 0) cub 4 = Ct04 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct04 cubP cub y
  dersimp
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_10 : dnum (PzI * y ^ 1) cub 0 = Ct10 := by
  simp only [dnum]
  unfold PzI Ct10
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_11 : dnum (PzI * y ^ 1) cub 1 = Ct11 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct11 cubP cub y
  dersimp
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_12 : dnum (PzI * y ^ 1) cub 2 = Ct12 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct12 cubP cub y
  dersimp
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_13 : dnum (PzI * y ^ 1) cub 3 = Ct13 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct13 cubP cub y
  dersimp
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_14 : dnum (PzI * y ^ 1) cub 4 = Ct14 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct14 cubP cub y
  dersimp
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_20 : dnum (PzI * y ^ 2) cub 0 = Ct20 := by
  simp only [dnum]
  unfold PzI Ct20
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_21 : dnum (PzI * y ^ 2) cub 1 = Ct21 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct21 cubP cub y
  dersimp
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_22 : dnum (PzI * y ^ 2) cub 2 = Ct22 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct22 cubP cub y
  dersimp
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_23 : dnum (PzI * y ^ 2) cub 3 = Ct23 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct23 cubP cub y
  dersimp
  ring

set_option maxHeartbeats 8000000 in
lemma dnum_PzI_24 : dnum (PzI * y ^ 2) cub 4 = Ct24 := by
  simp only [dnum, cub_dv]
  unfold PzI Ct24 cubP cub y
  dersimp
  ring

end Cascade

/-- `72·POLYq (y^k) = INTQ k`. -/
lemma mul72_Acoef_dnum (k j : ℕ) :
    Polynomial.C (72 : ℂ) * (Acoef j * dnum (Pz * y ^ k) cub j)
      = Acoef j * dnum (PzI * y ^ k) cub j := by
  rw [← mul_assoc, mul_comm (Polynomial.C (72 : ℂ)) (Acoef j), mul_assoc, mul72_dnum]

lemma mul72_POLYq_0 : Polynomial.C (72 : ℂ) * POLYq (y ^ 0) = INTQ0 := by
  unfold POLYq INTQ0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [mul_add, mul_add, mul_add, mul_add]
  simp only [mul72_Acoef_dnum 0 0, mul72_Acoef_dnum 0 1, mul72_Acoef_dnum 0 2,
    mul72_Acoef_dnum 0 3, mul72_Acoef_dnum 0 4]

lemma mul72_POLYq_1 : Polynomial.C (72 : ℂ) * POLYq (y ^ 1) = INTQ1 := by
  unfold POLYq INTQ1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [mul_add, mul_add, mul_add, mul_add]
  simp only [mul72_Acoef_dnum 1 0, mul72_Acoef_dnum 1 1, mul72_Acoef_dnum 1 2,
    mul72_Acoef_dnum 1 3, mul72_Acoef_dnum 1 4]

lemma mul72_POLYq_2 : Polynomial.C (72 : ℂ) * POLYq (y ^ 2) = INTQ2 := by
  unfold POLYq INTQ2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [mul_add, mul_add, mul_add, mul_add]
  simp only [mul72_Acoef_dnum 2 0, mul72_Acoef_dnum 2 1, mul72_Acoef_dnum 2 2,
    mul72_Acoef_dnum 2 3, mul72_Acoef_dnum 2 4]

/-- **The explicit remainder identity for `Q = y^0`.** -/
lemma cub5_dvd_INTQ_0 : cub ^ 5 ∣ Dv * INTQ0 - RR0 := by
  refine ⟨SS0, ?_⟩
  rw [INTQ0]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [dnum_PzI_00, dnum_PzI_01, dnum_PzI_02, dnum_PzI_03, dnum_PzI_04]
  simp only [Acoef_eq_zero, Acoef_eq_one, Acoef_eq_two, Acoef_eq_three, Acoef_eq_four,
    Dv]
  unfold RR0 SS0 Ct00 Ct01 Ct02 Ct03 Ct04
  unfold P0 P1 P2 P3 w cub y
  ring

/-- **The explicit remainder identity for `Q = y^1`.** -/
lemma cub5_dvd_INTQ_1 : cub ^ 5 ∣ Dv * INTQ1 - RR1 := by
  refine ⟨SS1, ?_⟩
  rw [INTQ1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [dnum_PzI_10, dnum_PzI_11, dnum_PzI_12, dnum_PzI_13, dnum_PzI_14]
  simp only [Acoef_eq_zero, Acoef_eq_one, Acoef_eq_two, Acoef_eq_three, Acoef_eq_four,
    Dv]
  unfold RR1 SS1 Ct10 Ct11 Ct12 Ct13 Ct14
  unfold P0 P1 P2 P3 w cub y
  ring

/-- **The explicit remainder identity for `Q = y^2`.** -/
lemma cub5_dvd_INTQ_2 : cub ^ 5 ∣ Dv * INTQ2 - RR2 := by
  refine ⟨SS2, ?_⟩
  rw [INTQ2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [dnum_PzI_20, dnum_PzI_21, dnum_PzI_22, dnum_PzI_23, dnum_PzI_24]
  simp only [Acoef_eq_zero, Acoef_eq_one, Acoef_eq_two, Acoef_eq_three, Acoef_eq_four,
    Dv]
  unfold RR2 SS2 Ct20 Ct21 Ct22 Ct23 Ct24
  unfold P0 P1 P2 P3 w cub y
  ring


/-! ## Linearity of `POLYq` -/

lemma POLYq_add (p q : Polynomial ℂ) : POLYq (p + q) = POLYq p + POLYq q := by
  unfold POLYq
  simp only [mul_add, dnum_add, Finset.sum_add_distrib]

lemma POLYq_smul (c : ℂ) (p : Polynomial ℂ) :
    POLYq (Polynomial.C c * p) = Polynomial.C c * POLYq p := by
  unfold POLYq
  have h : Pz * (Polynomial.C c * p) = Polynomial.C c * (Pz * p) := by ring
  rw [h]
  simp only [dnum_smul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma POLYq_eq_linear (Q : Polynomial ℂ) (h : Q.natDegree ≤ 2) :
    POLYq Q = Polynomial.C (Q.coeff 0) * POLYq (y ^ 0)
      + Polynomial.C (Q.coeff 1) * POLYq (y ^ 1) + Polynomial.C (Q.coeff 2) * POLYq (y ^ 2) := by
  conv_lhs => rw [Q.as_sum_range_C_mul_X_pow' (n := 3) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [POLYq_add, POLYq_add, POLYq_smul, POLYq_smul, POLYq_smul]

lemma mul72_coeff_0 (c : ℂ) :
    Polynomial.C (72 : ℂ) * (Polynomial.C c * POLYq (y ^ 0)) = Polynomial.C c * INTQ0 := by
  rw [← mul_assoc, mul_comm (Polynomial.C (72 : ℂ)) (Polynomial.C c), mul_assoc, mul72_POLYq_0]

lemma mul72_coeff_1 (c : ℂ) :
    Polynomial.C (72 : ℂ) * (Polynomial.C c * POLYq (y ^ 1)) = Polynomial.C c * INTQ1 := by
  rw [← mul_assoc, mul_comm (Polynomial.C (72 : ℂ)) (Polynomial.C c), mul_assoc, mul72_POLYq_1]

lemma mul72_coeff_2 (c : ℂ) :
    Polynomial.C (72 : ℂ) * (Polynomial.C c * POLYq (y ^ 2)) = Polynomial.C c * INTQ2 := by
  rw [← mul_assoc, mul_comm (Polynomial.C (72 : ℂ)) (Polynomial.C c), mul_assoc, mul72_POLYq_2]

/-! ## The degree bound for the remainders -/

set_option maxHeartbeats 4000000 in
lemma RR0_natDegree_le : RR0.natDegree ≤ 14 := by
  unfold RR0 y
  compute_degree!

set_option maxHeartbeats 4000000 in
lemma RR1_natDegree_le : RR1.natDegree ≤ 14 := by
  unfold RR1 y
  compute_degree!

set_option maxHeartbeats 4000000 in
lemma RR2_natDegree_le : RR2.natDegree ≤ 14 := by
  unfold RR2 y
  compute_degree!

/-! ## The final linear algebra -/

set_option maxHeartbeats 4000000 in
theorem eq_zero_of_cub5_dvd_POLYq (Q : Polynomial ℂ) (hdeg : Q.natDegree ≤ 2)
    (hdvd : cub ^ 5 ∣ POLYq Q) : Q = 0 := by
  have hlin := POLYq_eq_linear Q hdeg
  have h72 : Polynomial.C (72 : ℂ) * POLYq Q
      = Polynomial.C (Q.coeff 0) * INTQ0 + Polynomial.C (Q.coeff 1) * INTQ1
        + Polynomial.C (Q.coeff 2) * INTQ2 := by
    rw [hlin, mul_add, mul_add, mul72_coeff_0, mul72_coeff_1, mul72_coeff_2]
  have hdvd2 : cub ^ 5 ∣ Polynomial.C (Q.coeff 0) * INTQ0 + Polynomial.C (Q.coeff 1) * INTQ1
      + Polynomial.C (Q.coeff 2) * INTQ2 := by
    rw [← h72]
    exact Dvd.dvd.mul_left hdvd (Polynomial.C (72 : ℂ))
  have hpart : cub ^ 5 ∣ Polynomial.C (Q.coeff 0) * (Dv * INTQ0 - RR0)
      + Polynomial.C (Q.coeff 1) * (Dv * INTQ1 - RR1)
      + Polynomial.C (Q.coeff 2) * (Dv * INTQ2 - RR2) :=
    dvd_add (dvd_add (Dvd.dvd.mul_left cub5_dvd_INTQ_0 _) (Dvd.dvd.mul_left cub5_dvd_INTQ_1 _))
      (Dvd.dvd.mul_left cub5_dvd_INTQ_2 _)
  have hid : Dv * (Polynomial.C (Q.coeff 0) * INTQ0 + Polynomial.C (Q.coeff 1) * INTQ1
        + Polynomial.C (Q.coeff 2) * INTQ2)
      - (Polynomial.C (Q.coeff 0) * (Dv * INTQ0 - RR0)
        + Polynomial.C (Q.coeff 1) * (Dv * INTQ1 - RR1)
        + Polynomial.C (Q.coeff 2) * (Dv * INTQ2 - RR2))
      = Polynomial.C (Q.coeff 0) * RR0 + Polynomial.C (Q.coeff 1) * RR1
        + Polynomial.C (Q.coeff 2) * RR2 := by
    ring
  have hRR : cub ^ 5 ∣ Polynomial.C (Q.coeff 0) * RR0 + Polynomial.C (Q.coeff 1) * RR1
      + Polynomial.C (Q.coeff 2) * RR2 := by
    have h := dvd_sub (Dvd.dvd.mul_left hdvd2 Dv) hpart
    rwa [hid] at h
  have hRR0 : Polynomial.C (Q.coeff 0) * RR0 + Polynomial.C (Q.coeff 1) * RR1
      + Polynomial.C (Q.coeff 2) * RR2 = 0 := by
    obtain ⟨S, hS⟩ := hRR
    by_cases hS0 : S = 0
    · rw [hS0, mul_zero] at hS
      exact hS
    · exfalso
      have hcub5 : (cub : Polynomial ℂ) ^ 5 ≠ 0 := pow_ne_zero 5 cub_ne_zero
      have h15 : ((cub : Polynomial ℂ) ^ 5).natDegree = 15 := by
        rw [Polynomial.natDegree_pow, cub_natDegree]
      have hd1 : ((cub ^ 5 : Polynomial ℂ) * S).natDegree = 15 + S.natDegree := by
        rw [Polynomial.natDegree_mul hcub5 hS0, h15]
      have h0 : (Polynomial.C (Q.coeff 0) * RR0).natDegree ≤ 14 :=
        le_trans (Polynomial.natDegree_C_mul_le _ _) RR0_natDegree_le
      have h1 : (Polynomial.C (Q.coeff 1) * RR1).natDegree ≤ 14 :=
        le_trans (Polynomial.natDegree_C_mul_le _ _) RR1_natDegree_le
      have h2 : (Polynomial.C (Q.coeff 2) * RR2).natDegree ≤ 14 :=
        le_trans (Polynomial.natDegree_C_mul_le _ _) RR2_natDegree_le
      have hle : (Polynomial.C (Q.coeff 0) * RR0 + Polynomial.C (Q.coeff 1) * RR1
          + Polynomial.C (Q.coeff 2) * RR2).natDegree ≤ 14 := by
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ h2)
        exact le_trans (Polynomial.natDegree_add_le _ _) (max_le h0 h1)
      rw [← hS] at hd1
      omega
  -- the three coefficient equations
  have he0 : Q.coeff 0 * RR0.coeff 0 + Q.coeff 1 * RR1.coeff 0 + Q.coeff 2 * RR2.coeff 0 = 0 := by
    have h := congrArg (fun p : Polynomial ℂ => p.coeff 0) hRR0
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul] using h
  have he1 : Q.coeff 0 * RR0.coeff 1 + Q.coeff 1 * RR1.coeff 1 + Q.coeff 2 * RR2.coeff 1 = 0 := by
    have h := congrArg (fun p : Polynomial ℂ => p.coeff 1) hRR0
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul] using h
  have he2 : Q.coeff 0 * RR0.coeff 2 + Q.coeff 1 * RR1.coeff 2 + Q.coeff 2 * RR2.coeff 2 = 0 := by
    have h := congrArg (fun p : Polynomial ℂ => p.coeff 2) hRR0
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul] using h
  have hdet : RR0.coeff 0 * (RR1.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR1.coeff 2)
      - RR1.coeff 0 * (RR0.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR0.coeff 2)
      + RR2.coeff 0 * (RR0.coeff 1 * RR1.coeff 2 - RR1.coeff 1 * RR0.coeff 2) ≠ 0 := by
    unfold RR0 RR1 RR2 y
    simp only [Polynomial.coeff_add, Polynomial.coeff_intCast_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, ← Polynomial.C_eq_intCast, Polynomial.coeff_C]
    norm_num
  have hq0 : Q.coeff 0 = 0 := by
    have hid0 : (RR0.coeff 0 * (RR1.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR1.coeff 2)
        - RR1.coeff 0 * (RR0.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR0.coeff 2)
        + RR2.coeff 0 * (RR0.coeff 1 * RR1.coeff 2 - RR1.coeff 1 * RR0.coeff 2)) * Q.coeff 0
        = (RR1.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR1.coeff 2)
            * (Q.coeff 0 * RR0.coeff 0 + Q.coeff 1 * RR1.coeff 0 + Q.coeff 2 * RR2.coeff 0)
          - (RR1.coeff 0 * RR2.coeff 2 - RR2.coeff 0 * RR1.coeff 2)
            * (Q.coeff 0 * RR0.coeff 1 + Q.coeff 1 * RR1.coeff 1 + Q.coeff 2 * RR2.coeff 1)
          + (RR1.coeff 0 * RR2.coeff 1 - RR2.coeff 0 * RR1.coeff 1)
            * (Q.coeff 0 * RR0.coeff 2 + Q.coeff 1 * RR1.coeff 2 + Q.coeff 2 * RR2.coeff 2) := by
      ring
    have hz : (RR0.coeff 0 * (RR1.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR1.coeff 2)
        - RR1.coeff 0 * (RR0.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR0.coeff 2)
        + RR2.coeff 0 * (RR0.coeff 1 * RR1.coeff 2 - RR1.coeff 1 * RR0.coeff 2)) * Q.coeff 0 = 0 := by
      rw [hid0, he0, he1, he2]
      ring
    exact (mul_eq_zero.mp hz).resolve_left hdet
  have hq1 : Q.coeff 1 = 0 := by
    have hid1 : (RR0.coeff 0 * (RR1.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR1.coeff 2)
        - RR1.coeff 0 * (RR0.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR0.coeff 2)
        + RR2.coeff 0 * (RR0.coeff 1 * RR1.coeff 2 - RR1.coeff 1 * RR0.coeff 2)) * Q.coeff 1
        = - (RR0.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR0.coeff 2)
            * (Q.coeff 0 * RR0.coeff 0 + Q.coeff 1 * RR1.coeff 0 + Q.coeff 2 * RR2.coeff 0)
          + (RR0.coeff 0 * RR2.coeff 2 - RR2.coeff 0 * RR0.coeff 2)
            * (Q.coeff 0 * RR0.coeff 1 + Q.coeff 1 * RR1.coeff 1 + Q.coeff 2 * RR2.coeff 1)
          - (RR0.coeff 0 * RR2.coeff 1 - RR2.coeff 0 * RR0.coeff 1)
            * (Q.coeff 0 * RR0.coeff 2 + Q.coeff 1 * RR1.coeff 2 + Q.coeff 2 * RR2.coeff 2) := by
      ring
    have hz : (RR0.coeff 0 * (RR1.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR1.coeff 2)
        - RR1.coeff 0 * (RR0.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR0.coeff 2)
        + RR2.coeff 0 * (RR0.coeff 1 * RR1.coeff 2 - RR1.coeff 1 * RR0.coeff 2)) * Q.coeff 1 = 0 := by
      rw [hid1, he0, he1, he2]
      ring
    exact (mul_eq_zero.mp hz).resolve_left hdet
  have hq2 : Q.coeff 2 = 0 := by
    have hid2 : (RR0.coeff 0 * (RR1.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR1.coeff 2)
        - RR1.coeff 0 * (RR0.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR0.coeff 2)
        + RR2.coeff 0 * (RR0.coeff 1 * RR1.coeff 2 - RR1.coeff 1 * RR0.coeff 2)) * Q.coeff 2
        = (RR0.coeff 1 * RR1.coeff 2 - RR1.coeff 1 * RR0.coeff 2)
            * (Q.coeff 0 * RR0.coeff 0 + Q.coeff 1 * RR1.coeff 0 + Q.coeff 2 * RR2.coeff 0)
          - (RR0.coeff 0 * RR1.coeff 2 - RR1.coeff 0 * RR0.coeff 2)
            * (Q.coeff 0 * RR0.coeff 1 + Q.coeff 1 * RR1.coeff 1 + Q.coeff 2 * RR2.coeff 1)
          + (RR0.coeff 0 * RR1.coeff 1 - RR1.coeff 0 * RR0.coeff 1)
            * (Q.coeff 0 * RR0.coeff 2 + Q.coeff 1 * RR1.coeff 2 + Q.coeff 2 * RR2.coeff 2) := by
      ring
    have hz : (RR0.coeff 0 * (RR1.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR1.coeff 2)
        - RR1.coeff 0 * (RR0.coeff 1 * RR2.coeff 2 - RR2.coeff 1 * RR0.coeff 2)
        + RR2.coeff 0 * (RR0.coeff 1 * RR1.coeff 2 - RR1.coeff 1 * RR0.coeff 2)) * Q.coeff 2 = 0 := by
      rw [hid2, he0, he1, he2]
      ring
    exact (mul_eq_zero.mp hz).resolve_left hdet
  have hQform : Q = Polynomial.C (Q.coeff 0) + Polynomial.C (Q.coeff 1) * y
      + Polynomial.C (Q.coeff 2) * y ^ 2 := by
    conv_lhs => rw [Q.as_sum_range_C_mul_X_pow' (n := 3) (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, y, pow_one, pow_zero, mul_one]
  rw [hQform, hq0, hq1, hq2]
  simp


/-! ## The order bounds coming from `R = Rnum / y²` -/

lemma rootMultiplicity_X_eq (α : ℂ) :
    Polynomial.rootMultiplicity α (Polynomial.X : Polynomial ℂ) = if α = 0 then 1 else 0 := by
  rw [show (Polynomial.X : Polynomial ℂ) = Polynomial.X - Polynomial.C (0 : ℂ) from by simp]
  exact Polynomial.rootMultiplicity_X_sub_C

lemma ordAt_X_pow_two (α : ℂ) :
    ordAt α (am (Polynomial.X ^ 2 : Polynomial ℂ)) = 2 * (if α = 0 then (1 : ℤ) else 0) := by
  simp only [map_pow, ordAt_pow, ordAt_algebraMap, rootMultiplicity_X_eq]
  push_cast
  ring

/-- **The order bounds for the inhomogeneity** `R = Rnum/y²`: a double pole at `0`
and no poles elsewhere. -/
theorem ord_bounds_of_div_Xsq (R : RF) (Rnum : Polynomial ℂ) (hRnum : Rnum ≠ 0)
    (hR : R = am Rnum / am (Polynomial.X ^ 2)) :
    (-2 : ℤ) ≤ ordAt (0 : ℂ) R ∧ ∀ α : ℂ, α ≠ 0 → (0 : ℤ) ≤ ordAt α R := by
  have hamX2 : am (Polynomial.X ^ 2 : Polynomial ℂ) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero)
  have hamR : am Rnum ≠ 0 := RatFunc.algebraMap_ne_zero hRnum
  constructor
  · rw [hR, ordAt_div (0 : ℂ) hamR hamX2, ordAt_X_pow_two]
    rw [if_pos rfl]
    have : (0 : ℤ) ≤ (Polynomial.rootMultiplicity (0 : ℂ) Rnum : ℤ) := Int.natCast_nonneg _
    rw [ordAt_algebraMap]
    omega
  · intro α hα
    rw [hR, ordAt_div α hamR hamX2, ordAt_X_pow_two, if_neg hα, mul_zero, sub_zero,
      ordAt_algebraMap]
    exact Int.natCast_nonneg _

/-! ## The main theorem: the paper's system has no solution -/

/-- **Lemma `14functions` (final step).**  The fourth-order system
`b₃' + b₂ − W b₃ = 0`, `b₂' + b₁ − V b₃ = 0`, `b₁' + b₀ − U b₃ = 0`,
`b₀' − Z b₃ = R` with inhomogeneity `R = (a₀y² + a₁y + a₂)/y²` and
`(a₀,a₁,a₂) ≠ 0` has no solution `b₃ ≠ 0`. -/
theorem no_solution (b0 b1 b2 b3 R : RF) (Rnum : Polynomial ℂ) (hb : b3 ≠ 0)
    (hRnum : Rnum ≠ 0) (hRdeg : Rnum.natDegree ≤ 2)
    (hR : R = am Rnum / am (Polynomial.X ^ 2))
    (h1 : dRat b3 + b2 - Ww * b3 = 0) (h2 : dRat b2 + b1 - Vv * b3 = 0)
    (h3 : dRat b1 + b0 - Uu * b3 = 0) (h4 : dRat b0 - Zz * b3 = R) :
    False := by
  obtain ⟨hR0, hRgen⟩ := ord_bounds_of_div_Xsq R Rnum hRnum hR
  have hamX2 : am (Polynomial.X ^ 2 : Polynomial ℂ) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero)
  have hRne : R ≠ 0 := by
    rw [hR]
    exact div_ne_zero (RatFunc.algebraMap_ne_zero hRnum) hamX2
  have hb0 := zero_local b0 b1 b2 b3 R hb hRne hR0 h1 h2 h3 h4
  have hb4 := four_local b0 b1 b2 b3 R hb hRne (hRgen 4 (by norm_num)) h1 h2 h3 h4
  have hba := m72_local b0 b1 b2 b3 R hb hRne (hRgen a72 (by unfold a72; norm_num)) h1 h2 h3 h4
  have hbb : ∀ β : ℂ, cub.eval β = 0 → (-1 : ℤ) ≤ ordAt β b3 := by
    intro β hβ
    refine beta_local β hβ b0 b1 b2 b3 R hb hRne ?_ h1 h2 h3 h4
    refine hRgen β ?_
    intro h0
    rw [h0, cub_eval_zero_pt] at hβ
    norm_num at hβ
  have hbgen : ∀ α : ℂ, D1.eval α ≠ 0 → (0 : ℤ) ≤ ordAt α b3 := by
    intro α hD
    have hα : α ≠ 0 := by
      intro h0
      apply hD
      rw [h0]
      unfold D1 y
      simp
    exact generic_local α hD b0 b1 b2 b3 R hb hRne (hRgen α hα) h1 h2 h3 h4
  obtain ⟨Q, hQ⟩ := divisor_bound b3 hb hb0 hb4 hba hbb hbgen
  have hQ' : am cub * b3 = am (Pz * Q) := by
    rw [hQ]
    unfold Pz
    rfl
  have hcub0 : am cub ≠ 0 := RatFunc.algebraMap_ne_zero cub_ne_zero
  have hb3 : b3 = am (Pz * Q) / am cub := by
    rw [← hQ', mul_div_cancel_left₀ _ hcub0]
  have hQne : Q ≠ 0 := by
    intro hQ0
    have h : am cub * b3 = 0 := by
      rw [hQ', hQ0, mul_zero]
      exact map_zero _
    exact hb ((mul_eq_zero.mp h).resolve_left hcub0)
  have hEq : (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3))
      = am (D1 ^ 4) * (am Rnum / am (Polynomial.X ^ 2)) := by
    calc (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3)) = am (D1 ^ 4) * R := by
          rw [sum5_expand]
          exact elim_equation_cleared b0 b1 b2 b3 R h1 h2 h3 h4
      _ = am (D1 ^ 4) * (am Rnum / am (Polynomial.X ^ 2)) := by rw [hR]
  have hdeg := infty_bound Q Rnum hQne hRnum hRdeg b3 hb3 hEq
  have hpoly := POLYq_mul_X2 Q Rnum b3 hb3 hEq
  have hdvd : cub ^ 5 ∣ POLYq Q := cub_pow_five_dvd_POLYq Q Rnum hpoly
  have hQzero := eq_zero_of_cub5_dvd_POLYq Q hdeg hdvd
  have hlast : am cub * b3 = 0 := by
    rw [hQ', hQzero, mul_zero]
    exact map_zero _
  exact hb ((mul_eq_zero.mp hlast).resolve_left hcub0)

end FrobeniusApply
end Submission.CDT
