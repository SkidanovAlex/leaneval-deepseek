import Mathlib
import Submission.Work.Resample.pbCostDefs
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.Params.listSizesBig

/-!
# Arithmetic kit for `Work.Resample.pbCostArith`

Standalone `ℕ`-arithmetic lemmas used by the proof of `Work.Resample.pbCostArith` (the bound of
the sum of the four `progTensorB` block brackets by `HvdH.resCost`):

* `pbcaKge1` … `pbcaKge4`, `pbcaKge_sq`: any product of at most four factors, each at most `T`,
  is at most `100 * T ^ 8` — the shape in which every "the constant `100 * (…) ^ 8` is large
  enough" obligation appears;
* `pbca_sum_quarters` / `pbca_sum_thirds` / `pbca_sum_halves`: adding up `n` shares of a budget;
* the four bracket bounds `pbca_bracket1` … `pbca_bracket4`, each one a single bracket of
  `BrSetup`, `BrIter`, `BrFin`, `BrClr` bounded by an explicit constant times `ts.prod * p ^ 2`
  (the second term of `HvdH.resCost`).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## The dimension constant -/

theorem pbcaD : HvdH.D = 1729 := rfl

theorem pbcaD3 : HvdH.D ^ 3 = 1729 ^ 3 := by rw [pbcaD]

/-- `p ≤ p ^ 2` for `1 ≤ p`. -/
theorem pbca_le_sq (p : ℕ) (hp : 1 ≤ p) : p ≤ p ^ 2 := by
  have := Nat.mul_le_mul_left p hp
  simpa [pow_two] using this

/-! ## Absorption of a product into `100 * T ^ 8` -/

/-- A product of four factors, each at most `T`, is at most `100 * T ^ 8`. -/
theorem pbcaKge4 (T a b c d : ℕ) (hT : 1 ≤ T) (ha : a ≤ T) (hb : b ≤ T) (hc : c ≤ T)
    (hd : d ≤ T) : a * b * c * d ≤ 100 * T ^ 8 := by
  calc a * b * c * d ≤ T * T * T * T :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc) hd
    _ = T ^ 4 := by ring
    _ ≤ T ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ 100 * T ^ 8 := by omega

/-- A product of three factors, each at most `T`, is at most `100 * T ^ 8`. -/
theorem pbcaKge3 (T a b c : ℕ) (hT : 1 ≤ T) (ha : a ≤ T) (hb : b ≤ T) (hc : c ≤ T) :
    a * b * c ≤ 100 * T ^ 8 := by
  calc a * b * c ≤ T * T * T := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
    _ = T ^ 3 := by ring
    _ ≤ T ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ 100 * T ^ 8 := by omega

theorem pbcaKge2 (T a b : ℕ) (hT : 1 ≤ T) (ha : a ≤ T) (hb : b ≤ T) :
    a * b ≤ 100 * T ^ 8 := by
  calc a * b ≤ T * T := Nat.mul_le_mul ha hb
    _ = T ^ 2 := by ring
    _ ≤ T ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ 100 * T ^ 8 := by omega

theorem pbcaKge1 (T a : ℕ) (hT : 1 ≤ T) (ha : a ≤ T) : a ≤ 100 * T ^ 8 := by
  calc a ≤ T := ha
    _ ≤ T ^ 8 := by
        simpa using Nat.pow_le_pow_right (by omega : 0 < T) (show 1 ≤ 8 by norm_num)
    _ ≤ 100 * T ^ 8 := by omega

/-- `a * b ≤ 100 * T ^ 8` when `a ≤ T ^ 2` and `b ≤ T`. -/
theorem pbcaKge_sq (T a b : ℕ) (hT : 1 ≤ T) (ha : a ≤ T * T) (hb : b ≤ T) :
    a * b ≤ 100 * T ^ 8 := by
  calc a * b ≤ T * T * T := Nat.mul_le_mul ha hb
    _ = T ^ 3 := by ring
    _ ≤ T ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ 100 * T ^ 8 := by omega

/-! ## Adding shares of a budget -/

theorem pbca_sum_quarters {x1 x2 x3 x4 R : ℕ} (h1 : 4 * x1 ≤ R) (h2 : 4 * x2 ≤ R)
    (h3 : 4 * x3 ≤ R) (h4 : 4 * x4 ≤ R) : x1 + x2 + x3 + x4 ≤ R := by omega

theorem pbca_sum_thirds {x1 x2 x3 R : ℕ} (h1 : 3 * x1 ≤ R) (h2 : 3 * x2 ≤ R)
    (h3 : 3 * x3 ≤ R) : x1 + x2 + x3 ≤ R := by omega

theorem pbca_sum_halves {x1 x2 R : ℕ} (h1 : 2 * x1 ≤ R) (h2 : 2 * x2 ≤ R) :
    x1 + x2 ≤ R := by omega

/-! ## `vsz` of an integer value -/

theorem pbca_vsz_int (m : ℕ) : HvdH.vsz (HvdH.Val.int (m : ℤ)) = m.size + 2 := by
  show (HvdH.Val.int (m : ℤ)).enc.length = _
  rw [Work.IntLib.vsz_int]
  show HvdH.isz (m : ℤ) = _
  rw [HvdH.isz]
  simp

/-! ## The bracket constants -/

/-- Coefficient of the setup bracket (`BrSetup` minus `PBTab`). -/
def pbcaC1 : ℕ := 10 + 4 * HvdH.D ^ 3 + 2000 * HvdH.D + 100

/-- Coefficient of the epilogue bracket (`BrFin` minus `vsz M`). -/
def pbcaC2 : ℕ := 2 * HvdH.D + 20

/-- Coefficient of the frame-cleanup bracket (`BrClr` minus `vsz M`). -/
def pbcaC3 : ℕ := 5 * HvdH.D + 113

/-- Coefficient of the round-iteration bracket (`BrIter` minus its `PBTab`- and `Cm`-parts). -/
def pbcaC4 (Kb : ℕ) : ℕ :=
  16 * HvdH.D * Kb + 8 * HvdH.D * (HvdH.D + 2) ^ 2 + 1600 * HvdH.D ^ 2 + 484 * HvdH.D

/-! ## The four bracket bounds -/

/-- The setup bracket of `BrSetup` (everything but `PBTab`). -/
theorem pbca_bracket1 (A p : ℕ) (hA : 1 ≤ A) (hp : 1 ≤ p) :
    A * (2 * p + 8) + HvdH.D * (HvdH.D * (p + 1)) * (HvdH.D * (p + 1))
      + 1000 * (HvdH.D * (p + 1)) + 100 ≤ pbcaC1 * A * p ^ 2 := by
  have hp2 : p ≤ p ^ 2 := pbca_le_sq p (by omega)
  have h1 : A * (2 * p + 8) ≤ 10 * A * p ^ 2 := by
    calc A * (2 * p + 8) ≤ A * (10 * p) := Nat.mul_le_mul_left _ (by omega)
      _ = 10 * A * p := by ring
      _ ≤ 10 * A * p ^ 2 := Nat.mul_le_mul_left _ hp2
  have h2 : HvdH.D * (HvdH.D * (p + 1)) * (HvdH.D * (p + 1)) ≤ 4 * HvdH.D ^ 3 * A * p ^ 2 := by
    have he : HvdH.D * (HvdH.D * (p + 1)) * (HvdH.D * (p + 1)) = HvdH.D ^ 3 * (p + 1) ^ 2 := by
      ring
    rw [he]
    have hP : (p + 1) ^ 2 ≤ 4 * p ^ 2 := by nlinarith
    calc HvdH.D ^ 3 * (p + 1) ^ 2 ≤ HvdH.D ^ 3 * (4 * p ^ 2) := Nat.mul_le_mul_left _ hP
      _ = 4 * HvdH.D ^ 3 * p ^ 2 := by ring
      _ ≤ 4 * HvdH.D ^ 3 * (A * p ^ 2) := by
            apply Nat.mul_le_mul_left
            calc p ^ 2 = 1 * p ^ 2 := by ring
              _ ≤ A * p ^ 2 := Nat.mul_le_mul_right _ hA
      _ = 4 * HvdH.D ^ 3 * A * p ^ 2 := by ring
  have h3 : 1000 * (HvdH.D * (p + 1)) ≤ 2000 * HvdH.D * A * p ^ 2 := by
    calc 1000 * (HvdH.D * (p + 1)) ≤ 1000 * (HvdH.D * (2 * p)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = 2000 * HvdH.D * p := by ring
      _ ≤ 2000 * HvdH.D * (A * p ^ 2) := by
            apply Nat.mul_le_mul_left
            calc p = 1 * p := by ring
              _ ≤ A * p := Nat.mul_le_mul_right _ hA
              _ ≤ A * p ^ 2 := Nat.mul_le_mul_left _ hp2
      _ = 2000 * HvdH.D * A * p ^ 2 := by ring
  have h4 : 100 ≤ 100 * A * p ^ 2 := by
    have h1A : (1 : ℕ) ≤ A * p ^ 2 := by
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ A * p ^ 2 := Nat.mul_le_mul hA (by nlinarith)
    calc (100 : ℕ) = 100 * 1 := by ring
      _ ≤ 100 * (A * p ^ 2) := Nat.mul_le_mul_left _ h1A
      _ = 100 * A * p ^ 2 := by ring
  calc A * (2 * p + 8) + HvdH.D * (HvdH.D * (p + 1)) * (HvdH.D * (p + 1))
        + 1000 * (HvdH.D * (p + 1)) + 100
      ≤ 10 * A * p ^ 2 + 4 * HvdH.D ^ 3 * A * p ^ 2 + 2000 * HvdH.D * A * p ^ 2
        + 100 * A * p ^ 2 := by linarith [h1, h2, h3, h4]
    _ = pbcaC1 * A * p ^ 2 := by rw [pbcaC1]; ring

/-- The epilogue bracket of `BrFin` (everything but `vsz M`). -/
theorem pbca_bracket2 (A p : ℕ) (hA : 1 ≤ A) (hp : 1 ≤ p) :
    A * (2 * p + 8) + HvdH.D * (p + 1) + 10 ≤ pbcaC2 * A * p ^ 2 := by
  have hp2 : p ≤ p ^ 2 := pbca_le_sq p (by omega)
  have h1 : A * (2 * p + 8) ≤ 10 * A * p ^ 2 := by
    calc A * (2 * p + 8) ≤ A * (10 * p) := Nat.mul_le_mul_left _ (by omega)
      _ = 10 * A * p := by ring
      _ ≤ 10 * A * p ^ 2 := Nat.mul_le_mul_left _ hp2
  have h2 : HvdH.D * (p + 1) ≤ 2 * HvdH.D * A * p ^ 2 := by
    calc HvdH.D * (p + 1) ≤ HvdH.D * (2 * p) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * HvdH.D * p := by ring
      _ ≤ 2 * HvdH.D * (A * p ^ 2) := by
            apply Nat.mul_le_mul_left
            calc p = 1 * p := by ring
              _ ≤ A * p := Nat.mul_le_mul_right _ hA
              _ ≤ A * p ^ 2 := Nat.mul_le_mul_left _ hp2
      _ = 2 * HvdH.D * A * p ^ 2 := by ring
  have h3 : 10 ≤ 10 * A * p ^ 2 := by
    have h1A : (1 : ℕ) ≤ A * p ^ 2 := by
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ A * p ^ 2 := Nat.mul_le_mul hA (by nlinarith)
    calc (10 : ℕ) = 10 * 1 := by ring
      _ ≤ 10 * (A * p ^ 2) := Nat.mul_le_mul_left _ h1A
      _ = 10 * A * p ^ 2 := by ring
  calc A * (2 * p + 8) + HvdH.D * (p + 1) + 10
      ≤ 10 * A * p ^ 2 + 2 * HvdH.D * A * p ^ 2 + 10 * A * p ^ 2 := by linarith [h1, h2, h3]
    _ = pbcaC2 * A * p ^ 2 := by rw [pbcaC2]; ring

/-- The frame-cleanup bracket of `BrClr` (everything but `vsz M`). -/
theorem pbca_bracket3 (vts vss vsp v1 vp va A p : ℕ) (hA : 1 ≤ A) (hp : 3 ≤ p)
    (hvts : vts ≤ (HvdH.D + 1) * (p + 3)) (hvss : vss ≤ (HvdH.D + 1) * (p + 3))
    (hvsp : vsp ≤ HvdH.D * p + 2) (hv1 : v1 = 3) (hvp : vp ≤ p + 2) (hva : va ≤ p + 2) :
    vts + vss + vsp + v1 + vp + va + 100 ≤ pbcaC3 * A * p ^ 2 := by
  have h1A : (1 : ℕ) ≤ A * p ^ 2 := by
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ A * p ^ 2 := Nat.mul_le_mul hA (by nlinarith)
  have hpm : p ≤ A * p ^ 2 := by
    calc p = 1 * p := by ring
      _ ≤ A * p := Nat.mul_le_mul_right _ hA
      _ ≤ A * p ^ 2 := Nat.mul_le_mul_left _ (pbca_le_sq p (by omega))
  have t1 : vts ≤ (2 * HvdH.D + 2) * A * p ^ 2 := by
    calc vts ≤ (HvdH.D + 1) * (p + 3) := hvts
      _ ≤ (HvdH.D + 1) * (2 * p) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * HvdH.D + 2) * p := by ring
      _ ≤ (2 * HvdH.D + 2) * (A * p ^ 2) := Nat.mul_le_mul_left _ hpm
      _ = (2 * HvdH.D + 2) * A * p ^ 2 := by ring
  have t2 : vss ≤ (2 * HvdH.D + 2) * A * p ^ 2 := by
    calc vss ≤ (HvdH.D + 1) * (p + 3) := hvss
      _ ≤ (HvdH.D + 1) * (2 * p) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * HvdH.D + 2) * p := by ring
      _ ≤ (2 * HvdH.D + 2) * (A * p ^ 2) := Nat.mul_le_mul_left _ hpm
      _ = (2 * HvdH.D + 2) * A * p ^ 2 := by ring
  have t3 : vsp ≤ (HvdH.D + 2) * A * p ^ 2 := by
    calc vsp ≤ HvdH.D * p + 2 := hvsp
      _ ≤ (HvdH.D + 2) * p := by nlinarith
      _ ≤ (HvdH.D + 2) * (A * p ^ 2) := Nat.mul_le_mul_left _ hpm
      _ = (HvdH.D + 2) * A * p ^ 2 := by ring
  have t4 : v1 ≤ 3 * A * p ^ 2 := by
    rw [hv1]
    calc (3 : ℕ) = 3 * 1 := by ring
      _ ≤ 3 * (A * p ^ 2) := Nat.mul_le_mul_left _ h1A
      _ = 3 * A * p ^ 2 := by ring
  have t5 : vp ≤ 2 * A * p ^ 2 := by
    calc vp ≤ p + 2 := hvp
      _ ≤ 2 * p := by omega
      _ ≤ 2 * (A * p ^ 2) := Nat.mul_le_mul_left _ hpm
      _ = 2 * A * p ^ 2 := by ring
  have t6 : va ≤ 2 * A * p ^ 2 := by
    calc va ≤ p + 2 := hva
      _ ≤ 2 * p := by omega
      _ ≤ 2 * (A * p ^ 2) := Nat.mul_le_mul_left _ hpm
      _ = 2 * A * p ^ 2 := by ring
  have t7 : 100 ≤ 100 * A * p ^ 2 := by
    calc (100 : ℕ) = 100 * 1 := by ring
      _ ≤ 100 * (A * p ^ 2) := Nat.mul_le_mul_left _ h1A
      _ = 100 * A * p ^ 2 := by ring
  calc vts + vss + vsp + v1 + vp + va + 100
      ≤ (2 * HvdH.D + 2) * A * p ^ 2 + (2 * HvdH.D + 2) * A * p ^ 2
        + (HvdH.D + 2) * A * p ^ 2 + 3 * A * p ^ 2 + 2 * A * p ^ 2 + 2 * A * p ^ 2
        + 100 * A * p ^ 2 := by linarith [t1, t2, t3, t4, t5, t6, t7]
    _ = pbcaC3 * A * p ^ 2 := by rw [pbcaC3]; ring

/-- The round-iteration bracket of `BrIter` (everything but its `PBTab`- and `Cm`-parts). -/
theorem pbca_bracket4 (A p Kb sz : ℕ) (hA : 1 ≤ A) (hp : 3 ≤ p)
    (hsz : sz ≤ (HvdH.D + 1) * p + 2) :
    4 * HvdH.D * A * (Kb * (p + 1) ^ 2 + ((2 * p + 8) + sz + 1) * (sz + 1))
      + HvdH.D * (32 * (A * (2 * p + 8) + 2)) + HvdH.D * (800 * (HvdH.D * (p + 1)))
      + HvdH.D * 100 ≤ pbcaC4 Kb * A * p ^ 2 := by
  have hpm : p ≤ A * p ^ 2 := by
    calc p = 1 * p := by ring
      _ ≤ A * p := Nat.mul_le_mul_right _ hA
      _ ≤ A * p ^ 2 := Nat.mul_le_mul_left _ (pbca_le_sq p (by omega))
  have hsz1 : sz + 1 ≤ (HvdH.D + 2) * p := by nlinarith
  have hW : ((2 * p + 8) + sz + 1) * (sz + 1) ≤ 2 * (HvdH.D + 2) ^ 2 * p ^ 2 := by
    have h2 : 2 * p + 8 + sz + 1 ≤ (HvdH.D + 11) * p := by nlinarith
    have h3 : (HvdH.D + 11) * (HvdH.D + 2) ≤ 2 * (HvdH.D + 2) ^ 2 := by
      rw [pbcaD]; norm_num
    calc (2 * p + 8 + sz + 1) * (sz + 1) ≤ ((HvdH.D + 11) * p) * ((HvdH.D + 2) * p) :=
          Nat.mul_le_mul h2 hsz1
      _ = (HvdH.D + 11) * (HvdH.D + 2) * p ^ 2 := by ring
      _ ≤ 2 * (HvdH.D + 2) ^ 2 * p ^ 2 := Nat.mul_le_mul_right _ h3
  have t1 : 4 * HvdH.D * A * (Kb * (p + 1) ^ 2) ≤ 16 * HvdH.D * Kb * A * p ^ 2 := by
    have hP : Kb * (p + 1) ^ 2 ≤ Kb * (4 * p ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
    calc 4 * HvdH.D * A * (Kb * (p + 1) ^ 2) ≤ 4 * HvdH.D * A * (Kb * (4 * p ^ 2)) :=
          Nat.mul_le_mul_left _ hP
      _ = 16 * HvdH.D * Kb * A * p ^ 2 := by ring
  have t2 : 4 * HvdH.D * A * (((2 * p + 8) + sz + 1) * (sz + 1))
      ≤ 8 * HvdH.D * (HvdH.D + 2) ^ 2 * A * p ^ 2 := by
    calc 4 * HvdH.D * A * (((2 * p + 8) + sz + 1) * (sz + 1))
        ≤ 4 * HvdH.D * A * (2 * (HvdH.D + 2) ^ 2 * p ^ 2) := Nat.mul_le_mul_left _ hW
      _ = 8 * HvdH.D * (HvdH.D + 2) ^ 2 * A * p ^ 2 := by ring
  have t3 : HvdH.D * (32 * (A * (2 * p + 8) + 2)) ≤ 384 * HvdH.D * A * p ^ 2 := by
    have hAb : A * (2 * p + 8) + 2 ≤ A * (12 * p) := by
      calc A * (2 * p + 8) + 2 ≤ A * (2 * p + 8) + A * 2 := by
            exact Nat.add_le_add_left (by
              calc (2 : ℕ) = 1 * 2 := by ring
                _ ≤ A * 2 := Nat.mul_le_mul_right _ hA) _
        _ = A * (2 * p + 10) := by ring
        _ ≤ A * (12 * p) := Nat.mul_le_mul_left _ (by omega)
    calc HvdH.D * (32 * (A * (2 * p + 8) + 2)) = 32 * HvdH.D * (A * (2 * p + 8) + 2) := by ring
      _ ≤ 32 * HvdH.D * (A * (12 * p)) := Nat.mul_le_mul_left _ hAb
      _ = 384 * HvdH.D * A * p := by ring
      _ ≤ 384 * HvdH.D * A * p ^ 2 := Nat.mul_le_mul_left _ (pbca_le_sq p (by omega))
  have t4 : HvdH.D * (800 * (HvdH.D * (p + 1))) ≤ 1600 * HvdH.D ^ 2 * A * p ^ 2 := by
    have hP : HvdH.D * (p + 1) ≤ HvdH.D * (2 * p) := Nat.mul_le_mul_left _ (by omega)
    calc HvdH.D * (800 * (HvdH.D * (p + 1))) = 800 * HvdH.D * (HvdH.D * (p + 1)) := by ring
      _ ≤ 800 * HvdH.D * (HvdH.D * (2 * p)) := Nat.mul_le_mul_left _ hP
      _ = 1600 * HvdH.D ^ 2 * p := by ring
      _ ≤ 1600 * HvdH.D ^ 2 * (A * p ^ 2) := Nat.mul_le_mul_left _ hpm
      _ = 1600 * HvdH.D ^ 2 * A * p ^ 2 := by ring
  have t5 : HvdH.D * 100 ≤ 100 * HvdH.D * A * p ^ 2 := by
    have h1A : (1 : ℕ) ≤ A * p ^ 2 := by
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ A * p ^ 2 := Nat.mul_le_mul hA (by nlinarith)
    calc HvdH.D * 100 = 100 * HvdH.D * 1 := by ring
      _ ≤ 100 * HvdH.D * (A * p ^ 2) := Nat.mul_le_mul_left _ h1A
      _ = 100 * HvdH.D * A * p ^ 2 := by ring
  calc 4 * HvdH.D * A * (Kb * (p + 1) ^ 2 + ((2 * p + 8) + sz + 1) * (sz + 1))
        + HvdH.D * (32 * (A * (2 * p + 8) + 2)) + HvdH.D * (800 * (HvdH.D * (p + 1)))
        + HvdH.D * 100
      = 4 * HvdH.D * A * (Kb * (p + 1) ^ 2)
        + 4 * HvdH.D * A * (((2 * p + 8) + sz + 1) * (sz + 1))
        + HvdH.D * (32 * (A * (2 * p + 8) + 2)) + HvdH.D * (800 * (HvdH.D * (p + 1)))
        + HvdH.D * 100 := by ring
    _ ≤ 16 * HvdH.D * Kb * A * p ^ 2 + 8 * HvdH.D * (HvdH.D + 2) ^ 2 * A * p ^ 2
        + 384 * HvdH.D * A * p ^ 2 + 1600 * HvdH.D ^ 2 * A * p ^ 2
        + 100 * HvdH.D * A * p ^ 2 := by linarith [t1, t2, t3, t4, t5]
    _ = pbcaC4 Kb * A * p ^ 2 := by rw [pbcaC4]; ring

/-! ## Size facts for `ℕ` -/

/-- `n < 2 ^ n`. -/
theorem pbca_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      have h1 : k + 1 ≤ 2 ^ k := by omega
      have h3 : 0 < 2 ^ k := pow_pos (by norm_num) k
      omega

/-- `n.size ≤ n`. -/
theorem pbca_size_le (n : ℕ) : n.size ≤ n := by
  rw [Nat.size_le]
  exact pbca_lt_two_pow n

/-! ## Elementary consequences of `HvdH.ResParams` -/

/-- The list facts about `ts` and `ss` needed by the bracket arithmetic. -/
theorem pbcaParamFacts (p α : ℕ) (ss ts : List ℕ) (h : HvdH.ResParams p α ss ts) :
    1 ≤ ts.prod ∧ 3 ≤ ts.sum ∧ (∀ x ∈ ts, x.size ≤ p) ∧ (∀ x ∈ ss, x.size ≤ p) ∧
    (ts.prod * 2 ^ (p + 1)).size ≤ (HvdH.D + 1) * p + 2 := by
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hpt⟩ := h
  have hts3 : ∀ x ∈ ts, 3 ≤ x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hiD : i < HvdH.D := by rw [← htslen]; exact hi
    obtain ⟨h1, h2, -, -, -⟩ := hpt i hiD
    have he : ts[i] = ts.getD i 0 := (List.getD_eq_getElem ts 0 hi).symm
    omega
  have htsize : ∀ x ∈ ts, x.size ≤ p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hiD : i < HvdH.D := by rw [← htslen]; exact hi
    obtain ⟨-, -, h3, -, -⟩ := hpt i hiD
    have he : ts[i] = ts.getD i 0 := (List.getD_eq_getElem ts 0 hi).symm
    rw [Nat.size_le]
    rwa [he]
  have hsssize : ∀ x ∈ ss, x.size ≤ p := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hiD : i < HvdH.D := by rw [← hsslen]; exact hi
    obtain ⟨-, h2, h3, -, -⟩ := hpt i hiD
    have he : ss[i] = ss.getD i 0 := (List.getD_eq_getElem ss 0 hi).symm
    rw [Nat.size_le]
    rw [he]
    exact lt_trans h2 h3
  have hA1 : 1 ≤ ts.prod := by
    refine List.one_le_prod (fun x hx => ?_)
    have := hts3 x hx
    omega
  have hS3 : 3 ≤ ts.sum := by
    have h0 : 0 < ts.length := by rw [htslen]; rw [pbcaD]; norm_num
    have hmem : ts.getD 0 0 ∈ ts := by
      rw [List.getD_eq_getElem ts 0 h0]
      exact List.getElem_mem h0
    exact le_trans (hts3 _ hmem) (List.le_sum_of_mem hmem)
  have hsz : (ts.prod * 2 ^ (p + 1)).size ≤ (HvdH.D + 1) * p + 2 := by
    have hle : ts.prod ≤ 2 ^ (p * HvdH.D) := by
      have h1 : ts.prod ≤ (2 ^ p) ^ ts.length :=
        List.prod_le_pow_length ts (2 ^ p) (fun x hx => le_of_lt (by
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
          have hiD : i < HvdH.D := by rw [← htslen]; exact hi
          obtain ⟨-, -, h3, -, -⟩ := hpt i hiD
          have he : ts[i] = ts.getD i 0 := (List.getD_eq_getElem ts 0 hi).symm
          rwa [he]))
      calc ts.prod ≤ (2 ^ p) ^ ts.length := h1
        _ = (2 ^ p) ^ HvdH.D := by rw [htslen]
        _ = 2 ^ (p * HvdH.D) := by rw [← Nat.pow_mul]
    have hcalc : ts.prod * 2 ^ (p + 1) ≤ 2 ^ ((HvdH.D + 1) * p + 1) := by
      calc ts.prod * 2 ^ (p + 1) ≤ 2 ^ (p * HvdH.D) * 2 ^ (p + 1) :=
            Nat.mul_le_mul_right _ hle
        _ = 2 ^ (p * HvdH.D + (p + 1)) := (Nat.pow_add 2 (p * HvdH.D) (p + 1)).symm
        _ = 2 ^ ((HvdH.D + 1) * p + 1) := by
              congr 1
              ring
    calc (ts.prod * 2 ^ (p + 1)).size ≤ (2 ^ ((HvdH.D + 1) * p + 1)).size :=
          Nat.size_le_size hcalc
      _ = (HvdH.D + 1) * p + 2 := by rw [Nat.size_pow]
  exact ⟨hA1, hS3, htsize, hsssize, hsz⟩

/-- The `vsz` bookkeeping for the frame-cleanup bracket `BrClr`. -/
theorem pbcaVszFacts (p α : ℕ) (ss ts : List ℕ) (h : HvdH.ResParams p α ss ts) :
    HvdH.vsz (HvdH.intList ts) ≤ (HvdH.D + 1) * (p + 3) ∧
    HvdH.vsz (HvdH.intList ss) ≤ (HvdH.D + 1) * (p + 3) ∧
    HvdH.vsz (HvdH.Val.int ((ss.take HvdH.D).prod)) ≤ HvdH.D * p + 2 ∧
    HvdH.vsz (HvdH.Val.int ((ts.drop HvdH.D).prod)) = 3 ∧
    HvdH.vsz (HvdH.Val.int p) ≤ p + 2 ∧
    HvdH.vsz (HvdH.Val.int α) ≤ α + 2 := by
  obtain ⟨-, -, htsize, hsssize, -⟩ := pbcaParamFacts p α ss ts h
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hpt⟩ := h
  have htake : ss.take HvdH.D = ss := by
    rw [← hsslen]
    exact List.take_of_length_le (le_refl _)
  have hdrop : ts.drop HvdH.D = [] := by
    rw [← htslen]
    exact List.drop_eq_nil_of_le (le_refl _)
  have hsslt : ss.prod < 2 ^ (HvdH.D * p) := by
    have h1 : ss.prod ≤ (2 ^ p - 1) ^ ss.length :=
      List.prod_le_pow_length ss (2 ^ p - 1) (fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hiD : i < HvdH.D := by rw [← hsslen]; exact hi
        obtain ⟨-, h2, h3, -, -⟩ := hpt i hiD
        have he : ss[i] = ss.getD i 0 := (List.getD_eq_getElem ss 0 hi).symm
        rw [he]
        omega)
    have hlt : 2 ^ p - 1 < 2 ^ p := by
      have hpos : 0 < 2 ^ p := pow_pos (by norm_num) p
      omega
    calc ss.prod ≤ (2 ^ p - 1) ^ ss.length := h1
      _ = (2 ^ p - 1) ^ HvdH.D := by rw [hsslen]
      _ < (2 ^ p) ^ HvdH.D := Nat.pow_lt_pow_left hlt (by rw [pbcaD]; norm_num)
      _ = 2 ^ (p * HvdH.D) := by rw [← Nat.pow_mul]
      _ = 2 ^ (HvdH.D * p) := by rw [Nat.mul_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc HvdH.vsz (HvdH.intList ts) ≤ (ts.length + 1) * (p + 3) :=
          Work.Params.vsz_intList_le ts p htsize
      _ = (HvdH.D + 1) * (p + 3) := by rw [htslen]
  · calc HvdH.vsz (HvdH.intList ss) ≤ (ss.length + 1) * (p + 3) :=
          Work.Params.vsz_intList_le ss p hsssize
      _ = (HvdH.D + 1) * (p + 3) := by rw [hsslen]
  · rw [htake, pbca_vsz_int]
    have h : (ss.prod).size ≤ HvdH.D * p := by
      rw [Nat.size_le]
      exact hsslt
    omega
  · rw [hdrop, pbca_vsz_int]
    norm_num
  · rw [pbca_vsz_int]
    have h : p.size ≤ p := pbca_size_le p
    omega
  · rw [pbca_vsz_int]
    have h : α.size ≤ α := pbca_size_le α
    omega

/-! ## Rearrangements used by the assembly (kept here so that the main proof never has to
`ring` over the abbreviations `K`, `T`, `Zsum`, …) -/

theorem pbca_mulA (a b c : ℕ) : a * (b * c) = a * b * c := by ring

theorem pbca_mulB (x k s z : ℕ) : 4 * (x * k * (2 * s) * z) = (8 * x * k) * (s * z) := by ring

theorem pbca_mulC (x y : ℕ) : 4 * (x * 4 * y) = (16 * x) * y := by ring

theorem pbca_mulD (x : ℕ) : 4 * (3 * x) = (12 * x) * 1 := by ring

theorem pbca_mulE (a b : ℕ) : 4 * (1000 * a * b) = (4000 * a * b) * 1 := by ring

theorem pbca_mulF (a b c d e : ℕ) :
    4 * a * b * c * (2 * d) * (2 * e) = (16 * a * b * c) * (d * e) := by ring

theorem pbca_mulG (k c D A s a X : ℕ) :
    c * (4 * D * A * (k * s * a * X)) = (A * s) * (4 * c * D * k * a * X) := by ring

theorem pbca_mulH (A s K a X : ℕ) : (A * s) * (K * a * X) = K * A * s * a * X := by ring

theorem pbca_add3rot (x y z : ℕ) : y + z + x = x + y + z := by ring

end Work.Resample
