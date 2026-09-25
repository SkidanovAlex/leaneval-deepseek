import Mathlib
import Submission.Work.Tower.MinkowskiGS.Defs
import Submission.Work.CFT.GlobalClassFormation.card_classGroupTorsion_eq_pow_finrank
import Submission.Work.Tower.Unramified.Discriminant

/-!
# Minkowski's class-number bound for the `3`-torsion of the class group of a cubic field

For a number field `F` of degree `3` and a Minkowski-type constant `C_M > 0` satisfying

`h_K ≤ (C_M · A · (1 + log A)) ^ [K : ℚ]` whenever `rd K ≤ A` and `A ≥ 1`,

the `𝔽₃`-dimension of the `3`-torsion `Cl_F[3]` of the class group of `F` is at most

`3 · log₃ (C_M · rd F · (1 + log (rd F)))`.

The argument is the elementary one: apply the class-number bound with `A = rd F ≥ 1`
(`Work.one_le_rootDiscr`), so `h_F ≤ B ^ 3` where `B := C_M · rd F · (1 + log (rd F))`;
the `3`-torsion is a subgroup of the class group and an `𝔽₃`-vector space of dimension `d`
with `3 ^ d = #Cl_F[3] ≤ h_F`; taking `log₃` (monotone on positive reals) gives
`d ≤ log₃ (B ^ 3) = 3 log₃ B`.
-/

namespace Work.Tower.MinkowskiGS.Minkowski

open NumberField

theorem classGroupTorsion_finrank_le_minkowski
    (F : Type) [Field F] [NumberField F]
    (hdeg : Module.finrank ℚ F = 3)
    (C_M : ℝ) (hCMpos : 0 < C_M)
    (hCM : ∀ (K : Type) [Field K] [NumberField K] (A : ℝ), 1 ≤ A →
      NumberField.rootDiscr K ≤ A →
      (NumberField.classNumber K : ℝ) ≤ (C_M * A * (1 + Real.log A)) ^ (Module.finrank ℚ K)) :
    (Module.finrank (ZMod 3) (Work.CFT.Kummer.classGroupTorsion F 3) : ℝ) ≤
      3 * Real.logb 3 (C_M * NumberField.rootDiscr F *
        (1 + Real.log (NumberField.rootDiscr F))) := by
  classical
  set d : ℕ := Module.finrank (ZMod 3) (Work.CFT.Kummer.classGroupTorsion F 3) with hd
  set B : ℝ := C_M * NumberField.rootDiscr F * (1 + Real.log (NumberField.rootDiscr F)) with hB
  -- ## positivity of the Minkowski bound
  have hrd1 : (1 : ℝ) ≤ NumberField.rootDiscr F := Work.one_le_rootDiscr F
  have hlog0 : 0 ≤ Real.log (NumberField.rootDiscr F) := Real.log_nonneg hrd1
  have hBpos : 0 < B := by
    have h1 : (0 : ℝ) < 1 + Real.log (NumberField.rootDiscr F) := by linarith
    have h2 : (0 : ℝ) < NumberField.rootDiscr F := by linarith
    rw [hB]
    exact mul_pos (mul_pos hCMpos h2) h1
  -- ## Minkowski's class-number bound at `A = rd F`
  have hCN : (NumberField.classNumber F : ℝ) ≤ B ^ 3 := by
    have h := hCM F (NumberField.rootDiscr F) hrd1 le_rfl
    rw [hdeg] at h
    rw [← hB] at h
    exact h
  -- ## `#Cl_F[3] = 3 ^ d`
  have hcard : Nat.card (Work.CFT.Kummer.classGroupTorsion F 3) = 3 ^ d :=
    Work.CFT.GlobalClassFormation.card_classGroupTorsion_eq_pow_finrank F 3
  -- ## `Cl_F[3]` sits inside the class group, whose cardinality is the class number
  have hsub : Nat.card (Work.CFT.Kummer.classGroupTorsion F 3) ≤ NumberField.classNumber F := by
    have hle : Nat.card ↥(Work.CFT.Kummer.classGroupP F 3) ≤ Nat.card (ClassGroup (𝓞 F)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    calc Nat.card (Work.CFT.Kummer.classGroupTorsion F 3)
        = Nat.card ↥(Work.CFT.Kummer.classGroupP F 3) := rfl
      _ ≤ Nat.card (ClassGroup (𝓞 F)) := hle
      _ = NumberField.classNumber F := by
            rw [NumberField.classNumber, Nat.card_eq_fintype_card]
  -- ## hence `3 ^ d ≤ B ^ 3`
  have hpow : (3 : ℝ) ^ d ≤ B ^ 3 := by
    have h1 : (3 ^ d : ℕ) ≤ NumberField.classNumber F := by
      rw [← hcard]
      exact hsub
    have h2 : ((3 ^ d : ℕ) : ℝ) ≤ (NumberField.classNumber F : ℝ) := Nat.cast_le.mpr h1
    push_cast at h2
    exact h2.trans hCN
  -- ## monotonicity of `log₃` and the two logarithmic identities
  have hle : Real.logb 3 ((3 : ℝ) ^ d) ≤ Real.logb 3 (B ^ 3) :=
    (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mpr hpow
  have hpow3 : Real.logb 3 (B ^ 3) = 3 * Real.logb 3 B := by
    have h := Real.logb_pow 3 B 3
    push_cast at h
    exact h
  have hfin : (d : ℝ) = Real.logb 3 ((3 : ℝ) ^ d) := by
    have h := Real.logb_rpow (b := (3 : ℝ)) (x := (d : ℝ)) (by norm_num) (by norm_num)
    rw [Real.rpow_natCast] at h
    rw [h]
  rw [hfin]
  exact hle.trans hpow3.le

end Work.Tower.MinkowskiGS.Minkowski
