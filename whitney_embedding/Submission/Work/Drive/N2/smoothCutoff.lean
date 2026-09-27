import Mathlib

/-!
# A smooth, bounded, Lipschitz "cut-off" of the identity on `ℝ`

We produce a `C^∞` function `χ : ℝ → ℝ` which agrees with the identity on `[-2, 2]`,
is bounded by `3` everywhere and is Lipschitz.

The construction: let `b` be the smooth bump which equals `1` on `[-2,2]` and vanishes
outside `[-3,3]`, built from two copies of `Real.smoothTransition`.  Then
`χ a = ∫_0^a b` is the required function: its derivative is `b`, so it is smooth and
`1`-Lipschitz, it agrees with the identity on `[-2,2]`, and since `0 ≤ b ≤ 1` with
support in `[-3,3]`, it is bounded by `3`.
-/

namespace Work.Drive.N2

open MeasureTheory intervalIntegral

noncomputable section

/-- The smooth bump equal to `1` on `[-2,2]` and to `0` outside `[-3,3]`. -/
def cutBump (t : ℝ) : ℝ :=
  Real.smoothTransition (3 - t) * Real.smoothTransition (3 + t)

lemma cutBump_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cutBump := by
  unfold cutBump
  fun_prop

lemma cutBump_nonneg (t : ℝ) : 0 ≤ cutBump t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma cutBump_le_one (t : ℝ) : cutBump t ≤ 1 := by
  have h2 : 0 ≤ Real.smoothTransition (3 + t) := Real.smoothTransition.nonneg _
  calc cutBump t = Real.smoothTransition (3 - t) * Real.smoothTransition (3 + t) := rfl
    _ ≤ 1 * Real.smoothTransition (3 + t) :=
        mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) h2
    _ = Real.smoothTransition (3 + t) := one_mul _
    _ ≤ 1 := Real.smoothTransition.le_one _

lemma cutBump_abs_le_one (t : ℝ) : |cutBump t| ≤ 1 :=
  abs_le.mpr ⟨by linarith [cutBump_nonneg t], cutBump_le_one t⟩

lemma cutBump_eq_one {t : ℝ} (ht : |t| ≤ 2) : cutBump t = 1 := by
  rw [abs_le] at ht
  have h1 : Real.smoothTransition (3 - t) = 1 :=
    Real.smoothTransition.one_of_one_le (x := 3 - t) (by linarith [ht.2])
  have h2 : Real.smoothTransition (3 + t) = 1 :=
    Real.smoothTransition.one_of_one_le (x := 3 + t) (by linarith [ht.1])
  simp [cutBump, h1, h2]

lemma cutBump_eq_zero_of_three_le {t : ℝ} (ht : 3 ≤ t) : cutBump t = 0 := by
  have h1 : Real.smoothTransition (3 - t) = 0 :=
    Real.smoothTransition.zero_of_nonpos (x := 3 - t) (by linarith)
  simp [cutBump, h1]

lemma cutBump_eq_zero_of_le_neg_three {t : ℝ} (ht : t ≤ -3) : cutBump t = 0 := by
  have h1 : Real.smoothTransition (3 + t) = 0 :=
    Real.smoothTransition.zero_of_nonpos (x := 3 + t) (by linarith)
  simp [cutBump, h1]

lemma cutBump_continuous : Continuous cutBump := cutBump_contDiff.continuous

/-- The candidate cut-off: the primitive of `cutBump` vanishing at `0`. -/
def cutFun (a : ℝ) : ℝ := ∫ t in (0:ℝ)..a, cutBump t

lemma cutFun_hasDerivAt (b : ℝ) : HasDerivAt cutFun (cutBump b) b :=
  (cutBump_continuous.integral_hasStrictDerivAt 0 b).hasDerivAt

lemma cutFun_deriv : deriv cutFun = cutBump :=
  funext fun b => Continuous.deriv_integral cutBump cutBump_continuous 0 b

lemma cutFun_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cutFun := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun a => (cutFun_hasDerivAt a).differentiableAt,
    by rw [cutFun_deriv]; exact cutBump_contDiff⟩

lemma cutFun_eq_self {a : ℝ} (ha : |a| ≤ 2) : cutFun a = a := by
  have hcongr : cutFun a = ∫ t in (0:ℝ)..a, (1:ℝ) := by
    rw [cutFun]
    refine intervalIntegral.integral_congr fun x hx => ?_
    refine cutBump_eq_one ?_
    rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      (rw [abs_le] at ha ⊢; constructor <;> linarith)
  rw [hcongr, intervalIntegral.integral_const]
  simp

lemma cutFun_eq_of_three_le {a : ℝ} (ha : 3 ≤ a) : cutFun a = cutFun 3 := by
  have hsum : (∫ t in (0:ℝ)..(3:ℝ), cutBump t) + (∫ t in (3:ℝ)..a, cutBump t)
      = ∫ t in (0:ℝ)..a, cutBump t :=
    intervalIntegral.integral_add_adjacent_intervals
      (cutBump_continuous.intervalIntegrable _ _)
      (cutBump_continuous.intervalIntegrable _ _)
  have hz : (∫ t in (3:ℝ)..a, cutBump t) = 0 := by
    have : (∫ t in (3:ℝ)..a, cutBump t) = ∫ t in (3:ℝ)..a, (0:ℝ) :=
      intervalIntegral.integral_congr fun x hx => by
        rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          exact cutBump_eq_zero_of_three_le (by linarith)
    rw [this, intervalIntegral.integral_zero]
  change (∫ t in (0:ℝ)..a, cutBump t) = cutFun 3
  rw [← hsum, hz, add_zero]
  rfl

lemma cutFun_eq_of_le_neg_three {a : ℝ} (ha : a ≤ -3) : cutFun a = cutFun (-3) := by
  have hsum : (∫ t in a..(-3:ℝ), cutBump t) + (∫ t in (-3:ℝ)..(0:ℝ), cutBump t)
      = ∫ t in a..(0:ℝ), cutBump t :=
    intervalIntegral.integral_add_adjacent_intervals
      (cutBump_continuous.intervalIntegrable _ _)
      (cutBump_continuous.intervalIntegrable _ _)
  have hz : (∫ t in a..(-3:ℝ), cutBump t) = 0 := by
    have : (∫ t in a..(-3:ℝ), cutBump t) = ∫ t in a..(-3:ℝ), (0:ℝ) :=
      intervalIntegral.integral_congr fun x hx => by
        rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          exact cutBump_eq_zero_of_le_neg_three (by linarith)
    rw [this, intervalIntegral.integral_zero]
  have hs : (∫ t in a..(0:ℝ), cutBump t) = - cutFun a :=
    intervalIntegral.integral_symm (0:ℝ) a
  have hs2 : (∫ t in (-3:ℝ)..(0:ℝ), cutBump t) = - cutFun (-3) :=
    intervalIntegral.integral_symm (0:ℝ) (-3)
  rw [hs] at hsum
  have : - cutFun a = - cutFun (-3) := by
    rw [← hsum, hz, zero_add, hs2]
  linarith

lemma cutFun_abs_le_three_of_nonneg {a : ℝ} (ha : 0 ≤ a) (ha3 : a ≤ 3) : |cutFun a| ≤ 3 := by
  have hnn : ‖cutFun a‖ ≤ 1 * |a - 0| := by
    rw [cutFun]
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
      rw [Real.norm_eq_abs]; exact cutBump_abs_le_one x
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ha, one_mul] at hnn
  linarith

lemma cutFun_abs_le_three_of_nonpos {a : ℝ} (ha : a ≤ 0) (ha3 : -3 ≤ a) : |cutFun a| ≤ 3 := by
  have hsym : (∫ t in a..(0:ℝ), cutBump t) = - cutFun a :=
    intervalIntegral.integral_symm (0:ℝ) a
  have hnn : ‖∫ t in a..(0:ℝ), cutBump t‖ ≤ 1 * |(0:ℝ) - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
      rw [Real.norm_eq_abs]; exact cutBump_abs_le_one x
  rw [hsym, norm_neg, Real.norm_eq_abs, zero_sub, abs_neg, abs_of_nonpos ha, one_mul] at hnn
  linarith

lemma cutFun_abs_le_three (a : ℝ) : |cutFun a| ≤ 3 := by
  rcases le_or_gt 0 a with ha | ha
  · rcases le_or_gt a 3 with ha3 | ha3
    · exact cutFun_abs_le_three_of_nonneg ha ha3
    · rw [cutFun_eq_of_three_le ha3.le]
      exact cutFun_abs_le_three_of_nonneg (by norm_num) (by norm_num)
  · rcases le_or_gt (-3) a with ha3 | ha3
    · exact cutFun_abs_le_three_of_nonpos ha.le ha3
    · rw [cutFun_eq_of_le_neg_three ha3.le]
      exact cutFun_abs_le_three_of_nonpos (by norm_num) (by norm_num)

lemma cutFun_lipschitz : LipschitzWith 1 cutFun := by
  refine lipschitzWith_of_nnnorm_deriv_le (C := 1)
    (fun a => (cutFun_hasDerivAt a).differentiableAt) ?_
  intro x
  rw [cutFun_deriv, ← NNReal.coe_le_coe]
  simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (cutBump_nonneg x), NNReal.coe_one]
  exact cutBump_le_one x

theorem smoothCutoff : ∃ (χ : ℝ → ℝ) (L : NNReal),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
    (∀ a : ℝ, |a| ≤ 2 → χ a = a) ∧
    (∀ a : ℝ, |χ a| ≤ 3) ∧
    LipschitzWith L χ :=
  ⟨cutFun, 1, cutFun_contDiff,
    (fun _ ha => cutFun_eq_self ha),
    cutFun_abs_le_three,
    cutFun_lipschitz⟩

end

end Work.Drive.N2
