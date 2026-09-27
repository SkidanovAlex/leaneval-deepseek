import Mathlib
import Submission.Work.Whitney.EuclidModel
import Submission.Work.Whitney.fderiv_euclidModel

/-!
# Properties of the transported and scaled local model

This file collects the properties of `Work.Whitney.euclidModel n lam β`
(`Submission/Work/Whitney/EuclidModel.lean`): smoothness, immersivity, the structure of its unique
double point and the fact that the new double point is transverse.

Everything is stated for a general scaling parameter `lam` with `0 < lam` and `√n ≤ lam`; the
intended use is `lam = √n`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

variable {n : ℕ} {lam R δ : ℝ} {β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
  {a b : Fin n → ℝ}

/-- The transported and scaled model is smooth. -/
theorem contDiff_euclidModel (hβc : ContDiff ℝ ⊤ β) :
    ContDiff ℝ ⊤ (euclidModel n lam β) := by
  have hlin : ContDiff ℝ ⊤ (fun x : Fin n → ℝ => lam • x) :=
    (lam • ContinuousLinearMap.id ℝ (Fin n → ℝ)).contDiff
  have h1 : ContDiff ℝ ⊤ (fun x : Fin n → ℝ => β (lam • x)) := hβc.comp hlin
  have h2 : ContDiff ℝ ⊤ (scaledModel n lam β) := h1.const_smul (1 / lam)
  have h3 : ContDiff ℝ ⊤
      (fun u : EuclideanSpace ℝ (Fin n) => scaledModel n lam β (euclidOfLp n u)) :=
    h2.comp (euclidOfLp n).contDiff
  exact (pairToE n).contDiff.comp h3

/-- The transported and scaled model is an immersion. -/
theorem injective_fderiv_euclidModel (hlam : lam ≠ 0)
    (hβimm : ∀ x, Function.Injective (fderiv ℝ β x)) :
    ∀ u, Function.Injective (fderiv ℝ (euclidModel n lam β) u) := by
  intro u v w hvw
  rw [fderiv_euclidModel β hlam u] at hvw
  have h1 : (fderiv ℝ β (lam • euclidOfLp n u)) (euclidOfLp n v) =
      (fderiv ℝ β (lam • euclidOfLp n u)) (euclidOfLp n w) :=
    pairToE_injective n hvw
  exact euclidOfLp_injective n (hβimm (lam • euclidOfLp n u) h1)

/-- **The double point** of the transported scaled model: the image of the double point of `β`,
transported and scaled. -/
theorem euclidModel_double_point (hlam : 0 < lam)
    (hab : a ≠ b) (hβab : β a = β b) :
    euclidModel n lam β (scaledPt n lam a) = euclidModel n lam β (scaledPt n lam b) ∧
      scaledPt n lam a ≠ scaledPt n lam b := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have key : ∀ x : Fin n → ℝ,
      euclidModel n lam β (scaledPt n lam x) = pairToE n ((1 / lam) • β x) := by
    intro x
    simp only [euclidModel_apply, scaledModel_apply, scaledPt, euclidOfLp_lpOfEuclid,
      smul_one_div_smul lam hne x]
  constructor
  · rw [key a, key b, hβab]
  · intro h
    have h1 : (1 / lam) • a = (1 / lam) • b := by
      simpa only [scaledPt, euclidOfLp_lpOfEuclid] using congrArg (euclidOfLp n) h
    have h2 : a = b := by
      have h3 := congrArg (fun x : Fin n → ℝ => lam • x) h1
      rwa [smul_one_div_smul lam hne a, smul_one_div_smul lam hne b] at h3
    exact hab h2

/-- **Uniqueness of the double point** of the transported scaled model. -/
theorem euclidModel_eq_iff (hlam : 0 < lam)
    (hβuniq : ∀ u v, u ≠ v → β u = β v → (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
    ∀ u v, euclidModel n lam β u = euclidModel n lam β v →
      u = v ∨ (u = scaledPt n lam a ∧ v = scaledPt n lam b) ∨
        (u = scaledPt n lam b ∧ v = scaledPt n lam a) := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  intro u v huv
  have hβ : β (lam • euclidOfLp n u) = β (lam • euclidOfLp n v) := by
    have h := congrArg (pairOfE n) huv
    simp only [euclidModel_apply, scaledModel_apply, pairOfE_pairToE] at h
    have h' := congrArg (fun x : (Fin n → ℝ) × (Fin n → ℝ) => lam • x) h
    rwa [smul_one_div_smul lam hne (β (lam • euclidOfLp n u)),
      smul_one_div_smul lam hne (β (lam • euclidOfLp n v))] at h'
  by_cases huv' : lam • euclidOfLp n u = lam • euclidOfLp n v
  · left
    have h1 : euclidOfLp n u = euclidOfLp n v := by
      have h := congrArg (fun x : Fin n → ℝ => (1 / lam) • x) huv'
      rwa [one_div_smul_smul lam hne (euclidOfLp n u),
        one_div_smul_smul lam hne (euclidOfLp n v)] at h
    exact euclidOfLp_injective n h1
  · rcases hβuniq _ _ huv' hβ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; left
      constructor
      · have h3 : euclidOfLp n u = (1 / lam) • a := by
          have h := congrArg (fun x : Fin n → ℝ => (1 / lam) • x) h1
          rwa [one_div_smul_smul lam hne (euclidOfLp n u)] at h
        show u = lpOfEuclid n ((1 / lam) • a)
        rw [← h3]
        exact (lpOfEuclid_euclidOfLp n u).symm
      · have h3 : euclidOfLp n v = (1 / lam) • b := by
          have h := congrArg (fun x : Fin n → ℝ => (1 / lam) • x) h2
          rwa [one_div_smul_smul lam hne (euclidOfLp n v)] at h
        show v = lpOfEuclid n ((1 / lam) • b)
        rw [← h3]
        exact (lpOfEuclid_euclidOfLp n v).symm
    · right; right
      constructor
      · have h3 : euclidOfLp n u = (1 / lam) • b := by
          have h := congrArg (fun x : Fin n → ℝ => (1 / lam) • x) h1
          rwa [one_div_smul_smul lam hne (euclidOfLp n u)] at h
        show u = lpOfEuclid n ((1 / lam) • b)
        rw [← h3]
        exact (lpOfEuclid_euclidOfLp n u).symm
      · have h3 : euclidOfLp n v = (1 / lam) • a := by
          have h := congrArg (fun x : Fin n → ℝ => (1 / lam) • x) h2
          rwa [one_div_smul_smul lam hne (euclidOfLp n v)] at h
        show v = lpOfEuclid n ((1 / lam) • a)
        rw [← h3]
        exact (lpOfEuclid_euclidOfLp n v).symm

/-- **Placement of the new double point**: the scaled preimages still lie in the ball of radius
`R`. -/
theorem norm_scaledPt_lt (hlam : 0 < lam) (hsqrt : Real.sqrt n ≤ lam) (ha : ‖a‖ < R) :
    ‖scaledPt n lam a‖ < R := by
  rw [scaledPt_eq, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / lam)]
  have h1 : ‖lpOfEuclid n a‖ ≤ Real.sqrt n * ‖a‖ := norm_lpOfEuclid_le n a
  have h2 : 1 / lam * ‖lpOfEuclid n a‖ ≤ 1 / lam * (Real.sqrt n * ‖a‖) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 1 / lam * (Real.sqrt n * ‖a‖) ≤ ‖a‖ := by
    have hdiv : Real.sqrt n / lam ≤ 1 := (div_le_one hlam).mpr hsqrt
    calc 1 / lam * (Real.sqrt n * ‖a‖) = (Real.sqrt n / lam) * ‖a‖ := by ring
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right hdiv (norm_nonneg a)
      _ = ‖a‖ := one_mul _
  linarith

/-- **The transported scaled model cannot meet the axis outside the ball** from inside the ball:
this is the "activity" of the model's second block, needed to rule out unwanted double points that
mix an inside and an outside point. -/
theorem euclidModel_ne_axis_of_lt (hlam : 0 < lam)
    (hβact : ∀ x, ‖x‖ < R → (β x).2 ≠ 0) (hβR : ∀ x, R ≤ ‖x‖ → β x = inclModel n x)
    {u w : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < R) (hw : R ≤ ‖w‖)
    (h : euclidModel n lam β u = (w, 0)) : False := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have h2 : (1 / lam) • β (lam • euclidOfLp n u) = pairOfE n (w, 0) := by
    have := congrArg (pairOfE n) h
    rwa [euclidModel_apply, scaledModel_apply, pairOfE_pairToE] at this
  have hsnd : (β (lam • euclidOfLp n u)).2 = 0 := by
    have h' := congrArg Prod.snd h2
    simp only [pairOfE_apply, Prod.smul_snd, map_zero] at h'
    rcases smul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (by positivity)
    · exact h''
  have hfst : (β (lam • euclidOfLp n u)).1 = lam • euclidOfLp n w := by
    have h' := congrArg Prod.fst h2
    simp only [pairOfE_apply, Prod.smul_fst] at h'
    have h'' := congrArg (fun x : Fin n → ℝ => lam • x) h'
    rw [smul_one_div_smul lam hne ((β (lam • euclidOfLp n u)).1)] at h''
    exact h''
  by_cases hcase : R ≤ ‖lam • euclidOfLp n u‖
  · have hβv : β (lam • euclidOfLp n u) = inclModel n (lam • euclidOfLp n u) := hβR _ hcase
    have h3 : lam • euclidOfLp n u = lam • euclidOfLp n w := by
      have h4 := hfst
      rw [hβv] at h4
      simpa only [inclModel] using h4
    have h4 : euclidOfLp n u = euclidOfLp n w := by
      have h5 := congrArg (fun x : Fin n → ℝ => (1 / lam) • x) h3
      rwa [one_div_smul_smul lam hne (euclidOfLp n u),
        one_div_smul_smul lam hne (euclidOfLp n w)] at h5
    have h6 : u = w := euclidOfLp_injective n h4
    rw [← h6] at hw
    linarith
  · exact hβact _ (lt_of_not_ge hcase) hsnd

end Work.Whitney
