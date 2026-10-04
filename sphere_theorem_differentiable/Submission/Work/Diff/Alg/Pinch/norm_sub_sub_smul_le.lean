import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

/-- Quantitative mean-value estimate for a curve `R` with derivative `Q (R t)`:
if `‖Q (R s)‖ ≤ B` and `Q ∘ R` is `C`-Lipschitz along `[a, b]` with respect to `R`,
then the first-order Taylor error `R b - R a - (b - a) • Q (R a)` is bounded by
`C * B * (b - a)²`. -/
theorem norm_sub_sub_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ → E) (Q : E → E) {a b B C : ℝ} (hab : a ≤ b) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hder : ∀ t ∈ Set.Icc a b, HasDerivWithinAt R (Q (R t)) (Set.Icc a b) t)
    (hbound : ∀ s ∈ Set.Icc a b, ‖Q (R s)‖ ≤ B)
    (hlip : ∀ s ∈ Set.Icc a b, ‖Q (R s) - Q (R a)‖ ≤ C * ‖R s - R a‖) :
    ‖R b - R a - (b - a) • Q (R a)‖ ≤ C * B * (b - a) ^ 2 := by
  -- Step 1: the curve `R` moves at speed at most `B`.
  have hR : ∀ x ∈ Set.Icc a b, ‖R x - R a‖ ≤ B * (x - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hder
      (fun x hx => hbound x (Set.Ico_subset_Icc_self hx))
  -- Step 2: on `[a, b]` the derivative of the Taylor error is bounded by `C * B * (b - a)`.
  have hbnd : ∀ x ∈ Set.Ico a b, ‖Q (R x) - Q (R a)‖ ≤ C * B * (b - a) := by
    intro x hx
    have hxI : x ∈ Set.Icc a b := Set.Ico_subset_Icc_self hx
    have h2 : ‖R x - R a‖ ≤ B * (b - a) := by
      have h := hR x hxI
      have hle : B * (x - a) ≤ B * (b - a) :=
        mul_le_mul_of_nonneg_left (by linarith [hx.2]) hB
      linarith
    calc ‖Q (R x) - Q (R a)‖ ≤ C * ‖R x - R a‖ := hlip x hxI
      _ ≤ C * (B * (b - a)) := mul_le_mul_of_nonneg_left h2 hC
      _ = C * B * (b - a) := by ring
  have hder_g : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (fun t : ℝ => R t - R a - (t - a) • Q (R a))
        (Q (R x) - Q (R a)) (Set.Icc a b) x := by
    intro x hx
    have h1 := hder x hx
    have h2 : HasDerivWithinAt (fun _ : ℝ => R a) 0 (Set.Icc a b) x :=
      hasDerivWithinAt_const x (Set.Icc a b) (R a)
    have h3 : HasDerivWithinAt (fun t : ℝ => (t - a) • Q (R a)) (Q (R a)) (Set.Icc a b) x := by
      have hc : HasDerivWithinAt (fun t : ℝ => t - a) (1 : ℝ) (Set.Icc a b) x := by
        simpa using ((hasDerivAt_id x).sub_const a).hasDerivWithinAt
      simpa using hc.smul_const (Q (R a))
    convert (h1.sub h2).sub h3 using 1
    simp
  -- Step 3: apply the mean value inequality to the Taylor error, which vanishes at `a`.
  have key : ‖R b - R a - (b - a) • Q (R a)‖ ≤ (C * B * (b - a)) * (b - a) := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hder_g hbnd b (Set.right_mem_Icc.2 hab)
    simpa using h
  calc ‖R b - R a - (b - a) • Q (R a)‖ ≤ (C * B * (b - a)) * (b - a) := key
    _ = C * B * (b - a) ^ 2 := by ring

end Work.Diff.Alg.Pinch
