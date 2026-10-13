import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalDefs
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

-- `hab : a ≤ b` is part of the requested statement but is not needed: `Icc a b` is
-- contained in `Iz` as soon as `a > 0`, and is empty otherwise.
set_option linter.unusedVariables false

/-! ## The weighted angular energy `Ibd` is dominated by the `ℋ¹`-integrand

The pointwise core of the local integrability of `z ↦ Ibd α f z`: for `z > 0` the radial weight
satisfies `w(z)² ≥ 1`, so that the *single* `γ`-weighted slot

`(mixed 0 1 f z σ · Wt α z σ)² = sin(2σ)² (∂_θ f z σ)² w(z)² sin(2σ)^{-γ}`

of the `ℋ¹`-integrand dominates `sin(2σ)^{2-γ} (∂_θ f z σ)²` — indeed
`sin(2σ)² sin(2σ)^{-γ} = sin(2σ)^{2-γ}` and `w(z)² ≥ 1`.
-/

/-- `Ibd α f z` is nonnegative (its integrand is a nonnegative multiple of a square). -/
theorem Ibd_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Ibd α f z := by
  rw [Ibd, Work.Spaces.Iθ]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
  exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _) (sq_nonneg _)

/-- **The weighted angular energy is dominated by the `ℋ¹`-integrand of the same slice.**
For `z > 0` the weight `w(z) = (1+z)²/z²` satisfies `w(z)² ≥ 1`, while the `ℋ¹`-integrand
contains the slot `(mixed 0 1 f z σ · Wt α z σ)² = sin(2σ)² (∂_θf)² w(z)² sin(2σ)^{-γ}`,
which is `sin(2σ)^{2-γ} (∂_θf)²` up to the factor `w(z)² ≥ 1`. -/
theorem Ibd_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} (hm : Work.Spaces.HkMem α 1 f)
    {z : ℝ} (hz : 0 < z) :
    Ibd α f z ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ := by
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  rw [Ibd, Work.Spaces.Iθ]
  refine MeasureTheory.integral_mono_of_nonneg ?_ (hm.1 z hzIz) ?_
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _) (sq_nonneg _)
  · change ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))),
      (fun σ => Real.sin (2 * σ) ^ (2 - Work.Spaces.gam α) * Work.Spaces.pth f z σ ^ 2) θ
        ≤ Work.Spaces.HkIntegrand α 1 f z θ
    -- the only angles where the comparison `sin(2θ)² sin(2θ)^{-γ} = sin(2θ)^{2-γ}` could fail
    -- are the two endpoints of `Iθ`, which form a null set
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
    · intro θ hθ
      by_contra hnot
      refine hθ ?_
      intro hmem
      have h0 : θ ≠ 0 := by rintro rfl; exact hnot (by simp)
      have h2 : θ ≠ π / 2 := by rintro rfl; exact hnot (by simp)
      have hθ0 : 0 < θ := lt_of_le_of_ne hmem.1 (Ne.symm h0)
      have hθ1 : θ < π / 2 := lt_of_le_of_ne hmem.2 h2
      have hs : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      -- the square of the product weight `Wt = w·sin(2θ)^{-γ/2}`
      have hWt2 : (Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
        congr 1
        rw [← Real.rpow_natCast (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) 2,
            ← Real.rpow_mul (le_of_lt hs)]
        norm_num
      -- the exponent split `sin(2θ)^{2-γ} = sin(2θ)² · sin(2θ)^{-γ}`
      have hs2 : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
            Real.rpow_add hs, Real.rpow_two]
      -- `w(z)² ≥ 1` for `z > 0`
      have hw1 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
        rw [Work.Spaces.w]
        have hle : (1 : ℝ) ≤ (1 + z) ^ 2 / z ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        nlinarith
      refine le_trans ?_
        (Work.Spaces.sq_le_HkIntegrand_mixed α 1 f z θ 1 0 le_rfl (by norm_num))
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
        Work.Spaces.Dth, mul_pow, hWt2, hs2]
      have hABC : (0 : ℝ) ≤ Real.sin (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.pth f z θ) ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hs) _)) (sq_nonneg _)
      calc Real.sin (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.pth f z θ) ^ 2
          ≤ (Real.sin (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.pth f z θ) ^ 2) * (Work.Spaces.w z) ^ 2 :=
            le_mul_of_one_le_right hABC hw1
        _ = Real.sin (2 * θ) ^ 2 * (Work.Spaces.pth f z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    · rw [Set.Finite.measure_zero]
      exact (Set.finite_singleton (π / 2)).insert 0

/-- **Measurability of the weighted angular energy.**  For `f` smooth on the open quadrant the
uncurried integrand `(z,σ) ↦ sin(2σ)^{2-γ} (∂_θf z σ)²` is continuous on the open quadrant, hence
a.e. strongly measurable for the product of the restrictions of Lebesgue measure to `Iz` and `Iθ`
(`Work.Spaces.aesm_of_continuousOn_Qd`); Fubini's measurability theorem
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) then gives the a.e. strong
measurability of `z ↦ Ibd α f z` for the restriction of Lebesgue measure to `Iz`. -/
theorem aesm_Ibd {α : ℝ} {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => Ibd α f z)
      (volume.restrict Work.Spaces.Iz) := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pth f p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := ((hso.pth).continuousOn).pow 2
    exact h1.mul h2
  have h := (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  simpa [Ibd, Function.uncurry] using h

/-- **Local integrability of the weighted angular energy.**  With
`Ibd α f z = ∫_{σ ∈ Iθ} sin(2σ)^{2-γ} (∂_θ f z σ)² dσ` (defined in
`Submission/Work/FTS/StrongEps/EpsLocalPStar/JepsMarginalDefs.lean`, `γ = Work.Spaces.gam α`),
for `f` smooth on the open quadrant and `HkMem α 1 f`, the function `z ↦ Ibd α f z` is integrable
on every compact subinterval of `(0,∞)`.

Route: `1 ≤ w(z)²` and `sin(2σ)^{2-γ} ≤ w(z)² sin(2σ)^{-γ}`, so
`Ibd α f z ≤ ∫_σ HkIntegrand α 1 f z σ` for every `z > 0` (identify
`(mixed 0 1 f z σ * Wt α z σ)² = (∂_θ f z σ)² w(z)² sin(2σ)^{-γ}` and use
`Work.Spaces.sq_le_HkIntegrand_mixed` with `i = 1`, `j = 0`); integrate over `z ∈ [a,b] ⊆ Iz`
with `MeasureTheory.integral_mono_of_nonneg` and use `hm.2`.
Measurability of `z ↦ Ibd α f z` comes from the joint measurability of
`(z,σ) ↦ sin(2σ)^{2-γ} (∂_θ f z σ)²` on the open strip (`Work.Spaces.aesm_slice_of_continuousOn_Qd`,
`Work.Spaces.integrable_prod_of_iterated`; the product measures used in
`Submission/Work/FTS/EllipticEst/AeSlotOneAe/Interp/TkA_slotIntegrable.lean` are exactly the
right setting).
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem IbdLocalIntegrable {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MeasureTheory.IntegrableOn (fun z : ℝ => Ibd α f z) (Set.Icc a b) := by
  -- `[a,b] ⊆ (0,∞) ⊆ Iz`
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_of_lt (lt_of_lt_of_le ha hz.1)
  have hle : volume.restrict (Set.Icc a b) ≤ volume.restrict Work.Spaces.Iz :=
    Measure.restrict_mono hsub le_rfl
  -- the dominating function is the `z`-slice of the `ℋ¹`-integrand, integrable on `Iz`
  have hdom : Integrable (fun z : ℝ =>
      ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ) (volume.restrict (Set.Icc a b)) :=
    MeasureTheory.Integrable.mono_measure hm.2 hle
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => Ibd α f z)
      (volume.restrict (Set.Icc a b)) := (aesm_Ibd hso).mono_measure hle
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun z hz => ?_
  rw [Real.norm_of_nonneg (Ibd_nonneg α f z)]
  exact Ibd_le_HkIntegrand hm (lt_of_lt_of_le ha hz.1)

end Work.FTS.StrongEps.EpsLocalPStar
