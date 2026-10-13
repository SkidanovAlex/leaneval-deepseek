import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

open MeasureTheory Set Filter
open scoped Real Topology

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## Two bookkeeping lemmas about the `ℋ^k`-integrand

Both are the "one-sided Tonelli" facts behind the integrability of the single terms of
`HkIntegrand`: `HkMem α k h` supplies the angular integrability at each `z ∈ Iz` and the
integrability of the outer integral, `SmoothOpen h` supplies the joint a.e. strong
measurability (continuity on the open quadrant, the boundary being null), and Tonelli
(`Work.Spaces.integrable_prod_of_iterated`) upgrades these to the product-integrability of
the integrand.  The second lemma restricts the product measure — which is carried by
`Iz ×ˢ Iθ`, hence by `Q0` — to the open quadrant. -/

/-- The `ℋ^k`-integrand of a function which is `C^∞` on the open quadrant and in `ℋ^k` is
integrable for the product of the restricted Lebesgue measures on `Iz` and `Iθ`. -/
private theorem integrable_HkIntegrand_prod {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => Work.Spaces.HkIntegrand α k f z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hsm.continuousOn_HkIntegrand α k)) ?_ hmem.2).1
  rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
  exact Eventually.of_forall fun z hz => hmem.1 z hz

/-- The `ℋ^k`-integrand is integrable over the open quadrant `Q0 = (0,∞) × (0,π/2)`: the
product measure of `Iz ×ˢ Iθ` dominates the restriction of the planar Lebesgue measure to
`Q0`, since `Q0 ⊆ Iz ×ˢ Iθ`. -/
theorem integrableOn_HkIntegrand_Q0 {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      Q0 := by
  refine (integrable_HkIntegrand_prod hsm hmem).mono_measure ?_
  rw [MeasureTheory.Measure.prod_restrict]
  exact MeasureTheory.Measure.restrict_mono
    (Set.prod_mono Set.Ioi_subset_Ici_self Set.Ioo_subset_Icc_self) le_rfl

/-- **The angular weight of the mixed slots is continuous on the open quadrant.**  (The
`i = 0` counterpart is `Work.FTS.EllipticEst.continuousOn_wdivsin_Q0`.) -/
private theorem continuousOn_Wt_Q0lit (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hth : ContinuousOn (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hth

/-- **Each term of the level-`k` integrand is integrable over the open quadrant.**  For `h` smooth
on `Q0` and `h ∈ ℋ^k`, the `(j,i)`-term of `HkIntegrand α k h` — that is
`(mixed j i h · termWeight α i)²` — is integrable over `Q0`, under the same guard as the
corresponding summand of the integrand (pure: `i = 0`, `j ≤ k`; mixed: `1 ≤ i`, `i + j ≤ k`).
The proof combines the honest iterated integrability supplied by `HkMem α k h` with
Tonelli (both domains differ by the null boundary on which the integrand vanishes) and the joint
a.e. strong measurability coming from the smoothness of `mixed j i h` and of the weight. -/
theorem integrableOn_term (α : ℝ) (k : ℕ) {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) (hmem : Work.Spaces.HkMem α k h)
    (j i : ℕ) (hij : (i = 0 ∧ j ≤ k) ∨ (1 ≤ i ∧ i + j ≤ k)) :
    IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed j i h p.1 p.2 * termWeight α i p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 := by
  -- ### The pointwise domination by the full integrand
  have hFsq : ∀ z θ : ℝ, (Work.Spaces.mixed j i h z θ
      * termWeight α i z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k h z θ := by
    intro z θ
    rcases hij with ⟨rfl, hjk⟩ | ⟨hi1, hijk⟩
    · -- pure slot `(j,0)`
      have htw : termWeight α 0 z θ
          = Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
        simp [termWeight]
      rw [Work.Spaces.mixed_zero_right, htw]
      exact Work.Spaces.sq_le_HkIntegrand_z α k h z θ j hjk
    · -- mixed slot `(j,i)`, `1 ≤ i`
      have hne : i ≠ 0 := by omega
      have htw : termWeight α i z θ = Work.Spaces.Wt α z θ := by
        simp [termWeight, hne]
      rw [htw]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α k h z θ i j hi1 hijk
  -- ### A.e. strong measurability: the term is continuous on the open quadrant
  have htwc : ContinuousOn (fun p : ℝ × ℝ => termWeight α i p.1 p.2) Q0 := by
    rcases hij with ⟨rfl, -⟩ | ⟨hi1, -⟩
    · rw [show (fun p : ℝ × ℝ => termWeight α 0 p.1 p.2)
          = fun p : ℝ × ℝ => Work.Spaces.w p.1
              / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) from by
        funext p; simp [termWeight]]
      exact Work.FTS.EllipticEst.continuousOn_wdivsin_Q0
    · have hne : i ≠ 0 := by omega
      rw [show (fun p : ℝ × ℝ => termWeight α i p.1 p.2)
          = fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2 from by
        funext p; simp [termWeight, hne]]
      exact continuousOn_Wt_Q0lit α
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i h p.1 p.2
        * termWeight α i p.1 p.2) ^ 2)
      (MeasureTheory.volume.restrict Q0) :=
    ((((hsm.mixed j i).continuousOn).mul htwc).pow 2).aestronglyMeasurable
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- ### Integrability by domination
  refine (integrableOn_HkIntegrand_Q0 hsm hmem).mono' haesm ?_
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hFsq p.1 p.2

end Work.FTS.PhiStar.Honesty.SlotsLimit
