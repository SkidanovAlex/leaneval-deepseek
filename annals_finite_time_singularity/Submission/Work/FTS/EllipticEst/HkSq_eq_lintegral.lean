import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option maxHeartbeats 800000

/-- **`HkSq` as a `lintegral`.**  `Work.Spaces.HkSq` is the iterated *Bochner* integral of the
nonnegative integrand `Work.Spaces.HkIntegrand`, and `integral_eq_lintegral_of_nonneg_ae` turns
such a Bochner integral into the `toReal` of the corresponding `lintegral` as soon as the outer
integrand is a.e. strongly measurable.

That measurability is where the smoothness hypothesis is used: the uncurried integrand is
continuous on the open quadrant `(0,∞) × (0,π/2)` — the iterated weighted derivatives are `C^∞`
there because `f` is, and the weights `w(z)`, `sin(2θ)^{-γ/2}` are continuous there — while the
complement of the open quadrant inside `Iz ×ˢ Iθ` is the null set
`{z = 0} ∪ {θ = 0} ∪ {θ = π/2}`.  `Work.Spaces.aesm_of_continuousOn_Qd` performs that transfer;
the remaining step is `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` for the partial
`θ`-integration. -/
theorem HkSq_eq_lintegral (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Work.Spaces.HkSq α k f
      = ENNReal.toReal (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)) := by
  -- `∀ n, ContDiffOn ℝ n …` is exactly genuine `C^∞` (`Work.Stability.smoothOrder`).
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := contDiffOn_infty.mpr hf
  have hQ : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  -- `sin (2θ) > 0` on the open quadrant.
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  -- Continuity of the two weights on the open quadrant.
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  have hsinpow : ∀ c : ℝ, ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun c =>
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ =>
            Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    exact hw.mul (hsinpow _)
  have hwdiv : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hw.div (hsinpow _) (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))
  -- The iterated weighted derivatives are continuous on the open quadrant.
  have hDzC : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun i =>
    (Work.FTS.LocData.contDiffOn_DzIter hQ hsm i).continuousOn
  have hmC : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun j i =>
    (Work.FTS.LocData.contDiffOn_mixed hQ hsm j i).continuousOn
  -- Hence the uncurried `ℋ^k`-integrand is continuous on the open quadrant.
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
        = fun p : ℝ × ℝ =>
            (∑ i ∈ Finset.range (k + 1),
                (Work.Spaces.DzIter i f p.1 p.2
                  * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                  if 1 ≤ i ∧ i + j ≤ k
                  then (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                  else 0 := by
      funext p; rfl
    rw [hHk]
    refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ => ?_)
      exact ((hDzC i).mul hwdiv).pow 2
    · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ =>
        continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
      split_ifs with h
      · exact ((hmC j i).mul hWt).pow 2
      · exact continuousOn_const
  -- Continuity on the open quadrant gives a.e. strong measurability for the product measure,
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  -- hence the partially `θ`-integrated integrand is a.e. strongly measurable for `dz`,
  have hslice : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (volume.restrict Work.Spaces.Iz) :=
    hmeas.integral_prod_right'
  -- and the Bochner/`lintegral` bridge, valid for nonnegative a.e. strongly measurable
  -- functions, concludes.
  rw [Work.Spaces.HkSq]
  exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun z =>
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ) hslice

end Work.FTS.EllipticEst
