import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le
import Submission.Work.FTS.NonlinRows.AuxAngRad.angRad_majorant_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.AngRad

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Continuity of the `ℋ⁴`-integrand of an angular `×` radial product

Everything below is the *open-quadrant* continuity of
`(z,θ) ↦ HkIntegrand α 4 (fun z θ => a θ * r z) z θ` under the weakest hypotheses that make it
true: the angular iterates `D_θ^i a` are continuous on `(0,π/2)` and the radial iterates
`D_z^b r` are continuous on `(0,∞)`.  (The sibling
`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand` would need `C^∞` of the *uncurried*
product; the two separation identities `dzIter_ang_rad`/`mixed_ang_rad` make the iterates of the
product into products of the iterates of the factors, so only slice continuity is required.)

The weights are continuous where they are used: `w z = (1+z)²/z²` on `z ≠ 0` and
`sin(2θ)^c` on `(0,π/2)` (where `sin(2θ) > 0`). -/

/-- `(f * g) p = f p * g p` as a `ContinuousOn` statement (the `Pi`-instances are not
definitionally transparent, so the pointwise form is what the piecewise estimates need). -/
private lemma continuousOn_mul_apply {f g : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun p => f p * g p) s :=
  (hf.mul hg).congr (fun p _ => (Pi.mul_apply f g p).symm)

private lemma continuousOn_pow_apply {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (fun p => f p ^ n) s :=
  (hf.pow n).congr (fun p _ => (Pi.pow_apply f n p).symm)

private lemma continuousOn_w_angrad :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  simp only [Work.Spaces.w]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

private lemma continuousOn_sinpow_angrad (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt
      (Work.FTS.Nonlinear.RadialProd.sin_two_pos_of_mem_Ioo hp.2)))

private lemma continuousOn_wdivsin_angrad :
    ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  continuousOn_w_angrad.div (continuousOn_sinpow_angrad (Work.Spaces.eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos
      (Work.FTS.Nonlinear.RadialProd.sin_two_pos_of_mem_Ioo hp.2) _))

private lemma continuousOn_Wt_angrad (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  refine (continuousOn_w_angrad.mul (continuousOn_sinpow_angrad (-(Work.Spaces.gam α / 2)))).congr
    (fun p _ => ?_)
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, Pi.mul_apply]

/-- **The `ℋ⁴`-integrand of `a θ · r z` is continuous on the open quadrant**, from the slice
continuity of the angular and radial iterates only. -/
private lemma continuousOn_HkIntegrand_ang_rad_aux (α : ℝ) (a r : ℝ → ℝ)
    (hcontA : ∀ i : ℕ, i ≤ 4 → ContinuousOn
      (fun θ : ℝ => Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) (Set.Ioo 0 (π / 2)))
    (hcontR : ∀ b : ℕ, b ≤ 4 → ContinuousOn
      (fun z : ℝ => Work.Elliptic.DzdIter b r z) (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hA0 : ContinuousOn (fun θ : ℝ => a θ) (Set.Ioo 0 (π / 2)) :=
    (hcontA 0 (by norm_num)).congr (fun θ _ => by simp)
  have hA : ContinuousOn (fun p : ℝ × ℝ => a p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hA0.comp continuousOn_snd (fun p hp => hp.2)
  have hDzd : ∀ b : ℕ, b ≤ 4 → ContinuousOn
      (fun p : ℝ × ℝ => Work.Elliptic.DzdIter b r p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    fun b hb => (hcontR b hb).comp continuousOn_fst (fun p hp => hp.1)
  have hDth : ∀ i : ℕ, i ≤ 4 → ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    fun i hi => (hcontA i hi).comp continuousOn_snd (fun p hp => hp.2)
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ =>
      (∑ i ∈ Finset.range 5, (a p.2 * Work.Elliptic.DzdIter i r p.1
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0) ?_ ?_
  · refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finsetSum _ (fun i hi => ?_)
      have h1 : ContinuousOn (fun p : ℝ × ℝ =>
          a p.2 * Work.Elliptic.DzdIter i r p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        continuousOn_mul_apply hA (hDzd i (by have := Finset.mem_range.mp hi; omega))
      have h2 : ContinuousOn (fun p : ℝ × ℝ =>
          (a p.2 * Work.Elliptic.DzdIter i r p.1)
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        continuousOn_mul_apply h1 continuousOn_wdivsin_angrad
      exact continuousOn_pow_apply h2 2
    · refine continuousOn_finsetSum _ (fun i hi => continuousOn_finsetSum _ (fun j hj => ?_))
      by_cases h : 1 ≤ i ∧ i + j ≤ 4
      · have hfun : (fun p : ℝ × ℝ =>
            if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0)
            = fun p : ℝ × ℝ =>
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2 := by
          funext p; rw [if_pos h]
        rw [hfun]
        have h1 : ContinuousOn (fun p : ℝ × ℝ =>
            Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
              * Work.Elliptic.DzdIter j r p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          continuousOn_mul_apply (hDth i (by have := Finset.mem_range.mp hi; omega))
            (hDzd j (by have := Finset.mem_range.mp hj; omega))
        have h2 : ContinuousOn (fun p : ℝ × ℝ =>
            (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
              * Work.Elliptic.DzdIter j r p.1) * Work.Spaces.Wt α p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          continuousOn_mul_apply h1 (continuousOn_Wt_angrad α)
        exact continuousOn_pow_apply h2 2
      · have hfun : (fun p : ℝ × ℝ =>
            if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0) = fun _ : ℝ × ℝ => (0 : ℝ) := by
          funext p; rw [if_neg h]
        rw [hfun]
        exact continuousOn_const
  · intro p _hp
    simp only [Work.Spaces.HkIntegrand, Work.FTS.Nonlinear.Pieces.dzIter_ang_rad,
      Work.FTS.Nonlinear.Pieces.mixed_ang_rad]

-- `angular × radial` honesty of the weighted space `ℋ⁴`.
--
-- Let `a : ℝ → ℝ` be an angular profile bounded by `B0` whose `D_θ`-iterates of orders `1..4`
-- are bounded by `B1 · G`, and let `r : ℝ → ℝ` be radial with radial lift in `ℋ⁴`.  If the
-- angular iterates are continuous on `(0,π/2)` and the radial iterates `DzdIter b r`, `b ≤ 4`,
-- are continuous on `(0,∞)`, and if `G²·smG α` and `smE` are integrable on `Iθ`, then the
-- product `(z,θ) ↦ a θ · r z` lies in `ℋ⁴`.
--
-- PROOF RECIPE (all ingredients exist in the workspace):
-- * the *unconditional* identities `Work.FTS.Nonlinear.Pieces.dzIter_ang_rad` and
--   `Work.FTS.Nonlinear.Pieces.mixed_ang_rad` (`Submission/Work/FTS/Nonlinear/Pieces/rowsN0Q.lean`)
--   rewrite `DzIter i (a·r) z θ = a θ * DzdIter i r z` and
--   `mixed j i (a·r) z θ = DthIter i (fun _ θ' => a θ') 0 θ * DzdIter j r z`, with no
--   smoothness hypothesis;
-- * `Work.FTS.Nonlinear.RadialProd.light_sq` / `heavy_sq` turn the two weights into
--   `smE θ = sin(2θ)^(-η)` and `smG α θ = sin(2θ)^(-γ)`, giving, on the open quadrant,
--   `HkIntegrand α 4 (fun z θ => a θ * r z) z θ ≤ Rint r z * (B0^2 * smE θ + 4 * B1^2 * G θ^2 * smG α θ)`
--   (`Work.FTS.Nonlinear.RadialProd.Rint`); the mixed slots with a fixed `i` sum over `j ≤ 3`,
--   which `Rint r z` (a sum over `j ≤ 4`) dominates, and there are four `i`-values, whence the
--   coefficient `4`;
-- * continuity of `HkIntegrand α 4 (a·r)` on the open quadrant follows from the two `ContinuousOn`
--   hypotheses by the same pattern as `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`
--   (the weights `w` and `Wt α` are continuous there);
-- * conclude with `Work.FTS.LocData.HkMem_of_majorant` (or the a.e. variant
--   `Work.FTS.CoercivityFix.Assembly.HkMem_of_majorant_ae`, which only asks for the domination on
--   `Ioo 0 (π/2)`): the majorant's `θ`-slices are integrable by `hI1`, `hI2`, its `z`-integral
--   `Rint r z * (B0^2 * ∫ smE + 4 * B1^2 * ∫ G^2 smG)` is integrable by
--   `Work.FTS.Nonlinear.RadialProd.integrable_Rint` applied to `hrmem`.
theorem HkMem_ang_rad_le {α : ℝ} {a : ℝ → ℝ} {r : ℝ → ℝ} {B0 B1 : ℝ} {G : ℝ → ℝ}
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ| ≤ B1 * G θ)
    (hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (hI2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ) Work.Spaces.Iθ)
    (hrmem : Work.Spaces.HkMem α 4 (fun z θ => r z))
    (hcontA : ∀ i : ℕ, i ≤ 4 → ContinuousOn
      (fun θ : ℝ => Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) (Set.Ioo 0 (π / 2)))
    (hcontR : ∀ b : ℕ, b ≤ 4 → ContinuousOn
      (fun z : ℝ => Work.Elliptic.DzdIter b r z) (Set.Ioi 0)) :
    Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) := by
  -- the pointwise domination holds on the whole *closed* angular interval `Iθ` (existing
  -- lemma), and the majorant has integrable `θ`-slices and integrable `θ`-integral
  have hmaj := Work.FTS.NonlinRows.AuxAngRad.angRad_majorant_integrable (α := α) (r := r)
    (G := G) (B0 := B0) (B1 := B1) hI1 hrmem
  refine Work.FTS.LocData.HkMem_of_majorant α 4 (f := fun z θ => a θ * r z)
    (M := fun z θ => Work.FTS.Nonlinear.RadialProd.Rint r z
      * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)) ?_ ?_ ?_ ?_
  · exact continuousOn_HkIntegrand_ang_rad_aux α a r hcontA hcontR
  · exact hmaj.1
  · exact hmaj.2
  · intro z _hz θ hθ
    exact Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le ha0 ha1 hθ

end Work.FTS.NonlinRows.AngRad
