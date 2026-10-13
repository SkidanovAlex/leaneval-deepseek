/-
Copyright: work module for the Elgindi finite-time singularity project.

# The per-`z` bound for a single weighted `D_z`-slot of the `ℋ⁶`-integrand

`Work.FTS.StrongEps.E5Aux.HkIntegrand_zslot_perz_le`: for a datum `f` of class `C^∞` on the open
quadrant, honestly in `ℋ⁶` (`HkMem α 6 f`) with vanishing boundary traces (`BdryTraces α 6 f`),
every single weighted radial slot of the `ℋ⁶`-integrand,

  `∫_θ (D_z^i f(z,θ) · w(z)/sin(2θ)^{η/2})² dθ`,   `w(z) = (1+z)²/z²`, `η = 99/100`,

is bounded at *every* `z ∈ [0,∞)` by `C (1 + w(z)²) (1 + Xn₆(f))²`, with a universal constant `C`
(here `C = 3`) independent of `α ∈ (0,1]`, `i ≤ 4` and the datum.

This is the pure-`D_z` half of the per-`z` bound on the level-four `ℋ⁴`-integrand
(`Submission/Work/FTS/StrongEps/E5Aux/HkIntegrand_four_perz_le.lean`); the mixed half is the
proved `Work.FTS.StrongPersist.N6.sliceAng_le6` (`∫_θ (D_z^jD_θ^if)² sin(2θ)^{-γ} ≤ 4 ℋ⁶`).

## Proof

* `z = 0` is trivial: `w 0 = 0`, so the slot vanishes (`Work.FTS.EllipticEst.integrableOn_zSummand`
  makes the same point).
* For `z > 0` the key is the one-dimensional **window form of the radial Hardy inequality**
  `Work.FTS.TransportS.half_line_window_bound`: applied to the `θ`-slice
  `h := x ↦ D_z^i f(x,θ)` on the window `[z, 2R₀]` (with `R₀ = max z 2`) it gives
  `h(z)² ≤ 2∫_z^{2R₀}(x h'(x) w(x))² + (2/R₀)∫_{R₀}^{2R₀} h²`, and `x h'(x) = D_z^{i+1}f(x,θ)`
  (definitional, since `D_z^{i+1} = D_z ∘ D_z^i`).  Multiplying by
  `(w(z)/sin(2θ)^{η/2})²` turns the two window integrands — after the `rpow` bookkeeping
  `Work.FTS.H2.div_rpow_sq`, `(a/x^{c/2})² = a²x^{-c}` — exactly into the `D_z^{i+1}` resp.
  `D_z^i` slots of the `ℋ⁶`-integrand (the second uses `w(x) ≥ 1`), so both window integrals are
  dominated by `∫_{Iz} HkIntegrand α 6 f · θ`; `i + 1 ≤ 5 ≤ 6` is what makes the first one legal
  (this is the private lemma `zslot_window_perz_aux`).
* Integrating the resulting a.e.-in-`θ` pointwise bound over `θ ∈ Iθ` against the Tonelli
  identity `Work.FTS.StrongPersist.N6.sda_HkSqSwap_open6` (`∫_θ ∫_z HkIntegrand = HkSq α 6 f`)
  gives `∫_θ slot² ≤ 3 w(z)² ℋ⁶`, and `ℋ⁶ = Xn₆(f)²`, `w(z)² ≤ 1 + w(z)²` finish it.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`
(axiom record: `_axcheck_zslot.lean`).  The per-`σ` window lemma is also proved under the
standalone name `Work.FTS.StrongEps.E5Aux.zslot_window_perz` in the sibling file
`Submission/Work/FTS/StrongEps/E5Aux/zslot_window_perz.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongEps.E5Aux.AgmonWindow
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.H2.SupMixedNB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The per-`σ` window bound: for `0 < z ≤ R₀`, an interior angle and an `HkIntegrand`-slice
integrable on `Iz`, the weighted `i`-th `D_z`-slot at `(z,σ)` is bounded by
`w(z)²(2 + 2/R₀)` times the full radial integral of the `ℋ^k`-integrand at the angle `σ`. -/
private theorem zslot_window_perz_aux (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) (i : ℕ) (hi : i + 1 ≤ k)
    {z R₀ σ : ℝ} (hz : 0 < z) (hR : z ≤ R₀) (hσ : σ ∈ Set.Ioo 0 (Real.pi / 2))
    (hσint : MeasureTheory.IntegrableOn (fun s : ℝ => Work.Spaces.HkIntegrand α k f s σ)
      Work.Spaces.Iz) :
    (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / R₀)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  have hsinσ : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  -- the hypotheses of the one-dimensional window inequality
  have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
      HasDerivAt (fun x' : ℝ => Work.Spaces.DzIter i f x' σ)
        (Work.Spaces.pz (Work.Spaces.DzIter i f) x σ) x :=
    fun x hx => hF.hasDerivAt_slice_DzIter i hσ (lt_of_lt_of_le hz hx.1)
  have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.DzIter i f x σ) (Set.Icc R₀ (2 * R₀)) :=
    ((hF.DzIter i).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hRpos hx.1)
  have hcont' : ContinuousOn (fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter i f) x σ)
      (Set.Icc z (2 * R₀)) :=
    (((hF.DzIter i).pz).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz hx.1)
  have hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (Work.Spaces.DzIter i f x σ) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
    (hcont.pow 2).integrableOn_Icc
  have hwin := Work.FTS.TransportS.half_line_window_bound
    (h := fun x : ℝ => Work.Spaces.DzIter i f x σ)
    (h' := fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter i f) x σ)
    hz hR hderiv hcont hcont' hint
  -- the weight factor `A = (w z / sin(2σ)^{η/2})²` is nonnegative
  have hAnn : 0 ≤ (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
    sq_nonneg _
  -- continuity of the two window integrands and of the `ℋ^k`-integrand on the windows
  have hcontW : ContinuousOn
      (fun x : ℝ => x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x)
      (Set.Icc z (2 * R₀)) := by
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
  have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.Icc z (2 * R₀)) := by
    have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀)) Work.FTS.EllipticEst.Q0 :=
      fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
    have hc := (hF.continuousOn_HkIntegrand α k).comp
      (continuousOn_id.prodMk continuousOn_const) hmap
    simpa only [Function.comp_def, id_eq] using hc
  have hIntL1 : IntervalIntegrable
      (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ =>
      (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
      (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact hcontW.pow 2
  have hIntR1 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact hHkcont
  have hIntL2 : IntervalIntegrable
      (fun x : ℝ => (Work.Spaces.DzIter i f x σ) ^ 2) volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => (Work.Spaces.DzIter i f x σ) ^ 2)
      (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hcont.pow 2
  have hIntR2 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
  -- the pointwise domination of the two weighted window integrands
  have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
      (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hcomm : x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ
        = Work.Spaces.DzIter (i + 1) f x σ := rfl
    have hA : (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * σ)) Work.Spaces.eta hsinσ.le
        (ne_of_gt Work.Spaces.eta_pos)
    have hB : (Work.Spaces.DzIter (i + 1) f x σ
          * (Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter (i + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_pow, Work.FTS.H2.div_rpow_sq (Work.Spaces.w x) (Real.sin (2 * σ))
        Work.Spaces.eta hsinσ.le (ne_of_gt Work.Spaces.eta_pos)]
      ring
    calc (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter (i + 1) f x σ * Work.Spaces.w x) ^ 2 := by rw [hA, hcomm]
      _ = (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.DzIter (i + 1) f x σ
              * (Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [hB, mul_pow]; ring
      _ ≤ (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ :=
          mul_le_mul_of_nonneg_left
            (Work.Spaces.sq_le_HkIntegrand_z α k f x σ (i + 1) hi) (sq_nonneg _)
  have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
      (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (Work.Spaces.DzIter i f x σ) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hRpos hx.1
    have hwx : 1 ≤ Work.Spaces.w x := Work.FTS.TransportS.one_le_w hx0
    have hA : (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * σ)) Work.Spaces.eta hsinσ.le
        (ne_of_gt Work.Spaces.eta_pos)
    have hB : (Work.Spaces.DzIter i f x σ
          * (Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_pow, Work.FTS.H2.div_rpow_sq (Work.Spaces.w x) (Real.sin (2 * σ))
        Work.Spaces.eta hsinσ.le (ne_of_gt Work.Spaces.eta_pos)]
      ring
    have hwx2 : (1 : ℝ) ≤ (Work.Spaces.w x) ^ 2 := one_le_pow₀ hwx
    have hXle : (Work.Spaces.DzIter i f x σ) ^ 2
        ≤ (Work.Spaces.DzIter i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hwx2
        (sq_nonneg (Work.Spaces.DzIter i f x σ))
      simpa using h
    calc (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (Work.Spaces.DzIter i f x σ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter i f x σ) ^ 2 := by rw [hA]
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
          * ((Work.Spaces.DzIter i f x σ) ^ 2 * (Work.Spaces.w x) ^ 2) :=
          mul_le_mul_of_nonneg_left hXle (by positivity)
      _ = (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.DzIter i f x σ
              * (Work.Spaces.w x / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [hB]; ring
      _ ≤ (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ :=
          mul_le_mul_of_nonneg_left
            (Work.Spaces.sq_le_HkIntegrand_z α k f x σ i (by omega)) (sq_nonneg _)
  -- the two window integrals are dominated by the full radial integral
  have hbigA : ∫ x in z..(2 * R₀), (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ
      ≤ (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [intervalIntegral.integral_of_le hz2R]
    refine MeasureTheory.setIntegral_mono_set hσint
      (Filter.Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
    exact Filter.Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
  have hbigB : ∫ x in R₀..(2 * R₀), (Work.Spaces.w z) ^ 2 * Work.Spaces.HkIntegrand α k f x σ
      ≤ (Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [intervalIntegral.integral_of_le hR2R]
    refine MeasureTheory.setIntegral_mono_set hσint
      (Filter.Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
    exact Filter.Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
  have hmonoA := intervalIntegral.integral_mono_on hz2R (hIntL1.const_mul _) (hIntR1.const_mul _)
    hptA
  have hmonoB := intervalIntegral.integral_mono_on hR2R (hIntL2.const_mul _) (hIntR2.const_mul _)
    hptB
  have hmAeq : (∫ x in z..(2 * R₀),
        (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
      = (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (∫ x in z..(2 * R₀),
            (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2) :=
    intervalIntegral.integral_const_mul _ _
  have hmBeq : (∫ x in R₀..(2 * R₀),
        (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (Work.Spaces.DzIter i f x σ) ^ 2)
      = (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter i f x σ) ^ 2) :=
    intervalIntegral.integral_const_mul _ _
  have hcoe : (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
      * (Work.Spaces.DzIter i f z σ) ^ 2
      = (Work.Spaces.DzIter i f z σ
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [mul_pow]; ring
  rw [← hcoe]
  calc (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (Work.Spaces.DzIter i f z σ) ^ 2
      ≤ (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
        * (2 * (∫ x in z..(2 * R₀),
              (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
          + (2 / R₀) * ∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter i f x σ) ^ 2) :=
        mul_le_mul_of_nonneg_left hwin hAnn
    _ = 2 * ((Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
            * (∫ x in z..(2 * R₀),
              (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2))
          + (2 / R₀) * ((Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
            * (∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter i f x σ) ^ 2)) := by ring
    _ = 2 * (∫ x in z..(2 * R₀),
            (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
              * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
          + (2 / R₀) * (∫ x in R₀..(2 * R₀),
            (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2
              * (Work.Spaces.DzIter i f x σ) ^ 2) := by rw [← hmAeq, ← hmBeq]
    _ ≤ 2 * ((Work.Spaces.w z) ^ 2 * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
          + (2 / R₀) * ((Work.Spaces.w z) ^ 2
              * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left (le_trans hmonoA hbigA) (by norm_num)
        · exact mul_le_mul_of_nonneg_left (le_trans hmonoB hbigB) (by positivity)
    _ = (Work.Spaces.w z) ^ 2 * (2 + 2 / R₀)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by ring

theorem HkIntegrand_zslot_perz_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.Nonlin.BdryTraces α 6 f → ∀ i : ℕ, i ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
  refine ⟨3, by norm_num, ?_⟩
  intro α hα f hF hmem htr i hi z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- ### `z = 0`: the radial weight vanishes
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    have hzero : (fun θ : ℝ => (Work.Spaces.DzIter i f 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [hw0, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    rw [hzero]
    have h1 : (∫ _θ in Work.Spaces.Iθ, (0 : ℝ)) = 0 := by simp
    rw [h1]
    have h2 : 0 ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (1 : ℝ) + (Work.Spaces.w 0) ^ 2 := by rw [hw0]; norm_num
    nlinarith [h2, h3]
  · -- ### `z > 0`: the window bound at every angle, then integrate in `θ`
    have hR : z ≤ max z 2 := le_max_left z 2
    have hRpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
    have h2max : (2 : ℝ) ≤ max z 2 := le_max_right z 2
    obtain ⟨hswap, hGint, hGslice⟩ :=
      Work.FTS.StrongPersist.N6.sda_HkSqSwap_open6 α f hF hmem
    -- almost every angle is interior
    have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
      filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2)] with σ h
      exact fun hmem' => h.mpr hmem'
    -- the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 6 f s σ)) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact zslot_window_perz_aux α hF 6 i (by omega) hzpos hR hσθ hσint
    -- integrability of the two sides
    have hLI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.EllipticEst.integrableOn_zSummand α 6 hF hmem i (by omega)
        (Set.mem_Ici.mpr hzpos.le)
    have hRI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2)
        * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 6 f s σ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hGint.const_mul ((Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2))
    -- the integral bound
    have hmain : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2) * Work.Spaces.HkSq α 6 f := by
      have h1 := MeasureTheory.integral_mono_ae hLI hRI hle
      rw [MeasureTheory.integral_const_mul, hswap] at h1
      exact h1
    -- the coefficient is at most `3`
    have hcoef : 2 + 2 / max z 2 ≤ 3 := by
      have h : 2 / max z 2 ≤ 1 := by
        rw [div_le_one hRpos]
        exact h2max
      linarith
    have hHknn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
    have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have hXsq : Work.Spaces.HkSq α 6 f
        ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
      have h4 : Work.FTS.StrongGlobal.Xn6 α f = Real.sqrt (Work.Spaces.HkSq α 6 f) := rfl
      rw [h4]
      nlinarith [Real.sq_sqrt hHknn, hXnn, hHknn]
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2) * Work.Spaces.HkSq α 6 f := hmain
      _ ≤ (Work.Spaces.w z) ^ 2 * 3 * Work.Spaces.HkSq α 6 f := by
          have h := mul_le_mul_of_nonneg_right hcoef hHknn
          nlinarith [h, sq_nonneg (Work.Spaces.w z)]
      _ ≤ 3 * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
          have hstep : (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 6 f
              ≤ (1 + (Work.Spaces.w z) ^ 2)
                * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 :=
            mul_le_mul (by linarith [sq_nonneg (Work.Spaces.w z)]) hXsq hHknn
              (by linarith [sq_nonneg (Work.Spaces.w z)])
          nlinarith [mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 3)]

end Work.FTS.StrongEps.E5Aux
