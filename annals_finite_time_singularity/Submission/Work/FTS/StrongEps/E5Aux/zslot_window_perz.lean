/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise window bound for a `z`-slot of the `ℋ^k`-integrand

For a datum `f` which is `C^∞` on the open quadrant, a level `k`, a slot `i` with `i + 1 ≤ k`,
a radius `z > 0`, a window radius `R₀ ≥ z` and an interior angle `σ ∈ (0, π/2)`,

  `(D_z^i f z σ · w z / sin(2σ)^{η/2})² ≤ (w z)² · (2 + 2/R₀) · ∫_s HkIntegrand α k f s σ ds`.

The point is that a *single radial slice* of a slot of the `ℋ^k`-integrand is controlled by the
*whole* `s`-integral of the integrand at that angle: the radial Hardy inequality in its window
form `Work.FTS.TransportS.half_line_window_bound` buys the value of the slice at `z` from the
weighted square of its `z`-derivative, up to the average `(2/R₀)∫_{R₀}^{2R₀}` of the slice over
a far-away window `[R₀, 2R₀]`; both the derivative slot (`D_z^{i+1} f`, available because
`i + 1 ≤ k`) and the window average are dominated by `HkIntegrand α k f · σ`, with the extra
`sin(2σ)^{η}` weight cancelling against the `sin(2σ)^{-η}` produced by the weight
`w/sin(2σ)^{η/2}` of the slot.  No hypothesis on the sign of `α` is needed: only the *radial*
(`D_z`) slots of the integrand occur.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.H2.SupMixedNB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the `η`-weight `sin(2θ)^{-η}` -/

/-- On the open angular interval `sin(2θ) > 0`. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The pointwise slot dominations -/

/-- The exact rewriting of the weighted square of a `D_z`-slot:
`(D_z^jf z θ · w z / sin(2θ)^{η/2})² = sin(2θ)^{-η} · (D_z^jf z θ · w z)²`. -/
theorem dz_wt_ident (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (j : ℕ) :
    (Work.Spaces.DzIter j f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) := (sin_two_pos_of_mem_Ioo hθ).le
  rw [mul_pow,
    Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta hs
      (ne_of_gt Work.Spaces.eta_pos),
    mul_pow]
  ring

/-- A `D_z`-slot of the `ℋ^k`-integrand, with the weight `w` on the slot and the weight
`sin(2θ)^{-η}` in front, is dominated by `HkIntegrand`. -/
theorem dz_wt_slot_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {j : ℕ} (hj : j ≤ k) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [← dz_wt_ident f hθ j]
  exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ j hj

/-- The bare `D_z`-slot, with only the weight `sin(2θ)^{-η}` in front, is dominated by
`HkIntegrand`; the missing radial weight `w z` is paid for by `w z ≥ 1`. -/
theorem dz_slot_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {j : ℕ} (hj : j ≤ k) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.DzIter j f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hw : 1 ≤ Work.Spaces.w z := Work.FTS.TransportS.one_le_w hz
  have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg (sin_two_pos_of_mem_Ioo hθ).le _
  have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.DzIter j f z θ) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ hsnn
    calc (Work.Spaces.DzIter j f z θ) ^ 2
        = (Work.Spaces.DzIter j f z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hw) (sq_nonneg _)
      _ = (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2 := by rw [mul_pow]
  exact le_trans h1 (dz_wt_slot_le α k f hθ hj)

/-! ## The window step at a fixed angle -/

/-- **The window step for a `z`-slot.**  For `z > 0`, an interior angle `σ`, a slot `i` with
`i + 1 ≤ k` (so that both the slot and its radial derivative occur in `ℋ^k`) and a window
radius `R₀ ≥ z`,

  `sin(2σ)^{-η}·(D_z^if z σ)² ≤ (2 + 2/R₀)·∫_s HkIntegrand α k f s σ ds`.

The two window integrands of `half_line_window_bound` are dominated by `HkIntegrand` (at the
slots `i + 1` and `i`), so that multiplying the window inequality by `sin(2σ)^{-η}` cancels
the weight. -/
theorem zslot_window_step (α : ℝ) {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    {k i : ℕ} (hi : i + 1 ≤ k) {z R₀ σ : ℝ} (hz : 0 < z) (hR : z ≤ R₀)
    (hσ : σ ∈ Set.Ioo 0 (Real.pi / 2))
    (hσint : MeasureTheory.IntegrableOn (fun s : ℝ => Work.Spaces.HkIntegrand α k f s σ)
      Work.Spaces.Iz) :
    (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.DzIter i f z σ) ^ 2
      ≤ (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  -- the hypotheses of the radial Hardy inequality in window form
  have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
      HasDerivAt (fun x : ℝ => Work.Spaces.DzIter i f x σ)
        (Work.Spaces.pz (Work.Spaces.DzIter i f) x σ) x :=
    fun x hx => (hF.DzIter i).hasDerivAt_slice hσ (lt_of_lt_of_le hz hx.1)
  have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.DzIter i f x σ) (Set.Icc R₀ (2 * R₀)) :=
    ((hF.DzIter i).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hRpos hx.1)
  have hcont' : ContinuousOn (fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter i f) x σ)
      (Set.Icc z (2 * R₀)) :=
    (((hF.DzIter i).pz).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz hx.1)
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => (Work.Spaces.DzIter i f x σ) ^ 2)
      (Set.Icc R₀ (2 * R₀)) := (hcont.pow 2).integrableOn_Icc
  have hwin := Work.FTS.TransportS.half_line_window_bound hz hR hderiv hcont hcont' hint
  -- continuity of the two weighted window integrands and of the `HkIntegrand`
  have hcontW : ContinuousOn (fun x : ℝ =>
      x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x)
      (Set.Icc z (2 * R₀)) := by
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
  have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.Icc z (2 * R₀)) := by
    have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀))
        Work.FTS.EllipticEst.Q0 :=
      fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
    have hc := (hF.continuousOn_HkIntegrand α k).comp
      (continuousOn_id.prodMk continuousOn_const) hmap
    simpa only [Function.comp_def, id_eq] using hc
  -- the two window integrals
  set u : ℝ := (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) with hu_def
  have hu : 0 ≤ u := by
    rw [hu_def]
    exact Real.rpow_nonneg (sin_two_pos_of_mem_Ioo hσ).le _
  set IA : ℝ := ∫ x in z..(2 * R₀),
    (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2 with hIA_def
  set IB : ℝ := ∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter i f x σ) ^ 2 with hIB_def
  have hwin' : (Work.Spaces.DzIter i f z σ) ^ 2 ≤ 2 * IA + (2 / R₀) * IB := by
    rw [hIA_def, hIB_def]
    exact hwin
  have huAint : IntervalIntegrable (fun x : ℝ => u
      * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => u
        * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact continuousOn_const.mul (hcontW.pow 2)
  have hHkAint : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact hHkcont
  have huBint : IntervalIntegrable (fun x : ℝ => u * (Work.Spaces.DzIter i f x σ) ^ 2)
      volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => u * (Work.Spaces.DzIter i f x σ) ^ 2)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact continuousOn_const.mul (hcont.pow 2)
  have hHkBint : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
  -- the pointwise domination of the two window integrands
  have hptA : ∀ x ∈ Set.Icc z (2 * R₀), u
      * (x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ * Work.Spaces.w x) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
    have hcomm : x * Work.Spaces.pz (Work.Spaces.DzIter i f) x σ
        = Work.Spaces.DzIter (i + 1) f x σ := rfl
    rw [hcomm]
    exact dz_wt_slot_le α k f hσ hi
  have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀), u * (Work.Spaces.DzIter i f x σ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hRpos hx.1
    exact dz_slot_le α k f hxpos hσ (by omega)
  have hIA_le : u * IA ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
    rw [hIA_def, ← intervalIntegral.integral_const_mul]
    refine le_trans (intervalIntegral.integral_mono_on hz2R huAint hHkAint hptA) ?_
    rw [intervalIntegral.integral_of_le hz2R]
    refine MeasureTheory.setIntegral_mono_set hσint
      (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
    exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
  have hIB_le : u * IB ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
    rw [hIB_def, ← intervalIntegral.integral_const_mul]
    refine le_trans (intervalIntegral.integral_mono_on hR2R huBint hHkBint hptB) ?_
    rw [intervalIntegral.integral_of_le hR2R]
    refine MeasureTheory.setIntegral_mono_set hσint
      (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
    exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
  -- assembly
  have hmain : u * (Work.Spaces.DzIter i f z σ) ^ 2
      ≤ 2 * (u * IA) + (2 / R₀) * (u * IB) := by
    have h1 : u * (Work.Spaces.DzIter i f z σ) ^ 2 ≤ u * (2 * IA + (2 / R₀) * IB) :=
      mul_le_mul_of_nonneg_left hwin' hu
    calc u * (Work.Spaces.DzIter i f z σ) ^ 2 ≤ u * (2 * IA + (2 / R₀) * IB) := h1
      _ = 2 * (u * IA) + (2 / R₀) * (u * IB) := by ring
  have hfinal : u * (Work.Spaces.DzIter i f z σ) ^ 2
      ≤ (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
    have h2 : 2 * (u * IA) + (2 / R₀) * (u * IB)
        ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
          + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) :=
      add_le_add (mul_le_mul_of_nonneg_left hIA_le (by norm_num))
        (mul_le_mul_of_nonneg_left hIB_le (div_nonneg (by norm_num) hRpos.le))
    calc u * (Work.Spaces.DzIter i f z σ) ^ 2
        ≤ 2 * (u * IA) + (2 / R₀) * (u * IB) := hmain
      _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
            + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := h2
      _ = (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by ring
  rw [hu_def] at hfinal
  exact hfinal

/-! ## The assigned lemma -/

theorem zslot_window_perz (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) (i : ℕ) (hi : i + 1 ≤ k)
    {z R₀ σ : ℝ} (hz : 0 < z) (hR : z ≤ R₀) (hσ : σ ∈ Set.Ioo 0 (Real.pi / 2))
    (hσint : MeasureTheory.IntegrableOn (fun s : ℝ => Work.Spaces.HkIntegrand α k f s σ)
      Work.Spaces.Iz) :
    (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / R₀)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
  have hstep := zslot_window_step α hF hi hz hR hσ hσint
  have hLHS : (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter i f z σ) ^ 2) := by
    have hs : 0 ≤ Real.sin (2 * σ) := (sin_two_pos_of_mem_Ioo hσ).le
    rw [mul_pow,
      Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * σ)) Work.Spaces.eta hs
        (ne_of_gt Work.Spaces.eta_pos)]
    ring
  rw [hLHS, mul_assoc]
  exact mul_le_mul_of_nonneg_left hstep (sq_nonneg _)

end Work.FTS.StrongEps.E5Aux
