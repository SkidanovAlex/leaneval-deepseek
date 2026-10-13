/-
# `fkSliceSup` — the slice bounds of the angular moment `FK f`

For a level-six datum `f` (`T6Coef.DatData α f M`: `C^∞` on the open quadrant, `ℋ⁶`/`ℋ⁷`-honest
with `Xn α f = HkNorm α 4 f ≤ M`, angular/axis vanishing) this file proves the three slice
bounds used by the `FK f`-rows of the level-six pairing:

* `|FK f z| ≤ C·M` and `z ↦ FK f z` continuous on `(0,∞)`;
* `∫_θ sin(2θ)^{-η} (f z θ)² ≤ C·M²` and `∫_θ sin(2θ)^{-η} (D_θ f z θ)² ≤ C·M²` for **every**
  `z > 0` (not merely a.e.), with a **universal** constant `C`.

The point of the last two is that the bound is *uniform in `z`* while `M` only bounds the
**global** `ℋ⁴`-norm: an `L²`-bound on the whole quadrant does not, by itself, bound a single
slice.  What makes it work is the window form of the radial Hardy inequality
(`Work.FTS.TransportS.half_line_window_bound`): the radial derivative slots of `HkIntegrand`
control the value of the slice at each `z`, up to an average over a far-away window `[R,2R]`
which is paid for by one extra radial derivative.  Concretely, for every `z > 0`, every angle
`σ ∈ (0,π/2)` and every slot `(j,i)` with `i+j+1 ≤ k`,

  `sin(2σ)^{-η} (D_z^jD_θ^i f z σ)² ≤ (2 + 2/R)·∫_z^∞ HkIntegrand α k f s σ ds`,
  (`fkSliceSup_window_step`, `R ≥ z`),

because each of the two window integrands is dominated by the *same* `HkIntegrand`, weighted by
`sin(2σ)^{η}`, and multiplying by `sin(2σ)^{-η}` cancels the weight exactly.  Integrating in `σ`
against the Tonelli identity `swapK` gives `∫_θ sin(2θ)^{-η}(D_z^jD_θ^if z θ)² ≤ 3·HkSq α k f`,
i.e. `≤ 3 M²` at level `k = 4` — the universal constant `3` and the level `4` (not `6`, whose
norm is not bounded by `M`) are both essential.

All declarations here are hole-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.supDz_zslice6
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.supDzAvgLevel
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.SupMixedNB
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n5Bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Pointwise domination of the slots of `HkIntegrand`, with the weight `sin(2θ)^{-η}` -/

/-- On the open angular interval, `sin(2θ)^{-η} ≤ sin(2θ)^{-γ(α)}` for `0 < α` (both weights
are `≥ 1`, and `γ ≥ η`). -/
theorem fkSliceSup_sin_rpow_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hle : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    have h1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
    have h2 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
    linarith
  have hγ : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.eta) :=
    Real.rpow_le_rpow_of_exponent_ge hs0 hs1 hle
  rw [Real.rpow_neg (le_of_lt hs0), Real.rpow_neg (le_of_lt hs0)]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hs0 Work.Spaces.eta)
    (Real.rpow_pos_of_pos hs0 (Work.Spaces.gam α))).mpr hγ

/-- On the open quadrant, a *mixed* slot times `(w z)²` is dominated by `HkIntegrand`, with the
`η`-weight in place of the `γ`-weight. -/
theorem fkSliceSup_mixed_slot_le {α : ℝ} (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hstep : (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_left (fkSliceSup_sin_rpow_le hα hθ)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have heq : (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθI]
    ring
  rw [heq] at hstep
  exact le_trans hstep (Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij)

/-- On the open quadrant, a *radial* slot times `(w z)²` is dominated by `HkIntegrand`, with the
`η`-weight in place. -/
theorem fkSliceSup_dz_slot_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j : ℕ} (hj : j ≤ k) :
    (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hrew : (Work.Spaces.DzIter j f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta
      hs0.le (ne_of_gt Work.Spaces.eta_pos)]
    ring
  have hzle := Work.Spaces.sq_le_HkIntegrand_z α k f z θ j hj
  rwa [hrew] at hzle

/-- **The window domination of the `z`-derivative slot**: with `w` on the slot, the `η`-weight
in front. -/
theorem fkSliceSup_slot_wt_le {α : ℝ} (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j i : ℕ} (hij : i + j ≤ k) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp only [Work.Spaces.mixed_zero_right]
    have h := fkSliceSup_dz_slot_le α k f hz hθ (j := j) (by omega)
    have hrew : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2
        = (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_pow]; ring
    rw [hrew]
    exact h
  · have h := fkSliceSup_mixed_slot_le hα k f hz hθ (j := j) (i := i) hi hij
    have hrew : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
        = (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_pow]; ring
    rw [hrew]
    exact h

/-- **The bare slot domination**: `sin(2θ)^{-η}(D_z^jD_θ^if z θ)² ≤ HkIntegrand α k f z θ` on the
open quadrant, as soon as the slot `(j,i)` is one of the slots of `ℋ^k`.  (The `w² ≥ 1` of
`fkSliceSup_slot_wt_le` is dropped.) -/
theorem fkSliceSup_slice_integrand_le {α : ℝ} (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j i : ℕ} (hij : i + j ≤ k) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hsin0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  have h := fkSliceSup_slot_wt_le hα k f hz hθ hij
  have hle : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hsin0.le _)
    calc (Work.Spaces.mixed j i f z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2 := by rw [mul_pow]
  exact le_trans hle h

/-- The same domination without the `η`-weight: `(D_z^jD_θ^if z θ)² ≤ HkIntegrand α k f z θ`
(used for the integrability of the bare squared slice). -/
theorem fkSliceSup_sq_le_HkIntegrand {α : ℝ} (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j i : ℕ} (hij : i + j ≤ k) :
    (Work.Spaces.mixed j i f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ 1 :=
    Real.rpow_le_one hs0.le hs1 Work.Spaces.eta_nonneg
  have hkey : (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 1 := by
    rw [← Real.rpow_add hs0, show Work.Spaces.eta + -(Work.Spaces.eta) = 0 by ring,
      Real.rpow_zero]
  have hbase := fkSliceSup_slice_integrand_le hα k f hz hθ hij
  calc (Work.Spaces.mixed j i f z θ) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.mixed j i f z θ) ^ 2) := by
        rw [show (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                * (Work.Spaces.mixed j i f z θ) ^ 2)
            = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              * (Work.Spaces.mixed j i f z θ) ^ 2 from by ring, hkey, one_mul]
    _ ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.eta) * Work.Spaces.HkIntegrand α k f z θ :=
        mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hs0.le _)
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := by
        simpa using mul_le_mul_of_nonneg_right h1 (Work.Spaces.HkIntegrand_nonneg α k f z θ)

/-! ## Integrability of the `θ`-slices -/

/-- The weighted squared slice `θ ↦ sin(2θ)^{-η}(D_z^jD_θ^if z θ)²` is integrable on `Iθ`, for
every `z > 0`, as soon as the slot `(j,i)` occurs in `ℋ^k`. -/
theorem fkSliceSup_slice_integrable {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hij : i + j ≤ k) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.Integrable (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed j i f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le)) ?_ ?_
  · refine Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) ?_ hz
    have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
      intro p hp
      obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
        Work.FTS.EllipticEst.Q0 :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
    exact h1.mul ((hF.mixed j i).continuousOn.pow 2)
  · filter_upwards [ae_mem_Ioo_Iθ_k] with θ hθ
    have hsin0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hsin0.le _) (sq_nonneg _))]
    exact fkSliceSup_slice_integrand_le hα k f hz hθ hij

/-- The bare squared slice `θ ↦ (D_z^jD_θ^if z θ)²` is integrable on `Iθ` for every `z > 0`. -/
theorem fkSliceSup_sq_integrable {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hij : i + j ≤ k) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.Integrable (fun θ => (Work.Spaces.mixed j i f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le)) ?_ ?_
  · exact (Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
      ((hF.mixed j i).continuousOn.pow 2) hz)
  · filter_upwards [ae_mem_Ioo_Iθ_k] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact fkSliceSup_sq_le_HkIntegrand hα k f hz hθ hij

/-! ## The window step at a fixed angle -/

/-- **The window estimate at a fixed angle.**  For `z > 0`, an interior angle `σ`, a slot
`(j,i)` with `i + j + 1 ≤ k` (so that both `(j,i)` and `(j+1,i)` occur in `ℋ^k`) and a window
radius `R₀ ≥ z` (`d = 2/R₀`):

  `sin(2σ)^{-η}(D_z^jD_θ^if z σ)² ≤ (2 + d)·∫_z^∞ HkIntegrand α k f s σ ds`.

The two window integrands of `half_line_window_bound` are dominated by `HkIntegrand` multiplied
by `sin(2σ)^{η}` (`fkSliceSup_slice_integrand_le` at the slots `(j+1,i)` and `(j,i)`), so
multiplying the window inequality by `sin(2σ)^{-η}` cancels the weight. -/
theorem fkSliceSup_window_step {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hji : i + j + 1 ≤ k) {z σ R₀ d : ℝ} (hz : 0 < z) (hR : z ≤ R₀)
    (hd : d = 2 / R₀) (hσ : σ ∈ Set.Ioo 0 (π / 2))
    (hσint : MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α k f s σ)
      Work.Spaces.Iz) :
    (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed j i f z σ) ^ 2
      ≤ (2 + d) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  have hs0 : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  -- derivatives, continuity and integrability on the two windows
  have hderiv : ∀ x ∈ Set.Icc z (2 * R₀), HasDerivAt (fun x => Work.Spaces.mixed j i f x σ)
      (Work.Spaces.pz (Work.Spaces.mixed j i f) x σ) x :=
    fun x hx => (hF.mixed j i).hasDerivAt_slice hσ (lt_of_lt_of_le hz hx.1)
  have hcont : ContinuousOn (fun x => Work.Spaces.mixed j i f x σ) (Set.Icc R₀ (2 * R₀)) :=
    ((hF.mixed j i).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hRpos hx.1)
  have hcont' : ContinuousOn (fun x => Work.Spaces.pz (Work.Spaces.mixed j i f) x σ)
      (Set.Icc z (2 * R₀)) :=
    (((hF.mixed j i).pz).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz hx.1)
  have hint : MeasureTheory.IntegrableOn (fun x => (Work.Spaces.mixed j i f x σ) ^ 2)
      (Set.Icc R₀ (2 * R₀)) :=
    (hcont.pow 2).integrableOn_Icc
  have hwin := Work.FTS.TransportS.half_line_window_bound hz hR hderiv hcont hcont' hint
  -- the continuity of the weighted integrands
  have hcontW : ContinuousOn (fun x : ℝ =>
      x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x)
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
  -- the pointwise window estimates, localised
  set u : ℝ := (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) with hu_def
  have hu : 0 ≤ u := by rw [hu_def]; exact Real.rpow_nonneg hs0.le _
  set IA : ℝ := ∫ x in z..(2 * R₀),
    (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2 with hIA_def
  set IB : ℝ := ∫ x in R₀..(2 * R₀), (Work.Spaces.mixed j i f x σ) ^ 2 with hIB_def
  have hwin' : (Work.Spaces.mixed j i f z σ) ^ 2 ≤ 2 * IA + d * IB := by
    rw [hIA_def, hIB_def, hd]
    exact hwin
  -- the two window integrals, with the weight `u` pulled in
  have huAint : IntervalIntegrable (fun x : ℝ => u
      * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => u
        * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact continuousOn_const.mul (hcontW.pow 2)
  have hHkAint : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact hHkcont
  have huBint : IntervalIntegrable (fun x : ℝ => u * (Work.Spaces.mixed j i f x σ) ^ 2)
      volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => u * (Work.Spaces.mixed j i f x σ) ^ 2)
      (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact continuousOn_const.mul (hcont.pow 2)
  have hHkBint : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
  have hptA : ∀ x ∈ Set.Icc z (2 * R₀), u
      * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
    have hcomm : x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
        = Work.Spaces.mixed (j + 1) i f x σ := rfl
    rw [hcomm]
    exact fkSliceSup_slot_wt_le hα k f hxpos hσ (by omega)
  have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀), u * (Work.Spaces.mixed j i f x σ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hRpos hx.1
    exact fkSliceSup_slice_integrand_le hα k f hxpos hσ (by omega)
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
  have hmain : u * (Work.Spaces.mixed j i f z σ) ^ 2 ≤ 2 * (u * IA) + d * (u * IB) := by
    have h1 : u * (Work.Spaces.mixed j i f z σ) ^ 2 ≤ u * (2 * IA + d * IB) :=
      mul_le_mul_of_nonneg_left hwin' hu
    calc u * (Work.Spaces.mixed j i f z σ) ^ 2 ≤ u * (2 * IA + d * IB) := h1
      _ = 2 * (u * IA) + d * (u * IB) := by ring
  have hfinal : u * (Work.Spaces.mixed j i f z σ) ^ 2
      ≤ (2 + d) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
    have h2 : 2 * (u * IA) + d * (u * IB)
        ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
          + d * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) :=
      add_le_add (mul_le_mul_of_nonneg_left hIA_le (by norm_num))
        (mul_le_mul_of_nonneg_left hIB_le (by rw [hd]; positivity))
    calc u * (Work.Spaces.mixed j i f z σ) ^ 2 ≤ 2 * (u * IA) + d * (u * IB) := hmain
      _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
            + d * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := h2
      _ = (2 + d) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by ring
  rw [hu_def] at hfinal
  exact hfinal

/-! ## The uniform-in-`z` weighted slice bound -/

/-- **The graded weighted slice bound.**  For a datum which is `C^∞` on the open quadrant and
`ℋ^k`-honest, every slot `(j,i)` with `i + j + 1 ≤ k` satisfies, for **every** `z > 0`,

  `∫_θ sin(2θ)^{-η}(D_z^jD_θ^if z θ)² dθ ≤ 3 ∫∫ HkIntegrand α k f`.

The constant `3` is universal (independent of `α`, `k`, `f`, `z`): the window step with
`R₀ = max z 2` gives `∫_θ … ≤ 3 ∫_σ ∫_s HkIntegrand`, and the double integral is `HkSq` by
Tonelli (`swapK`). -/
theorem fkSliceSup_sliceSupGraded {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    ∀ (j i : ℕ), i + j + 1 ≤ k → ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed j i f z θ) ^ 2) ≤ 3 * Work.Spaces.HkSq α k f := by
  intro j i hji z hz
  obtain ⟨hswap, hGint, hGslice⟩ := swapK α k f hF hmem
  have hbound : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed j i f z σ) ^ 2
        ≤ (2 + 2 / max z 2) * (∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α k f s σ) := by
    filter_upwards [hGslice, ae_mem_Ioo_Iθ_k] with σ hσint hσθ
    exact fkSliceSup_window_step hα hF hmem hji hz (le_max_left z 2) rfl hσθ hσint
  have hLI := fkSliceSup_slice_integrable hα hF hmem (j := j) (i := i) (by omega) hz
  have hcoef : 2 + 2 / max z 2 ≤ 3 := by
    have hpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
    have h2max : 2 ≤ max z 2 := le_max_right z 2
    have h : 2 / max z 2 ≤ 1 := by
      rw [div_le_one hpos]
      exact h2max
    linarith
  calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed j i f z θ) ^ 2)
      ≤ ∫ σ in Work.Spaces.Iθ, (2 + 2 / max z 2) * (∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α k f s σ) :=
        MeasureTheory.integral_mono_ae hLI (hGint.const_mul _) hbound
    _ = (2 + 2 / max z 2) * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α k f s σ) := MeasureTheory.integral_const_mul _ _
    _ = (2 + 2 / max z 2) * Work.Spaces.HkSq α k f := by rw [hswap]
    _ ≤ 3 * Work.Spaces.HkSq α k f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α k f)

/-! ## The target -/

theorem fkSliceSup : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (∀ z : ℝ, 0 < z → |Work.Construction.FK f z| ≤ C * M) ∧
      ContinuousOn (fun z => Work.Construction.FK f z) (Set.Ioi 0) ∧
      (∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2) ≤ C * M ^ 2) ∧
      (∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.Dth f z θ) ^ 2) ≤ C * M ^ 2) := by
  refine ⟨100, by norm_num, ?_⟩
  intro α hαI f M hD
  obtain ⟨hα0, hα1⟩ := hαI
  have hSO : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  have hmem6 : Work.Spaces.HkMem α 6 f := hD.h6
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO 4 (by norm_num) hmem6
  have hXn : Work.Spaces.HkNorm α 4 f ≤ M := hD.bdd
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXn
  have hSq4 : Work.Spaces.HkSq α 4 f ≤ M ^ 2 := by
    have h1 : (Work.Spaces.HkNorm α 4 f) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 f) hXn 2
    rwa [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)] at h1
  -- the two weighted slice bounds
  have hslice0 : ∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2)
      ≤ 3 * Work.Spaces.HkSq α 4 f := by
    intro z hz
    have h := fkSliceSup_sliceSupGraded hα0 hSO hmem4 0 0 (by norm_num) z hz
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  have hslice1 : ∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.Dth f z θ) ^ 2)
      ≤ 3 * Work.Spaces.HkSq α 4 f := by
    intro z hz
    have h := fkSliceSup_sliceSupGraded hα0 hSO hmem4 0 1 (by norm_num) z hz
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth] using h
  -- the angular moment
  have hf2 : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) ≤ 3 * Work.Spaces.HkSq α 4 f := by
    intro z hz
    have hI1 : MeasureTheory.Integrable (fun θ => (f z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h := fkSliceSup_sq_integrable hα0 hSO hmem4 (j := 0) (i := 0) (by norm_num) hz
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
    have hI2 : MeasureTheory.Integrable (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (f z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h := fkSliceSup_slice_integrable hα0 hSO hmem4 (j := 0) (i := 0) (by norm_num) hz
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
    have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (f z θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2 := by
      filter_upwards [Work.FTS.H2.ae_sin_two_pos] with θ hsin
      have h1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Work.FTS.H2.one_le_rpow_neg hsin (Real.sin_le_one _) Work.Spaces.eta_nonneg
      nlinarith [sq_nonneg (f z θ)]
    exact le_trans (MeasureTheory.integral_mono_ae hI1 hI2 hpt) (hslice0 z hz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `|FK f z| ≤ 100 M`
    intro z hz
    have hFK2 : (Work.Construction.FK f z) ^ 2 ≤ 16 * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 := by
      have h := FKdzIter_sq_le hSO hmem6 0 (by norm_num) hz
      simpa only [Work.Spaces.DzIter_zero] using h
    have hsq : (Work.Construction.FK f z) ^ 2 ≤ (7 * M) ^ 2 := by
      have h2 := hf2 z hz
      nlinarith [hSq4, hM0, sq_nonneg M]
    have h7M : 0 ≤ 7 * M := by linarith
    calc |Work.Construction.FK f z| = Real.sqrt ((Work.Construction.FK f z) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((7 * M) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 7 * M := Real.sqrt_sq h7M
      _ ≤ 100 * M := by linarith
  · -- continuity
    exact fk_cont_FK hSO hmem4
  · -- the `f`-slice
    intro z hz
    have h := hslice0 z hz
    calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2)
        ≤ 3 * Work.Spaces.HkSq α 4 f := h
      _ ≤ 100 * M ^ 2 := by nlinarith [hSq4, sq_nonneg M]
  · -- the `D_θ f`-slice
    intro z hz
    have h := hslice1 z hz
    calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.Dth f z θ) ^ 2)
        ≤ 3 * Work.Spaces.HkSq α 4 f := h
      _ ≤ 100 * M ^ 2 := by nlinarith [hSq4, sq_nonneg M]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
