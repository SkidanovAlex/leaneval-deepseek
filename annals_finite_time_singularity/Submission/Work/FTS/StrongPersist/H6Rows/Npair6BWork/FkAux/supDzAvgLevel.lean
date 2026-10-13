import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.HkSqSwap
import Submission.Work.FTS.H2.SupMixedNB
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The level-`k` uniform-in-`z` angular-average bound

This file proves `supDzAvgLevel`: for a datum `f` of class `C^∞` on the open quadrant which
lies in the weighted space `ℋ^k` (`Work.Spaces.HkMem α k f`), the angular average at a fixed
radius `z > 0` of any radial derivative `D_z^b f` with `b + 1 ≤ k` is bounded by a universal
multiple of `HkSq α k f`:

  `∫_{Iθ} (D_z^b f z θ)^2 dθ ≤ 3 · HkSq α k f`   for every `z > 0`.

The proof is the level-`k` version of `Work.FTS.TransportS.SupDzAux.sup_dz_avg_le` (level `4`,
`b ≤ 2`) and of `Work.FTS.StrongPersist.N6.sliceAvg_le6` (level `6`, `a + b ≤ 5`): the same
window form of the radial Hardy inequality (`Work.FTS.TransportS.half_line_window_bound`) +
Tonelli.  The level-`k` ingredients used here are

* the pointwise domination `(D_z^j f z θ)^2 (w z)^2 ≤ HkIntegrand α k f z θ` for `j ≤ k`
  (`dzIter_sq_w_sq_le_HkIntegrand_k` below, which is `Work.Spaces.sq_le_HkIntegrand_z`
  combined with `sin(2θ)^(-η) ≥ 1`);
* the level-`k` Tonelli swap (`swapK` below, `Work.FTS.H2.swap_iterated_integral_of_nonneg`
  with `SmoothOpen.continuousOn_HkIntegrand`).

The hypothesis `b + 1 ≤ k` is exactly what the window argument needs: the derivative slot
`D_z^{b+1} f` must be a slot of `ℋ^k`, while the window term only needs `D_z^b f`, i.e. `b ≤ k`.
-/

/-! ## Pointwise domination of a single `D_z`-slot -/

/-- On the open quadrant, `(D_z^j f z θ)² * (w z)² ≤ HkIntegrand α k f z θ` for `j ≤ k`:
the plain `D_z`-slot bound `sq_le_HkIntegrand_z`, multiplied by the factor
`sin(2θ)^(-η) ≥ 1`.  (Level-`k` version of `Work.FTS.H2.dzIter_sq_w_le_HkIntegrand`.) -/
theorem dzIter_sq_w_sq_le_HkIntegrand_k (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hsin : 0 < Real.sin (2 * θ)) (j : ℕ) (hj : j ≤ k) :
    (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.FTS.H2.one_le_rpow_neg hsin hs1 Work.Spaces.eta_nonneg
  have hrew : (Work.Spaces.DzIter j f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta
      (le_of_lt hsin) (ne_of_gt Work.Spaces.eta_pos)]
    ring
  have hzle := Work.Spaces.sq_le_HkIntegrand_z α k f z θ j hj
  rw [hrew] at hzle
  calc (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h1
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := hzle

/-- On the open quadrant, `(D_z^j f z θ)² ≤ HkIntegrand α k f z θ` for `j ≤ k`: the previous
bound divided by `w² ≥ 1` at `z > 0`.  (Level-`k` version of `avgDzIter_sq_le`.) -/
theorem avgDzIter_sq_le_k (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hz : 0 < z)
    (hsin : 0 < Real.sin (2 * θ)) (j : ℕ) (hj : j ≤ k) :
    (Work.Spaces.DzIter j f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have h := dzIter_sq_w_sq_le_HkIntegrand_k α k f z θ hsin j hj
  have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  calc (Work.Spaces.DzIter j f z θ) ^ 2
      = (Work.Spaces.DzIter j f z θ) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_left hw (sq_nonneg _)
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := h

/-! ## Tonelli for the level-`k` integrand -/

/-- **Tonelli for the `ℋ^k`-integrand of an open-class datum.**  For `f` of class `C^∞` on the
open quadrant with `HkMem α k f`, the iterated integral of `HkIntegrand α k f` in the order
`∫_θ ∫_z` equals `HkSq α k f`, its partially integrated function is integrable on the angles,
and for almost every angle the radial slice is integrable.  (The `SmoothOpen`-version of
`Work.FTS.H2.HkSqSwap` and of `Work.FTS.TransportS.SupDzAux.avgHkSqSwap`, with the numeral `4`
replaced by `k`.) -/
theorem swapK (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α k f) :
    (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ
        = Work.Spaces.HkSq α k f) ∧
      MeasureTheory.Integrable
        (fun σ : ℝ => ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α k f s σ)
          Work.Spaces.Iz) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_HkIntegrand α k)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  have houter : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice houter
  refine ⟨?_, h2, h3⟩
  rw [Work.Spaces.HkSq]
  exact h1

/-- Almost every angle of `Iθ` lies in the open interval `(0, π/2)`. -/
theorem ae_mem_Ioo_Iθ_k :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
  filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
    (b := Real.pi / 2)] with σ h
  exact fun hmem' => h.mpr hmem'

/-! ## The main estimate -/

/-- Level-`k` generalisation of the uniform-in-`z` angular-average bound.
Templates in the tree: `Work.FTS.TransportS.SupDzAux.sup_dz_avg_le` (level 4, `b ≤ 2`, constant 3)
and `Work.FTS.StrongPersist.N6.sliceAvg_le6` (level 6, mixed slots with `a + b ≤ 5`, constant 4);
both are the same window-bound + Tonelli argument with `4`/`6` replaced by `k`.  The needed
level-`k` ingredients are: the pointwise domination
`(DzIter j f z θ)^2 * (w z)^2 ≤ HkIntegrand α k f z θ` for `j ≤ k` (from
`Work.Spaces.sq_le_HkIntegrand_z` plus `1 ≤ sin(2θ)^(-η)`), the level-`k` Tonelli swap
(`Work.FTS.H2.swap_iterated_integral_of_nonneg` with `SmoothOpen.continuousOn_HkIntegrand`),
and `Work.FTS.TransportS.half_line_window_bound`. -/
theorem supDzAvgLevel : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (k b : ℕ), 0 < α →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α k f → b + 1 ≤ k →
    ∀ z : ℝ, 0 < z →
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 ≤ C * Work.Spaces.HkSq α k f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α f k b hα hF hmem hbk z hz
  obtain ⟨hswap, hGint, hGslice⟩ := swapK α k f hF hmem
  have hbk' : b ≤ k := by omega
  have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ae_mem_Ioo_Iθ_k
  -- the window bound, for every radius `R₀ ≥ z`
  have hbound : ∀ R₀ : ℝ, z ≤ R₀ →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
        ≤ (2 + 2 / R₀) * Work.Spaces.HkSq α k f := by
    intro R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
    have hz2R : z ≤ 2 * R₀ := by linarith
    have hR2R : R₀ ≤ 2 * R₀ := by linarith
    have hσbound : ∀ σ : ℝ, σ ∈ Set.Ioo 0 (π/2) →
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α k f s σ)
          Work.Spaces.Iz →
        (Work.Spaces.DzIter b f z σ) ^ 2
          ≤ (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
      intro σ hσ hσint
      have hsinσ : 0 < Real.sin (2 * σ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
      -- the hypotheses of the one-dimensional window inequality
      have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
          HasDerivAt (fun x : ℝ => Work.Spaces.DzIter b f x σ)
            (Work.Spaces.pz (Work.Spaces.DzIter b f) x σ) x :=
        fun x hx => hF.hasDerivAt_slice_DzIter b hσ (lt_of_lt_of_le hz hx.1)
      have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.DzIter b f x σ)
          (Set.Icc R₀ (2 * R₀)) :=
        ((hF.DzIter b).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hRpos hx.1)
      have hcont' : ContinuousOn (fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ)
          (Set.Icc z (2 * R₀)) :=
        (((hF.DzIter b).pz).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have hint : MeasureTheory.IntegrableOn
          (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
        (hcont.pow 2).integrableOn_Icc
      have hwin := Work.FTS.TransportS.half_line_window_bound
        (h := fun x : ℝ => Work.Spaces.DzIter b f x σ)
        (h' := fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ)
        hz hR hderiv hcont hcont' hint
      -- continuity of the two relevant slices on the window intervals
      have hcontW : ContinuousOn
          (fun x : ℝ => x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x)
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
      have hIntL1 : IntervalIntegrable
          (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            * Work.Spaces.w x) ^ 2) volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            * Work.Spaces.w x) ^ 2) (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hcontW.pow 2
      have hIntR1 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
          (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hHkcont
      have hIntL2 : IntervalIntegrable
          (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2) volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2)
            (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hcont.pow 2
      have hIntR2 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
          volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
          (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
      -- pointwise domination of the two window integrands
      have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
          (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x) ^ 2
            ≤ Work.Spaces.HkIntegrand α k f x σ := by
        intro x hx
        have hcomm : x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            = Work.Spaces.DzIter (b + 1) f x σ := rfl
        rw [hcomm, mul_pow]
        exact dzIter_sq_w_sq_le_HkIntegrand_k α k f x σ hsinσ (b + 1) (by omega)
      have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
          (Work.Spaces.DzIter b f x σ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f x σ :=
        fun x hx => avgDzIter_sq_le_k α k f x σ (lt_of_lt_of_le hRpos hx.1) hsinσ b hbk'
      -- the two window integrals are dominated by the full radial integral
      have hbigA : ∫ x in z..(2 * R₀), Work.Spaces.HkIntegrand α k f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
        rw [intervalIntegral.integral_of_le hz2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
      have hbigB : ∫ x in R₀..(2 * R₀), Work.Spaces.HkIntegrand α k f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
        rw [intervalIntegral.integral_of_le hR2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
      have hmonoA := intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hptA
      have hmonoB := intervalIntegral.integral_mono_on hR2R hIntL2 hIntR2 hptB
      calc (Work.Spaces.DzIter b f z σ) ^ 2
          ≤ 2 * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
              * Work.Spaces.w x) ^ 2)
            + (2 / R₀) * ∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter b f x σ) ^ 2 := hwin
        _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
            + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_trans hmonoA hbigA) (by norm_num))
              (mul_le_mul_of_nonneg_left (le_trans hmonoB hbigB) (by positivity))
        _ = (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz,
              Work.Spaces.HkIntegrand α k f s σ) := by ring
    -- integrate the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α k f s σ) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact hσbound σ hσθ hσint
    have hLI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine MeasureTheory.Integrable.mono'
        (hmem.1 z (show z ∈ Work.Spaces.Iz from le_of_lt hz)) ?_ ?_
      · exact (Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => Work.Spaces.DzIter b f p.1 p.2)
          ((hF.DzIter b).continuousOn) hz).pow 2
      · filter_upwards [Work.FTS.H2.ae_sin_two_pos] with σ hsin
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact avgDzIter_sq_le_k α k f z σ hz hsin b hbk'
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α k f s σ :=
          MeasureTheory.integral_mono_ae hLI (hGint.const_mul _) hle
      _ = (2 + 2 / R₀) * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α k f s σ) := MeasureTheory.integral_const_mul _ _
      _ = (2 + 2 / R₀) * Work.Spaces.HkSq α k f := by rw [hswap]
  -- take `R₀ = max z 2`, so that the coefficient is at most `3`
  have hzmax : z ≤ max z 2 := le_max_left z 2
  have hbnd := hbound (max z 2) hzmax
  have hpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
  have h2max : 2 ≤ max z 2 := le_max_right z 2
  have hcoef : 2 + 2 / max z 2 ≤ 3 := by
    have h : 2 / max z 2 ≤ 1 := by
      rw [div_le_one hpos]
      exact h2max
    linarith
  calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
      ≤ (2 + 2 / max z 2) * Work.Spaces.HkSq α k f := hbnd
    _ ≤ 3 * Work.Spaces.HkSq α k f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α k f)

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
