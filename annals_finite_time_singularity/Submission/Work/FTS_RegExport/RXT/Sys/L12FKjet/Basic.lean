import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.Sys.EPCDefs
import Submission.Work.FTS_RegExport.RXT.hasDerivAt_integral_Itheta_of_bound
import Submission.Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FM.Core2
import Submission.Work.Construction.Basic
import Submission.Work.Coercivity.integral_Itheta_K
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_Prelim
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKjet.Basic` — the angular kernel and the derivative of `𝔽K`

First half of the jet package of `L12_FK_jets_of_datum`: the elementary bounds of the angular
integrals `∫_θ K(θ)g(θ) dθ`, the angular-moment bound `|Qang F m z| ≤ 18C` for `m ≤ 2` under
the datum bounds `|D_z^k F| ≤ C`, the identity `Qang F 0 = 𝔽K(F)`, the slice differentiability
of an open-quadrant `C¹` function, and the fundamental identity
`∂_z 𝔽K(F)(z) = ∫_θ ∂_zF(z,θ)K(θ) dθ`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The crude bound `|∫_θ K(θ)g(θ)| ≤ 6 C` when `|g| ≤ C` a.e. on `Iθ`.  (The sharp constant
is `C`, by `∫_θ K = 1`; `6` is enough for the whole development.) -/
theorem lfj_abs_integral_K_mul_le {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |g θ| ≤ C) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g θ| ≤ 6 * C := by
  have hbd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ‖Work.Spaces.K θ * g θ‖ ≤ 3 * C := by
    filter_upwards [hb] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    have hK : |Work.Spaces.K θ| ≤ 3 := by
      rw [← Work.Elliptic.Ktheta_eq_K]
      exact Work.FTS_RegExport.RXT.Slots.abs_Ktheta_le θ
    exact mul_le_mul hK hθ (abs_nonneg _) (by norm_num)
  have h1 := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := volume.restrict Work.Spaces.Iθ) hbd
  rw [Work.FTS_RegExport.RXT.Slots.real_univ_restrict_Iθ] at h1
  rw [Real.norm_eq_abs] at h1
  have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
  have h2 : 3 * C * (Real.pi / 2) ≤ 6 * C := by nlinarith
  linarith

/-- `DatumBnd F C` gives the bound on every `D_z`-slot of order `≤ 2`. -/
theorem DatumBnd.DzIter_le {F : ℝ → ℝ → ℝ} {C : ℝ} (h : DatumBnd F C) {k : ℕ} (hk : k ≤ 2)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Work.Spaces.DzIter k F z θ| ≤ C := by
  interval_cases k
  · simpa only [Work.Spaces.DzIter_zero] using (h z θ hz h0 h1).1
  · simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using (h z θ hz h0 h1).2.1
  · simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using (h z θ hz h0 h1).2.2

/-- The angular moment bound: `|Qang F m z| ≤ 18 C` for `m ≤ 2`. -/
theorem lfj_Qang_abs_le {F : ℝ → ℝ → ℝ} {C z : ℝ} (hC : 0 ≤ C)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k F z θ| ≤ C)
    {m : ℕ} (hm : m ≤ 2) (hz : 0 < z) :
    |Work.Elliptic.Qang F m z| ≤ 18 * C := by
  have hb' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |Work.Spaces.DzIter m F z θ| ≤ C := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => hb m hm z θ hz hθ.1 hθ.2)
  have h1 : |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter m F z θ| ≤ 6 * C :=
    lfj_abs_integral_K_mul_le hC hb'
  have hQg : Work.Elliptic.Qang F m z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter m F z θ := by
    rw [Work.Elliptic.Qang, Work.Elliptic.Ktheta_eq_K]
  rw [hQg]
  linarith [h1]

/-- The angular moment at level `0` is the angular moment `(F,K)` of the datum. -/
theorem lfj_Qang_zero_eq_FK (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Qang F 0 z = Work.Construction.FK F z := by
  rw [Work.Elliptic.Qang, Work.Elliptic.Ktheta_eq_K, Work.Construction.FK]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ _ => by rw [Work.Spaces.DzIter_zero]; ring)

/-- `Qang f (k+1) z = z · ∫_θ K(θ)∂_z(D_z^k f)(z,θ) dθ`, by linearity of the `θ`-integral. -/
theorem lfj_Qang_succ_eq (f : ℝ → ℝ → ℝ) (k : ℕ) (z : ℝ) :
    Work.Elliptic.Qang f (k + 1) z
      = z * ∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ := by
  have h1 : Work.Elliptic.Qang f (k + 1) z
      = ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ
          * (z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) := rfl
  rw [h1, show (fun θ => Work.Elliptic.Ktheta θ
        * (z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ))
      = fun θ => z * (Work.Elliptic.Ktheta θ
          * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) from by funext θ; ring,
    MeasureTheory.integral_const_mul]

/-- The level one angular moment against `∂_zF`:
`Qang F 1 z = z ∫_θ ∂_zF(z,θ)K(θ) dθ`. -/
theorem lfj_Qang_one_eq (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Qang F 1 z
      = z * ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F z θ * Work.Spaces.K θ := by
  rw [lfj_Qang_succ_eq F 0 z]
  simp only [Work.Spaces.DzIter_zero]
  congr 1
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
    rw [Work.Elliptic.Ktheta_eq_K]; ring)

/-- `K(θ) = 3 sinθ cos²θ` is continuous as a function of the *pair* `(z,θ)`. -/
theorem lfj_continuousOn_Ktheta_jet :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
      = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
    funext p; rw [Work.Elliptic.Ktheta]
  rw [hfun]
  exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
    ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn

/-- The same, for the weight `K` of `Spaces`. -/
theorem lfj_continuousOn_K_jet :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      = fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 := by
    funext p; rw [Work.Elliptic.Ktheta_eq_K]
  rw [hfun]
  exact lfj_continuousOn_Ktheta_jet

/-- The radial slice of a `C¹` function on the open quadrant is differentiable with
derivative `pz`. -/
theorem lfj_slice_hasDerivAt {g : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {x θ : ℝ} (hx : 0 < x) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    HasDerivAt (fun y => g y θ) (Work.Spaces.pz g x θ) x := by
  have hd : DifferentiableAt ℝ (Function.uncurry g) (x, θ) :=
    (h.differentiableOn (by norm_num)).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hx, h0, h1⟩))
  have h2 : HasFDerivAt (fun y : ℝ => (y, θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) x :=
    hasFDerivAt_prodMk_left x θ
  have h3 : HasDerivAt (fun y : ℝ => Function.uncurry g (y, θ))
      ((fderiv ℝ (Function.uncurry g) (x, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1) x := by
    simpa only [Function.comp_def] using (hd.hasFDerivAt.comp x h2).hasDerivAt
  have hval : (fderiv ℝ (Function.uncurry g) (x, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1
      = Work.Spaces.pz g x θ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    exact (Work.Spaces.deriv_slice_fst (Function.uncurry g) x θ hd).symm
  rw [hval] at h3
  exact h3

/-- **`∂_z 𝔽K(F)(z) = ∫_θ ∂_zF(z,θ)K(θ) dθ`** for a datum which is `C²` on the open quadrant
with `|D_z^k F| ≤ C` (`k ≤ 2`) there and `C ≥ 0`. -/
theorem lfj_hasDerivAt_FK {F : ℝ → ℝ → ℝ} {C z : ℝ}
    (h2 : ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k F z θ| ≤ C)
    (hC : 0 ≤ C) (hz : 0 < z) :
    HasDerivAt (fun z' => Work.Construction.FK F z')
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F z θ * Work.Spaces.K θ) z := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS_RegExport.RXT.Slots.isFiniteMeasure_restrict_Iθ
  have hz2 : 0 < z / 2 := by linarith
  have hVmem : z ∈ Set.Ioi (z / 2) := Set.mem_Ioi.mpr (by linarith)
  have hVpos : ∀ x ∈ Set.Ioi (z / 2), 0 < x := fun x hx => lt_trans hz2 (Set.mem_Ioi.mp hx)
  have h1 : ContDiffOn ℝ 1 (Function.uncurry F) Work.FTS.EllipticEst.Q0 := h2.of_le (by norm_num)
  have hpz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz F)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin Work.FTS.EllipticEst.isOpen_Q0 (n := 1) h2
  have hcg : ContinuousOn (Function.uncurry (fun x θ => F x θ * Work.Spaces.K θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 * Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 from h2.continuousOn.mul lfj_continuousOn_K_jet
  have hcg' : ContinuousOn
      (Function.uncurry (fun x θ => Work.Spaces.pz F x θ * Work.Spaces.K θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2 * Work.Spaces.K p.2)
      Work.FTS.EllipticEst.Q0 from hpz.continuousOn.mul lfj_continuousOn_K_jet
  have hKbd : ∀ θ : ℝ, |Work.Spaces.K θ| ≤ 3 := by
    intro θ; rw [← Work.Elliptic.Ktheta_eq_K]
    exact Work.FTS_RegExport.RXT.Slots.abs_Ktheta_le θ
  have hint : Integrable (fun θ => F z θ * Work.Spaces.K θ) (volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (3 * C))
      (Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 hcg hz) ?_
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |F z θ| * |Work.Spaces.K θ| ≤ C * 3 :=
          mul_le_mul (hb 0 (by norm_num) z θ hz hθ.1 hθ.2) (hKbd θ) (abs_nonneg _) hC
      _ = 3 * C := by ring
  have hpzbd : ∀ x ∈ Set.Ioi (z / 2), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz F x θ| ≤ 2 * C / z := by
    intro x hx θ hθ
    have hx0 : 0 < x := hVpos x hx
    have hxz : z / 2 < x := Set.mem_Ioi.mp hx
    have h := hb 1 (by norm_num) x θ hx0 hθ.1 hθ.2
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz] at h
    rw [abs_mul, abs_of_pos hx0] at h
    have hle : |Work.Spaces.pz F x θ| ≤ C / x := by
      rw [le_div_iff₀ hx0]; rw [mul_comm]; exact h
    have h2' : C / x ≤ 2 * C / z := by
      have h3 : C / x ≤ C / (z / 2) := div_le_div_of_nonneg_left hC hz2 hxz.le
      have h4 : C / (z / 2) = 2 * C / z := by field_simp
      linarith [h3, le_of_eq h4]
    linarith
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ Set.Ioi (z / 2),
      ‖Work.Spaces.pz F x θ * Work.Spaces.K θ‖ ≤ 3 * (2 * C / z) := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h3 := hpzbd x hx θ hθ
    have h4 : 0 ≤ 2 * C / z := by positivity
    calc |Work.Spaces.pz F x θ| * |Work.Spaces.K θ| ≤ (2 * C / z) * 3 :=
          mul_le_mul h3 (hKbd θ) (abs_nonneg _) h4
      _ = 3 * (2 * C / z) := by ring
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioi (z / 2),
      HasDerivAt (fun y => F y θ * Work.Spaces.K θ)
        (Work.Spaces.pz F x θ * Work.Spaces.K θ) x :=
    fun θ hθ x hx =>
      (lfj_slice_hasDerivAt h1 (hVpos x hx) hθ.1 hθ.2).mul_const (Work.Spaces.K θ)
  have key := Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0 (V := Set.Ioi (z / 2))
    isOpen_Ioi hVmem hVpos hcg hcg' hint hbound hdiff
  simpa only [Work.Construction.FK] using key

end Work.FTS_RegExport.RXT.Sys
