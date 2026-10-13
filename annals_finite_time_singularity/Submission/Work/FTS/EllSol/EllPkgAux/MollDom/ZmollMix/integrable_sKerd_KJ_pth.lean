import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.prod_integrable_of_slice_bound
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.aeStronglyMeasurable_exp
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt
import Submission.Work.FTS.EllSol.PkgK5.i0TraceMoll.PsiAuxExp
import Submission.Work.FTS.EllSol.PkgK5.i0TraceMoll.PsiAux.pthSliceLeE2s
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv_bdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the *mixed* kernel `sKerd δ (log z - t) · KJ ε θ s · ∂_θG(eᵗ,s)`

The product-integrability statement behind the Fubini/Tonelli arguments that mix the
log-radial mollification `sKerd δ (log z - ·)` (`δ ≤ 1/2`, supported in `|·| ≤ δ ≤ 1`) with
the angular Jensen kernel `KJ ε θ ·` (`ε ≤ 1/2`) applied to the *angular* derivative
`∂_θG` of a trace-class datum `G` (`TraceClass G`, `FourInts G`).

The proof is a direct application of `MollDom.prod_integrable_of_slice_bound`, whose
hypotheses are exactly what the trace-class structure supplies:

* the radial kernel `sKerd δ` is continuous with compact support in `[-δ, δ]`, hence
  measurable, bounded, and vanishing for `|x| > 1` (`δ ≤ 1/2 < 1`);
* the `t`-slice `s ↦ KJ ε θ s · ∂_θG(eᵗ,s)` is a.e. strongly measurable (the angular
  kernel is continuous and `∂_θG` is continuous on the open quadrant) and integrable on
  `Iθ` for every `t` (dominated by the constant `3(ε·sMass)⁻¹ · sup_s|∂_θG(eᵗ,s)|`);
* the slice integrals are dominated by `3(ε·sMass)⁻¹ √(π/2) MGf G (eᵗ)`, where `MGf G` is
  the slice domination of `MollBase`'s companion `mollSliceBound`:
  `|∂_θG(w,s)| ≤ |∂_θG(w,π/4)| + √(π/2)√(E2s G w) ≤ √(π/2) MGf G w` a.e. in `s`
  (`pthSliceLeE2s`);
* `t ↦ MGf G (eᵗ)` is integrable on compact intervals in the logarithmic variable
  (`PkgK5.i0TraceMoll.integrableOn_MGf_exp_of_trace`, from `FourInts`), and the window
  `[log z - 1, log z + 1]` is compact, so the closed-interval form required by the
  product-integrability lemma follows from the open-interval form by nullity of the
  endpoints.
-/

namespace Work.FTS.EllSol.EllPkgAux.MollDom.ZmollMix

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-! ## Elementary pieces -/

/-- The derivative kernel `sKerd δ = (sKer δ)'` is bounded for `δ > 0`: it is continuous and
supported in `[-δ, δ]`. -/
private theorem sKerd_bdd_of_pos {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ t : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd δ t| ≤ M := by
  have hcontOn : ContinuousOn (Work.FTS.EllSol.EllPkgAux.sKerd δ) (Set.Icc (-δ) δ) :=
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd δ).continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontOn
  refine ⟨max M 0, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-δ) δ
  · have h1 : ‖Work.FTS.EllSol.EllPkgAux.sKerd δ t‖ ≤ M := hM t ht
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  · have hgt : δ < |t| := by
      rw [Set.mem_Icc, not_and_or] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hδ hgt, abs_zero]
    exact le_max_right _ _

/-- **The a.e. slice bound for `∂_θG`**: for `w > 0` and almost every `s ∈ Iθ`,
`|∂_θG(w,s)| ≤ √(π/2) MGf G w`. -/
private theorem abs_pth_le_sqrt_MGf {G : ℝ → ℝ → ℝ}
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) {w : ℝ} (hw : 0 < w)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Work.Spaces.pth G w θ| ≤ Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G w := by
  have hp := Work.FTS.EllSol.PkgK5.i0TraceMoll.PsiAux.pthSliceLeE2s G hT w hw θ hθ.1 hθ.2
  have hsp : (1 : ℝ) ≤ Real.sqrt (Real.pi / 2) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hMG : Work.FTS.EllSol.EllPkgAux.MGf G w
      = 1 + |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)|
        + Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G w) := rfl
  have hA : |Work.Spaces.pth G w (Real.pi / 4)|
      ≤ Real.sqrt (Real.pi / 2) * |Work.Spaces.pth G w (Real.pi / 4)| := by
    nlinarith [hsp, abs_nonneg (Work.Spaces.pth G w (Real.pi / 4))]
  rw [hMG] at *
  nlinarith [hp, hA, hsp, abs_nonneg (G w (Real.pi / 4)),
    Real.sqrt_nonneg (Work.FTS.EllSol.EllPkgAux.E2s G w)]

/-- The a.e. slice bound for the full mixed slice `KJ ε θ s · ∂_θG(eᵗ,s)`. -/
private theorem abs_KJ_pth_slice_le {G : ℝ → ℝ → ℝ}
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) {ε θ c : ℝ} (hε0 : 0 < ε)
    (hc : ∀ s : ℝ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s ≤ c) (hc0 : 0 ≤ c) (t : ℝ) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.FTS.EllSol.EllPkgAux.KJ ε θ s * Work.Spaces.pth G (Real.exp t) s|
        ≤ c * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)) := by
  filter_upwards [Work.FTS.EllSol.EllPkgAux.ae_mem_Ioo_Iθ] with s hs
  have hp := abs_pth_le_sqrt_MGf hT (Real.exp_pos t) hs
  have hKJ := hc s
  rw [abs_mul, abs_of_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε0 θ s)]
  exact mul_le_mul hKJ hp (abs_nonneg _) hc0

/-- The domination `t ↦ MGf G (eᵗ)` is integrable on the closed window
`[log z - 1, log z + 1]`. -/
private theorem phi_integrable (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (K : ℝ) {z : ℝ} (_hz : 0 < z) :
    MeasureTheory.Integrable (fun t : ℝ => K * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))
      (MeasureTheory.volume.restrict (Set.Icc (Real.log z - 1) (Real.log z + 1))) := by
  have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))
      (Set.Ioo (Real.log z - 1) (Real.log z + 1)) :=
    Work.FTS.EllSol.PkgK5.i0TraceMoll.integrableOn_MGf_exp_of_trace G hT hF (by linarith)
  have h2 : MeasureTheory.Integrable (fun t : ℝ => K * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))
      (MeasureTheory.volume.restrict (Set.Ioo (Real.log z - 1) (Real.log z + 1))) := h1.const_mul K
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)
      (a := Real.log z - 1) (b := Real.log z + 1))]
  exact h2

/-! ## The target -/

theorem integrable_sKerd_KJ_pth (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - p.1)
        * (Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 * Work.Spaces.pth G (Real.exp p.1) p.2))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  obtain ⟨M, hM⟩ := sKerd_bdd_of_pos hδ0
  -- the constant `3(ε sMass)⁻¹` dominating `KJ`
  have hKJ0 : (0 : ℝ) ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ :=
    mul_nonneg (by norm_num)
      (inv_nonneg.mpr (mul_nonneg hε0.le Work.FTS.EllSol.PkgK5.K5c.sMass_pos.le))
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  refine Work.FTS.EllSol.EllPkgAux.MollDom.prod_integrable_of_slice_bound
    (k := Work.FTS.EllSol.EllPkgAux.sKerd δ)
    (w := fun t s => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * Work.Spaces.pth G (Real.exp t) s)
    (Φ := fun t => (Real.pi / 2) * (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
      * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))))
    (M := M) (σ := Real.log z) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd δ).measurable
  · exact hM
  · intro x hx
    exact Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hδ0 (by linarith)
  · -- a.e. strong measurability of the uncurried integrand
    have hA : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.pth G (Real.exp p.1) p.2)
        (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.FTS.EllSol.EllPkgAux.MollDom.aeStronglyMeasurable_exp
        (X := Work.Spaces.pth G) hsm.pth.continuousOn
    have hB : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2)
        (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      ((Work.FTS.EllSol.EllPkgAux.continuous_KJ ε).comp
        (continuous_const.prodMk continuous_snd)).aestronglyMeasurable
    exact hB.mul hA
  · -- integrability of every `t`-slice
    intro t
    have hle := abs_KJ_pth_slice_le hT hε0
      (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ_le hε0 θ s) hKJ0 t
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
        Work.Spaces.Iθ :=
      (hone.const_mul (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))).congr
        (Filter.Eventually.of_forall (fun s => by simp))
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * Work.Spaces.pth G (Real.exp t) s)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hg : ContinuousOn
          (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 * Work.Spaces.pth G p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (((Work.FTS.EllSol.EllPkgAux.continuous_KJ ε).comp
            (continuous_const.prodMk continuous_snd)).continuousOn).mul hsm.pth.continuousOn
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hg (Real.exp_pos t)
    exact MeasureTheory.Integrable.mono' hconst haesm
      (by filter_upwards [hle] with s hs; simpa only [Real.norm_eq_abs] using hs)
  · -- the domination of the slice integrals
    intro t
    have hle := abs_KJ_pth_slice_le hT hε0
      (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ_le hε0 θ s) hKJ0 t
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
        Work.Spaces.Iθ :=
      (hone.const_mul (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))).congr
        (Filter.Eventually.of_forall (fun s => by simp))
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun s : ℝ => |Work.FTS.EllSol.EllPkgAux.KJ ε θ s * Work.Spaces.pth G (Real.exp t) s|)
      (g := fun _ : ℝ => 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
      (Filter.Eventually.of_forall (fun s => abs_nonneg _)) hconst hle
    have hvol : (∫ s in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
      rw [intervalIntegral.integral_const]
      simp
    have hval : (∫ s in Work.Spaces.Iθ, 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
        = (Real.pi / 2) * (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))) := by
      have h1 : (∫ s in Work.Spaces.Iθ, (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
            * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))) * (1 : ℝ))
          = (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
            * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
            * ∫ s in Work.Spaces.Iθ, (1 : ℝ) :=
        MeasureTheory.integral_const_mul _ _
      have h2 : (∫ s in Work.Spaces.Iθ, 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
            * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
          = (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
            * (Real.sqrt (Real.pi / 2) * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)))
            * ∫ s in Work.Spaces.Iθ, (1 : ℝ) := by
        rw [← h1]
        congr 1
        funext s
        ring
      rw [h2, hvol]
      ring
    rw [hval] at hmono
    exact hmono
  · -- integrability of the domination on the compact window
    exact (phi_integrable G hT hF
        (Real.pi / 2 * (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ * Real.sqrt (Real.pi / 2)))
        hz).congr
      (Filter.Eventually.of_forall (fun t => by ring))

end Work.FTS.EllSol.EllPkgAux.MollDom.ZmollMix
