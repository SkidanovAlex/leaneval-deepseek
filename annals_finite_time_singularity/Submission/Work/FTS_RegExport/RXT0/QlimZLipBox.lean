import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_limit_bound
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.RXT0.L12FtauTauLip
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetContinuousOn
import Submission.Work.FTS_RegExport.RXVP3.velPert_unif
import Submission.Work.FTS_RegExport.RXVP3.velVanish2_unif
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.Spaces.pz_DthIter_mul_eq
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.QlimSelf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.QlimSelf` — the fake-time Lipschitz bound of the angular moment `Qlim · 0`

The angular moment `Qlim α g τ 0 z = ∫_θ K(θ)·(F_*(z,θ) + slice g τ z θ) dθ` of the limit
family is Lipschitz in the fake time on every horizon `[0,T]`: the `F_*`-part is `τ`-independent,
and the perturbation is dominated in the limit by the class-`C` approximants, whose `L^∞`-modulus
in `τ` is `app_diff_unif_Icc`.  The bound is uniform in `z > 0` because `K` is integrable.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The fake-time Lipschitz bound of the angular moment `Qlim · 0` of the limit family.** -/
theorem Qlim_zero_tau_lip_self {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T, ∀ z : ℝ, 0 < z →
      |Qlim α g τ 0 z - Qlim α g τ' 0 z| ≤ C * |τ - τ'| := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨gn, B, L, hC, hLip, hjet0, -⟩ := hA (max T 1)
    (lt_of_lt_of_le zero_lt_one (le_max_right T 1))
  have hmemT : ∀ τ ∈ Set.Icc (0 : ℝ) T, τ ∈ Set.Icc (0 : ℝ) (max T 1) :=
    fun τ hτ => ⟨hτ.1, le_trans hτ.2 (le_max_left T 1)⟩
  have hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
    fun n τ hτ => (hC n τ (hmemT τ hτ)).1
  have hXn : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    fun n τ hτ => (hC n τ (hmemT τ hτ)).2.1
  have hXn6 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (slice (gn n) τ) ≤ B :=
    fun n τ hτ => (hC n τ (hmemT τ hτ)).2.2
  have hlip : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
        (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'| :=
    fun n τ hτ τ' hτ' => hLip n τ (hmemT τ hτ) τ' (hmemT τ' hτ')
  obtain ⟨CwA, hCwA0, hbdA⟩ := approx_slot_bound (C₀ := C₀) hα hα13 hT hcl hXn
  obtain ⟨CB, hCBnn, hCB⟩ := ftau_slot_bound (B := B) hα hα13 hcl hXn6
  obtain ⟨K2, hK2nn, hK2b⟩ := app_diff_unif_Icc hβ hβ1 hcl hlip
  have hKc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2) Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rw [Work.Spaces.K]
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  refine ⟨3 * (Real.pi / 2) * K2, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 3 * (Real.pi / 2) := by positivity
    exact mul_nonneg h1 hK2nn
  · intro τ hτ τ' hτ' z hz
    have h4τ : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 := fun n => (hcl n τ hτ).reg.forall 4
    have h4τ' : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ'))
        Work.FTS.EllipticEst.Q0 := fun n => (hcl n τ' hτ').reg.forall 4
    have hbdτ : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ CwA * SW z :=
      fun n k hk z θ hz' h0 h1 => hbdA n τ hτ k hk z θ hz' h0 h1
    have hbdτ' : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter k (slice (gn n) τ') z θ| ≤ CwA * SW z :=
      fun n k hk z θ hz' h0 h1 => hbdA n τ' hτ' k hk z θ hz' h0 h1
    have h2τ : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
        Work.FTS.EllipticEst.Q0 := fun n =>
      (Fstar_contDiffOn hβ hβ1 4).add ((hcl n τ hτ).reg.forall 4)
    have h2τ' : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ'))
        Work.FTS.EllipticEst.Q0 := fun n =>
      (Fstar_contDiffOn hβ hβ1 4).add ((hcl n τ' hτ').reg.forall 4)
    have hslτ : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (gn n) τ) z θ| ≤ CB :=
      fun n k hk z θ hz' h0 h1 => hCB τ hτ n k hk z θ hz' h0 h1
    have hslτ' : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (gn n) τ') z θ| ≤ CB :=
      fun n k hk z θ hz' h0 h1 => hCB τ' hτ' n k hk z θ hz' h0 h1
    have hjetτ : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
          (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)) := by
      intro k hk z θ hzθ
      simpa only [Work.Spaces.mixed_zero_right] using
        hjet0 τ (hmemT τ hτ) k 0 (by omega) z θ hzθ
    have hjetτ' : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ') z θ) Filter.atTop
          (𝓝 (Work.Spaces.DzIter k (slice g τ') z θ)) := by
      intro k hk z θ hzθ
      simpa only [Work.Spaces.mixed_zero_right] using
        hjet0 τ' (hmemT τ' hτ') k 0 (by omega) z θ hzθ
    have hlim := (Qapp_tendsto (α := α) hα hα13 hCwA0 hCBnn h4τ hbdτ h2τ hslτ hjetτ
        (k := 0) (by norm_num) hz).sub
      (Qapp_tendsto (α := α) hα hα13 hCwA0 hCBnn h4τ' hbdτ' h2τ' hslτ' hjetτ'
        (k := 0) (by norm_num) hz)
    refine le_of_tendsto hlim.abs (Filter.Eventually.of_forall fun n => ?_)
    have hint1 : Integrable (fun θ : ℝ => Work.Spaces.K θ
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ z θ)
        (volume.restrict Work.Spaces.Iθ) := by
      refine Integrable.mono' (MeasureTheory.integrable_const (3 * CB)) ?_ ?_
      · refine Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 (g := fun x θ => Work.Spaces.K θ
          * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ x θ) ?_ hz
        show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2
          * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ p.1 p.2)
          Work.FTS.EllipticEst.Q0
        exact hKc.mul (h2τ n).continuousOn
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        rcases eq_or_lt_of_le hθ.1 with h0 | h0
        · subst h0
          have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
          simp only [hK0, zero_mul, norm_zero]
          linarith [hCBnn]
        · rcases eq_or_lt_of_le hθ.2 with h1 | h1
          · subst h1
            have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
              rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
            simp only [hK1, zero_mul, norm_zero]
            linarith [hCBnn]
          · rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul (abs_K_le_three θ) (hslτ n 0 (by norm_num) z θ hz h0 h1)
              (abs_nonneg _) (by norm_num)
    have hint2 : Integrable (fun θ : ℝ => Work.Spaces.K θ
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ' z θ)
        (volume.restrict Work.Spaces.Iθ) := by
      refine Integrable.mono' (MeasureTheory.integrable_const (3 * CB)) ?_ ?_
      · refine Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 (g := fun x θ => Work.Spaces.K θ
          * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ' x θ) ?_ hz
        show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2
          * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ' p.1 p.2)
          Work.FTS.EllipticEst.Q0
        exact hKc.mul (h2τ' n).continuousOn
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        rcases eq_or_lt_of_le hθ.1 with h0 | h0
        · subst h0
          have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
          simp only [hK0, zero_mul, norm_zero]
          linarith [hCBnn]
        · rcases eq_or_lt_of_le hθ.2 with h1 | h1
          · subst h1
            have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
              rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
            simp only [hK1, zero_mul, norm_zero]
            linarith [hCBnn]
          · rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul (abs_K_le_three θ) (hslτ' n 0 (by norm_num) z θ hz h0 h1)
              (abs_nonneg _) (by norm_num)
    have hdiff : Qapp α gn τ n 0 z - Qapp α gn τ' n 0 z
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ
            * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ z θ
          - Work.Spaces.K θ
            * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ' z θ) := by
      show (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter 0
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ)
          - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.DzIter 0
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ') z θ) = _
      rw [Work.Spaces.DzIter_zero, Work.Spaces.DzIter_zero]
      rw [← MeasureTheory.integral_sub hint1 hint2]
    rw [hdiff]
    have hInt : Integrable (fun θ : ℝ => |Work.Spaces.K θ
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ z θ
        - Work.Spaces.K θ
          * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ' z θ|)
        (volume.restrict Work.Spaces.Iθ) := (hint1.sub hint2).abs
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |Work.Spaces.K θ * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ z θ
          - Work.Spaces.K θ
            * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ' z θ|
        ≤ 3 * (K2 * |τ - τ'|) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have hnn : (0 : ℝ) ≤ 3 * (K2 * |τ - τ'|) :=
        mul_nonneg (by norm_num) (mul_nonneg hK2nn (abs_nonneg _))
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · subst h0
        have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
        simp only [hK0, zero_mul, zero_sub, abs_neg, abs_zero]
        exact hnn
      · rcases eq_or_lt_of_le hθ.2 with h1 | h1
        · subst h1
          have hK1 : Work.Spaces.K (Real.pi / 2) = 0 := by
            rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
          simp only [hK1, zero_mul, zero_sub, abs_neg, abs_zero]
          exact hnn
        · have hQd : (z, θ) ∈ Work.Construction.Qd := ⟨hz, h0, h1⟩
          rw [show Work.Spaces.K θ * Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (gn n) τ z θ
              - Work.Spaces.K θ * Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (gn n) τ' z θ
              = Work.Spaces.K θ * (slice (gn n) τ z θ - slice (gn n) τ' z θ) from by
            rw [show Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ
                = Work.Construction.Fstar (Work.FTS.Regularity.pExp α)
                  + slice (gn n) τ from rfl]
            rw [show Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ'
                = Work.Construction.Fstar (Work.FTS.Regularity.pExp α)
                  + slice (gn n) τ' from rfl]
            simp only [Pi.add_apply]
            ring]
          rw [abs_mul]
          exact mul_le_mul (abs_K_le_three θ) (hK2b n τ hτ τ' hτ' z θ hQd)
            (abs_nonneg _) (by norm_num)
    have hkey := MeasureTheory.abs_integral_le_integral_abs (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ : ℝ => Work.Spaces.K θ
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ z θ
        - Work.Spaces.K θ
          * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ' z θ)
    have hstep : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ
          * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ z θ
        - Work.Spaces.K θ
          * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ' z θ|)
        ≤ ∫ _θ in Work.Spaces.Iθ, 3 * (K2 * |τ - τ'|) :=
      MeasureTheory.integral_mono_ae hInt (MeasureTheory.integrable_const _) hpt
    have hconst : (∫ _θ in Work.Spaces.Iθ, 3 * (K2 * |τ - τ'|))
        = 3 * (Real.pi / 2) * (K2 * |τ - τ'|) := by
      rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      ring
    rw [hconst] at hstep
    refine le_trans (le_trans hkey hstep) (le_of_eq ?_)
    ring

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.L12densFtauIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT0

/-- The `L₁₂`-density of the profile `F(τ) = F_* + g(τ)` of the strong route is integrable on the
tail `(z,∞)`, `z > 0`, along the whole fake-time horizon.

`LimApprox` supplies the approximating class-`C` families `gn`; the weighted slot bound
`|D_z^kD_θ^a (slice (gn n) τ)| ≤ C·z^{3/2}/(1+z)²` (from the interior `L^∞`–`ℋ⁴` trade-off
`RXA1w.abs_mixed_le_HkNorm_C4_w_proved` and `Xn (slice (gn n) τ) ≤ C₀·(pExp α)²`) bounds the
integrand of the density pointwise against the elementary majorant
`3(π/2)(20/(1+s)² + C_{w}·s^{1/2}/(1+s)²)`, which is integrable on `(z,∞)`
(`abs_L12dens_Fstar_add_le` + `majorant_Ioi_integrable`).  The only remaining ingredient is the
a.e. strong measurability of the limiting density: each approximant density
`s ↦ L₁₂dens (F_* + slice (gn n) τ)(s) = 2β/(1+s)² + L₁₂dens (slice (gn n) τ)(s)` is continuous
on `(0,∞)` (`L12dens_Fstar_add_le`/`dens_add` + `L12dens_continuousOn`), and it converges
pointwise, for every `s > 0`, to the limiting density (`dens_tendsto`), so the limit is a.e.
strongly measurable (`aestronglyMeasurable_of_tendsto_ae`). -/
theorem L12densFtauIntegrable {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (Work.Construction.L12dens
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi z) := by
  intro S hS τ hτ z hz
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the approximating families of `LimApprox`, and the weighted slot bounds of the limit family
  obtain ⟨gn, B, L, hC, hLip, hjet, hmu⟩ := hA S hS
  obtain ⟨Cw, hCw0, hCw⟩ := Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
    (αG := Work.FTS.Regularity.pExp α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hβ hβ1 hA S hS
  -- §1 the weighted bound for the `GR`-slice
  have hub : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
        ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro z θ hz0 h0 h1
    rw [Work.FTS_RegExport.RXT.ftau_slice_GR_eq hτ.1 hz0 h0.le h1.le]
    have h := hCw τ hτ 0 0 (by norm_num) z θ hz0 h0 h1
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  -- §2 the pointwise bound of the limiting density
  have hpt : ∀ s : ℝ, 0 < s →
      |Work.Construction.L12dens (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) s|
        ≤ 3 * (Real.pi / 2)
            * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
    intro s hs
    have h := Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
      (α := Work.FTS.Regularity.pExp α) hβ hβ1 hCw0
      (u := Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ) hub hs
    have hfun : Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ
        = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
            + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ := rfl
    rw [hfun]
    exact h
  -- §3 the majorant is integrable on the tail
  have hmaj : MeasureTheory.IntegrableOn
      (fun s : ℝ => 3 * (Real.pi / 2)
        * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))) (Set.Ioi z) :=
    (Work.FTS_RegExport.RXT.Sys.majorant_Ioi_integrable hCw0).1.mono_set
      (Set.Ioi_subset_Ioi hz.le)
  -- §4 the standing data of the approximants
  have h4n : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice (gn n) τ))
      Work.FTS.EllipticEst.Q0 := fun n => (hC n τ hτ).1.reg.forall 4
  obtain ⟨Cd, hCd0, hCd⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hβ hβ1
  have hC0β : 0 ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg (Work.FTS.Regularity.pExp α) 4
        (Work.FTS.Galerkin.slice (gn 0) 0)) (hC 0 0 ⟨le_rfl, hS.le⟩).2.1
  have hCwA0 : 0 ≤ Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) := mul_nonneg hCd0 hC0β
  have hbd : ∀ (n k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2))
            * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z := by
    intro n k hk z θ hz' h0 h1
    have hcl := (hC n τ hτ).1
    have h1' := hCd (Work.FTS.Galerkin.slice (gn n) τ) (hcl.reg.forall 4)
      (Work.FTS.ClassC.classC_hkMem_four hcl)
      (Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcl.tr) k 0 (by omega) z θ hz' h0 h1
    rw [Work.Spaces.mixed_zero_right] at h1'
    have h2 : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (Work.FTS.Galerkin.slice (gn n) τ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 := (hC n τ hτ).2.1
    calc |Work.Spaces.DzIter k (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cd * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z
            * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
              (Work.FTS.Galerkin.slice (gn n) τ) := h1'
      _ ≤ Cd * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z
            * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg hCd0 (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW_nonneg hz'.le))
      _ = (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2))
            * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z := by ring
  -- §5 the slices of the approximants converge to those of `GR α g` on the open quadrant
  have hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.FTS.Galerkin.slice (gn n) τ z θ) Filter.atTop
        (nhds (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ)) := by
    intro z θ hzθ
    have h := hjet τ hτ 0 0 (by norm_num) z θ hzθ
    have hGr : Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ
        = Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z θ := by
      rw [Work.FTS_RegExport.RXT.ftau_slice_GR_eq hτ.1 hzθ.1 hzθ.2.1.le hzθ.2.2.le]
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
    rw [hGr]
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  -- §6 the density of every approximant is continuous on `(0,∞)`
  have hcont : ∀ n : ℕ, ContinuousOn (Work.Construction.L12dens (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (gn n) τ)) (Set.Ioi 0) := by
    intro n
    have h1 : ContinuousOn (fun s : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2)
        (Set.Ioi 0) :=
      continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
        (fun s hs => pow_ne_zero 2 (by have hs0 : 0 < s := hs; linarith))
    have h2 := Work.FTS_RegExport.RXT.L12Iter.L12dens_continuousOn hCwA0 (h4n n) (hbd n)
    have h3 : ContinuousOn (fun s : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
        + Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s) (Set.Ioi 0) :=
      h1.add h2
    refine h3.congr (fun s hs => ?_)
    exact Work.FTS_RegExport.RXT.Sys.L12FKaux.L12dens_Ftau_eq hβ hβ1 hCwA0 (h4n n) (hbd n)
      (u := Work.FTS.Galerkin.slice (gn n) τ) hs
  -- §7 a.e. strong measurability of the limiting density
  have haesm_n : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (fun s => Work.Construction.L12dens
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) s)
      (MeasureTheory.volume.restrict (Set.Ioi z)) := fun n =>
    ((hcont n).mono (Set.Ioi_subset_Ioi hz.le)).aestronglyMeasurable measurableSet_Ioi
  have hlim : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)),
      Filter.Tendsto (fun n => Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) s) Filter.atTop
        (nhds (Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs =>
      Work.FTS_RegExport.RXT.Sys.L12FKaux.dens_tendsto
        (gn := gn) (h := Work.FTS.RegExportIface.RXT.GR α g) (τ := τ)
        hβ hβ1 hCwA0 h4n hbd hconv (show (0:ℝ) < s from lt_trans hz hs))
  have haesm : MeasureTheory.AEStronglyMeasurable (fun s => Work.Construction.L12dens
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) s)
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop haesm_n hlim
  -- §8 conclusion
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
  rw [Real.norm_eq_abs]
  exact hpt s (show (0:ℝ) < s from lt_trans hz hs)

end Work.FTS_RegExport.RXT0
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.QlimTauLipW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT0

open Work.FTS_RegExport.RXT.Sys.L12FKaux
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §1 Two elementary inputs of the limit passage -/

/-- `θ ↦ K(θ)` is continuous on the open quadrant. -/
private theorem continuousOn_K_snd :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
    funext p; rw [Work.Spaces.K]
  rw [hfun]
  exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
    ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn

/-- **`θ`-integrability of the angular slices of a profile `F(τ) = F_* + slice (gn n) τ`**,
from an interior `L^∞` bound and open-quadrant smoothness. -/
private theorem integrable_K_DzIter_Ftau {α : ℝ} {gn : ℕ → Fam} {σ CB : ℝ} {n : ℕ}
    (hCB : 0 ≤ CB)
    (hCD : ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (gn n) σ)) Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (j : ℕ), j ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter j (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) σ) z θ| ≤ CB)
    {z : ℝ} (hz : 0 < z) (j : ℕ) (hj : j ≤ 3) :
    Integrable (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.DzIter j
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) σ) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hj4 : j ≤ 4 := le_trans hj (by norm_num)
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) σ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.continuousOn_DzIter_of_contDiffOn (k := 4) (i := j) hCD hj4
  refine Integrable.mono' (integrable_const (3 * CB)) ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.DzIter j
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) σ) p.1 p.2)
      (continuousOn_K_snd.mul hD) hz
  · rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hb := hsl j hj z θ hz hθ.1 hθ.2
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three θ) hb (abs_nonneg _) (by norm_num)

/-- **The weighted `τ`-increment of a single `D_z^k`-slot of the approximants.**  The
`F_*`-part cancels (`FtauSlot.DzIter_Fstar_add`), leaving the `k`-th radial slot of the
difference of the two slices, which the standing weighted modulus controls. -/
private theorem diff_DzIter_Ftau_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {τ τ' CwD : ℝ} {n : ℕ}
    (h4τ : ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ)) Work.FTS.EllipticEst.Q0)
    (h4τ' : ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ')) Work.FTS.EllipticEst.Q0)
    (hCwD : ∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (slice (gn n) τ') z θ| ≤ CwD * SW z * |τ - τ'|)
    {k : ℕ} (hk : k ≤ 2) {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ
      - Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (gn n) τ') z θ| ≤ CwD * SW z * |τ - τ'| := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hsplitτ : Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ
      = Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice (gn n) τ) z θ := by
    rw [show Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ
        = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + slice (gn n) τ z θ from rfl]
    exact DzIter_Fstar_add hβ hβ1 h4τ hk z θ hz h0 h1
  have hsplitτ' : Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ') z θ
      = Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice (gn n) τ') z θ := by
    rw [show Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ'
        = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + slice (gn n) τ' z θ from rfl]
    exact DzIter_Fstar_add hβ hβ1 h4τ' hk z θ hz h0 h1
  rw [hsplitτ, hsplitτ']
  have hrd : (Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice (gn n) τ) z θ)
      - (Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice (gn n) τ') z θ)
      = Work.Spaces.DzIter k (slice (gn n) τ) z θ
        - Work.Spaces.DzIter k (slice (gn n) τ') z θ := by ring
  rw [hrd]
  have h := hCwD k 0 (by omega) z θ hz h0 h1
  simpa only [Work.Spaces.mixed_zero_right] using h

/-! ## §2 The target -/

theorem QlimTauLipW {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≤ 2 →
      ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
        |Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k z
          - Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ' k z|
          ≤ C * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z * |τ - τ'| := by
  intro S hS
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨gn, B, L, hC, hLip, hjet0, -⟩ := hA S hS
  -- the standing weighted slot bounds of the approximants
  obtain ⟨Cw, hCw0, hCw⟩ := approx_slot_bound (α := α) (C₀ := C₀) (T := S) hα hα13 hS
    (fun n τ hτ => (hC n τ hτ).1) (fun n τ hτ => (hC n τ hτ).2.1)
  -- the order-`3` slot bounds of the profiles `F(τ) = F_* + slice (gn n) τ`
  obtain ⟨CB, hCB0, hCB⟩ := ftau_slot_bound (α := α) (B := B) (T := S) hα hα13
    (fun n τ hτ => (hC n τ hτ).1) (fun n τ hτ => (hC n τ hτ).2.2)
  -- the weighted `τ`-modulus of the approximants
  obtain ⟨CwD, hCwD0, hCwD⟩ := app_diff_w (α := Work.FTS.Regularity.pExp α) (T := S) (L := L)
    hβ hβ1 (fun n τ hτ => (hC n τ hτ).1)
    (fun n τ hτ τ' hτ' => hLip n τ hτ τ' hτ')
  refine ⟨3 * (Real.pi / 2) * CwD, mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hCwD0,
    ?_⟩
  intro k hk τ hτ τ' hτ' z hz
  -- the standing inputs on the horizon
  have h4s : ∀ (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) S → ∀ n : ℕ, ContDiffOn ℝ 4
      (Function.uncurry (slice (gn n) σ)) Work.FTS.EllipticEst.Q0 :=
    fun σ hσ n => (hC n σ hσ).1.reg.forall 4
  have h2s : ∀ (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) S → ∀ n : ℕ, ContDiffOn ℝ 4
      (Function.uncurry (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) σ))
      Work.FTS.EllipticEst.Q0 :=
    fun σ hσ n => (Fstar_contDiffOn hβ hβ1 4).add ((hC n σ hσ).1.reg.forall 4)
  have hbds : ∀ (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) S → ∀ (n j : ℕ), j ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter j (slice (gn n) σ) z θ| ≤ Cw * SW z :=
    fun σ hσ n j hj z' θ hz' h0 h1 => hCw n σ hσ j hj z' θ hz' h0 h1
  have hsls : ∀ (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) S → ∀ (n j : ℕ), j ≤ 3 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter j (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) σ) z θ| ≤ CB :=
    fun σ hσ n j hj z' θ hz' h0 h1 => hCB σ hσ n j hj z' θ hz' h0 h1
  have hjets : ∀ (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) S → ∀ (j : ℕ), j ≤ 2 →
      ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter j (slice (gn n) σ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter j (slice g σ) z θ)) := by
    intro σ hσ j hj z' θ hQd
    simpa only [Work.Spaces.mixed_zero_right] using hjet0 σ hσ j 0 (by omega) z' θ hQd
  -- the moments of the approximants converge to the moments of the limit
  have hlimτ : Filter.Tendsto (fun n => Qapp α gn τ n k z) Filter.atTop
      (𝓝 (Qlim α g τ k z)) :=
    Qapp_tendsto (α := α) hα hα13 hCw0 hCB0 (h4s τ hτ) (hbds τ hτ) (h2s τ hτ)
      (hsls τ hτ) (hjets τ hτ) hk hz
  have hlimτ' : Filter.Tendsto (fun n => Qapp α gn τ' n k z) Filter.atTop
      (𝓝 (Qlim α g τ' k z)) :=
    Qapp_tendsto (α := α) hα hα13 hCw0 hCB0 (h4s τ' hτ') (hbds τ' hτ') (h2s τ' hτ')
      (hsls τ' hτ') (hjets τ' hτ') hk hz
  -- the per-`n` bound on the increment of the moments
  have hper : ∀ n : ℕ, |Qapp α gn τ n k z - Qapp α gn τ' n k z|
      ≤ 3 * (Real.pi / 2) * (CwD * SW z * |τ - τ'|) := by
    intro n
    have hint := integrable_K_DzIter_Ftau (α := α) (gn := gn) (σ := τ) (CB := CB) (n := n)
      hCB0 (h2s τ hτ n) (fun j hj z' θ hz' h0 h1 => hsls τ hτ n j hj z' θ hz' h0 h1)
      hz k (by omega)
    have hint' := integrable_K_DzIter_Ftau (α := α) (gn := gn) (σ := τ') (CB := CB) (n := n)
      hCB0 (h2s τ' hτ' n) (fun j hj z' θ hz' h0 h1 => hsls τ' hτ' n j hj z' θ hz' h0 h1)
      hz k (by omega)
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (gn n) τ) z θ
          - Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (gn n) τ') z θ| ≤ CwD * SW z * |τ - τ'| := by
      rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact diff_DzIter_Ftau_le (α := α) (gn := gn) (τ := τ) (τ' := τ') (CwD := CwD) (n := n)
        hα hα13 ((hC n τ hτ).1.reg.forall 4) ((hC n τ' hτ').1.reg.forall 4)
        (fun b a hab z' θ hz' h0 h1 => hCwD n τ hτ τ' hτ' b a hab z' θ hz' h0 h1)
        hk hz hθ.1 hθ.2
    exact KweightIntegralSub (F := fun θ => Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ)
      (F' := fun θ => Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ') z θ)
      (C := CwD * SW z * |τ - τ'|)
      (mul_nonneg (mul_nonneg hCwD0 (SW_nonneg hz.le)) (abs_nonneg _)) hint hint' hae
  -- pass to the limit `n → ∞`
  have htend : Filter.Tendsto (fun n => |Qapp α gn τ n k z - Qapp α gn τ' n k z|) Filter.atTop
      (𝓝 |Qlim α g τ k z - Qlim α g τ' k z|) := (hlimτ.sub hlimτ').abs
  refine le_of_tendsto htend (Filter.Eventually.of_forall fun n => ?_)
  have h := hper n
  have hgoal : 3 * (Real.pi / 2) * (CwD * SW z * |τ - τ'|)
      = 3 * (Real.pi / 2) * CwD * SW z * |τ - τ'| := by ring
  rw [hgoal] at h
  exact h

end Work.FTS_RegExport.RXT0
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.QlimZLipBox =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RXT0.QlimZLipBox` — the `z`-Lipschitz bound of the angular moments `Qlim` on a box `[a,b]`

The angular moments of the limit profile, `Qlim α g τ k`, are the `z`-jets of the `L₁₂`-profile:
`Qlim · (k+1) z / z` is the `z`-derivative of `Qlim · k` (`FKDeriv.Qlim_hasDerivAt_1/2`).  Hence
each `Qlim · k` (`k ≤ 2`) is Lipschitz on every box `[a,b]` with `0 < a`, uniformly in `τ ∈ [0,S]`:

    |Qlim α g τ k z - Qlim α g τ k z'| ≤ C · |z - z'|.

The proof is by the uniform-in-`n` mean value theorem on the approximants `Qapp α gn τ n k` — whose
`z`-derivative is `Qapp · (k+1) x / x`, bounded by `3(π/2)C_B / a` uniformly, since the slot
bound `Ftau_slot_le3` (uniform on the horizon, `Horizon.ftau_slot_bound`) controls the moments up
to order `3` — and then passing to the limit `n → ∞` with `FKJets.Qapp_tendsto`.

`sorry`-free; rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT0

open Work.FTS.Galerkin (Fn Fam slice)

set_option maxHeartbeats 800000

theorem QlimZLipBox {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ a b : ℝ, 0 < a → a ≤ b → ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≤ 2 →
      ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z ∈ Set.Icc a b, ∀ z' ∈ Set.Icc a b,
        |Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k z
          - Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k z'| ≤ C * |z - z'| := by
  intro S hS a b ha hab
  obtain ⟨gn, B, L, hC, hLip, hjet0, -⟩ := hA S hS
  -- the two uniform slot bounds on the horizon `[0,S]`
  obtain ⟨Cw, hCw0, hblock⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FKaux.approx_slot_bound (α := α) (C₀ := C₀) hα hα13
      (T := S) hS (fun n τ hτ => (hC n τ hτ).1) (fun n τ hτ => (hC n τ hτ).2.1)
  obtain ⟨CB, hCB0, hsl⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FKaux.ftau_slot_bound (α := α) (B := B) hα hα13
      (fun n τ hτ => (hC n τ hτ).1) (fun n τ hτ => (hC n τ hτ).2.2)
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the profiles are `C⁴` on the open quadrant
  have hCD : ∀ (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) S → ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0 := by
    intro τ hτ n
    have hstar := Work.FTS_RegExport.RXT.Sys.L12FKaux.Fstar_contDiffOn hβ hβ1 4
    have hsl' : ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 := (hC n τ hτ).1.reg.forall 4
    have heq : Function.uncurry (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (gn n) τ)
        = fun x : ℝ × ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) x.1 x.2
          + slice (gn n) τ x.1 x.2 := by
      funext x
      rfl
    rw [heq]
    exact hstar.add hsl'
  -- pointwise jet convergence of the approximants
  have hjet : ∀ (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) S → ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)) := by
    intro τ hτ k hk z θ hQd
    simpa only [Work.Spaces.mixed_zero_right] using hjet0 τ hτ k 0 (by omega) z θ hQd
  have hCBnn : 0 ≤ 3 * (Real.pi / 2) * CB := by positivity
  refine ⟨3 * (Real.pi / 2) * CB / a, div_nonneg hCBnn ha.le, ?_⟩
  intro k hk τ hτ z hz z' hz'
  have hza : 0 < z := lt_of_lt_of_le ha hz.1
  have hza' : 0 < z' := lt_of_lt_of_le ha hz'.1
  -- the approximant moments converge to the limit moment, at both points
  have hlimz : Filter.Tendsto (fun n => Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n k z)
      Filter.atTop (𝓝 (Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k z)) :=
    Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp_tendsto (α := α) hα hα13 hCw0 hCB0
      (fun n => (hC n τ hτ).1.reg.forall 4)
      (fun n k' hk' y θ hy h0 h1 => hblock n τ hτ k' hk' y θ hy h0 h1)
      (hCD τ hτ)
      (fun n k' hk' y θ hy h0 h1 => hsl τ hτ n k' hk' y θ hy h0 h1)
      (hjet τ hτ) hk hza
  have hlimz' : Filter.Tendsto (fun n => Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n k z')
      Filter.atTop (𝓝 (Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k z')) :=
    Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp_tendsto (α := α) hα hα13 hCw0 hCB0
      (fun n => (hC n τ hτ).1.reg.forall 4)
      (fun n k' hk' y θ hy h0 h1 => hblock n τ hτ k' hk' y θ hy h0 h1)
      (hCD τ hτ)
      (fun n k' hk' y θ hy h0 h1 => hsl τ hτ n k' hk' y θ hy h0 h1)
      (hjet τ hτ) hk hza'
  refine le_of_tendsto ((hlimz.sub hlimz').abs) (Filter.Eventually.of_forall fun n => ?_)
  -- the uniform-in-`n` mean value theorem on `[a,b]`
  have hder : ∀ x ∈ Set.Icc a b, HasDerivAt (Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n k)
      (Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n (k + 1) x / x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    exact Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp_hasDerivAt (α := α) hα hα13 hCB0
      (hCD τ hτ)
      (fun m k' hk' y θ hy h0 h1 => hsl τ hτ m k' hk' y θ hy h0 h1) n hk hx0
  have hbnd : ∀ x ∈ Set.Icc a b,
      ‖deriv (Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n k) x‖
        ≤ 3 * (Real.pi / 2) * CB / a := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hdx := hder x hx
    rw [hdx.deriv, Real.norm_eq_abs, abs_div, abs_of_pos hx0]
    refine div_le_div₀ hCBnn ?_ ha hx.1
    exact Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp_bound (α := α) hα hα13 hCB0
      (hCD τ hτ)
      (fun m k' hk' y θ hy h0 h1 => hsl τ hτ m k' hk' y θ hy h0 h1) n (by omega) hx0
  have hMV := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Work.FTS_RegExport.RXT.Sys.L12FKaux.Qapp α gn τ n k) (s := Set.Icc a b)
    (x := z') (y := z) (C := 3 * (Real.pi / 2) * CB / a)
    (fun x hx => (hder x hx).differentiableAt) hbnd (convex_Icc a b) hz' hz
  simpa using hMV

end Work.FTS_RegExport.RXT0
end
end
