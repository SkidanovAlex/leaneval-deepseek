import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FKJets
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Horizon

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
