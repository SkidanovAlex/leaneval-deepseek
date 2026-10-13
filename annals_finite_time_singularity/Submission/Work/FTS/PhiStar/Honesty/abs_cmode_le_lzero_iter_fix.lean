import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Honesty.abs_cmode_le_lzero
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

theorem abs_cmode_le_lzero_iter_fix {G : ℝ → ℝ} {m N : ℕ} (hm : 1 ≤ m)
    (hC2 : ∀ k : ℕ, k ≤ N → ContDiffOn ℝ 2 (Work.FTS.EllipticEst.Lzero1^[k] G)
      (Set.Icc 0 (Real.pi / 2)))
    (h0 : ∀ k : ℕ, k < N → (Work.FTS.EllipticEst.Lzero1^[k] G) 0 = 0)
    (h1 : ∀ k : ℕ, k < N → (Work.FTS.EllipticEst.Lzero1^[k] G) (Real.pi / 2) = 0) :
    |(∫ θ in (0 : ℝ)..(Real.pi / 2),
        G θ * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ))|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
            ((Work.FTS.EllipticEst.Lzero1^[N] G) θ) ^ 2 * Real.cos θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
          / (Work.FTS.PhiStar.Gegenbauer.lam m) ^ N := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  let L : (ℝ → ℝ) → (ℝ → ℝ) := Work.FTS.EllipticEst.Lzero1
  let e : ℝ → ℝ := Work.FTS.PhiStar.Gegenbauer.eFam m
  let lam : ℝ := Work.FTS.PhiStar.Gegenbauer.lam m
  let Q : ℝ := ∫ θ in Work.Spaces.Iθ, ((L^[N] G) θ) ^ 2 * Real.cos θ
  let D : ℝ := ∫ θ in Work.Spaces.Iθ, (e θ) ^ 2 * Real.cos θ
  have hlam : 0 < lam := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    dsimp only [lam, Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith
  have hC2' : ∀ k : ℕ, k ≤ N → ContDiffOn ℝ 2 (L^[k] G) (Set.Icc 0 (Real.pi / 2)) := hC2
  have h0' : ∀ k : ℕ, k < N → (L^[k] G) 0 = 0 := h0
  have h1' : ∀ k : ℕ, k < N → (L^[k] G) (Real.pi / 2) = 0 := h1
  let A : ℕ → ℝ := fun k => ∫ θ in Work.Spaces.Iθ, (L^[k] G) θ * e θ * Real.cos θ
  -- the pairing identity relates consecutive levels
  have hstep : ∀ k : ℕ, k < N → A (k+1) = lam * A k := by
    intro k hk
    have hCk : ContDiffOn ℝ 2 (L^[k] G) (Set.Icc 0 (Real.pi / 2)) := hC2' k (le_of_lt hk)
    have hbdd := lzero1_bdd_on_Ioo hCk (h0' k hk) (h1' k hk)
    have hp := lzero1_pair_eFam_c2 (L^[k] G) m hCk (h0' k hk) (h1' k hk) hbdd
    dsimp only [A]
    rw [show L^[k+1] G = L (L^[k] G) from Function.iterate_succ_apply' L k G]
    exact hp
  -- hence `A 0 * lam^N = A N`
  have hmain : ∀ j : ℕ, j ≤ N → A (N - j) * lam^j = A N := by
    intro j
    induction j with
    | zero => intro _; rw [Nat.sub_zero, pow_zero, mul_one]
    | succ j ih =>
        intro hj
        have hkN : N - (j+1) < N := by omega
        have hstepk := hstep (N - (j+1)) hkN
        have heq : N - (j+1) + 1 = N - j := by omega
        have ihj : A (N - j) * lam^j = A N := ih (by omega)
        calc A (N - (j+1)) * lam^(j+1)
            = A (N - (j+1)) * lam * lam^j := by rw [pow_succ']; ring
          _ = (lam * A (N - (j+1))) * lam^j := by ring
          _ = A (N - (j+1) + 1) * lam^j := by rw [← hstepk]
          _ = A (N - j) * lam^j := by rw [heq]
          _ = A N := ihj
  have hA0 : A 0 = A N / lam^N := by
    rw [eq_div_iff (pow_ne_zero N (ne_of_gt hlam))]
    have h := hmain N le_rfl
    rwa [Nat.sub_self] at h
  -- integrability at the top level
  have he_cont : Continuous e := by
    change Continuous (fun θ : ℝ => Real.cos θ
      * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
    exact Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
        Real.continuous_sin)
  have hQ_int : IntegrableOn (fun θ : ℝ => ((L^[N] G) θ) ^ 2 * Real.cos θ)
      Work.Spaces.Iθ volume :=
    ContinuousOn.integrableOn_compact (μ := volume) isCompact_Icc
      ((hC2' N le_rfl).continuousOn.pow 2 |>.mul Real.continuous_cos.continuousOn)
  have hD_int : IntegrableOn (fun θ : ℝ => (e θ) ^ 2 * Real.cos θ)
      Work.Spaces.Iθ volume :=
    ContinuousOn.integrableOn_compact (μ := volume) isCompact_Icc
      (he_cont.continuousOn.pow 2 |>.mul Real.continuous_cos.continuousOn)
  have hP_int : IntegrableOn (fun θ : ℝ => (L^[N] G) θ * e θ * Real.cos θ)
      Work.Spaces.Iθ volume :=
    ContinuousOn.integrableOn_compact (μ := volume) isCompact_Icc
      ((hC2' N le_rfl).continuousOn.mul he_cont.continuousOn |>.mul
        Real.continuous_cos.continuousOn)
  have hcs : (A N) ^ 2 ≤ Q * D := sq_integral_mul_cos_le (L^[N] G) e hQ_int hD_int hP_int
  have hQnn : 0 ≤ Q := by
    dsimp only [Q]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hAN_le : |A N| ≤ Real.sqrt Q * Real.sqrt D := by
    have h2 : Real.sqrt ((A N) ^ 2) ≤ Real.sqrt (Q * D) := Real.sqrt_le_sqrt hcs
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul hQnn] at h2
    exact h2
  -- the left-hand side is `A 0`
  have hLHS : (∫ θ in (0 : ℝ)..(Real.pi / 2), G θ * (e θ * Real.cos θ)) = A 0 := by
    have hcongr : (∫ θ in (0 : ℝ)..(Real.pi / 2), G θ * (e θ * Real.cos θ))
        = ∫ θ in (0 : ℝ)..(Real.pi / 2), G θ * e θ * Real.cos θ :=
      intervalIntegral.integral_congr (fun θ _ => by ring)
    have htoSet : (∫ θ in Work.Spaces.Iθ, G θ * e θ * Real.cos θ)
        = ∫ θ in (0 : ℝ)..(Real.pi / 2), G θ * e θ * Real.cos θ := by
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hpi]
    have hA0' : A 0 = ∫ θ in Work.Spaces.Iθ, G θ * e θ * Real.cos θ := by
      dsimp only [A]
      simp only [Function.iterate_zero_apply]
    rw [hcongr, ← htoSet, ← hA0']
  calc |(∫ θ in (0 : ℝ)..(Real.pi / 2), G θ * (e θ * Real.cos θ))|
      = |A 0| := by rw [hLHS]
    _ = |A N| / lam^N := by rw [hA0, abs_div, abs_of_pos (pow_pos hlam N)]
    _ ≤ Real.sqrt Q * Real.sqrt D / lam^N :=
        div_le_div_of_nonneg_right hAN_le (pow_nonneg hlam.le N)

end Work.FTS.PhiStar.Honesty
