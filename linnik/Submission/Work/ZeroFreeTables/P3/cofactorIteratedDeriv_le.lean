import Mathlib
import Submission.Work.ZeroFreeTables.P3.Imports

open scoped Classical

namespace Work.ZeroFreeTables.P3

/-!
# Cauchy/Borel–Carathéodory bound for the iterated derivatives of `logDeriv g`

If `g` is analytic and non-vanishing on the disc `B(0,T)` with `log ‖g‖ ≤ M0` there and
`|log ‖g 0‖| ≤ M0`, then the `k`-th derivative of the logarithmic derivative `g'/g` at a
point `s` with `8 ‖s‖ ≤ T` is bounded by `k! · 192 · 16^k · max M0 1 / T^{k+1}`.

The proof routes through a holomorphic logarithm: `g` admits an analytic primitive `F` of
`logDeriv g` with `(F w).re = log ‖g w‖` (`pf_logPrimitiveOnBall`).  Then `F - F 0`
vanishes at the origin and has `(F w - F 0).re ≤ 2 max M0 1`, so Borel–Carathéodory gives
`‖F w - F 0‖ ≤ 4 max M0 1` on the disc of radius `T/2`; Cauchy's estimate on the disc of
radius `T/4` around `s` (which lies inside it) then bounds `F^{(k+1)}(s)`.
-/

/-- Elementary arithmetic used at the end: for every `k`,
`(k+1)! · 4^{k+2} ≤ k! · 192 · 16^k`. -/
private lemma factorial_pow_arith (k : ℕ) :
    ((k+1).factorial : ℝ) * 4 ^ (k+2) ≤ (k.factorial : ℝ) * 192 * 16 ^ k := by
  have hkf : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hfac : ((k+1).factorial : ℝ) = ((k:ℝ)+1) * (k.factorial:ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hpow4 : (4:ℝ)^(k+2) = 16 * 4^k := by rw [pow_add]; ring
  have h4sq : (4:ℝ)^k * 4^k = 4^(2*k) := by rw [← pow_add, two_mul]
  have hpow16 : (16:ℝ)^k = 4^(2*k) := by rw [show (16:ℝ) = 4^2 by norm_num, pow_mul]
  have hkk : k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
  have h1 : ((k:ℝ) + 1) ≤ (2:ℝ)^k := by exact_mod_cast hkk
  have h2 : (2:ℝ)^k ≤ 12 * 4^k := by
    have hle : (2:ℝ)^k ≤ (4:ℝ)^k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
    have h4 : (0:ℝ) ≤ (4:ℝ)^k := by positivity
    nlinarith
  have hkey : (k:ℝ) + 1 ≤ 12 * 4^k := le_trans h1 h2
  have hstep : 16 * ((k:ℝ)+1) * 4^k ≤ 16 * (12 * 4^k) * 4^k := by
    calc 16 * ((k:ℝ)+1) * 4^k = ((k:ℝ)+1) * (16*4^k) := by ring
      _ ≤ (12*4^k) * (16*4^k) := by
          exact mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = 16 * (12 * 4^k) * 4^k := by ring
  calc ((k+1).factorial : ℝ) * 4^(k+2)
      = ((k:ℝ)+1) * (k.factorial:ℝ) * (16 * 4^k) := by rw [hfac, hpow4]
    _ = (k.factorial : ℝ) * (16 * ((k:ℝ)+1) * 4^k) := by ring
    _ ≤ (k.factorial : ℝ) * (16 * (12 * 4^k) * 4^k) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt hkf)
    _ = (k.factorial : ℝ) * 192 * (4^k * 4^k) := by ring
    _ = (k.factorial : ℝ) * 192 * 4^(2*k) := by rw [h4sq]
    _ = (k.factorial : ℝ) * 192 * 16^k := by rw [hpow16]

theorem cofactorIteratedDeriv_le {g : ℂ → ℂ} {T M0 : ℝ} (hT : 0 < T) (k : ℕ) (hk : 1 ≤ k)
    (hg_an : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) T))
    (hg_nz : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) T → g w ≠ 0)
    (hM0 : 0 ≤ M0) (hball : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) T → Real.log ‖g w‖ ≤ M0)
    (horigin : |Real.log ‖g 0‖| ≤ M0)
    {s : ℂ} (hsT : 8 * ‖s‖ ≤ T) :
    ‖iteratedDeriv k (logDeriv g) s‖ ≤ (k.factorial : ℝ) * 192 * 16 ^ k * max M0 1 / T ^ (k + 1) := by
  classical
  obtain ⟨F, hFdiff, hFh, hF0re, hFre⟩ :=
    Commons.NumberTheory.Linnik.pf_logPrimitiveOnBall (g := g) (R := T) hT hg_an hg_nz
  let G : ℂ → ℂ := fun w => F w - F 0
  let M : ℝ := 2 * max M0 1
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hMge : 2 * M0 ≤ M := by
    dsimp [M]
    have h1 : M0 ≤ max M0 1 := le_max_left M0 1
    nlinarith
  have hFreM : Set.MapsTo G (Metric.ball (0:ℂ) T) {z : ℂ | z.re ≤ M} := by
    intro w hw
    have hle1 : (F w).re ≤ M0 := by rw [hFre w hw]; exact hball w hw
    have hle2 : -M0 ≤ (F 0).re := by
      rw [hF0re]; exact (abs_le.mp horigin).1
    have hmain : (F w).re - (F 0).re ≤ 2 * M0 := by linarith
    have hz : (G w).re = (F w).re - (F 0).re := by simp [G]
    change (G w).re ≤ M
    rw [hz]
    exact le_trans hmain hMge
  have hG0 : G 0 = 0 := by simp [G]
  have hGdiff : DifferentiableOn ℂ G (Metric.ball (0:ℂ) T) := by
    intro w hw
    exact (DifferentiableAt.sub (hFdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hw))
      (differentiableAt_const (F 0))).differentiableWithinAt
  have hsup : ∀ w : ℂ, ‖w‖ ≤ T/2 → ‖G w‖ ≤ 2 * M := by
    intro w hw
    have hwb : w ∈ Metric.ball (0:ℂ) T := by
      rw [mem_ball_zero_iff]; nlinarith [hT]
    have hbc := Complex.borelCaratheodory_zero (M := M) (f := G) (R := T) hMpos hGdiff hFreM hT hwb hG0
    have hden : 0 < T - ‖w‖ := by rw [mem_ball_zero_iff] at hwb; linarith
    have hfrac : ‖w‖ / (T - ‖w‖) ≤ 1 := by
      rw [div_le_one hden]; nlinarith [hT]
    calc ‖G w‖ ≤ 2 * M * ‖w‖ / (T - ‖w‖) := hbc
      _ = 2 * M * (‖w‖ / (T - ‖w‖)) := by ring
      _ ≤ 2 * M * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 2 * M := by ring
  -- Cauchy's estimate on the disc of radius `T/4` around `s`
  have hρ : 0 < T / 4 := by positivity
  have hs8 : ‖s‖ ≤ T / 8 := by linarith
  have hsball : s ∈ Metric.ball (0:ℂ) T := by
    rw [mem_ball_zero_iff]; nlinarith [hT]
  have hclosed : Metric.closedBall s (T/4) ⊆ Metric.ball (0:ℂ) T := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [mem_ball_zero_iff]
    have htri : ‖x‖ ≤ ‖s‖ + ‖x - s‖ := by
      have h2 : ‖x‖ = ‖s + (x - s)‖ := by rw [← add_sub_cancel s x]; ring_nf
      rw [h2]; exact norm_add_le s (x - s)
    nlinarith [htri, hx, hs8, hT]
  have hGclosed : DifferentiableOn ℂ G (Metric.closedBall s (T/4)) := by
    intro x hx
    have hxT : x ∈ Metric.ball (0:ℂ) T := hclosed hx
    exact (DifferentiableAt.sub (hFdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hxT))
      (differentiableAt_const (F 0))).differentiableWithinAt
  have hdiffCl : DiffContOnCl ℂ G (Metric.ball s (T/4)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rwa [closure_ball s (ne_of_gt hρ)]
  have hC : ∀ w : ℂ, w ∈ Metric.sphere s (T/4) → ‖G w‖ ≤ 2 * M := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have htri : ‖w‖ ≤ ‖s‖ + ‖w - s‖ := by
      have h2 : ‖w‖ = ‖s + (w - s)‖ := by rw [← add_sub_cancel s w]; ring_nf
      rw [h2]; exact norm_add_le s (w - s)
    exact hsup w (by nlinarith [htri, hw, hs8, hT])
  have hCau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (F := ℂ)
      (f := G) (c := s) (R := T/4) (C := 2 * M) (k+1) hρ hdiffCl hC
  -- convert `iteratedDeriv k (logDeriv g) s` into `iteratedDeriv (k+1) G s`
  have hEvF : logDeriv g =ᶠ[nhds s] deriv F := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Metric.ball (0:ℂ) T, Metric.isOpen_ball.mem_nhds hsball, ?_⟩
    intro w hw
    rw [logDeriv_apply]
    exact (hFh w hw).deriv.symm
  have hEvG : deriv G =ᶠ[nhds s] deriv F := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Metric.ball (0:ℂ) T, Metric.isOpen_ball.mem_nhds hsball, ?_⟩
    intro w hw
    have hdw : DifferentiableAt ℂ F w := hFdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hw)
    have hGdw : HasDerivAt G (deriv F w) w := by
      have := (hdw.hasDerivAt).sub_const (F 0)
      simpa [G] using this
    exact hGdw.deriv
  have hkey : iteratedDeriv k (logDeriv g) s = iteratedDeriv (k+1) G s := by
    have h1 : iteratedDeriv k (logDeriv g) s = iteratedDeriv k (deriv F) s :=
      Filter.EventuallyEq.iteratedDeriv_eq k hEvF
    have h2 : iteratedDeriv (k+1) F s = iteratedDeriv k (deriv F) s := by
      rw [iteratedDeriv_succ']
    have h3 : iteratedDeriv (k+1) F s = iteratedDeriv (k+1) G s := by
      rw [iteratedDeriv_succ' (n := k) (f := F), iteratedDeriv_succ' (n := k) (f := G)]
      exact (Filter.EventuallyEq.iteratedDeriv_eq k hEvG).symm
    rw [h1, ← h2, h3]
  rw [hkey]
  -- arithmetic
  have hsimp : ((k+1).factorial : ℝ) * (2 * M) / (T/4)^(k+1)
      = ((k+1).factorial : ℝ) * 4 ^ (k+2) * max M0 1 / T ^ (k+1) := by
    have h4 : (4:ℝ)^(k+2) = 4 * 4^(k+1) := by
      rw [show k+2 = k+1+1 by omega, pow_succ']
    have hM : M = 2 * max M0 1 := rfl
    rw [hM, div_pow, h4]
    field_simp
    ring
  have harith : ((k+1).factorial : ℝ) * 4 ^ (k+2) * max M0 1 / T ^ (k+1)
      ≤ (k.factorial : ℝ) * 192 * 16 ^ k * max M0 1 / T ^ (k+1) := by
    have hmax : 0 ≤ max M0 1 := le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right M0 1)
    have hprod : ((k+1).factorial : ℝ) * 4 ^ (k+2) * max M0 1
        ≤ (k.factorial : ℝ) * 192 * 16 ^ k * max M0 1 :=
      mul_le_mul_of_nonneg_right (factorial_pow_arith k) hmax
    exact div_le_div_of_nonneg_right hprod (le_of_lt (pow_pos hT _))
  calc ‖iteratedDeriv (k+1) G s‖
      ≤ ((k+1).factorial : ℝ) * (2 * M) / (T/4)^(k+1) := hCau
    _ = ((k+1).factorial : ℝ) * 4 ^ (k+2) * max M0 1 / T ^ (k+1) := hsimp
    _ ≤ (k.factorial : ℝ) * 192 * 16 ^ k * max M0 1 / T ^ (k+1) := harith
  -- (`hk`, `hM0` are part of the interface; the argument above does not need them)

end Work.ZeroFreeTables.P3
