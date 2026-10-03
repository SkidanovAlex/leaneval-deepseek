import Mathlib
import Submission.Work.Motion.Basic
import Submission.Work.Motion.Coding

namespace Work.Motion

open Metric Set Filter
open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary

/-- **Backward quadratic orbit bound.**  If the `t+d`-th iterate of `y` under `Tc c` lies in the
closed ball of radius `W ≥ 0`, then every intermediate iterate `(Tc c)^[t'], t ≤ t' ≤ t+d`,
satisfies `‖(Tc c)^[t'] y‖ ≤ W + ‖c‖ + 1`.

This is the elementary fact behind boundedness of "limit set" orbits: a point whose forward image
at some time is bounded has a bounded orbit *up to* that time, because
`‖z‖² = ‖Tc c z - c‖ ≤ ‖Tc c z‖ + ‖c‖`. -/
lemma tc_iter_bound {c y : ℂ} {W : ℝ} (hW : 0 ≤ W) :
    ∀ d t : ℕ, ‖(Tc c)^[t + d] y‖ ≤ W → ‖(Tc c)^[t] y‖ ≤ W + ‖c‖ + 1 := by
  intro d
  induction d with
  | zero => intro t h; rw [Nat.add_zero] at h; linarith [h, norm_nonneg c]
  | succ d ih =>
    intro t h
    have h' : ‖(Tc c)^[(t + 1) + d] y‖ ≤ W := by
      rw [show (t + 1) + d = t + (d + 1) from by omega]
      exact h
    have h2 : ‖(Tc c)^[t + 1] y‖ ≤ W + ‖c‖ + 1 := ih (t + 1) h'
    have hz : (Tc c)^[t + 1] y = ((Tc c)^[t] y) ^ 2 + c := by
      rw [Function.iterate_succ_apply', Tc]
    have h1 : ((Tc c)^[t] y) ^ 2 = (Tc c)^[t + 1] y - c := by rw [hz]; ring
    have hsq : ‖(Tc c)^[t] y‖ ^ 2 ≤ (W + ‖c‖ + 1) * (W + ‖c‖ + 1) := by
      calc ‖(Tc c)^[t] y‖ ^ 2 = ‖((Tc c)^[t] y) ^ 2‖ := (norm_pow _ 2).symm
        _ = ‖(Tc c)^[t + 1] y - c‖ := by rw [h1]
        _ ≤ ‖(Tc c)^[t + 1] y‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ (W + ‖c‖ + 1) + ‖c‖ := by linarith
        _ ≤ (W + ‖c‖ + 1) * (W + ‖c‖ + 1) := by nlinarith [hW, norm_nonneg c]
    have h3 : ‖(Tc c)^[t] y‖ ^ 2 ≤ (W + ‖c‖ + 1) ^ 2 := by nlinarith [hsq]
    have hBnn : (0 : ℝ) ≤ W + ‖c‖ + 1 := by linarith [hW, norm_nonneg c]
    have h4 := sq_le_sq.mp h3
    rw [abs_of_nonneg hBnn, abs_of_nonneg (norm_nonneg _)] at h4
    exact h4

/-- **Uniform boundedness of the forward orbits of the limit set.** -/
theorem coding_bounded {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
    (hN : 1 ≤ N) (D : PertData c₀ N τ n p r K) :
    ∃ B : ℝ, ∀ c ∈ ball c₀ D.ρ, ∀ ω : ℕ → Fin N, ∀ j : ℕ,
      ‖(Tc c)^[j] (D.coding c ω)‖ ≤ B := by
  -- `‖(Tc c) (p + r/2) - p‖ = r/2`, so the branch point at exact distance `r/2` from `p`.
  have hnorm2 : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
    rw [show ‖((r / 2 : ℝ) : ℂ)‖ = |r| / 2 from by simp, abs_of_pos D.r_pos]
  -- Every exponent is positive: a `0`-fold iterate would force `τc c i = id` on the core,
  -- contradicting that the core is mapped into the strictly smaller ball `closedBall p D.s`.
  have hnpos : ∀ i : Fin N, 1 ≤ n i := by
    intro i
    by_contra hlt
    have h0 : n i = 0 := by omega
    have hzmem : p + ((r / 2 : ℝ) : ℂ) ∈ closedBall p (r / 2) := by
      rw [mem_closedBall, dist_eq_norm]
      have hsub : p + ((r / 2 : ℝ) : ℂ) - p = ((r / 2 : ℝ) : ℂ) := by ring
      rw [hsub, hnorm2]
    have hzball : p + ((r / 2 : ℝ) : ℂ) ∈ ball p D.r₁ :=
      PertData.closedBall_half_subset D hzmem
    have hdyn := D.dyn c₀ (mem_ball_self D.hρ) i (p + ((r / 2 : ℝ) : ℂ)) hzball
    rw [h0, Function.iterate_zero_apply] at hdyn
    have himg := D.img c₀ (mem_ball_self D.hρ) i hzmem
    rw [hdyn, mem_closedBall, dist_eq_norm] at himg
    have hsub : p + ((r / 2 : ℝ) : ℂ) - p = ((r / 2 : ℝ) : ℂ) := by ring
    rw [hsub, hnorm2] at himg
    linarith [himg, D.hsr]
  refine ⟨‖p‖ + D.s + (‖c₀‖ + D.ρ) + 1, ?_⟩
  intro c hc ω j
  have hcρ : ‖c‖ ≤ ‖c₀‖ + D.ρ := by
    have h1 : ‖c - c₀‖ < D.ρ := by
      have h := hc
      rw [mem_ball, dist_eq_norm] at h
      exact h
    calc ‖c‖ = ‖(c - c₀) + c₀‖ := by ring_nf
      _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
      _ ≤ D.ρ + ‖c₀‖ := by linarith
      _ = ‖c₀‖ + D.ρ := by ring
  -- Main estimate, by strong induction on the time `t`: the orbit of `coding c Ω` is decomposed
  -- at the first return time `n (Ω 0)`.  Before the return the backward bound `tc_iter_bound`
  -- applies (the point returns to the compact core at time `n (Ω 0)`); after the return the
  -- orbit is that of the shifted code, already handled at the smaller time `t - n (Ω 0)`.
  have key : ∀ t : ℕ, ∀ Ω : ℕ → Fin N,
      ‖(Tc c)^[t] (D.coding c Ω)‖ ≤ ‖p‖ + D.s + ‖c‖ + 1 := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro Ω
      have hevar : (Tc c)^[n (Ω 0)] (D.coding c Ω) = D.coding c (fun k => Ω (k + 1)) :=
        D.coding_equivar c hc Ω
      have hu : ‖D.coding c (fun k => Ω (k + 1))‖ ≤ ‖p‖ + D.s := by
        have hm := D.coding_mem c hc (fun k => Ω (k + 1))
        rw [mem_closedBall, dist_eq_norm] at hm
        calc ‖D.coding c (fun k => Ω (k + 1))‖
            ≤ ‖D.coding c (fun k => Ω (k + 1)) - p‖ + ‖p‖ := by
              simpa using norm_add_le (D.coding c (fun k => Ω (k + 1)) - p) p
          _ ≤ D.s + ‖p‖ := by linarith
          _ = ‖p‖ + D.s := by ring
      by_cases ht : t ≤ n (Ω 0)
      · -- before (or at) the return time: go backwards from the return point
        have hb := tc_iter_bound (c := c) (y := (Tc c)^[t] (D.coding c Ω)) (W := ‖p‖ + D.s)
          (by linarith [D.hs0, norm_nonneg p]) (n (Ω 0) - t) 0 ?_
        · simpa using hb
        · rw [Nat.zero_add]
          have hcomp : (Tc c)^[n (Ω 0) - t] ((Tc c)^[t] (D.coding c Ω))
              = (Tc c)^[n (Ω 0)] (D.coding c Ω) := by
            rw [← Function.iterate_add_apply, Nat.sub_add_cancel ht]
          rw [hcomp, hevar]
          exact hu
      · -- after the return time: reduce to the shifted code at an earlier time
        have hgt : n (Ω 0) < t := by omega
        have hlt : t - n (Ω 0) < t := by
          have := hnpos (Ω 0); omega
        have hdiv : (Tc c)^[t] (D.coding c Ω)
            = (Tc c)^[t - n (Ω 0)] (D.coding c (fun k => Ω (k + 1))) := by
          calc (Tc c)^[t] (D.coding c Ω)
              = (Tc c)^[(t - n (Ω 0)) + n (Ω 0)] (D.coding c Ω) := by
                rw [Nat.sub_add_cancel (le_of_lt hgt)]
            _ = (Tc c)^[t - n (Ω 0)] ((Tc c)^[n (Ω 0)] (D.coding c Ω)) :=
                Function.iterate_add_apply _ _ _ _
            _ = (Tc c)^[t - n (Ω 0)] (D.coding c (fun k => Ω (k + 1))) := by rw [hevar]
        rw [hdiv]
        exact ih (t - n (Ω 0)) hlt (fun k => Ω (k + 1))
  have hfin := key j ω
  linarith [hfin, hcρ]

end Work.Motion
