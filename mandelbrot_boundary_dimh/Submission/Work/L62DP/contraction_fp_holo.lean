import Mathlib

/-!
# A contraction fixed point depending holomorphically on a parameter

For `Ψ` holomorphic on an open set `Ω ⊆ ℂ`, and for every `w` in an open set `s` a closed ball
`closedBall (w + β) r ⊆ Ω` on which `‖Ψ‖ ≤ (1 - λ) r` and `‖deriv Ψ‖ ≤ λ` with `0 ≤ λ < 1`, the
map `u ↦ w + β - Ψ u` has a unique fixed point `H w` in that ball, and `w ↦ H w` is holomorphic
on `s`.

The proof is the standard contraction argument: the iterates starting at `w + β` are holomorphic
in `w` and converge uniformly (with rate `λⁿ r`) to the fixed point, so the limit is holomorphic
by Weierstrass' theorem (`TendstoLocallyUniformlyOn.differentiableOn`).
-/

open Set Metric Filter
open scoped Topology

namespace Work.L62DP

/-- The `n`-fold iterate of `u ↦ w + β - Ψ u`, starting from `w + β`. -/
def iter (Psi : ℂ → ℂ) (beta : ℂ) : ℕ → ℂ → ℂ
  | 0 => fun w => w + beta
  | (n + 1) => fun w => w + beta - Psi (iter Psi beta n w)

theorem iter_zero (Psi : ℂ → ℂ) (beta : ℂ) : iter Psi beta 0 = fun w => w + beta := rfl

theorem iter_succ (Psi : ℂ → ℂ) (beta : ℂ) (n : ℕ) :
    iter Psi beta (n + 1) = fun w => w + beta - Psi (iter Psi beta n w) := rfl

theorem iter_succ_apply (Psi : ℂ → ℂ) (beta : ℂ) (n : ℕ) (w : ℂ) :
    iter Psi beta (n + 1) w = w + beta - Psi (iter Psi beta n w) := rfl

/-- **Contraction fixed point depending holomorphically on a parameter.** -/
theorem contraction_fp_holo {s Omega : Set ℂ} (hs : IsOpen s) (hOm : IsOpen Omega)
    {Psi : ℂ → ℂ} (hPsi : DifferentiableOn ℂ Psi Omega) {beta : ℂ} {r lam : ℝ} (hr : 0 < r)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hball : ∀ w ∈ s, Metric.closedBall (w + beta) r ⊆ Omega)
    (hsmall : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + beta) r, ‖Psi u‖ ≤ (1 - lam) * r)
    (hlip : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + beta) r, ‖deriv Psi u‖ ≤ lam) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H s ∧
      (∀ w ∈ s, H w ∈ Metric.closedBall (w + beta) r ∧ H w = w + beta - Psi (H w)) ∧
      (∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + beta) r, u = w + beta - Psi u → u = H w) := by
  -- The iterates all stay inside the (closed) ball.
  have hbdd : ∀ n : ℕ, ∀ w ∈ s, iter Psi beta n w ∈ Metric.closedBall (w + beta) r := by
    intro n
    induction n with
    | zero =>
        intro w _
        show w + beta ∈ Metric.closedBall (w + beta) r
        rw [Metric.mem_closedBall, dist_self]
        exact hr.le
    | succ n ih =>
        intro w hw
        rw [iter_succ_apply Psi beta n w, Metric.mem_closedBall, dist_eq_norm]
        have h1 : (w + beta - Psi (iter Psi beta n w)) - (w + beta) = -Psi (iter Psi beta n w) := by
          ring
        rw [h1, norm_neg]
        calc ‖Psi (iter Psi beta n w)‖ ≤ (1 - lam) * r := hsmall w hw _ (ih w hw)
          _ ≤ r := by
              have h2 : (1 - lam) * r ≤ 1 * r := mul_le_mul_of_nonneg_right (by linarith) hr.le
              simpa using h2
  -- `Ψ` is `lam`-Lipschitz on each of the balls.
  have hLip : ∀ w ∈ s, ∀ a ∈ Metric.closedBall (w + beta) r,
      ∀ b ∈ Metric.closedBall (w + beta) r, ‖Psi a - Psi b‖ ≤ lam * ‖a - b‖ := by
    intro w hw a ha b hb
    exact Convex.norm_image_sub_le_of_norm_deriv_le (f := Psi)
      (s := Metric.closedBall (w + beta) r) (C := lam)
      (fun x hx => hPsi.differentiableAt (hOm.mem_nhds (hball w hw hx)))
      (fun x hx => hlip w hw x hx) (convex_closedBall (w + beta) r) hb ha
  -- One-step contraction estimate.
  have hone : ∀ w ∈ s, ∀ n : ℕ,
      ‖iter Psi beta (n + 1) w - iter Psi beta n w‖ ≤ lam ^ n * ((1 - lam) * r) := by
    intro w hw n
    induction n with
    | zero =>
        have h1 : iter Psi beta (0 + 1) w - iter Psi beta 0 w = -Psi (w + beta) := by
          simp only [iter_succ_apply, iter_zero]
          ring
        rw [h1, norm_neg, pow_zero, one_mul]
        exact hsmall w hw (w + beta) (by rw [Metric.mem_closedBall, dist_self]; exact hr.le)
    | succ n ih =>
        have h2 : iter Psi beta (n + 1 + 1) w - iter Psi beta (n + 1) w
            = Psi (iter Psi beta n w) - Psi (iter Psi beta (n + 1) w) := by
          rw [iter_succ_apply Psi beta (n + 1) w, iter_succ_apply Psi beta n w]
          ring
        rw [h2]
        calc ‖Psi (iter Psi beta n w) - Psi (iter Psi beta (n + 1) w)‖
            ≤ lam * ‖iter Psi beta n w - iter Psi beta (n + 1) w‖ :=
              hLip w hw _ (hbdd n w hw) _ (hbdd (n + 1) w hw)
          _ = lam * ‖iter Psi beta (n + 1) w - iter Psi beta n w‖ := by rw [norm_sub_rev]
          _ ≤ lam * (lam ^ n * ((1 - lam) * r)) := mul_le_mul_of_nonneg_left ih hlam0
          _ = lam ^ (n + 1) * ((1 - lam) * r) := by rw [pow_succ]; ring
  -- Geometric bound on the increments.
  have hgeo : ∀ w ∈ s, ∀ k n : ℕ,
      ‖iter Psi beta (n + k) w - iter Psi beta n w‖ ≤ lam ^ n * r := by
    intro w hw k
    induction k with
    | zero =>
        intro n
        rw [Nat.add_zero, sub_self, norm_zero]
        exact mul_nonneg (pow_nonneg hlam0 n) hr.le
    | succ k ih =>
        intro n
        have hnk : n + (k + 1) = (n + 1) + k := by omega
        rw [hnk]
        calc ‖iter Psi beta ((n + 1) + k) w - iter Psi beta n w‖
            ≤ ‖iter Psi beta ((n + 1) + k) w - iter Psi beta (n + 1) w‖
                + ‖iter Psi beta (n + 1) w - iter Psi beta n w‖ := by
              have htri := dist_triangle (iter Psi beta ((n + 1) + k) w)
                (iter Psi beta (n + 1) w) (iter Psi beta n w)
              rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
          _ ≤ lam ^ (n + 1) * r + lam ^ n * ((1 - lam) * r) :=
              add_le_add (ih (n + 1)) (hone w hw n)
          _ = lam ^ n * r := by rw [pow_succ]; ring
  -- The iterates form a uniformly Cauchy family.
  have hcauchy : UniformCauchySeqOn (fun n => iter Psi beta n) atTop s := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have htend : Tendsto (fun n : ℕ => lam ^ n * r) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1).mul_const r
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 htend).2 ε hε)
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    rw [dist_eq_norm]
    rcases le_total n m with hnm | hmn
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      exact lt_of_le_of_lt (hgeo x hx k n) (hN n hn)
    · rw [norm_sub_rev]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact lt_of_le_of_lt (hgeo x hx k m) (hN m hm)
  -- The limit function.
  let H : ℂ → ℂ := fun w => limUnder atTop (fun n => iter Psi beta n w)
  have hHlim : ∀ w ∈ s, Tendsto (fun n => iter Psi beta n w) atTop (𝓝 (H w)) := by
    intro w hw
    have hcw : CauchySeq (fun n => iter Psi beta n w) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp hcauchy) ε hε
      exact ⟨N, fun m hm n hn => hN m hm n hn w hw⟩
    simpa only [H] using hcw.tendsto_limUnder
  have hHmem : ∀ w ∈ s, H w ∈ Metric.closedBall (w + beta) r := fun w hw =>
    IsClosed.mem_of_tendsto isClosed_closedBall (hHlim w hw)
      (Eventually.of_forall (fun n => hbdd n w hw))
  have hHfix : ∀ w ∈ s, H w = w + beta - Psi (H w) := by
    intro w hw
    have hHΩ : H w ∈ Omega := hball w hw (hHmem w hw)
    have hcont : ContinuousAt Psi (H w) := (hPsi.differentiableAt (hOm.mem_nhds hHΩ)).continuousAt
    have hlim1 : Tendsto (fun n => iter Psi beta (n + 1) w) atTop (𝓝 (H w)) :=
      (tendsto_add_atTop_iff_nat 1).mpr (hHlim w hw)
    have hlim2 : Tendsto (fun n => w + beta - Psi (iter Psi beta n w)) atTop
        (𝓝 (w + beta - Psi (H w))) :=
      (hcont.tendsto.comp (hHlim w hw)).const_sub (w + beta)
    have heqfun : (fun n => iter Psi beta (n + 1) w) = fun n => w + beta - Psi (iter Psi beta n w) := by
      funext n
      rw [iter_succ_apply Psi beta n w]
    rw [heqfun] at hlim1
    exact tendsto_nhds_unique hlim1 hlim2
  have hunif : TendstoUniformlyOn (fun n => iter Psi beta n) H atTop s :=
    hcauchy.tendstoUniformlyOn_of_tendsto (fun w hw => hHlim w hw)
  -- Each iterate is holomorphic.
  have hGdiff : ∀ n : ℕ, DifferentiableOn ℂ (iter Psi beta n) s := by
    intro n
    induction n with
    | zero =>
        rw [iter_zero]
        exact (differentiableOn_id (𝕜 := ℂ) (s := s)).add_const beta
    | succ n ih =>
        rw [iter_succ]
        exact ((differentiableOn_id (𝕜 := ℂ) (s := s)).add_const beta).sub
          (hPsi.comp ih (fun w hw => hball w hw (hbdd n w hw)))
  -- The limit is holomorphic (Weierstrass).
  have hHdiff : DifferentiableOn ℂ H s :=
    hunif.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall hGdiff) hs
  refine ⟨H, hHdiff, fun w hw => ⟨hHmem w hw, hHfix w hw⟩, ?_⟩
  -- Uniqueness of the fixed point in the ball.
  intro w hw u hu heq
  have hHu : u - H w = Psi (H w) - Psi u := by
    conv_lhs => rw [heq, hHfix w hw]
    ring
  have h1 : ‖u - H w‖ ≤ lam * ‖u - H w‖ := by
    calc ‖u - H w‖ = ‖Psi (H w) - Psi u‖ := by rw [hHu]
      _ ≤ lam * ‖H w - u‖ := hLip w hw (H w) (hHmem w hw) u hu
      _ = lam * ‖u - H w‖ := by rw [norm_sub_rev]
  have h2 : ‖u - H w‖ = 0 := by
    have h3 : (1 - lam) * ‖u - H w‖ ≤ 0 := by nlinarith [h1]
    have h4 : 0 < 1 - lam := by linarith
    have h5 : 0 ≤ ‖u - H w‖ := norm_nonneg _
    nlinarith [h3, h4, h5]
  exact sub_eq_zero.mp (norm_eq_zero.mp h2)

end Work.L62DP
