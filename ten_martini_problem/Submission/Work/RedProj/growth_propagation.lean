import Mathlib
import Submission.Work.RedProj.local_propagation
import Submission.Work.RedProj.chain_of_isPreconnected

/-!
# Propagation of smallness for bounded holomorphic functions

If `W ⊆ ℂ` is open and preconnected and contains the closed ball `closedBall a r` with `r > 0`,
then a function `g` holomorphic on `W`, bounded by `1` on all of `W` and by `exp(-s)` on
`closedBall a r`, satisfies `‖g‖ ≤ exp(-c * s)` on every compact `K ⊆ W`, for a constant `c > 0`
depending only on `K` (and on `W`, `a`, `r`).

Mathematically this is the standard "propagation of smallness" (a quantitative form of the
identity/maximum principle): since `W` is an open connected subset of `ℂ` it is path connected,
so a ball of radius `ε` around `a` can be transported to a ball of radius `ε` around any point
`z ∈ K` along a finite chain of balls; each link of the chain loses a factor `2` in the exponent
(Lemma `local_propagation`, a two-circle maximum principle / Hadamard three-lines estimate),
producing a positive constant `2^{-N_z}`.  Compactness of `K` makes the minimum of finitely many
such constants positive.
-/

namespace Work.RedProj

/-- **Propagation of smallness.**  On a connected open set, a holomorphic function that is
bounded by `1` and exponentially small on a fixed ball is exponentially small, with a fixed
positive exponent loss, on every compact subset. -/
theorem growth_propagation {W : Set ℂ} (hWo : IsOpen W) (hWc : IsPreconnected W)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall a r ⊆ W) :
    ∀ K ⊆ W, IsCompact K → ∃ c : ℝ, 0 < c ∧ ∀ (g : ℂ → ℂ) (s : ℝ), 0 ≤ s →
      AnalyticOnNhd ℂ g W → (∀ z ∈ W, ‖g z‖ ≤ 1) →
      (∀ z ∈ Metric.closedBall a r, ‖g z‖ ≤ Real.exp (-s)) →
      ∀ z ∈ K, ‖g z‖ ≤ Real.exp (-(c * s)) := by
  intro K hKW hKc
  classical
  have haW : a ∈ W := hball (Metric.mem_closedBall_self hr.le)
  -- For every point of `K` we produce a neighbourhood and a positive exponent.
  have hdata : ∀ z : K, ∃ (ε : ℝ) (c : ℝ), 0 < ε ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ (g : ℂ → ℂ) (s : ℝ), 0 ≤ s →
        AnalyticOnNhd ℂ g W → (∀ w ∈ W, ‖g w‖ ≤ 1) →
        (∀ w ∈ Metric.closedBall a r, ‖g w‖ ≤ Real.exp (-s)) →
        ∀ ζ ∈ Metric.ball z.1 ε, ‖g ζ‖ ≤ Real.exp (-(c * s)) := by
    intro z
    have hzW : z.1 ∈ W := hKW z.2
    -- A chain of balls from `a` to `z.1` inside `W`.
    obtain ⟨ε, hεpos, hεr, N, p, hp0, hpN, hroom, hstep⟩ :=
      chain_of_isPreconnected hWo hWc haW hzW hr
    refine ⟨ε, (1 / 2) ^ N, hεpos, by positivity, ?_, ?_⟩
    · exact pow_le_one₀ (by norm_num) (by norm_num)
    · intro g s hs hgan hg1 hgb
      -- The invariant: on `closedBall (p i) ε` the bound is `exp(-(s * 2^{-i}))`.
      have hcert : ∀ i ≤ N, ∀ ζ ∈ Metric.closedBall (p i) ε,
          ‖g ζ‖ ≤ Real.exp (-(s * (1 / 2) ^ i)) := by
        intro i
        induction i with
        | zero =>
          intro _ ζ hζ
          rw [hp0] at hζ
          have hmem : ζ ∈ Metric.closedBall a r :=
            Metric.closedBall_subset_closedBall hεr hζ
          simpa using hgb ζ hmem
        | succ i ih =>
          intro hi ζ hζ
          have hiN : i ≤ N := le_trans (Nat.le_succ i) hi
          have hlt : i < N := Nat.lt_of_succ_le hi
          -- one propagation step on the ball `ball (p i) (5 * ε) ⊆ W`
          have hloc := local_propagation (w := p i) (ρ := ε) (R := 5 * ε) (s := s * (1 / 2) ^ i)
            hεpos (by linarith)
            (hgan.mono (hroom i hiN))
            (fun u hu => hg1 u (hroom i hiN hu))
            (ih hiN)
          have hmem : ζ ∈ Metric.closedBall (p i) (2 * ε) := by
            rw [Metric.mem_closedBall, dist_eq_norm] at hζ ⊢
            have hst : ‖p (i + 1) - p i‖ ≤ ε := hstep i hlt
            have htri : ‖ζ - p i‖ ≤ ‖ζ - p (i + 1)‖ + ‖p (i + 1) - p i‖ := by
              have h : ζ - p i = (ζ - p (i + 1)) + (p (i + 1) - p i) := by ring
              rw [h]; exact norm_add_le _ _
            linarith
          have hb := hloc ζ hmem
          have heq : (s * (1 / 2) ^ i) / 2 = s * (1 / 2) ^ (i + 1) := by
            rw [pow_succ]; ring
          rw [heq] at hb
          exact hb
      -- At the end of the chain: `p N = z.1`.
      intro ζ hζ
      have hmem : ζ ∈ Metric.closedBall (p N) ε := by
        rw [hpN]; exact Metric.ball_subset_closedBall hζ
      have hb := hcert N le_rfl ζ hmem
      rwa [mul_comm s] at hb
  choose ε c hε using hdata
  -- The balls `ball z (ε z)` cover the compact set `K`; extract a finite subcover.
  have hcover : K ⊆ ⋃ z : K, Metric.ball z.1 (ε z) := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hε ⟨z, hz⟩).1⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun z : K => Metric.ball z.1 (ε z))
    (fun _ => Metric.isOpen_ball) hcover
  -- The product of the finitely many exponents is positive and at most each of them.
  refine ⟨∏ z ∈ t, c z, Finset.prod_pos (fun z _ => (hε z).2.1), ?_⟩
  intro g s hs hgan hg1 hgb z hz
  have hzt := ht hz
  simp only [Set.mem_iUnion, exists_prop] at hzt
  obtain ⟨z₀, hz0t, hzz0⟩ := hzt
  have hbound := (hε z₀).2.2.2 g s hs hgan hg1 hgb z hzz0
  have hprod_le : (∏ z ∈ t, c z) ≤ c z₀ := by
    rw [← Finset.mul_prod_erase t c hz0t]
    have h1 : (∏ x ∈ t.erase z₀, c x) ≤ 1 :=
      Finset.prod_le_one₀ (fun x _ => le_of_lt (hε x).2.1) (fun x _ => (hε x).2.2.1)
    nlinarith [(hε z₀).2.1, h1]
  refine hbound.trans (Real.exp_le_exp.mpr (neg_le_neg ?_))
  exact mul_le_mul_of_nonneg_right hprod_le hs

end Work.RedProj
