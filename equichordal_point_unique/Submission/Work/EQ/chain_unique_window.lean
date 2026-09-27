import Mathlib
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.chain_step_unique
import Submission.Work.EQ.eqLam_ne_zero_of_injOn
import Submission.Work.EQ.window_ball_eps

namespace Work.EQ

/-- **Uniqueness of chains with equal `ψ₁` inside a window.**

Let `p : ChainData` be arbitrary, `N M K : ℕ` with `N ≤ K`, `M ≤ K`, `ρg > 0` such that the second
coordinate of `germC a h` is injective on `Metric.ball 0 ρg`, and `λ^M * p.2.2 ∈ Metric.ball 0 ρg`
(`λ = eqLam a`).  Then there is `ε > 0` such that any two chains `q`, `q'` (`IsChain a h q`,
`IsChain a h q'`) with

* `q.2.1 = q'.2.1`,
* `‖q.1 k - p.1 k‖ < ε` and `‖q'.1 k - p.1 k‖ < ε` for all `|k| ≤ K`,
* `‖q.2.2 - p.2.2‖ < ε`, `‖q'.2.2 - p.2.2‖ < ε`,
* the forward tail from `N` and the backward tail from `M` (as displayed in the statement)

satisfy `q = q'`.

Route (no hypothesis on `p` itself is needed).
* Descend from index `N` to index `-M`.  Base: the tails give
  `q.1 N = germC (λ^N q.2.1) = germC (λ^N q'.2.1) = q'.1 N` (uses `q.2.1 = q'.2.1`).
  Step: if `q.1 (j+1) = q'.1 (j+1) =: Q`, then `RegPair a (q.1 j) (q.1 (j+1))` from `IsChain a h q`
  gives `bsq (subO1 a Q) ≠ 0`, so `Work.EQ.eqRelC_solutions`
  (`Submission/Work/EQ/HeteroAlgebra.lean`) gives that each of `q.1 j`, `q'.1 j` is
  `invBranch a true Q` or `invBranch a false Q`.  If they differed they would be the two distinct
  branches, hence `≥ 1` apart by `Work.EQ.invBranch_separation`
  (`Submission/Work/EQ/H0_tail_bounded.lean`), contradicting both being `ε`-close to `p.1 j` once
  `ε ≤ 1/2`.  Here `-M ≤ j ≤ N - 1` so the window hypothesis applies (`K ≥ N`, `K ≥ M`).
* At `j = -M` we get `q.1 (-M) = q'.1 (-M)`.  Since `(ugermC a h v).2 = (germC a h v).2`, the two
  backward tails give `(germC (λ^M q.2.2)).2 = (germC (λ^M q'.2.2)).2`; choosing
  `ε ≤ (ρg - ‖λ^M * p.2.2‖) / (2 * λ^M)` puts both `λ^M * q.2.2` and `λ^M * q'.2.2` in the
  injectivity ball, so `q.2.2 = q'.2.2` (divide by `λ^M ≠ 0`, using `Complex.ofReal_ne_zero`).
* The remaining indices follow from the two tails together with `q.2.1 = q'.2.1` and
  `q.2.2 = q'.2.2`.
The constant `ε` does not depend on `q, q'`. -/
theorem chain_unique_window {a : ℝ} {h : ℂ → ℂ} {p : ChainData}
    {N M K : ℕ} (hNK : N ≤ K) (hMK : M ≤ K) {ρg : ℝ} (hρg : 0 < ρg)
    (hinj : Set.InjOn (fun u => (germC a h u).2) (Metric.ball (0 : ℂ) ρg))
    (hball : (eqLam a : ℂ) ^ M * p.2.2 ∈ Metric.ball (0 : ℂ) ρg) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q q' : ChainData, IsChain a h q → IsChain a h q' →
      q.2.1 = q'.2.1 →
      (∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q.1 k - p.1 k‖ < ε) →
      (∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q'.1 k - p.1 k‖ < ε) →
      ‖q.2.2 - p.2.2‖ < ε → ‖q'.2.2 - p.2.2‖ < ε →
      (∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * q.2.1)) →
      (∀ n : ℕ, N ≤ n → q'.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * q'.2.1)) →
      (∀ n : ℕ, M ≤ n → q.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * q.2.2)) →
      (∀ n : ℕ, M ≤ n → q'.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * q'.2.2)) →
      q = q' := by
  -- `eqLam a ≠ 0`, otherwise the second coordinate of `germC a h` is identically zero and the
  -- injectivity hypothesis fails.
  have hlam : eqLam a ≠ 0 := eqLam_ne_zero_of_injOn hρg hinj
  -- the quantitative constant: `ε` is small enough that `λ^M ·` maps the `ε`-ball around
  -- `p.2.2` into the injectivity ball.
  obtain ⟨ε, hεpos, hε2, hεball⟩ := window_ball_eps (a := a) (M := M) (p2 := p.2.2) (ρ := ρg) hρg hlam hball
  refine ⟨ε, hεpos, ?_⟩
  intro q q' hqc hq'c hpsi1 hclose hclose' hclose2 hclose2' htail htail' hback hback'
  -- ### The descent step, with the index bound `|j| ≤ K` discharged from the window.
  have hstep : ∀ j : ℤ, -((M : ℤ)) ≤ j → j ≤ (N : ℤ) - 1 →
      q.1 (j + 1) = q'.1 (j + 1) → q.1 j = q'.1 j := by
    intro j hjM hjNm hnext
    have hMK' : (M : ℤ) ≤ (K : ℤ) := by exact_mod_cast hMK
    have hNK' : (N : ℤ) ≤ (K : ℤ) := by exact_mod_cast hNK
    have hjK : |j| ≤ (K : ℤ) := by
      rw [abs_le]
      omega
    exact chain_step_unique hqc hq'c hnext (hclose j hjK) (hclose' j hjK) hε2
  -- ### Descending induction from index `N`.
  have key : ∀ k : ℕ, ∀ j : ℤ, j = (N : ℤ) - (k : ℤ) → -((M : ℤ)) ≤ j → q.1 j = q'.1 j := by
    intro k
    induction k with
    | zero =>
      intro j hj hM
      have hjN : j = (N : ℤ) := by omega
      rw [hjN, htail N le_rfl, htail' N le_rfl, hpsi1]
    | succ k ih =>
      intro j hj hM
      have hj' : j + 1 = (N : ℤ) - (k : ℤ) := by omega
      have hM' : -((M : ℤ)) ≤ j + 1 := by omega
      have hnext : q.1 (j + 1) = q'.1 (j + 1) := ih (j + 1) hj' hM'
      have hjNm : j ≤ (N : ℤ) - 1 := by omega
      exact hstep j hM hjNm hnext
  have main : ∀ j : ℤ, -((M : ℤ)) ≤ j → j ≤ (N : ℤ) → q.1 j = q'.1 j := by
    intro j hjM hjN
    obtain ⟨k, hk⟩ : ∃ k : ℕ, j = (N : ℤ) - (k : ℤ) := by
      refine ⟨((N : ℤ) - j).toNat, ?_⟩
      have h0 : (0 : ℤ) ≤ (N : ℤ) - j := by omega
      rw [Int.toNat_of_nonneg h0]
      ring
    exact key k j hk hjM
  -- ### The second linearising parameter at `j = -M`.
  have hpsi2 : q.2.2 = q'.2.2 := by
    have hm : q.1 (-(M : ℤ)) = q'.1 (-(M : ℤ)) := main _ le_rfl (by omega)
    have hsnd : (germC a h ((eqLam a : ℂ) ^ M * q.2.2)).2
        = (germC a h ((eqLam a : ℂ) ^ M * q'.2.2)).2 := by
      have h := congrArg Prod.snd
        ((hback M le_rfl).symm.trans (hm.trans (hback' M le_rfl)))
      simpa [ugermC, eqMirror] using h
    have hmem : (eqLam a : ℂ) ^ M * q.2.2 ∈ Metric.ball (0 : ℂ) ρg := hεball _ hclose2
    have hmem' : (eqLam a : ℂ) ^ M * q'.2.2 ∈ Metric.ball (0 : ℂ) ρg := hεball _ hclose2'
    have heq : (eqLam a : ℂ) ^ M * q.2.2 = (eqLam a : ℂ) ^ M * q'.2.2 := hinj hmem hmem' hsnd
    have hpow : (eqLam a : ℂ) ^ M ≠ 0 := by
      apply pow_ne_zero
      simpa using hlam
    have h0 : (eqLam a : ℂ) ^ M * (q.2.2 - q'.2.2) = 0 := by rw [mul_sub, heq, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hpow
    · exact sub_eq_zero.mp h
  -- ### Everything else is the two tails.
  have hfun : q.1 = q'.1 := by
    funext j
    rcases lt_or_ge j ((N : ℤ)) with hjN | hjN
    · rcases le_or_gt j (-((M : ℤ))) with hjM | hjM
      · -- backward tail
        have hnj : (((-j).toNat : ℕ) : ℤ) = -j := Int.toNat_of_nonneg (by omega)
        have hjn : j = -(((-j).toNat : ℕ) : ℤ) := by omega
        rw [hjn]
        have hMn : M ≤ (-j).toNat := by omega
        rw [hback (-j).toNat hMn, hback' (-j).toNat hMn, hpsi2]
      · -- in the window
        exact main j (by omega) (by omega)
    · -- forward tail
      have hnj : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (by omega)
      rw [← hnj]
      have hNn : N ≤ j.toNat := by omega
      rw [htail j.toNat hNn, htail' j.toNat hNn, hpsi1]
  exact Prod.ext hfun (Prod.ext hpsi1 hpsi2)

end Work.EQ
