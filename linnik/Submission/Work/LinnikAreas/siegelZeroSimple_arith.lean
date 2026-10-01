import Mathlib
import Submission.Work.LinnikAreas.szSimple_arith_core
import Submission.Work.LinnikAreas.log_unbounded_nat

namespace Work.LinnikAreas

/-- Elementary rewrite converting the displayed expression into the normalised form
`(L/√λ + C + log N + K) * ((√λ + λ)/L)`, `L = log q`:
`((1 + √λ/L) - 1) = √λ/L`, `(1 + √λ/L) - (1 - λ/L) = (√λ + λ)/L` and `1/(√λ/L) = L/√λ`. -/
theorem arith_rewrite {L lam : ℝ} (_hL : 0 < L) (hlam : 0 < lam) (C N : ℝ) :
    (1 / ((1 + Real.sqrt lam / L) - 1) + C + N + Real.log 2 / 2 + 3 / 2) *
        ((1 + Real.sqrt lam / L) - (1 - lam / L))
      = (L / Real.sqrt lam + C + N + Real.log 2 / 2 + 3 / 2) *
        ((Real.sqrt lam + lam) / L) := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have h1 : (1 + Real.sqrt lam / L) - 1 = Real.sqrt lam / L := by ring
  have h2 : (1 + Real.sqrt lam / L) - (1 - lam / L) = (Real.sqrt lam + lam) / L := by ring
  rw [h1, h2]
  have h3 : 1 / (Real.sqrt lam / L) = L / Real.sqrt lam := by
    rw [one_div, inv_div]
  rw [h3]

theorem siegelZeroSimple_arith : ∀ C : ℝ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ N lam : ℝ,
    2 ≤ q → 2 ≤ N → N ≤ (q : ℝ) → 0 < lam → lam ≤ 1 / 100 →
    (1 / ((1 + Real.sqrt lam / Real.log q) - 1) + C + Real.log N + Real.log 2 / 2 + 3 / 2) *
      ((1 + Real.sqrt lam / Real.log q) - (1 - lam / Real.log q)) < 2 := by
  intro C
  obtain ⟨M, hM⟩ := szSimple_arith_core C
  obtain ⟨q₀, hq₀⟩ := log_unbounded_nat M
  refine ⟨q₀, ?_⟩
  intro q hq N lam h2q h2N hNq hlam0 hlam1
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h2q
  have hLpos : 0 < Real.log (q : ℝ) := by
    apply Real.log_pos
    linarith
  have hNpos : 0 < N := by linarith
  have hlogN : Real.log N ≤ Real.log (q : ℝ) := Real.log_le_log hNpos hNq
  have hML : M ≤ Real.log (q : ℝ) := hq₀ q hq
  have key := hM (Real.log (q : ℝ)) (Real.log N) lam hLpos hML hlogN hlam0 hlam1
  rw [arith_rewrite hLpos hlam0 C (Real.log N)]
  exact key

end Work.LinnikAreas
