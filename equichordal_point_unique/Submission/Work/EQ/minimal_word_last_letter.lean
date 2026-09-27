import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.germC_facts

/-! # The last letter of the minimal word of a chain is `false`

If `ε` is a chain word of the chain `q` of length exactly the tail index `tailIdx a h q > 0`, then
its last letter is `false`: a last letter `true` would propagate the principal leaf one step
further back (`invBranch a true (germC (λ u)) = germC u`), contradicting the minimality of the tail
index.

This is the small combinatorial input that makes the case-(ii) reading of Rychlik's Lemma 5.1
non-trivial: the returning word `C` of the decomposition `ε = ε₀ ++ true^s ++ C` contains a
`false`, hence `charVal C = wtAux (C.reverse) 0 ≤ γ < 1` (`Work.EQ.charVal_of_closed`,
`Work.EQ.walk_count`). -/

namespace Work.EQ

open Filter _root_.Topology
open Complex

noncomputable section

/-- A nonempty list is a list with one appended last letter. -/
lemma exists_append_singleton_of_ne_nil {ε : List Bool} (hne : ε ≠ []) :
    ∃ (l : List Bool) (b : Bool), ε = l ++ [b] := by
  induction ε with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    rcases xs with _ | ⟨y, ys⟩
    · exact ⟨[], x, rfl⟩
    · obtain ⟨l, b, hl⟩ := ih (by simp)
      exact ⟨x :: l, b, by rw [hl]; rfl⟩

/-- **The last letter of a minimal chain word is `false`.**  `hleaf` is the principal-leaf identity
`invBranch a true (germC (λ u)) = germC u` on the ball of radius `δl`, and `‖ψ₁ q‖ < δl` puts the
whole recursion in that ball. -/
theorem last_letter_false_of_isChainWord {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {r : ℝ} (hh : IsStableGerm a h r) {q : ChainData} (hq : IsChain a h q) {ε : List Bool}
    (hw : IsChainWord a h q (tailIdx a h q) ε) (hpos : 0 < tailIdx a h q)
    {δl : ℝ} (hleaf : ∀ u : ℂ, ‖u‖ < δl →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    (hsmall : ‖q.2.1‖ < δl) :
    ε.getLast? = some false := by
  have hlen : ε.length = tailIdx a h q := hw.1
  have hne : ε ≠ [] := by
    intro h0
    have h1 : ε.length = 0 := by rw [h0]; rfl
    omega
  obtain ⟨l, b, hl⟩ := exists_append_singleton_of_ne_nil hne
  rcases b with _ | _  -- `false` : done; `true` : contradiction
  · rw [hl, List.getLast?_concat]
  · exfalso
    -- the index of the last step
    set n : ℕ := l.length with hn
    have hεlen : ε.length = n + 1 := by rw [hl]; simp [hn]
    have hτ : tailIdx a h q = n + 1 := by rw [← hlen, hεlen]
    have hnlt : n < tailIdx a h q := by omega
    -- the label of the last step is `true`
    have hgetD : ε.getD n true = true := by
      rw [List.getD_eq_getElem?_getD, hl, List.getElem?_append,
        if_neg (by simp [hn]), hn, Nat.sub_self]
      rfl
    -- the tail at the last step
    have htail : q.1 ((n : ℤ) + 1) = germC a h ((eqLam a : ℂ) ^ (tailIdx a h q) * q.2.1) := by
      have h1 : ((n : ℤ) + 1) = ((tailIdx a h q : ℕ) : ℤ) := by
        rw [hτ]; push_cast; ring
      rw [h1]
      exact TailP_of_isChain hq (tailIdx a h q) le_rfl
    -- the step relation
    have hstep : q.1 (n : ℤ) = invBranch a true (q.1 ((n : ℤ) + 1)) := by
      have h := hw.2.2 n hnlt
      rw [hgetD] at h
      exact h
    -- the smallness
    have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
    have hlam1 : eqLam a ≤ 1 := (eqLam_lt_one' ha0 ha1).le
    have hnorm : ‖(eqLam a : ℂ) ^ n * q.2.1‖ ≤ ‖q.2.1‖ := by
      have h2 : ‖(eqLam a : ℂ) ^ n‖ = (eqLam a) ^ n := by
        rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg hlam0.le n)]
      rw [norm_mul, h2]
      calc (eqLam a) ^ n * ‖q.2.1‖ ≤ 1 * ‖q.2.1‖ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hlam0.le hlam1) (norm_nonneg _)
        _ = ‖q.2.1‖ := one_mul _
    have hpow : (eqLam a : ℂ) ^ (tailIdx a h q) * q.2.1
        = (eqLam a : ℂ) * ((eqLam a : ℂ) ^ n * q.2.1) := by
      rw [hτ, pow_succ]
      ring
    have hleafn := hleaf ((eqLam a : ℂ) ^ n * q.2.1) (lt_of_le_of_lt hnorm hsmall)
    have hqn : q.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * q.2.1) := by
      rw [hstep, htail, hpow]
      exact hleafn
    -- hence the principal tail holds from `n`, contradicting minimality
    have hTailP : TailP a h q n := by
      intro m hm
      rcases eq_or_lt_of_le hm with h | h
      · rw [← h]; exact hqn
      · exact TailP_of_isChain hq m (by omega)
    have hle : tailIdx a h q ≤ n := tailIdx_le (tailP_of_isChain hq) hTailP
    omega

end

end Work.EQ
