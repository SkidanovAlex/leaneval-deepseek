import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.exists_fin3_decomp

/-!
# Expansion of the `b`-sum (frame count, "singleton" step)

The left-hand side sums, over the triples `b` in the box `[1,H]^3`, the weight
`∏_k (if b k ≠ α then F k (b k) else 0)`, restricted to those `b` with
`g ∣ ∏_k |α - b k|` (note that a coordinate equal to `α` makes the weight vanish anyway,
so the condition `g ∣ 0` is harmless there).

The right-hand side is the standard divisor expansion: sum over the ordered factorisations
`g = a 0 * a 1 * a 2` of `g` into divisors of `g`, and then take the product over `k` of the
single-coordinate sums over `y ∈ [1,H]`, `y ≠ α`, `a k ∣ |α - y|`.

The point is that every admissible `b` admits *some* such factorisation with `a k ∣ |α - b k|`
for all `k` (`exists_fin3_decomp`); distributing the "there exists `a`" and expanding the
resulting product of sums (`Finset.prod_univ_sum`) gives the estimate, since all terms are
nonnegative.
-/

open scoped BigOperators

namespace Work.LinnikBurgess.frame_count_prov_aux

theorem bsum_expansion {g α H : ℕ} (hg : 0 < g) (F : Fin 3 → ℕ → ℝ) (hF : ∀ k y, 0 ≤ F k y) :
    (∑ b ∈ box3 H, (if g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del α (b k) then
        ∏ k : Fin 3, (if b k ≠ α then F k (b k) else 0) else 0))
      ≤ ∑ a ∈ (Fintype.piFinset (fun _ : Fin 3 => g.divisors)).filter
            (fun a : Fin 3 → ℕ => ∏ k : Fin 3, a k = g),
          ∏ k : Fin 3, ∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ α ∧ a k ∣ Work.LinnikBurgess.del α y),
            F k y := by
  classical
  set T : (Fin 3 → ℕ) → Fin 3 → Finset ℕ :=
    fun a k => (Finset.Icc 1 H).filter (fun y => y ≠ α ∧ a k ∣ Work.LinnikBurgess.del α y) with hT
  set A : Finset (Fin 3 → ℕ) :=
    (Fintype.piFinset (fun _ : Fin 3 => g.divisors)).filter
      (fun a : Fin 3 → ℕ => ∏ k : Fin 3, a k = g) with hA
  -- membership in the set of factorisations of `g`
  have memA : ∀ a : Fin 3 → ℕ, a ∈ A ↔ (∏ k : Fin 3, a k = g) ∧ ∀ k : Fin 3, a k ∣ g := by
    intro a
    rw [hA, Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun k => (Nat.mem_divisors.mp (h1 k)).1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun k => Nat.mem_divisors.mpr ⟨h2 k, hg.ne'⟩, h1⟩
  -- expansion of one product of coordinate sums into a sum over the product of the filters
  have hexp : ∀ a : Fin 3 → ℕ,
      (∏ k : Fin 3, ∑ y ∈ T a k, F k y)
        = ∑ b ∈ Fintype.piFinset (T a), ∏ k : Fin 3, F k (b k) := by
    intro a
    exact Finset.prod_univ_sum (T a) F
  -- the product of the filters is the box cut down by the divisibility conditions
  have hset : ∀ a : Fin 3 → ℕ,
      Fintype.piFinset (T a)
        = (box3 H).filter
            (fun b : Fin 3 → ℕ => ∀ k : Fin 3, b k ≠ α ∧ a k ∣ Work.LinnikBurgess.del α (b k)) := by
    intro a
    ext b
    simp only [Fintype.mem_piFinset, Finset.mem_filter, box3, hT, Finset.mem_Icc, forall_and]
  have hinner : ∀ a : Fin 3 → ℕ,
      (∑ b ∈ Fintype.piFinset (T a), ∏ k : Fin 3, F k (b k))
        = ∑ b ∈ box3 H, (if ∀ k : Fin 3, b k ≠ α ∧ a k ∣ Work.LinnikBurgess.del α (b k)
            then ∏ k : Fin 3, F k (b k) else 0) := by
    intro a
    rw [hset a, Finset.sum_filter]
  -- pointwise bound: every admissible `b` contributes through at least one factorisation
  have key : ∀ b ∈ box3 H,
      (if g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del α (b k) then
          ∏ k : Fin 3, (if b k ≠ α then F k (b k) else 0) else 0)
        ≤ ∑ a ∈ A, (if ∀ k : Fin 3, b k ≠ α ∧ a k ∣ Work.LinnikBurgess.del α (b k)
            then ∏ k : Fin 3, F k (b k) else 0) := by
    intro b _
    have hnn : ∀ a : Fin 3 → ℕ, 0 ≤ (if ∀ k : Fin 3, b k ≠ α ∧ a k ∣ Work.LinnikBurgess.del α (b k)
            then ∏ k : Fin 3, F k (b k) else 0) := by
      intro a
      by_cases h : ∀ k : Fin 3, b k ≠ α ∧ a k ∣ Work.LinnikBurgess.del α (b k)
      · rw [if_pos h]; exact Finset.prod_nonneg (fun k _ => hF k _)
      · rw [if_neg h]
    by_cases hgd : g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del α (b k)
    · rw [if_pos hgd]
      by_cases hper : ∀ k : Fin 3, b k ≠ α
      · -- all coordinates avoid `α`: split `g` along a factorisation adapted to `b`
        obtain ⟨a0, hprod, hdvd⟩ :=
          exists_fin3_decomp hg (fun k => Work.LinnikBurgess.del α (b k)) hgd
        have ha0A : a0 ∈ A := by
          rw [memA]
          exact ⟨hprod, fun k => hprod ▸ Finset.dvd_prod_of_mem a0 (Finset.mem_univ k)⟩
        have hprod0 : (∏ k : Fin 3, (if b k ≠ α then F k (b k) else 0))
            = ∏ k : Fin 3, F k (b k) :=
          Finset.prod_congr rfl (fun k _ => if_pos (hper k))
        rw [hprod0]
        refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun a _ => hnn a) ha0A)
        exact (if_pos (fun k => ⟨hper k, hdvd k⟩)).symm
      · -- some coordinate equals `α`, so the left-hand term vanishes
        obtain ⟨k0, hk0⟩ : ∃ k : Fin 3, b k = α := by
          by_contra h
          exact hper (fun k hk => h ⟨k, hk⟩)
        have hzero : (∏ k : Fin 3, (if b k ≠ α then F k (b k) else 0)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k0)
            (if_neg (by simp [hk0]))
        rw [hzero]
        exact Finset.sum_nonneg (fun a _ => hnn a)
    · rw [if_neg hgd]
      exact Finset.sum_nonneg (fun a _ => hnn a)
  calc (∑ b ∈ box3 H, (if g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del α (b k) then
        ∏ k : Fin 3, (if b k ≠ α then F k (b k) else 0) else 0))
      ≤ ∑ b ∈ box3 H, ∑ a ∈ A, (if ∀ k : Fin 3, b k ≠ α ∧ a k ∣ Work.LinnikBurgess.del α (b k)
            then ∏ k : Fin 3, F k (b k) else 0) := Finset.sum_le_sum key
    _ = ∑ a ∈ A, ∑ b ∈ box3 H, (if ∀ k : Fin 3, b k ≠ α ∧ a k ∣ Work.LinnikBurgess.del α (b k)
            then ∏ k : Fin 3, F k (b k) else 0) := Finset.sum_comm
    _ = ∑ a ∈ A, ∑ b ∈ Fintype.piFinset (T a), ∏ k : Fin 3, F k (b k) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        exact (hinner a).symm
    _ = ∑ a ∈ A, ∏ k : Fin 3, ∑ y ∈ T a k, F k y := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        exact (hexp a).symm
    _ = ∑ a ∈ (Fintype.piFinset (fun _ : Fin 3 => g.divisors)).filter
            (fun a : Fin 3 → ℕ => ∏ k : Fin 3, a k = g),
          ∏ k : Fin 3, ∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ α ∧ a k ∣ Work.LinnikBurgess.del α y),
            F k y := by
        rw [hA, hT]

end Work.LinnikBurgess.frame_count_prov_aux
