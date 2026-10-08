import Mathlib
import Submission.Work.GlaubermanZJ.Thm41.PComm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Iterated commutators `[H, K; k]`

Glauberman writes `[H,K;k]` for the `k`-fold left-normed commutator `[[[H,K],K],…,K]`
(`k` copies of `K`), with `[H,K;0] = H`.  This file fixes that vocabulary (`iterComm`) and proves
the elementary properties used in the proof of Glauberman's Theorem 4.1: monotonicity, the
comparison with the lower central series, and the vanishing of `[H,K;k]` for large `k` in a
nilpotent group.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-- `iterComm H K k = [H,K;k]`, the `k`-fold left-normed commutator of `H` with `K`. -/
def iterComm (H K : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => ⁅iterComm H K n, K⁆

@[simp]
theorem iterComm_zero (H K : Subgroup G) : iterComm H K 0 = H := rfl

theorem iterComm_succ (H K : Subgroup G) (n : ℕ) :
    iterComm H K (n + 1) = ⁅iterComm H K n, K⁆ := rfl

theorem iterComm_one (H K : Subgroup G) : iterComm H K 1 = ⁅H, K⁆ := rfl

/-- `K` normalizes every term `[H,K;k]` of the iterated commutator series, when `K` normalizes
`H`.  (Each term is normalized by `K` by construction.) -/
theorem iterComm_normalizer (H K : Subgroup G) (h : K ≤ Subgroup.normalizer (H : Set G)) :
    ∀ n, K ≤ Subgroup.normalizer (iterComm H K n : Set G) := by
  intro n
  cases n with
  | zero => exact h
  | succ n => rw [iterComm_succ]; exact Subgroup.normalizer_commutator_ge_right _ K

/-- Consecutive terms of the iterated commutator series are nested: `[H,K;k+1] ≤ [H,K;k]`
when `K` normalizes `H`. -/
theorem iterComm_antitone (H K : Subgroup G) (h : K ≤ Subgroup.normalizer (H : Set G)) :
    ∀ n, iterComm H K (n + 1) ≤ iterComm H K n := by
  intro n
  rw [iterComm_succ]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp (iterComm_normalizer H K h n)

/-- `[H,K;k]` is antitone in `k` for `k ≥ 0`. -/
theorem iterComm_le_of_le (H K : Subgroup G) (h : K ≤ Subgroup.normalizer (H : Set G))
    {m n : ℕ} (hmn : m ≤ n) : iterComm H K n ≤ iterComm H K m := by
  induction hmn with
  | refl => exact le_rfl
  | step hmn ih => exact (iterComm_antitone H K h _).trans ih

/-- `[H,K;k] ≤ H` when `K` normalizes `H`. -/
theorem iterComm_le (H K : Subgroup G) (h : K ≤ Subgroup.normalizer (H : Set G)) (n : ℕ) :
    iterComm H K n ≤ H :=
  (iterComm_le_of_le H K h (Nat.zero_le n)).trans_eq (iterComm_zero H K)

/-- Adding exponents: `[[H,K;m],K;n] = [H,K;m+n]`. -/
theorem iterComm_iterComm (H K : Subgroup G) (m n : ℕ) :
    iterComm (iterComm H K m) K n = iterComm H K (m + n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterComm_succ, ih, Nat.add_succ, iterComm_succ]

/-- The iterated commutators are monotone in both arguments. -/
theorem iterComm_mono {H₁ H₂ K₁ K₂ : Subgroup G} (hH : H₁ ≤ H₂) (hK : K₁ ≤ K₂) :
    ∀ n, iterComm H₁ K₁ n ≤ iterComm H₂ K₂ n := by
  intro n
  induction n with
  | zero => exact hH
  | succ n ih => rw [iterComm_succ, iterComm_succ]; exact Subgroup.commutator_mono ih hK

/-- `[H,K;k] ≤ γ_k(H)` (the lower central series of `H`), for `K ≤ H`. -/
theorem iterComm_le_lowerCentralSeries (H K : Subgroup G) (hKH : K ≤ H) :
    ∀ n, iterComm H K n ≤ H.lowerCentralSeries n := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [iterComm_succ, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mono ih hKH

/-- If `[H,K;N] = ⊥` then `[H,K;n] = ⊥` for all `n ≥ N`. -/
theorem iterComm_eq_bot_of_le {H K : Subgroup G} (h : K ≤ Subgroup.normalizer (H : Set G))
    {N : ℕ} (hN : iterComm H K N = ⊥) {n : ℕ} (hn : N ≤ n) : iterComm H K n = ⊥ :=
  le_bot_iff.mp (hN ▸ iterComm_le_of_le H K h hn)

/-- For a nilpotent group `H` and `K ≤ H`, the iterated commutators `[H,K;k]` vanish for large
`k`. -/
theorem exists_iterComm_eq_bot (H K : Subgroup G) (hKH : K ≤ H)
    (hnil : Group.IsNilpotent ↥H) : ∃ N, iterComm H K N = ⊥ := by
  obtain ⟨N, hN⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries H).mp hnil
  exact ⟨N, le_bot_iff.mp ((iterComm_le_lowerCentralSeries H K hKH N).trans_eq hN)⟩

end Work.GlaubermanZJ
