/-
# The raw two-dimensional dyadic family is dominated by the tiling family

The raw family `rawLp2 r K m₁ m₂ a` is the `ℓ ^ r` norm of the increments of the dyadic telescope
in the second coordinate, `rawH2 a m₁ m₂ k₁ k₂ = a (2 ^ m₁ k₁) (2 ^ m₂ k₂)
- a (2 ^ m₁ (k₁ - k₁ % 2)) (2 ^ m₂ k₂) - a (2 ^ m₁ k₁) (2 ^ m₂ (k₂ - k₂ % 2))
+ a (2 ^ m₁ (k₁ - k₁ % 2)) (2 ^ m₂ (k₂ - k₂ % 2))`.  As in one dimension
(`Work.Analysis.Variation.rawLp_le_incLp`), every nonzero value occurs for `k₁` and `k₂` odd, and
is then the second difference over the full aligned rectangle with lower-left corner
`(2 ^ m₁ (k₁ - 1), 2 ^ m₂ (k₂ - 1))`, a rectangle of the tiling family of side lengths
`2 ^ m₁, 2 ^ m₂` covering `(0, K] × (0, K]` (up to the truncation of the last block).  Hence the
raw `ℓ ^ r` sum is at most the tiling `ℓ ^ r` sum, and the claim follows by monotonicity of
`y ↦ y ^ (1 / r)`.
-/
import Mathlib
import Submission.Work.Analysis.Variation.RawFamily

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Variation

/-! ## Parity of the raw two-dimensional increment -/

/-- A raw two-dimensional increment `rawH2 a m₁ m₂ k₁ k₂` vanishes as soon as one of the indices
`k₁`, `k₂` is even: the block `(2 ^ m k - 2 ^ m (k % 2), 2 ^ m k]` in that coordinate is then
empty. -/
lemma rawH2_eq_zero_of_even (a : ℕ → ℕ → ℂ) (m₁ m₂ k₁ k₂ : ℕ)
    (h : k₁ % 2 = 0 ∨ k₂ % 2 = 0) : rawH2 a m₁ m₂ k₁ k₂ = 0 := by
  unfold rawH2
  rcases h with h | h
  · have e : k₁ - k₁ % 2 = k₁ := by omega
    rw [e]
    ring
  · have e : k₂ - k₂ % 2 = k₂ := by omega
    rw [e]
    ring

/-- For odd `k₁`, `k₂` with `2 ^ m₁ * k₁ ≤ K` and `2 ^ m₂ * k₂ ≤ K`, the raw two-dimensional
increment is the second difference over the rectangle with lower-left corner
`(2 ^ m₁ * (k₁ - 1), 2 ^ m₂ * (k₂ - 1))` and side lengths `2 ^ m₁`, `2 ^ m₂`. -/
lemma rawH2_eq_blockDelta2 (a : ℕ → ℕ → ℂ) (K m₁ m₂ k₁ k₂ : ℕ)
    (hk₁ : k₁ % 2 = 1) (hk₂ : k₂ % 2 = 1)
    (hK₁ : 2 ^ m₁ * k₁ ≤ K) (hK₂ : 2 ^ m₂ * k₂ ≤ K) :
    rawH2 a m₁ m₂ k₁ k₂
      = blockDelta2 a K (2 ^ m₁) (2 ^ m₁ * (k₁ - 1)) (2 ^ m₂) (2 ^ m₂ * (k₂ - 1)) := by
  unfold rawH2 blockDelta2
  have e₁ : k₁ - k₁ % 2 = k₁ - 1 := by omega
  have e₂ : k₂ - k₂ % 2 = k₂ - 1 := by omega
  have s₁ : 2 ^ m₁ * (k₁ - 1) + 2 ^ m₁ = 2 ^ m₁ * k₁ := by
    have h : k₁ - 1 + 1 = k₁ := by omega
    calc 2 ^ m₁ * (k₁ - 1) + 2 ^ m₁ = 2 ^ m₁ * (k₁ - 1 + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
      _ = 2 ^ m₁ * k₁ := by rw [h]
  have s₂ : 2 ^ m₂ * (k₂ - 1) + 2 ^ m₂ = 2 ^ m₂ * k₂ := by
    have h : k₂ - 1 + 1 = k₂ := by omega
    calc 2 ^ m₂ * (k₂ - 1) + 2 ^ m₂ = 2 ^ m₂ * (k₂ - 1 + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
      _ = 2 ^ m₂ * k₂ := by rw [h]
  rw [e₁, e₂, s₁, s₂, min_eq_left hK₁, min_eq_left hK₂]

/-- An odd `k ≤ K / M` has `k - 1 < nb K M`, i.e. `k` is the right end of the block of the
tiling family of size `M` with index `k - 1`. -/
lemma odd_sub_one_lt_nb (K M k : ℕ) (hM : 0 < M) (hk : k ≤ K / M) (hmod : k % 2 = 1) :
    k - 1 < nb K M := by
  have hle : K / M ≤ (K + M - 1) / M := Nat.div_le_div_right (by omega)
  unfold nb
  omega

/-! ## Shifting a finite sum along an injective index map -/

/-- If `O ⊆ S`, the terms of `f` outside `O` vanish, `φ` is injective on `O`, `φ` maps `O` into
`T`, and `f q = g (φ q)` on `O`, then `∑_{q ∈ S} f q ≤ ∑_{p ∈ T} g p`.  This is the abstract form
of the reindexing that turns the raw dyadic family into the tiling family. -/
lemma sum_le_sum_of_shift {ι M : Type*} [DecidableEq ι] [AddCommMonoid M] [Preorder M]
    [CanonicallyOrderedAdd M] {S T O : Finset ι} {φ : ι → ι} {f g : ι → M}
    (hOS : O ⊆ S) (hf : ∀ q ∈ S, q ∉ O → f q = 0) (hinj : Set.InjOn φ ↑O)
    (hmap : Finset.image φ O ⊆ T) (hfg : ∀ q ∈ O, f q = g (φ q)) :
    ∑ q ∈ S, f q ≤ ∑ p ∈ T, g p := by
  calc ∑ q ∈ S, f q = ∑ q ∈ O, f q := (Finset.sum_subset hOS hf).symm
    _ = ∑ q ∈ O, g (φ q) := Finset.sum_congr rfl hfg
    _ = ∑ p ∈ Finset.image φ O, g p := (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ T, g p := Finset.sum_le_sum_of_subset hmap

/-- Two-dimensional analogue of `rawLp_le_incLp`: the raw two-dimensional family at scales
`(2^m₁, 2^m₂)` is dominated by the family of second differences over the rectangles of side
lengths `2^m₁, 2^m₂` tiling `(0,K]²`.  A nonzero raw value has both `k₁`, `k₂` odd, and equals
`blockDelta2 a K (2^m₁) (2^m₁ * (k₁-1)) (2^m₂) (2^m₂ * (k₂-1))`, the general term of the tiling
family at the grid point `(k₁-1, k₂-1)`. -/
theorem rawLp2_le_incLp2 {r : ℝ} (hr : 0 < r) (K m₁ m₂ : ℕ) (a : ℕ → ℕ → ℂ) :
    rawLp2 r K m₁ m₂ a ≤ incLp2 r K (2 ^ m₁) (2 ^ m₂) a := by
  classical
  have hpow₁ : 0 < 2 ^ m₁ := by positivity
  have hpow₂ : 0 < 2 ^ m₂ := by positivity
  unfold rawLp2 incLp2
  refine ENNReal.rpow_le_rpow ?_ (div_nonneg zero_le_one hr.le)
  refine sum_le_sum_of_shift
    (S := (Finset.range (K / 2 ^ m₁ + 1)).product (Finset.range (K / 2 ^ m₂ + 1)))
    (T := (Finset.range (nb K (2 ^ m₁))).product (Finset.range (nb K (2 ^ m₂))))
    (O := ((Finset.range (K / 2 ^ m₁ + 1)).product (Finset.range (K / 2 ^ m₂ + 1))).filter
      (fun q => q.1 % 2 = 1 ∧ q.2 % 2 = 1))
    (φ := fun q : ℕ × ℕ => (q.1 - 1, q.2 - 1))
    (f := fun q => ‖rawH2 a m₁ m₂ q.1 q.2‖ₑ ^ r)
    (g := fun p => ‖blockDelta2 a K (2 ^ m₁) (2 ^ m₁ * p.1) (2 ^ m₂) (2 ^ m₂ * p.2)‖ₑ ^ r)
    (Finset.filter_subset _ _) ?_ ?_ ?_ ?_
  · -- off the odd pairs the raw term vanishes
    intro q hqS hqO
    have hpar : q.1 % 2 = 0 ∨ q.2 % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one q.1 with h1 | h1
      · exact Or.inl h1
      · rcases Nat.mod_two_eq_zero_or_one q.2 with h2 | h2
        · exact Or.inr h2
        · exact absurd ⟨h1, h2⟩ fun hcon => hqO (Finset.mem_filter.mpr ⟨hqS, hcon⟩)
    show ‖rawH2 a m₁ m₂ q.1 q.2‖ₑ ^ r = 0
    rw [rawH2_eq_zero_of_even a m₁ m₂ q.1 q.2 hpar, enorm_zero,
      ENNReal.zero_rpow_of_pos hr]
  · -- the shift `(k₁, k₂) ↦ (k₁ - 1, k₂ - 1)` is injective on the odd pairs
    intro q hq q' hq' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1e, h2e⟩ := heq
    have hqodd := (Finset.mem_filter.mp hq).2
    have hq'odd := (Finset.mem_filter.mp hq').2
    exact Prod.ext (by omega) (by omega)
  · -- the shifted pairs lie in the tiling index set
    intro p hp
    obtain ⟨q, hqO, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqS, hqodd⟩ := Finset.mem_filter.mp hqO
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hqS
    have hle₁ : q.1 ≤ K / 2 ^ m₁ := by
      have := Finset.mem_range.mp hq₁; omega
    have hle₂ : q.2 ≤ K / 2 ^ m₂ := by
      have := Finset.mem_range.mp hq₂; omega
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩
    · exact odd_sub_one_lt_nb K (2 ^ m₁) q.1 hpow₁ hle₁ hqodd.1
    · exact odd_sub_one_lt_nb K (2 ^ m₂) q.2 hpow₂ hle₂ hqodd.2
  · -- on the odd pairs the raw term is the shifted tiling term
    intro q hq
    obtain ⟨hqS, hqodd⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hqS
    have hle₁ : q.1 ≤ K / 2 ^ m₁ := by
      have := Finset.mem_range.mp hq₁; omega
    have hle₂ : q.2 ≤ K / 2 ^ m₂ := by
      have := Finset.mem_range.mp hq₂; omega
    have hk₁ : 2 ^ m₁ * q.1 ≤ K :=
      (Nat.mul_le_mul (Nat.le_refl _) hle₁).trans (Nat.mul_div_le K (2 ^ m₁))
    have hk₂ : 2 ^ m₂ * q.2 ≤ K :=
      (Nat.mul_le_mul (Nat.le_refl _) hle₂).trans (Nat.mul_div_le K (2 ^ m₂))
    show ‖rawH2 a m₁ m₂ q.1 q.2‖ₑ ^ r
      = ‖blockDelta2 a K (2 ^ m₁) (2 ^ m₁ * (q.1 - 1)) (2 ^ m₂)
          (2 ^ m₂ * (q.2 - 1))‖ₑ ^ r
    rw [rawH2_eq_blockDelta2 a K m₁ m₂ q.1 q.2 hqodd.1 hqodd.2 hk₁ hk₂]

end Work.Analysis.Variation
