import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option linter.unusedVariables false

open Finset

namespace Commons.Combinatorics.Transference

/-- Weighted sums over the blocks of a partition.

Let `S` be a finite set and `b : X → Finset X` a "block" map whose blocks
`b y` (for `y ∈ S`) cover `S`, each contains `y`, and are constant along
themselves (`z ∈ b y → b z = b y`).  Then each block `B` is counted exactly
`|B|` times in the sum, and since the weight attached to the block
containing `y` is `|b y|⁻¹`, the weighted sum over the blocks collapses to the
plain sum over `S`. -/
lemma sum_block_weighted {X : Type*} [DecidableEq X] {S : Finset X}
    (b : X → Finset X) (hb_sub : ∀ y ∈ S, b y ⊆ S)
    (hb_mem : ∀ y ∈ S, y ∈ b y)
    (hb_eq : ∀ y ∈ S, ∀ z ∈ b y, b z = b y)
    (g : X → ℝ) :
    ∑ y ∈ S, ((b y).card : ℝ)⁻¹ * ∑ z ∈ b y, g z = ∑ z ∈ S, g z := by
  classical
  -- Distinct blocks are disjoint.
  have hdisj : Set.PairwiseDisjoint (↑(S.image b)) (fun B : Finset X => B) := by
    intro B hB B' hB' hne
    simp only [Finset.mem_coe, Finset.mem_image] at hB hB'
    obtain ⟨y, hy, rfl⟩ := hB
    obtain ⟨y', hy', rfl⟩ := hB'
    change Disjoint (b y) (b y')
    rw [Finset.disjoint_left]
    intro k hk hk'
    exact hne ((hb_eq y hy k hk).symm.trans (hb_eq y' hy' k hk'))
  -- The blocks cover `S`.
  have hbiUnion : (S.image b).biUnion (fun B => B) = S := by
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨B, ⟨y, hy, rfl⟩, hz⟩
      exact hb_sub y hy hz
    · intro hz
      exact ⟨b z, ⟨z, hz, rfl⟩, hb_mem z hz⟩
  -- On a block `B = b y₀` every term equals the block average.
  have h2 : ∀ B ∈ S.image b,
      ∑ y ∈ B, ((b y).card : ℝ)⁻¹ * ∑ z ∈ b y, g z = ∑ y ∈ B, g y := by
    intro B hB
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hB
    have hcard_ne : ((b y₀).card : ℝ) ≠ 0 := by
      have : 0 < (b y₀).card := Finset.card_pos.mpr ⟨y₀, hb_mem y₀ hy₀⟩
      exact_mod_cast this.ne'
    have hconst : ∀ y ∈ b y₀, ((b y).card : ℝ)⁻¹ * ∑ z ∈ b y, g z
        = ((b y₀).card : ℝ)⁻¹ * ∑ z ∈ b y₀, g z := by
      intro y hy
      rw [hb_eq y₀ hy₀ y hy]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hcard_ne, one_mul]
  calc ∑ y ∈ S, ((b y).card : ℝ)⁻¹ * ∑ z ∈ b y, g z
      = ∑ B ∈ S.image b, ∑ y ∈ B, ((b y).card : ℝ)⁻¹ * ∑ z ∈ b y, g z := by
        rw [← Finset.sum_biUnion hdisj
              (f := fun y => ((b y).card : ℝ)⁻¹ * ∑ z ∈ b y, g z), hbiUnion]
    _ = ∑ B ∈ S.image b, ∑ y ∈ B, g y := Finset.sum_congr rfl h2
    _ = ∑ z ∈ S, g z := by
        rw [← Finset.sum_biUnion hdisj (f := g), hbiUnion]

/-- Tower property of conditional expectation for two partitions.

`P` and `Q` present two partitions of `X` (via their containing-block maps),
and `Q` refines `P`.  Then averaging `f` over the `Q`-blocks and then over the
`P`-blocks is the same as averaging `f` over the `P`-blocks directly. -/
theorem condExp_tower {X : Type*} [Fintype X] [DecidableEq X] (P Q : X → Finset X)
    (hPmem : ∀ x, x ∈ P x) (hPeq : ∀ x y : X, y ∈ P x → P y = P x)
    (hQmem : ∀ x, x ∈ Q x) (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x)
    (href : ∀ x, Q x ⊆ P x) (f : X → ℝ) :
    (fun x => ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, ((Q y).card : ℝ)⁻¹ * ∑ z ∈ Q y, f z)
      = fun x => ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y := by
  funext x
  show ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, ((Q y).card : ℝ)⁻¹ * ∑ z ∈ Q y, f z
      = ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y
  congr 1
  exact sum_block_weighted Q
    (fun y hy => by rw [← hPeq x y hy]; exact href y)
    (fun y _ => hQmem y)
    (fun y _ z hz => hQeq y z hz) f

end Commons.Combinatorics.Transference