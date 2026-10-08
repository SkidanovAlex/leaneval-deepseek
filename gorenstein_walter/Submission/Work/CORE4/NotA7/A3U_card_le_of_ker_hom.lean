import Mathlib

namespace Work.CORE4.NotA7

/-- **A3`U` cardinal bound from a homomorphism.**

Let `π : M →* T` be a homomorphism whose kernel is `F` (more precisely `F.subgroupOf M`),
and suppose every subgroup of `T` of odd order has order at most `21`.  Then for every
subgroup `X ≤ M` of odd order,
`|X| ≤ 21 * |X ⊓ F|`.

Indeed `π` restricts to a homomorphism `X →* T` whose kernel is `X ⊓ F`; the first
isomorphism theorem gives `|X| = |π(X)| * |X ⊓ F|` and `π(X)` is an odd-order subgroup
of `T`, hence `|π(X)| ≤ 21`. -/
theorem A3U_card_le_of_ker_hom {G T : Type} [Group G] [Group T] [Finite G] [Finite T]
    {M F : Subgroup G} (π : ↥M →* T) (hker : π.ker = F.subgroupOf M)
    (h21 : ∀ Y : Subgroup T, Odd (Nat.card Y) → Nat.card Y ≤ 21)
    (X : Subgroup G) (hXM : X ≤ M) (hXodd : Odd (Nat.card X)) :
    Nat.card X ≤ 21 * Nat.card (X ⊓ F : Subgroup G) := by
  -- The restricted homomorphism `φ : X →* T` and its kernel.
  let φ : ↥X →* T := π.comp (Subgroup.inclusion hXM)
  have key : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ X ⊓ F := by
    intro x
    rw [Subgroup.mem_inf]
    constructor
    · intro h
      have hmem : Subgroup.inclusion hXM x ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        simpa only [φ, MonoidHom.comp_apply] using h
      rw [hker, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at hmem
      exact ⟨x.2, hmem⟩
    · rintro ⟨_hx, hF⟩
      have hmem : Subgroup.inclusion hXM x ∈ π.ker := by
        rw [hker, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
        exact hF
      rw [MonoidHom.mem_ker] at hmem
      simpa only [φ, MonoidHom.comp_apply] using hmem
  have hkerφ : φ.ker = (X ⊓ F).subgroupOf X := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact key x
  -- First isomorphism theorem: `|X| = |range φ| * |ker φ|`.
  have hcard : Nat.card X = Nat.card φ.range * Nat.card (X ⊓ F : Subgroup G) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (φ.ker)
    have h2 : Nat.card (↥X ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have h3 : Nat.card φ.ker = Nat.card (X ⊓ F : Subgroup G) := by
      rw [hkerφ]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : X ⊓ F ≤ X)).toEquiv
    rw [h2, h3] at h1
    exact h1
  -- `range φ` is an odd-order subgroup of `T`.
  have hoddrange : Odd (Nat.card φ.range) := by
    have hodd' := hXodd
    rw [hcard] at hodd'
    exact Nat.Odd.of_mul_left hodd'
  rw [hcard]
  exact Nat.mul_le_mul_right _ (h21 φ.range hoddrange)

end Work.CORE4.NotA7
