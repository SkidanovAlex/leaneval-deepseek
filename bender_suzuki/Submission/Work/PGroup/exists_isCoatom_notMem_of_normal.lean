import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A maximal subgroup avoiding an element outside a suitable normal subgroup

Let `H` be a finite group, `N ⊴ H` a normal subgroup such that `H / N` is abelian
(`⁅⊤, ⊤⁆ ≤ N`) of exponent dividing a prime `p` (`∀ x, x ^ p ∈ N`).  Then for every `x ∉ N`
there is a maximal subgroup `M < H` (a coatom of the subgroup lattice) with `x ∉ M`.

The proof goes through the abelian quotient `Q = H / N`, which is a finite abelian group of
exponent dividing `p`, i.e. an `𝔽_p`-vector space.  A linear functional `f : Q → 𝔽_p` with
`f (xN) = 1` produces a group homomorphism `g : Q →* Multiplicative (ZMod p)`; its kernel has
index `p` in `Q` and does not contain `xN`.  Pulling this subgroup back along the quotient map
`H →* Q` yields a subgroup `M ≤ H` of index `p` not containing `x`, and a subgroup of prime
index is a coatom.
-/

namespace Work.PGroup

open scoped Classical Pointwise
open scoped IsMulCommutative
open Subgroup

/-- A subgroup of a group with prime index is a coatom of the subgroup lattice. -/
theorem isCoatom_of_index_eq_prime {H : Type*} [Group H] {M : Subgroup H} {p : ℕ}
    (hp : p.Prime) (h : M.index = p) : IsCoatom M := by
  refine ⟨?_, ?_⟩
  · intro htop
    rw [htop, Subgroup.index_top] at h
    exact hp.ne_one h.symm
  · intro b hb
    have hle : M ≤ b := le_of_lt hb
    have hne : M ≠ b := ne_of_lt hb
    have hmul : M.relIndex b * b.index = p := by
      rw [Subgroup.relIndex_mul_index hle, h]
    have hri_ne1 : M.relIndex b ≠ 1 := by
      intro h1
      exact hne (hle.antisymm (Subgroup.relIndex_eq_one.mp h1))
    have hri_eq : M.relIndex b = p := by
      rcases hp.eq_one_or_self_of_dvd _ (hmul ▸ dvd_mul_right _ _) with h1 | h1
      · exact absurd h1 hri_ne1
      · exact h1
    have hb1 : b.index = 1 := by
      rw [hri_eq] at hmul
      exact Nat.eq_of_mul_eq_mul_left hp.pos (hmul.trans (mul_one p).symm)
    exact Subgroup.index_eq_one.mp hb1

/-- For a finite abelian group `Q` (written with `IsMulCommutative`) of exponent dividing a prime
`p` and an element `xq ≠ 1`, there is a group homomorphism `g : Q →* Multiplicative (ZMod p)`
which is nonzero at `xq` and whose kernel has index `p`. -/
theorem exists_monoidHom_zmod_ker_index {Q : Type*} [Group Q] [IsMulCommutative Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hexp : Monoid.exponent Q ∣ p) {xq : Q} (hxq : xq ≠ 1) :
    ∃ g : Q →* Multiplicative (ZMod p), g xq ≠ 1 ∧ g.ker.index = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpowQ : ∀ y : Q, y ^ p = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp
  -- `Additive Q` is a `ZMod p`-module because `p • a = 0` for all `a`.
  have hsmul : ∀ a : Additive Q, p • a = 0 := by
    intro a
    obtain ⟨y, rfl⟩ := Additive.ofMul.surjective a
    rw [(ofMul_pow p y).symm, hpowQ y, ofMul_one]
  haveI hmod : Module (ZMod p) (Additive Q) := AddCommGroup.zmodModule hsmul
  haveI hfree : Module.Free (ZMod p) (Additive Q) :=
    Module.Free.of_divisionRing (ZMod p) (Additive Q)
  haveI hproj : Module.Projective (ZMod p) (Additive Q) :=
    @Module.Projective.of_free (ZMod p) _ (Additive Q) _ _ hfree
  have hx0 : Additive.ofMul xq ≠ 0 := by
    intro h
    exact hxq (by simpa using h)
  -- A linear functional taking the value `1` at `xq`.
  obtain ⟨f, hf⟩ :=
    @Module.Projective.exists_dual_eq_one (Additive Q) _ (ZMod p) _ _ hproj _ hx0
  let g : Q →* Multiplicative (ZMod p) :=
  { toFun := fun q => Multiplicative.ofAdd (f (Additive.ofMul q))
    map_one' := by
      show Multiplicative.ofAdd (f (Additive.ofMul 1)) = 1
      rw [ofMul_one, map_zero]; rfl
    map_mul' := fun a b => by
      change Multiplicative.ofAdd (f (Additive.ofMul a + Additive.ofMul b)) =
        Multiplicative.ofAdd (f (Additive.ofMul a)) * Multiplicative.ofAdd (f (Additive.ofMul b))
      rw [map_add]; rfl }
  have hgx : g xq = Multiplicative.ofAdd 1 := by
    show Multiplicative.ofAdd (f (Additive.ofMul xq)) = Multiplicative.ofAdd 1
    rw [hf]
  refine ⟨g, ?_, ?_⟩
  · rw [hgx]
    intro h
    exact one_ne_zero (Multiplicative.ofAdd.injective h)
  · have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [← Nat.card_congr (Multiplicative.ofAdd (α := ZMod p)), Nat.card_eq_fintype_card,
        ZMod.card]
    have hgen : Multiplicative.ofAdd (1 : ZMod p) ≠ 1 := by
      intro h
      exact one_ne_zero (Multiplicative.ofAdd.injective h)
    have hgran : g.range = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← zpowers_eq_top_of_prime_card hcard hgen, Subgroup.zpowers_le]
      exact MonoidHom.mem_range.mpr ⟨xq, hgx⟩
    rw [Subgroup.index_ker, hgran, Subgroup.card_top, hcard]

theorem exists_isCoatom_notMem_of_normal {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (N : Subgroup H) [N.Normal] (hcomm : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ N)
    (hpow : ∀ x : H, x ^ p ∈ N) {x : H} (hx : x ∉ N) :
    ∃ M : Subgroup H, IsCoatom M ∧ x ∉ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Q := H ⧸ N
  haveI hQcomm : IsMulCommutative Q :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let xq : Q := QuotientGroup.mk' N x
  have hxq : xq ≠ 1 := by
    intro h
    exact hx (QuotientGroup.eq_one_iff x |>.mp h)
  have hexp : Monoid.exponent Q ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hpow g
  obtain ⟨g, hgx, hgidx⟩ := exists_monoidHom_zmod_ker_index hp hexp hxq
  refine ⟨g.ker.comap (QuotientGroup.mk' N), ?_, ?_⟩
  · apply isCoatom_of_index_eq_prime hp
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]
    exact hgidx
  · intro hmem
    rw [Subgroup.mem_comap] at hmem
    exact hgx (by rwa [show (QuotientGroup.mk' N) x = xq from rfl] at hmem)

end Work.PGroup
