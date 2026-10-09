import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
import Submission.NK.RamificationDeep.ramificationSubgroup_inf_fixingSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.RamificationDeep

/-! ### A cardinality lemma for images of subgroups

For a group homomorphism `f : G →* N` and a subgroup `S ≤ G`, the restriction of `f` to `S` has
image `S.map f` and kernel `S ⊓ f.ker`, so by the first isomorphism theorem

  `Nat.card ↥S = Nat.card ↥(S.map f) * Nat.card ↥(S ⊓ f.ker)`.

This is the counting form of the exact sequence `1 → S ⊓ f.ker → S → S.map f → 1`, used below to
recover the multiplicative behaviour of the lower indices `g_i = #G_i` from the classical index
identity `π(G_n(L/K)) = G_{⌊φ_{L/M}(n)⌋}(M/K)`. -/
theorem natCard_eq_card_map_mul_card_inf_ker {G N : Type*} [Group G] [Group N]
    (f : G →* N) (S : Subgroup G) :
    Nat.card ↥S = Nat.card ↥(S.map f) * Nat.card ↥(S ⊓ f.ker) := by
  let g : ↥S →* N := f.comp S.subtype
  have hker : g.ker = (S ⊓ f.ker).subgroupOf S := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hrange : g.range = S.map f := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have h1 : Nat.card ↥S = Nat.card (↥S ⧸ g.ker) * Nat.card ↥g.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  have h2 : Nat.card (↥S ⧸ g.ker) = Nat.card ↥g.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have h3 : Nat.card ↥((S ⊓ f.ker).subgroupOf S) = Nat.card ↥(S ⊓ f.ker) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := S ⊓ f.ker) (K := S) inf_le_left).toEquiv
  rw [h1, h2, hrange, hker, h3]

/-- **Multiplicativity of the lower indices from the index identity, in image form.**

Let `K ⊆ M ⊆ L`, `L/K` and `M/K` Galois with `A : ValuationSubring L` a discrete valuation ring
whose decomposition subgroup in `Gal(L/K)` is all of `Gal(L/K)`.  `H` is the classical *index
identity* in its subgroup form: the image of the lower ramification subgroup `G_n(L/K)` in
`Gal(M/K)` (under `AlgEquiv.restrictNormalHom`) is the lower ramification subgroup
`G_{⌊φ_{L/M}(n)⌋}(M/K)` of the extension `M/K` with valuation ring `A ∩ M`.

Then the lower indices multiply across the tower:

  `g_n(L/K) = g_n(L/M) · g_{⌊φ_{L/M}(n)⌋}(M/K)`.

The proof is the counting argument of the roadmap: `G_n(L/K) → π(G_n(L/K))` has kernel
`G_n(L/K) ∩ Gal(L/M) = G_n(L/M)` (`ramificationSubgroup_inf_fixingSubgroup`), so
`#G_n(L/K) = #G_n(L/M) · #π(G_n(L/K))` by `natCard_eq_card_map_mul_card_inf_ker`, and `H`
evaluates the second factor as `g_{⌊φ_{L/M}(n)⌋}(M/K)`. -/
theorem lowerIndex_eq_mul_herbrand_of_tower_of_image {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (M : IntermediateField K L) [IsGalois K ↥M] [IsGalois K L]
    [Finite ↥(A.decompositionSubgroup K)] (hA : A.decompositionSubgroup K = ⊤)
    [PerfectField (IsLocalRing.ResidueField A)]
    (H : ∀ n : ℕ,
      Subgroup.map (AlgEquiv.restrictNormalHom (K₁ := L) ↥M)
          (Subgroup.map (A.decompositionSubgroup K).subtype
            (NK.Ramification.ramificationSubgroup (K := K) A n))
        = Subgroup.map ((A.comap (algebraMap ↥M L)).decompositionSubgroup K).subtype
            (NK.Ramification.ramificationSubgroup (K := K) (A.comap (algebraMap ↥M L))
              ⌊NK.Ramification.herbrand (K := ↥M) A n⌋₊))
    (n : ℕ) :
    NK.Ramification.lowerIndex (K := K) A n =
      NK.Ramification.lowerIndex (K := ↥M) A n *
        NK.Ramification.lowerIndex (K := K) (A.comap (algebraMap ↥M L))
          ⌊NK.Ramification.herbrand (K := ↥M) A n⌋₊ := by
  change Nat.card ↥(NK.Ramification.ramificationSubgroup (K := K) A n) =
      Nat.card ↥(NK.Ramification.ramificationSubgroup (K := ↥M) A n) *
        Nat.card ↥(NK.Ramification.ramificationSubgroup (K := K)
            (A.comap (algebraMap ↥M L)) ⌊NK.Ramification.herbrand (K := ↥M) A n⌋₊)
  have hcard1 : Nat.card ↥(NK.Ramification.ramificationSubgroup (K := K) A n) =
      Nat.card ↥((NK.Ramification.ramificationSubgroup (K := K) A n).map
        (A.decompositionSubgroup K).subtype) :=
    (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  have hcard2 := natCard_eq_card_map_mul_card_inf_ker
    (AlgEquiv.restrictNormalHom (K₁ := L) ↥M)
    ((NK.Ramification.ramificationSubgroup (K := K) A n).map (A.decompositionSubgroup K).subtype)
  have hcard3 : Nat.card ↥(Subgroup.map (AlgEquiv.restrictNormalHom (K₁ := L) ↥M)
      (Subgroup.map (A.decompositionSubgroup K).subtype
        (NK.Ramification.ramificationSubgroup (K := K) A n))) =
      Nat.card ↥(NK.Ramification.ramificationSubgroup (K := K)
        (A.comap (algebraMap ↥M L)) ⌊NK.Ramification.herbrand (K := ↥M) A n⌋₊) := by
    rw [H n]
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hcard4 : Nat.card ↥(((NK.Ramification.ramificationSubgroup (K := K) A n).map
        (A.decompositionSubgroup K).subtype) ⊓
        (AlgEquiv.restrictNormalHom (K₁ := L) ↥M).ker) =
      Nat.card ↥(NK.Ramification.ramificationSubgroup (K := ↥M) A n) := by
    rw [IntermediateField.restrictNormalHom_ker M,
      NK.RamificationDeep.ramificationSubgroup_inf_fixingSubgroup A M n]
    exact Subgroup.card_map_of_injective ((Subgroup.subtype_injective _).comp
      ((IntermediateField.fixingSubgroupEquiv M).symm.injective.comp (Subgroup.subtype_injective _)))
  calc Nat.card ↥(NK.Ramification.ramificationSubgroup (K := K) A n)
      = Nat.card ↥((NK.Ramification.ramificationSubgroup (K := K) A n).map
          (A.decompositionSubgroup K).subtype) := hcard1
    _ = Nat.card ↥(Subgroup.map (AlgEquiv.restrictNormalHom (K₁ := L) ↥M)
            (Subgroup.map (A.decompositionSubgroup K).subtype
              (NK.Ramification.ramificationSubgroup (K := K) A n)))
        * Nat.card ↥(((NK.Ramification.ramificationSubgroup (K := K) A n).map
            (A.decompositionSubgroup K).subtype) ⊓
            (AlgEquiv.restrictNormalHom (K₁ := L) ↥M).ker) := hcard2
    _ = Nat.card ↥(NK.Ramification.ramificationSubgroup (K := K)
          (A.comap (algebraMap ↥M L)) ⌊NK.Ramification.herbrand (K := ↥M) A n⌋₊)
        * Nat.card ↥(NK.Ramification.ramificationSubgroup (K := ↥M) A n) := by
        rw [hcard3, hcard4]
    _ = Nat.card ↥(NK.Ramification.ramificationSubgroup (K := ↥M) A n)
        * Nat.card ↥(NK.Ramification.ramificationSubgroup (K := K)
          (A.comap (algebraMap ↥M L)) ⌊NK.Ramification.herbrand (K := ↥M) A n⌋₊) := by
        rw [mul_comm]

end NK.RamificationDeep
