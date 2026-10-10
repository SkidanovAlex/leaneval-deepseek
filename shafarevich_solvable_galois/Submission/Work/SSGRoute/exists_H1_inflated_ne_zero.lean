import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

set_option linter.style.haveILetI false

noncomputable section

/-- For a group homomorphism `f : H →* G`, the cocycle-level inflation
`mapCocycles₁ f (trivResInv f (ZMod p))` is precomposition with `f` on the underlying functions;
here the coefficients are the trivial `G`-module `ZMod p`. -/
lemma coe_mapCocycles₁_trivResInv_aux' {G H : Type} [Group G] [Group H] (f : H →* G) (p : ℕ)
    (z : groupCohomology.cocycles₁ (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p))) :
    ⇑((groupCohomology.mapCocycles₁ f (SSGRoute.PTExt.trivResInv f (ZMod p))).hom z)
      = fun h : H => z (f h) := by
  rw [groupCohomology.coe_mapCocycles₁]
  funext h
  rfl

/-- If `H` is a cyclic group of prime order `p`, there is a nonzero `1`-cocycle of `H` with
coefficients in the trivial module `ZMod p`. -/
lemma exists_cocycles₁_triv_ne_zero {H : Type} [Group H] (p : ℕ) [Fact p.Prime]
    (hcyc : IsCyclic H) (hcard : Nat.card H = p) :
    ∃ z : groupCohomology.cocycles₁ (Rep.trivial SSGRoute.PTExt.Coeff H (ZMod p)), z ≠ 0 := by
  haveI : IsAddCyclic (Additive H) := isAddCyclic_additive
  haveI : IsAddCyclic (ZMod p) := ZMod.instIsAddCyclic p
  have hcard' : Nat.card (Additive H) = Nat.card (ZMod p) := by
    rw [Nat.card_zmod]; exact hcard
  let e : Additive H ≃+ ZMod p := addEquivOfAddCyclicCardEq hcard'
  let g : Additive H →+ ZMod p := e.toAddMonoidHom
  have hg : ∃ x : Additive H, g x ≠ 0 := by
    obtain ⟨x, hx⟩ := e.surjective 1
    exact ⟨x, by rw [show g x = 1 from hx]; exact one_ne_zero⟩
  let z : groupCohomology.cocycles₁ (Rep.trivial SSGRoute.PTExt.Coeff H (ZMod p)) :=
    ⟨g ∘ ⇑Additive.ofMul,
      groupCohomology.mem_cocycles₁_of_addMonoidHom
        (A := Rep.trivial SSGRoute.PTExt.Coeff H (ZMod p)) g⟩
  refine ⟨z, ?_⟩
  intro hz0
  obtain ⟨x, hx⟩ := hg
  have h : z (Additive.toMul x) = 0 := by rw [hz0]; rfl
  simp only [z] at h
  exact hx h

theorem exists_H1_inflated_ne_zero {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)] (p : ℕ) [Fact p.Prime]
    (hcyc : IsCyclic (G ⧸ N)) (hcard : Nat.card (G ⧸ N) = p) :
    ∃ χ : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff (G ⧸ N) (ZMod p)) 1,
      χ ≠ 0 ∧
      (groupCohomology.map (QuotientGroup.mk' N)
        (SSGRoute.PTExt.trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom χ ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_cocycles₁_triv_ne_zero p (H := G ⧸ N) hcyc hcard
  refine ⟨(groupCohomology.H1π _).hom z, ?_, ?_⟩
  · -- `χ` is nonzero: the only coboundary of a trivial module is `0`.
    intro h0
    have hmem := (groupCohomology.H1π_eq_zero_iff z).1 h0
    rw [groupCohomology.coboundaries₁_eq_bot_of_isTrivial] at hmem
    exact hz (Submodule.coe_eq_zero.mp (by simpa using hmem))
  · -- The inflated class is nonzero: inflation is injective on a surjection.
    set f : G →* (G ⧸ N) := QuotientGroup.mk' N with hf
    set φ : Rep.res f (Rep.trivial SSGRoute.PTExt.Coeff (G ⧸ N) (ZMod p))
        ⟶ Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p) :=
      SSGRoute.PTExt.trivResInv f (ZMod p) with hφ
    set w := (groupCohomology.mapCocycles₁ f φ).hom z with hwdef
    have hw : w ≠ 0 := by
      intro hw0
      have hy : ∃ y, z y ≠ 0 := by
        by_contra h
        simp only [not_exists, not_not] at h
        exact hz (Subtype.ext (funext h))
      obtain ⟨y, hy⟩ := hy
      obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective N y
      have hcoe : ⇑w = fun x : G => z (f x) := coe_mapCocycles₁_trivResInv_aux' f p z
      have h1 : ⇑w g' = 0 := by rw [hw0]; rfl
      rw [hcoe] at h1
      exact hy h1
    have hwne : (groupCohomology.H1π _).hom w ≠ 0 := by
      intro h0
      have hmem := (groupCohomology.H1π_eq_zero_iff w).1 h0
      rw [groupCohomology.coboundaries₁_eq_bot_of_isTrivial] at hmem
      exact hw (Submodule.coe_eq_zero.mp (by simpa using hmem))
    rw [groupCohomology.H1π_comp_map_apply f φ z]
    exact hwne

end

end Work.SSGRoute
