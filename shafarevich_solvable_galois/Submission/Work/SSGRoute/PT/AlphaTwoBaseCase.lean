import Mathlib
import Submission.Work.SSGRoute.PT.AlphaTwoKummer
import Submission.Work.SSGRoute.PT.AlphaTwoTrivMod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer base case: the map `H²(G, Hom_ℤ(ℤ/p, C)) → H²(G, C)` is a bijection onto `C[p]`

`range_mapH2_ptorEquiv` (image = the `p`-torsion) and `ker_mapH2_ptorEquiv` (Hilbert 90) give
injectivity and surjectivity of the coefficient map, stated for the composite
`C[p] ⊆ C` after the coefficient identification `Hom_ℤ(ℤ/p, C) ≅ C[p]`.
-/

open Classical

namespace Work.SSGRoute.PT

noncomputable section

universe u

/-- **Injectivity** (Hilbert 90). -/
theorem mapH2_ptorEquiv_injective {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (p : ℕ) [Fact p.Prime] {C : Type u} [AddCommGroup C]
    [DistribMulAction G C]
    (S : Work.AbsoluteKummer.ShortExactSeq G (ConjHom (TrivMod G p) C) C C)
    (hSι : S.iota = evalOne G p C)
    (h1 : Subsingleton (Work.AbsoluteKummer.H1 G C)) :
    Function.Injective (Work.AbsoluteKummer.mapH2
      ((AddSubgroup.subtype (PTor p C)).comp (conjHomTrivModEquivPTor G p C).toAddMonoidHom)
      (subtype_comp_conjHomTrivModEquivPTor_equivariant G p C)) := by
  exact (AddMonoidHom.ker_eq_bot_iff _).mp (ker_mapH2_ptorEquiv (G := G) p S hSι h1)

/-- **Surjectivity onto the `p`-torsion.** -/
theorem mapH2_ptorEquiv_surjective {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (p : ℕ) [Fact p.Prime] {C : Type u} [AddCommGroup C]
    [DistribMulAction G C]
    (S : Work.AbsoluteKummer.ShortExactSeq G (ConjHom (TrivMod G p) C) C C)
    (hSι : S.iota = evalOne G p C) (hSπ : ∀ c : C, S.pi c = p • c) :
    ∀ y : ↥(PTor p (Work.AbsoluteKummer.H2 G C)),
      ∃ x : Work.AbsoluteKummer.H2 G (ConjHom (TrivMod G p) C),
        Work.AbsoluteKummer.mapH2
            ((AddSubgroup.subtype (PTor p C)).comp
              (conjHomTrivModEquivPTor G p C).toAddMonoidHom)
            (subtype_comp_conjHomTrivModEquivPTor_equivariant G p C) x = (y : _) := by
  intro y
  have hy : (y : Work.AbsoluteKummer.H2 G C) ∈ (Work.AbsoluteKummer.mapH2
      ((AddSubgroup.subtype (PTor p C)).comp (conjHomTrivModEquivPTor G p C).toAddMonoidHom)
      (subtype_comp_conjHomTrivModEquivPTor_equivariant G p C)).range := by
    rw [range_mapH2_ptorEquiv (G := G) p S hSι hSπ, AddMonoidHom.mem_ker, nsmulHom_apply]
    exact y.2
  exact (AddMonoidHom.mem_range).mp hy

end

end Work.SSGRoute.PT
