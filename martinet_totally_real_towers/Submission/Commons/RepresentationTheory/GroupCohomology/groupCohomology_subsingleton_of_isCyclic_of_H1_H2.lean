import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory

theorem groupCohomology_subsingleton_of_isCyclic_of_H1_H2 {G : Type} [Group G] [Fintype G]
    [IsCyclic G] (M : Rep ℤ G)
    (h1 : Subsingleton (groupCohomology M 1))
    (h2 : Subsingleton (groupCohomology M 2)) (n : ℕ) (hn : 0 < n) :
    Subsingleton (groupCohomology M n) := by
  classical
  letI : CommGroup G := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  rcases Nat.even_or_odd n with hne | hno
  · haveI : NeZero n := ⟨hn.ne'⟩
    haveI : NeZero 2 := ⟨by norm_num⟩
    have e2 := Rep.FiniteCyclicGroup.groupCohomologyIsoEven M g hg 2 (by norm_num)
    have e1 := Rep.FiniteCyclicGroup.groupCohomologyIsoEven M g hg n hne
    haveI : Subsingleton (groupCohomology M 2) := h2
    haveI : Subsingleton (Rep.FiniteCyclicGroup.normHomCompSub M g).homology :=
      e2.toLinearEquiv.symm.injective.subsingleton
    exact e1.toLinearEquiv.injective.subsingleton
  · haveI : Subsingleton (groupCohomology M 1) := h1
    have e2 := Rep.FiniteCyclicGroup.groupCohomologyIsoOdd M g hg 1 (by norm_num)
    have e1 := Rep.FiniteCyclicGroup.groupCohomologyIsoOdd M g hg n hno
    haveI : Subsingleton (Rep.FiniteCyclicGroup.subCompNormHom M g).homology :=
      e2.toLinearEquiv.symm.injective.subsingleton
    exact e1.toLinearEquiv.injective.subsingleton

end Commons.RepresentationTheory.GroupCohomology