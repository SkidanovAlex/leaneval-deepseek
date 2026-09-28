import Mathlib

/-!
# A cycle whose homology class vanishes is a boundary

If `z` is a cycle of a chain complex `K` of `R`-modules and its class in `H_n(K)` is zero, then
`z` is the boundary of an `(n+1)`-chain.  This is the elementwise form of the description of the
`n`-th homology as `cycles n / boundaries n`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

set_option maxHeartbeats 800000

/-- **A short complex version**: if the class of a cycle of a short complex of modules is zero,
then it is the image of a `1`-chain under `toCycles`. -/
lemma pd_shortComplex_exists_toCycles {R : Type} [CommRing R]
    {S : ShortComplex (ModuleCat R)} {z : S.cycles}
    (h : (S.homologyπ).hom z = 0) : ∃ y : S.X₁, (S.toCycles).hom y = z := by
  have key := IsColimit.comp_coconePointUniqueUpToIso_hom (S.homologyIsCokernel)
    (ModuleCat.cokernelIsColimit S.toCycles) WalkingParallelPair.one
  have h2 : (ConcreteCategory.hom ((ModuleCat.cokernelCocone S.toCycles).ι.app
      WalkingParallelPair.one)) z = 0 := by
    rw [← key]
    rw [show (CokernelCofork.ofπ S.homologyπ S.toCycles_comp_homologyπ).ι.app
        WalkingParallelPair.one = S.homologyπ from rfl]
    simp only [ConcreteCategory.comp_apply]
    rw [h, map_zero]
  have h3 : ((ModuleCat.Hom.hom S.toCycles).range.mkQ) z = 0 := h2
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h3
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp h3
  exact ⟨y, hy⟩

/-- **A cycle whose homology class vanishes is a boundary.** -/
theorem pd_boundary_of_zero_class {R : Type} [CommRing R]
    (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (z : K.cycles n)
    (h : (HomologicalComplex.homologyπ K n).hom z = 0) :
    ∃ y : K.X (n+1), (K.d (n+1) n).hom y = (HomologicalComplex.iCycles K n).hom z := by
  have hi : (ComplexShape.down ℕ).prev n = n + 1 :=
    ComplexShape.prev_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel (n+1) n from rfl)
  obtain ⟨y₀, hy₀⟩ := pd_shortComplex_exists_toCycles (S := K.sc n) (z := z) h
  refine ⟨(K.XIsoOfEq hi).hom y₀, ?_⟩
  have h1 : (ConcreteCategory.hom (HomologicalComplex.iCycles K n)) z
      = (ConcreteCategory.hom (K.d ((ComplexShape.down ℕ).prev n) n)) y₀ := by
    have hh : (ConcreteCategory.hom (HomologicalComplex.iCycles K n))
        ((ConcreteCategory.hom (HomologicalComplex.sc K n).toCycles) y₀)
      = (ConcreteCategory.hom (K.d ((ComplexShape.down ℕ).prev n) n)) y₀ :=
      congrArg (fun g => (ConcreteCategory.hom g) y₀) (ShortComplex.toCycles_i (K.sc n))
    rwa [hy₀] at hh
  have h2 : (ConcreteCategory.hom (K.d (n+1) n)) ((ConcreteCategory.hom (K.XIsoOfEq hi).hom) y₀)
      = (ConcreteCategory.hom (K.d ((ComplexShape.down ℕ).prev n) n)) y₀ :=
    (ConcreteCategory.comp_apply (K.XIsoOfEq hi).hom (K.d (n+1) n) y₀).symm.trans
      (congrArg (fun g => (ConcreteCategory.hom g) y₀)
        (HomologicalComplex.XIsoOfEq_hom_comp_d K hi n))
  rw [h2, h1]

end

end Work.Cohomology
