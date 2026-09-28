import Mathlib
import Submission.Work.Cohomology.pd_boundary_of_zero_class
import Submission.Work.Cohomology.pd_split_aux

/-!
# Equal homology classes of cycles differ by a boundary

If two cycles of a cochain complex of `R`-modules have the same class in homology, then their
difference (as chains) is the differential of a chain in one degree less.  This is the elementwise
form of the standard description of the `n`-th homology group as `cycles n / boundaries n`, in the
form needed for the Poincaré duality development (`pd_union_split` and relatives).

The mathematical content is purely the universal property of the cokernel: `homologyπ` is the
cokernel of `toCycles`, which is the map sending a chain to its boundary viewed as a cycle.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **A cokernel projection equal on two elements gives a difference in the range.**

If `p : B ⟶ C` together with `f ≫ p = 0` exhibits `p` as the cokernel of `f : A ⟶ B`, then
`p x = p y` forces `x - y` to lie in the image of `f`.  This is the concrete shape of the
universal property in `ModuleCat R`. -/
lemma ModuleCat.exists_eq_sub_of_cokernel_π_eq {R : Type} [CommRing R] {A B C : ModuleCat R}
    (f : A ⟶ B) (p : B ⟶ C) (w : f ≫ p = 0)
    (hp : IsColimit (CokernelCofork.ofπ p w)) (x y : B) (h : p x = p y) :
    ∃ a : A, f a = x - y := by
  have key : p ≫ (IsColimit.coconePointUniqueUpToIso hp (ModuleCat.cokernelIsColimit f)).hom
      = ModuleCat.ofHom (LinearMap.range f.hom).mkQ :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hp (ModuleCat.cokernelIsColimit f)
      WalkingParallelPair.one
  have h2 : (IsColimit.coconePointUniqueUpToIso hp (ModuleCat.cokernelIsColimit f)).hom (p x)
      = (IsColimit.coconePointUniqueUpToIso hp (ModuleCat.cokernelIsColimit f)).hom (p y) := by
    rw [h]
  have e1 : (IsColimit.coconePointUniqueUpToIso hp (ModuleCat.cokernelIsColimit f)).hom (p x)
      = (Submodule.Quotient.mk x : B ⧸ (f.hom).range) := by
    have hh := ConcreteCategory.congr_hom key x
    simp only [ConcreteCategory.comp_apply] at hh
    exact hh
  have e2 : (IsColimit.coconePointUniqueUpToIso hp (ModuleCat.cokernelIsColimit f)).hom (p y)
      = (Submodule.Quotient.mk y : B ⧸ (f.hom).range) := by
    have hh := ConcreteCategory.congr_hom key y
    simp only [ConcreteCategory.comp_apply] at hh
    exact hh
  have hq : (Submodule.Quotient.mk x : B ⧸ (f.hom).range) = Submodule.Quotient.mk y := by
    rw [← e1, h2, e2]
  rw [Submodule.Quotient.eq] at hq
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hq
  exact ⟨a, ha⟩

lemma pd_us_cycles_eq_of_class_eq {R : Type} [CommRing R]
    {K : CochainComplex (ModuleCat R) ℕ} {n : ℕ}
    (z₁ z₂ : K.cycles (n + 1))
    (h : (HomologicalComplex.homologyπ K (n + 1)).hom z₁
        = (HomologicalComplex.homologyπ K (n + 1)).hom z₂) :
    ∃ y : K.X n, (K.d n (n+1)).hom y
      = (HomologicalComplex.iCycles K (n+1)).hom z₁
        - (HomologicalComplex.iCycles K (n+1)).hom z₂ := by
  -- `homologyπ` in degree `n + 1` is the cokernel of `toCycles n (n+1)`, the boundary map
  -- seen as a map into the cycles.
  have hprev : (ComplexShape.up ℕ).prev (n+1) = n :=
    ComplexShape.prev_eq' (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel n (n+1) from rfl)
  obtain ⟨y, hy⟩ := ModuleCat.exists_eq_sub_of_cokernel_π_eq (K.toCycles n (n+1))
    (K.homologyπ (n+1)) (K.toCycles_comp_homologyπ n (n+1))
    (K.homologyIsCokernel n (n+1) hprev) z₁ z₂ h
  refine ⟨y, ?_⟩
  -- `iCycles ∘ toCycles = d` on the nose.
  have h5 : (K.d n (n+1)).hom y
      = (HomologicalComplex.iCycles K (n+1)).hom ((HomologicalComplex.toCycles K n (n+1)) y) := by
    have hcomp : (K.toCycles n (n+1) ≫ K.iCycles (n+1)) = K.d n (n+1) :=
      HomologicalComplex.toCycles_i K n (n+1)
    rw [← hcomp]
    rfl
  rw [h5, hy]
  simp

end

end Work.Cohomology
