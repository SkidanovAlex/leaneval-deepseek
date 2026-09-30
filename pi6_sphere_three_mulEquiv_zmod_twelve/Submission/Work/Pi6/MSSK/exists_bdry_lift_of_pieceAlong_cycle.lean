import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaBasic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

/-- In `ModuleCat R`, an element killed by the cokernel projection of `f` lies in the range
of `f`. -/
lemma exists_eq_of_cokernel_π_eq_zero (R : Type) [Ring R] {M N : ModuleCat R} (f : M ⟶ N)
    {x : N} (h : cokernel.π f x = 0) : ∃ y : M, f y = x := by
  have h2 : (LinearMap.range (ModuleCat.Hom.hom f)).mkQ x = 0 := by
    have hh := congrArg (fun (g : N ⟶ ↧(N ⧸ LinearMap.range (ModuleCat.Hom.hom f))) => g x)
      (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom f)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, h, map_zero,
      ModuleCat.hom_ofHom] at hh
    exact hh.symm
  have hx : x ∈ LinearMap.range (ModuleCat.Hom.hom f) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact h2
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

/-- A cycle of the cokernel of a morphism of chain complexes of `R`-modules, of degree `n+1`,
lies in the image of the differential applied to the source of the morphism. -/
lemma exists_lift_of_cokernel_cycle (R : Type) [CommRing R] {A X : ChainComplex (ModuleCat R) ℕ}
    (i : A ⟶ X) {n : ℕ} (c : X.X (n+1))
    (hc : (cokernel i).d (n+1) n ((cokernel.π i).f (n+1) c) = 0) :
    ∃ y : A.X n, i.f n y = X.d (n+1) n c := by
  -- `π` commutes with the differentials, so `π (d c) = d (π c) = 0`.
  have hcomm := HomologicalComplex.Hom.comm (cokernel.π i) (n+1) n
  have h1 : (cokernel.π i).f n (X.d (n+1) n c) = 0 := by
    have hh := congrArg (fun (g : X.X (n+1) ⟶ (cokernel i).X n) => g c) hcomm
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
    rw [hc] at hh
    exact hh.symm
  -- The `n`-th evaluation functor preserves the cokernel, so `π` in degree `n` is the
  -- categorical cokernel projection of `i.f n`.
  haveI : PreservesColimit (parallelPair i 0)
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n) :=
    HomologicalComplex.eval_preservesColimit_of_hasCokernel_f i n
  have h2 : cokernel.π (i.f n) (X.d (n+1) n c) = 0 := by
    have hiso := CategoryTheory.Limits.PreservesCokernel.π_iso_hom
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n) i
    have hh := congrArg (fun (g :
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n).obj X ⟶
          cokernel ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n).map i)) =>
      g (X.d (n+1) n c)) hiso
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
    simp only [HomologicalComplex.eval_map] at hh
    rw [h1, map_zero] at hh
    exact hh.symm
  obtain ⟨y, hy⟩ := exists_eq_of_cokernel_π_eq_zero R (i.f n) h2
  exact ⟨y, hy⟩

theorem exists_bdry_lift_of_pieceAlong_cycle (R : Type) [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {s n : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (n+1))
    (hc : ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (n+1) n).hom
        ((CategoryTheory.Limits.cokernel.π
          (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (n+1) c) = 0) :
    ∃ y : (Work.SSSR.sCC R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ)).X n,
      (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f n y
        = ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (n+1) n).hom c := by
  exact exists_lift_of_cokernel_cycle R
    (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι) c hc

end

end Work.Pi6.MSSK
