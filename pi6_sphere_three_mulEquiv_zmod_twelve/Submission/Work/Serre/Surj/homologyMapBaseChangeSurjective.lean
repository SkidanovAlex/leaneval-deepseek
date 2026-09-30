import Mathlib
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.StemsB.WangCohRat

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Surjectivity of the `ℤ → ℚ` base change of `H_n` when the cokernel is torsion

Let `f : C ⟶ D` be a morphism of chain complexes of `ℤ`-modules and let `g = H_n(f)`.  If the
cokernel of `g` is a torsion group — here expressed as the vanishing of its rationalisation,
`Subsingleton (coker g ⊗[ℤ] ℚ)` — then the induced map on the rationalised homology

`H_n(C ⊗[ℤ] ℚ) ⟶ H_n(D ⊗[ℤ] ℚ)`

is surjective.

## The argument

Write `F = extendScalars (ℤ → ℚ)`, so that `F.obj M = ℚ ⊗[ℤ] M` and `F` is exact (ℚ is flat over
`ℤ`).  Two ingredients are needed.

* *Algebra.*  A map of `ℤ`-modules whose cokernel is torsion becomes an epimorphism after base
  change to `ℚ`.  Indeed `F` preserves cokernels, so `F.obj (coker g) ≅ coker (F.map g)`; the
  hypothesis says that the source of this isomorphism is a subsingleton, hence a zero object,
  hence `coker (F.map g) = 0`, i.e. `F.map g` is an epimorphism.  Over `ModuleCat` the underlying
  type of `F.obj (coker g)` is `ℚ ⊗[ℤ] coker g`, which is `coker g ⊗[ℤ] ℚ` up to
  `TensorProduct.comm`, so the hypothesis of the statement transfers directly.

* *Homology.*  `F` also preserves homology, and the naturality of the comparison isomorphism
  `S.mapHomologyIso F : (S.map F).homology ≅ F.obj S.homology` on the short complexes cutting out
  degree `n` identifies `H_n(F.map f)` with `F.map (H_n f)` up to isomorphisms on both sides;
  surjectivity is then transported along those isomorphisms.

Both ingredients are formal: the mathematics is Serre's observation that a torsion quotient dies
after rationalisation (cf. `Work.StemsB.tensorRat_iff_torsion` and
`Work.RatHurewicz.intRat_mono_of_torsion_ker`, the dual statement for kernels).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre.Surj

noncomputable section

/-- **The underlying type of `ℚ ⊗[ℤ] M` is `M ⊗[ℤ] ℚ`.**  The extension of scalars
`ModuleCat.extendScalars (ℤ → ℚ)` sends `M` to `ℚ ⊗[ℤ] M`, whose underlying type is linearly
equivalent to `M ⊗[ℤ] ℚ` by symmetry of the tensor product; hence a subsingleton of the latter
transfers to the former. -/
theorem subsingleton_intRatF_obj_of_tensorRat {M : ModuleCat ℤ}
    (h : Subsingleton (TensorProduct ℤ ↥M ℚ)) :
    Subsingleton ↥(Work.StemsB.IntRatF.obj M) := by
  have he : Nonempty (↥(Work.StemsB.IntRatF.obj M) ≃ (TensorProduct ℤ ↥M ℚ)) :=
    ⟨(TensorProduct.comm ℤ ↥M ℚ).symm.toEquiv⟩
  obtain ⟨e⟩ := he
  exact ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩

/-- **A torsion cokernel becomes an epimorphism after base change to `ℚ`.**

If `M ⊗[ℤ] ℚ = 0` where `M = coker g`, then `ℚ ⊗[ℤ] g` is an epimorphism: the functor
`ℚ ⊗[ℤ] -` preserves cokernels, so `ℚ ⊗[ℤ] coker g` is the cokernel of `ℚ ⊗[ℤ] g`, and a map whose
cokernel is a zero object (that is, a subsingleton) is an epimorphism. -/
theorem epi_intRatF_map_of_subsingleton_cokernel {A B : ModuleCat ℤ} (g : A ⟶ B)
    (h : Subsingleton ↥(Work.StemsB.IntRatF.obj (cokernel g))) :
    Epi (Work.StemsB.IntRatF.map g) := by
  haveI : PreservesColimit (parallelPair g 0) Work.StemsB.IntRatF := inferInstance
  have hZ : IsZero (Work.StemsB.IntRatF.obj (cokernel g)) :=
    ModuleCat.isZero_iff_subsingleton.mpr h
  have hZ' : IsZero (cokernel (Work.StemsB.IntRatF.map g)) :=
    (Iso.isZero_iff (CategoryTheory.Limits.PreservesCokernel.iso Work.StemsB.IntRatF g)).mp hZ
  exact CategoryTheory.Abelian.epi_of_cokernel_π_eq_zero _
    (hZ'.eq_of_tgt (cokernel.π (Work.StemsB.IntRatF.map g)) 0)

/-- **The base change of `H_n` is surjective when the cokernel of `H_n(f)` is torsion.** -/
theorem homologyMapBaseChangeSurjective (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ)
    (h : Subsingleton (TensorProduct ℤ ↥(CategoryTheory.Limits.cokernel (HomologicalComplex.homologyMap f n)) ℚ)) :
    Function.Surjective (HomologicalComplex.homologyMap (Work.StemsB.IntRatCM.map f) n).hom := by
  -- the map on homology, in the `ShortComplex` spelling (definitionally the same map)
  set g := ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map f) with hg
  -- exactness of `ℚ ⊗[ℤ] -`
  haveI : PreservesFiniteLimits Work.StemsB.IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits Work.StemsB.IntRatF := inferInstance
  haveI : Work.StemsB.IntRatF.PreservesHomology := inferInstance
  -- the algebraic step: the base change of `H_n(f)` is an epimorphism
  have hepi : Epi (Work.StemsB.IntRatF.map g) :=
    epi_intRatF_map_of_subsingleton_cokernel g (subsingleton_intRatF_obj_of_tensorRat h)
  -- the naturality of the homology comparison
  let EA := ShortComplex.mapHomologyIso (C.sc n) Work.StemsB.IntRatF
  let EB := ShortComplex.mapHomologyIso (D.sc n) Work.StemsB.IntRatF
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map f)
    Work.StemsB.IntRatF
  have hcomp : HomologicalComplex.homologyMap (Work.StemsB.IntRatCM.map f) n
      = EA.hom ≫ Work.StemsB.IntRatF.map g ≫ EB.inv :=
    (Iso.eq_comp_inv EB (f := EA.hom ≫ Work.StemsB.IntRatF.map g)).mpr hnat
  rw [hcomp]
  -- elementwise surjectivity of the conjugate of an epimorphism
  intro y
  have hsurj : Function.Surjective ⇑(ModuleCat.Hom.hom (Work.StemsB.IntRatF.map g)) :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  obtain ⟨x, hx⟩ := hsurj (EB.hom.hom y)
  refine ⟨EA.inv.hom x, ?_⟩
  show (EA.hom ≫ Work.StemsB.IntRatF.map g ≫ EB.inv).hom (EA.inv.hom x) = y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [Iso.inv_hom_id_apply EA x, hx, Iso.hom_inv_id_apply EB y]

end

end Work.Serre.Surj
