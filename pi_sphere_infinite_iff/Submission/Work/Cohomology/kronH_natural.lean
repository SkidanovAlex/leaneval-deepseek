import Mathlib
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.AlexanderWhitney
import Submission.Work.Cohomology.CupRing

/-!
# Naturality of the Kronecker pairing

`Work.Cohomology.kronH ℤ X n : Hⁿ(X) ⟶ (Hₙ(X) →ₗ ℤ)` is the Kronecker pairing fixed in
`Submission/Work/Cohomology/KroneckerH.lean`.  This file proves that it is natural in the space:
for a continuous map `f : X ⟶ Y`, a cohomology class `α ∈ Hⁿ(Y)` and a homology class
`c ∈ Hₙ(X)`,

  `⟨α, f_* c⟩ = ⟨f^* α, c⟩`.

Both sides are linear in each variable, so by surjectivity of the homology projections `homologyπ`
it suffices to check the identity when `α` is the class of a cochain cycle `w` and `c` the class of
a chain cycle `v`.  Then both sides are computed by the evaluation rule `kronH_cyc_apply` (the
value of the pairing on classes of cycles), which reduces the identity to

  `(iCycles_Y w) (chain f v) = (pullback f (iCycles_Y w)) (iCycles_X v)`,

and this is the defining formula of the dual chain map together with the naturality of the cycle
inclusions (`cyclesMap_i`).

## Formalisation remark

The Kronecker pairing is a pairing on the simplicial (co)chain complexes `chainC`/`cochainC`,
whereas `chainMap`/`dualChainMap` are stated for the singular (co)chain complexes of a topological
space.  These are definitionally equal but the two presentations unfold through different
definitions, which makes rewriting across them delicate.  We therefore introduce the small
"simplicial presentations"
`chainMapS`, `cochainPullbackHomS`, `dualChainMapS` of the chain map, its transpose and the dual
cochain map, with the *same* underlying terms but with the types written in the simplicial
notation, and record their computation rules (`dualChainMapS_f`, `cochainPullbackHomS_apply`).

## Main results

* `Work.Cohomology.homologyMap_homologyπ_apply` — a morphism of complexes sends the class of a
  cycle to the class of the image cycle;
* `Work.Cohomology.kronH_cyc_apply` — the computation rule for `kronH` on classes of cycles;
* `Work.Cohomology.cochainOfCycle_cyclesMapS_apply` — the dual cochain map evaluated on the
  underlying cochain of a cycle;
* `Work.Cohomology.kronH_natural` — **naturality of the Kronecker pairing**.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## Generalities -/

/-- **Naturality of `homologyπ`**: a morphism of complexes of `R`-modules sends the homology class
of a cycle to the homology class of the image cycle. -/
lemma homologyMap_homologyπ_apply {R : Type} [CommRing R] {ι : Type} {cs : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat R) cs} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i).hom ((K.homologyπ i).hom z) =
      (L.homologyπ i).hom ((HomologicalComplex.cyclesMap φ i).hom z) := by
  have h := HomologicalComplex.homologyπ_naturality φ i
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.homology i) => g.hom z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- **The computation rule for the Kronecker pairing on cycles**: the pairing of the class of a
cochain cycle `w` with the class of a chain cycle `v` is the evaluation of the underlying cochain
of `w` on `v`. -/
lemma kronH_cyc_apply (X : SSet) (n : ℕ)
    (w : (cochainC ℤ X).cycles n) (v : (chainC ℤ X).cycles n) :
    kronH ℤ X n ((cochainC ℤ X).homologyπ n w) ((chainC ℤ X).homologyπ n v) =
      cochainOfCycle ℤ X n w ((chainC ℤ X).iCycles n v) := by
  rw [← cohomologyClassOf_eq_homologyπ ℤ X n w]
  exact kronH_apply ℤ X ((cochainC ℤ X).iCycles n w) (cochainDiff_iCycles ℤ X n w) v

/-! ## The simplicial presentation of the (dual) chain map

The definitions below have the same underlying terms as `chainMap`, `cochainPullbackHom` and
`dualChainMap`, but their types are written with the simplicial chain complex `chainC` instead of
the singular chain complex `singularChains`; this is what allows rewriting in the simplicial
notation. -/

/-- The `R`-dual of the `n`-th simplicial chain module, with the type written so that it reduces
to the type of linear functionals on the chains. -/
abbrev dualChainsT (R : Type) [CommRing R] (X : TopCat) (n : ℕ) : ModuleCat R :=
  ModuleCat.of R ((chainC R (TopCat.toSSet.obj X)).X n →ₗ[R] R)

/-- The simplicial presentation of the chain map induced by a continuous map. -/
noncomputable def chainMapS (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y) :
    chainC R (TopCat.toSSet.obj X) ⟶ chainC R (TopCat.toSSet.obj Y) :=
  chainMap R X Y f

/-- The simplicial presentation of the transpose of the chain map induced by a continuous map. -/
noncomputable def cochainPullbackHomS (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) :
    dualChainsT R Y n ⟶ dualChainsT R X n :=
  ModuleCat.ofHom ((chainMapS R X Y f).f n).hom.dualMap

/-- The simplicial presentation of the dual cochain map induced by a continuous map. -/
noncomputable def dualChainMapS (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y) :
    cochainC R (TopCat.toSSet.obj Y) ⟶ cochainC R (TopCat.toSSet.obj X) :=
  dualChainMap R X Y f

/-- The `n`-th component of the simplicial presentation of the dual cochain map is the simplicial
presentation of the transposed chain map. -/
lemma dualChainMapS_f (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) :
    (dualChainMapS R X Y f).f n = cochainPullbackHomS R X Y f n := rfl

/-- The defining formula of the transposed chain map: `(f^* φ)(x) = φ(f x)`. -/
lemma cochainPullbackHomS_apply (R : Type) [CommRing R] (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (φ : dualChainsT R Y n) (x : (chainC R (TopCat.toSSet.obj X)).X n) :
    ((cochainPullbackHomS R X Y f n).hom φ) x = φ (((chainMapS R X Y f).f n).hom x) := by
  rw [cochainPullbackHomS, ModuleCat.hom_ofHom, LinearMap.dualMap_apply]

/-- The transpose of the chain map sends the underlying cochain of a cycle to the underlying
cochain of the image cycle. -/
lemma cochainOfCycle_cyclesMapS (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (w : (cochainC ℤ (TopCat.toSSet.obj Y)).cycles n) :
    cochainOfCycle ℤ (TopCat.toSSet.obj X) n
        ((HomologicalComplex.cyclesMap (dualChainMapS ℤ X Y f) n).hom w)
      = (cochainPullbackHomS ℤ X Y f n).hom (cochainOfCycle ℤ (TopCat.toSSet.obj Y) n w) := by
  exact congrArg (fun (g : (cochainC ℤ (TopCat.toSSet.obj Y)).cycles n ⟶
      (cochainC ℤ (TopCat.toSSet.obj X)).X n) => g.hom w)
    (HomologicalComplex.cyclesMap_i (dualChainMapS ℤ X Y f) n)

/-- The pointwise form of `cochainOfCycle_cyclesMapS`, in the form needed for the naturality of
the Kronecker pairing. -/
lemma cochainOfCycle_cyclesMapS_apply (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (w : (cochainC ℤ (TopCat.toSSet.obj Y)).cycles n)
    (x : (chainC ℤ (TopCat.toSSet.obj X)).X n) :
    cochainOfCycle ℤ (TopCat.toSSet.obj X) n
        ((HomologicalComplex.cyclesMap (dualChainMapS ℤ X Y f) n).hom w) x
      = cochainOfCycle ℤ (TopCat.toSSet.obj Y) n w (((chainMapS ℤ X Y f).f n).hom x) := by
  have h := LinearMap.congr_fun (cochainOfCycle_cyclesMapS X Y f n w) x
  exact h.trans (cochainPullbackHomS_apply ℤ X Y f n
    (cochainOfCycle ℤ (TopCat.toSSet.obj Y) n w) x)

/-! ## Naturality of the Kronecker pairing -/

theorem kronH_natural (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (α : (Work.Cohomology.singularCochainComplex ℤ Y).homology n)
    (c : (Work.Cohomology.singularChains ℤ X).homology n) :
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj Y) n α
        ((HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) n) c)
      = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) n
          ((Work.Cohomology.singularCohomologyMap ℤ X Y f n) α) c := by
  change kronH ℤ (TopCat.toSSet.obj Y) n α
      (HomologicalComplex.homologyMap (chainMapS ℤ X Y f) n c)
    = kronH ℤ (TopCat.toSSet.obj X) n
      (HomologicalComplex.homologyMap (dualChainMapS ℤ X Y f) n α) c
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainC ℤ (TopCat.toSSet.obj Y)).homologyπ n)).mp inferInstance α
  obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((chainC ℤ (TopCat.toSSet.obj X)).homologyπ n)).mp inferInstance c
  have hA : (HomologicalComplex.homologyMap (chainMapS ℤ X Y f) n)
      ((chainC ℤ (TopCat.toSSet.obj X)).homologyπ n v)
      = (chainC ℤ (TopCat.toSSet.obj Y)).homologyπ n
          ((HomologicalComplex.cyclesMap (chainMapS ℤ X Y f) n).hom v) :=
    homologyMap_homologyπ_apply (chainMapS ℤ X Y f) n v
  have hB : (HomologicalComplex.homologyMap (dualChainMapS ℤ X Y f) n)
      ((cochainC ℤ (TopCat.toSSet.obj Y)).homologyπ n w)
      = (cochainC ℤ (TopCat.toSSet.obj X)).homologyπ n
          ((HomologicalComplex.cyclesMap (dualChainMapS ℤ X Y f) n).hom w) :=
    homologyMap_homologyπ_apply (dualChainMapS ℤ X Y f) n w
  have hcA : ((chainC ℤ (TopCat.toSSet.obj Y)).iCycles n).hom
        ((HomologicalComplex.cyclesMap (chainMapS ℤ X Y f) n).hom v)
      = ((chainMapS ℤ X Y f).f n).hom
        (((chainC ℤ (TopCat.toSSet.obj X)).iCycles n).hom v) :=
    congrArg (fun (g : (chainC ℤ (TopCat.toSSet.obj X)).cycles n ⟶
        (chainC ℤ (TopCat.toSSet.obj Y)).X n) => g.hom v)
      (HomologicalComplex.cyclesMap_i (chainMapS ℤ X Y f) n)
  rw [hA, hB]
  rw [kronH_cyc_apply (TopCat.toSSet.obj Y) n w
        ((HomologicalComplex.cyclesMap (chainMapS ℤ X Y f) n).hom v),
      kronH_cyc_apply (TopCat.toSSet.obj X) n
        ((HomologicalComplex.cyclesMap (dualChainMapS ℤ X Y f) n).hom w) v]
  rw [hcA, cochainOfCycle_cyclesMapS_apply X Y f n w
        (((chainC ℤ (TopCat.toSSet.obj X)).iCycles n).hom v)]

end

end Work.Cohomology
