/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Composition compatibility of `OperatorMap.h2Map`

`Work.CohomologicalShrinking.OperatorMap.h2Map` is the map induced on the group cohomology
group `H²(G, E(-,τ) ⊗ T)` by a surjective `G`-equivariant homomorphism `F(m) ⇢ F(n)` of free
`G`-operator groups.  This file records that it is compatible with composition of operator maps:
the induced map of `Ψ.comp Φ` is the composite of the induced maps of `Φ` and `Ψ`.

The proof is a direct application of the functoriality of `H²` (`GroupCohomology.mapH2_comp`):
it suffices to know that the `𝔽_p`-linear map `E(m,τ) ⊗ T → E(l,τ) ⊗ T` induced by `Ψ.comp Φ`
is the composite of the maps induced by `Φ` and by `Ψ`, which is `gradedMapLin_comp`
(`Ψ̄ ∘ Φ̄ = (Ψ ∘ Φ)̄`) together with the compatibility of `rTensor` with composition,
`LinearMap.rTensor_comp_apply`.

## Main results

* `Work.CohomologicalShrinking.operator.mapH2_congr` : `mapH2` only depends on the underlying
  additive map, not on the proof of equivariance.
* `Work.CohomologicalShrinking.operator.h2Map_comp` :
  `h2Map (Ψ.comp Φ) = h2Map Ψ ∘ h2Map Φ`.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Corollaries
import Submission.Work.CohomologicalShrinking.OperatorMap
import Submission.Work.CohomologicalShrinking.functorial.gradedMapLin_comp
import Submission.Work.GroupCohomology.All

open scoped TensorProduct

namespace Work.CohomologicalShrinking.operator

open Work.CohomologicalShrinking

set_option maxHeartbeats 800000

/-- The map induced on `H²` by a `G`-equivariant additive map depends only on the underlying
map, not on the proof of equivariance. -/
theorem mapH2_congr {G A B : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] {f f' : A →+ B}
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (hf' : ∀ (g : G) (a : A), f' (g • a) = g • f' a) (h : f = f') :
    Work.GroupCohomology.mapH2 G f hf = Work.GroupCohomology.mapH2 G f' hf' := by
  subst h
  rfl

/-- Functoriality of `H²` stated with an arbitrary proof of equivariance for the composite. -/
theorem mapH2_comp' {G A B C : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (e : A →+ B) (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (f : B →+ C) (hf : ∀ (g : G) (b : B), f (g • b) = g • f b)
    (hfe : ∀ (g : G) (a : A), (f.comp e) (g • a) = g • (f.comp e) a) :
    Work.GroupCohomology.mapH2 G (f.comp e) hfe
      = (Work.GroupCohomology.mapH2 G f hf).comp (Work.GroupCohomology.mapH2 G e he) := by
  rw [mapH2_congr hfe (Work.GroupCohomology.IsEquivariant.comp hf he) rfl]
  exact Work.GroupCohomology.mapH2_comp G e f he hf

theorem h2Map_comp (p : ℕ) [NeZero p] (G : Type*) [Group G] [Fintype G] (i j : ℕ) (T : Type*)
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T]
    {m n l : ℕ} (Φ : Work.CohomologicalShrinking.OperatorMap G m n)
    (Ψ : Work.CohomologicalShrinking.OperatorMap G n l) :
    Work.CohomologicalShrinking.OperatorMap.h2Map (p := p) (G := G) (i := i) (j := j) (T := T)
        (Ψ.comp Φ)
      = (Work.CohomologicalShrinking.OperatorMap.h2Map (p := p) (G := G) (i := i) (j := j) (T := T) Ψ).comp
          (Work.CohomologicalShrinking.OperatorMap.h2Map (p := p) (G := G) (i := i) (j := j) (T := T) Φ) := by
  -- the additive map `E(m,τ) ⊗ T → E(l,τ) ⊗ T` induced by `Ψ.comp Φ` ...
  have hcomp : (LinearMap.rTensor T (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
        (E p G m i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T))
      = ((LinearMap.rTensor T (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
          (E p G n i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T))).comp
        (LinearMap.rTensor T (gradedMapLin p Φ.toHom Φ.surjective i j) :
          (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)) := by
    ext x
    show (LinearMap.rTensor T
          (gradedMapLin p (Ψ.toHom.comp Φ.toHom) (Ψ.surjective.comp Φ.surjective) i j)) x
        = (LinearMap.rTensor T (gradedMapLin p Ψ.toHom Ψ.surjective i j))
            ((LinearMap.rTensor T (gradedMapLin p Φ.toHom Φ.surjective i j)) x)
    rw [show gradedMapLin p (Ψ.toHom.comp Φ.toHom) (Ψ.surjective.comp Φ.surjective) i j
        = (gradedMapLin p Ψ.toHom Ψ.surjective i j).comp
            (gradedMapLin p Φ.toHom Φ.surjective i j)
        from functorial.gradedMapLin_comp p Φ.toHom Φ.surjective Ψ.toHom Ψ.surjective i j]
    exact LinearMap.rTensor_comp_apply (M := T)
      (g := gradedMapLin p Ψ.toHom Ψ.surjective i j)
      (f := gradedMapLin p Φ.toHom Φ.surjective i j) x
  -- ... `G`-equivariant (this is the equivariance datum of the induced map) ...
  have heq1 : ∀ (g : G) (x : E p G m i j ⊗[ZMod p] T),
      (LinearMap.rTensor T (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
        (E p G m i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T)) (g • x)
      = g • (LinearMap.rTensor T (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
        (E p G m i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T)) x :=
    fun g x => rTensor_equiv p (G := G)
      (f := gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j)
      (fun g y => gradedMapLin_smul p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective
        (Ψ.comp Φ).equivariant i j g y) g x
  -- ... and the composite map is `G`-equivariant because it *is* that map.
  have hfe : ∀ (g : G) (x : E p G m i j ⊗[ZMod p] T),
      (((LinearMap.rTensor T (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
          (E p G n i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T))).comp
        (LinearMap.rTensor T (gradedMapLin p Φ.toHom Φ.surjective i j) :
          (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T))) (g • x)
      = g • (((LinearMap.rTensor T (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
          (E p G n i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T))).comp
        (LinearMap.rTensor T (gradedMapLin p Φ.toHom Φ.surjective i j) :
          (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T))) x := by
    intro g x
    calc (((LinearMap.rTensor T (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
          (E p G n i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T))).comp
        (LinearMap.rTensor T (gradedMapLin p Φ.toHom Φ.surjective i j) :
          (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T))) (g • x)
        = (LinearMap.rTensor T (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
            (E p G m i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T)) (g • x) :=
          (congrArg (fun f : (E p G m i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T) =>
            f (g • x)) hcomp).symm
      _ = g • (LinearMap.rTensor T (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
            (E p G m i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T)) x := heq1 g x
      _ = g • (((LinearMap.rTensor T (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
          (E p G n i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T))).comp
        (LinearMap.rTensor T (gradedMapLin p Φ.toHom Φ.surjective i j) :
          (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T))) x := by
          rw [congrArg (fun f : (E p G m i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T) =>
            f x) hcomp]
  simp only [Work.CohomologicalShrinking.OperatorMap.h2Map]
  exact (mapH2_congr (G := G)
      (A := E p G m i j ⊗[ZMod p] T) (B := E p G l i j ⊗[ZMod p] T)
      (f := (LinearMap.rTensor T
        (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
        (E p G m i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T)))
      (f' := ((LinearMap.rTensor T (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
        (E p G n i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T))).comp
        (LinearMap.rTensor T (gradedMapLin p Φ.toHom Φ.surjective i j) :
        (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)))
      heq1 hfe hcomp).trans
    (mapH2_comp' (G := G)
      (A := E p G m i j ⊗[ZMod p] T) (B := E p G n i j ⊗[ZMod p] T)
      (C := E p G l i j ⊗[ZMod p] T)
      (e := (LinearMap.rTensor T (gradedMapLin p Φ.toHom Φ.surjective i j) :
        (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)))
      (f := (LinearMap.rTensor T (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
        (E p G n i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T)))
      _ _ hfe)

end Work.CohomologicalShrinking.operator
