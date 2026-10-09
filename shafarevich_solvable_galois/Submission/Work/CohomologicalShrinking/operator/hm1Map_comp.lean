/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Composition compatibility of `OperatorMap.hm1Map`

`Work.CohomologicalShrinking.OperatorMap.hm1Map` is the map induced on the Tate cohomology
group `Ĥ⁻¹(G, E(-,τ) ⊗ N)` by a surjective `G`-equivariant homomorphism `F(m) ⇢ F(n)` of free
`G`-operator groups.  This file records that it is compatible with composition of operator
maps: the induced map of `Ψ.comp Φ` is the composite of the induced maps of `Φ` and `Ψ`.

The proof is a direct application of the functoriality of Tate cohomology
(`Work.CohomologicalShrinking.tate.Hm1Map_comp`): it suffices to know that the `𝔽_p`-linear map
`E(m,τ) ⊗ N → E(l,τ) ⊗ N` induced by `Ψ.comp Φ` is the composite of the maps induced by `Φ`
and by `Ψ`, which is `gradedMapLin_comp` (`Ψ̄ ∘ Φ̄ = (Ψ ∘ Φ)̄`) together with the compatibility
of `rTensor` with composition, `LinearMap.rTensor_comp`.

## Main results

* `Work.CohomologicalShrinking.operator.Hm1Map_congr` : the induced map on `Ĥ⁻¹` only depends
  on the underlying map, not on the proof of equivariance.
* `Work.CohomologicalShrinking.operator.hm1Map_comp` : `hm1Map (Ψ.comp Φ) = hm1Map Ψ ∘ hm1Map Φ`.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.OperatorMap
import Submission.Work.CohomologicalShrinking.Shrinking
import Submission.Work.CohomologicalShrinking.tate.Hm1Map_comp
import Submission.Work.CohomologicalShrinking.functorial.gradedMapLin_comp

open scoped TensorProduct

namespace Work.CohomologicalShrinking.operator

open Work.CohomologicalShrinking

/-- The map induced on `Ĥ⁻¹` by a `G`-equivariant additive map depends only on the underlying
map, not on the proof of equivariance. -/
theorem Hm1Map_congr {G A B : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] {f f' : A →+ B}
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (hf' : ∀ (g : G) (a : A), f' (g • a) = g • f' a) (h : f = f') :
    Work.Tate.Hm1Map G A B f hf = Work.Tate.Hm1Map G A B f' hf' := by
  subst h
  rfl

theorem hm1Map_comp (p : ℕ) [NeZero p] (G : Type*) [Group G] [Fintype G]
    (i j : ℕ) (N : Type*) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] {m n l : ℕ}
    (Φ : Work.CohomologicalShrinking.OperatorMap G m n)
    (Ψ : Work.CohomologicalShrinking.OperatorMap G n l) :
    Work.CohomologicalShrinking.OperatorMap.hm1Map (p := p) (G := G) (i := i) (j := j) (N := N)
        (Ψ.comp Φ)
      = (Work.CohomologicalShrinking.OperatorMap.hm1Map (p := p) (G := G) (i := i) (j := j) (N := N) Ψ).comp
          (Work.CohomologicalShrinking.OperatorMap.hm1Map (p := p) (G := G) (i := i) (j := j) (N := N) Φ) := by
  -- the additive map `E(m,τ) ⊗ N → E(l,τ) ⊗ N` induced by `Ψ.comp Φ` ...
  have hcomp : (LinearMap.rTensor N (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
        (E p G m i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N))
      = ((LinearMap.rTensor N (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
          (E p G n i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N))).comp
        (LinearMap.rTensor N (gradedMapLin p Φ.toHom Φ.surjective i j) :
          (E p G m i j ⊗[ZMod p] N) →+ (E p G n i j ⊗[ZMod p] N)) := by
    ext x
    show (LinearMap.rTensor N
          (gradedMapLin p (Ψ.toHom.comp Φ.toHom) (Ψ.surjective.comp Φ.surjective) i j)) x
        = (LinearMap.rTensor N (gradedMapLin p Ψ.toHom Ψ.surjective i j))
            ((LinearMap.rTensor N (gradedMapLin p Φ.toHom Φ.surjective i j)) x)
    rw [show gradedMapLin p (Ψ.toHom.comp Φ.toHom) (Ψ.surjective.comp Φ.surjective) i j
        = (gradedMapLin p Ψ.toHom Ψ.surjective i j).comp
            (gradedMapLin p Φ.toHom Φ.surjective i j)
        from functorial.gradedMapLin_comp p Φ.toHom Φ.surjective Ψ.toHom Ψ.surjective i j]
    exact LinearMap.rTensor_comp_apply (M := N)
      (g := gradedMapLin p Ψ.toHom Ψ.surjective i j)
      (f := gradedMapLin p Φ.toHom Φ.surjective i j) x
  -- ... `G`-equivariant (this is the equivariance datum of the induced map) ...
  have heq1 : ∀ (g : G) (x : E p G m i j ⊗[ZMod p] N),
      (LinearMap.rTensor N (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
        (E p G m i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N)) (g • x)
      = g • (LinearMap.rTensor N (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
        (E p G m i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N)) x :=
    fun g x => rTensor_equiv p (G := G)
      (f := gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j)
      (fun g y => gradedMapLin_smul p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective
        (Ψ.comp Φ).equivariant i j g y) g x
  -- ... and the composite map is `G`-equivariant because it *is* that map.
  have hfe : ∀ (g : G) (x : E p G m i j ⊗[ZMod p] N),
      (((LinearMap.rTensor N (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
          (E p G n i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N))).comp
        (LinearMap.rTensor N (gradedMapLin p Φ.toHom Φ.surjective i j) :
          (E p G m i j ⊗[ZMod p] N) →+ (E p G n i j ⊗[ZMod p] N))) (g • x)
      = g • (((LinearMap.rTensor N (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
          (E p G n i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N))).comp
        (LinearMap.rTensor N (gradedMapLin p Φ.toHom Φ.surjective i j) :
          (E p G m i j ⊗[ZMod p] N) →+ (E p G n i j ⊗[ZMod p] N))) x := by
    intro g x
    calc (((LinearMap.rTensor N (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
          (E p G n i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N))).comp
        (LinearMap.rTensor N (gradedMapLin p Φ.toHom Φ.surjective i j) :
          (E p G m i j ⊗[ZMod p] N) →+ (E p G n i j ⊗[ZMod p] N))) (g • x)
        = (LinearMap.rTensor N (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
            (E p G m i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N)) (g • x) :=
          (congrArg (fun f : (E p G m i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N) =>
            f (g • x)) hcomp).symm
      _ = g • (LinearMap.rTensor N (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
            (E p G m i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N)) x := heq1 g x
      _ = g • (((LinearMap.rTensor N (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
          (E p G n i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N))).comp
        (LinearMap.rTensor N (gradedMapLin p Φ.toHom Φ.surjective i j) :
          (E p G m i j ⊗[ZMod p] N) →+ (E p G n i j ⊗[ZMod p] N))) x := by
          rw [congrArg (fun f : (E p G m i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N) =>
            f x) hcomp]
  simp only [Work.CohomologicalShrinking.OperatorMap.hm1Map]
  exact (Hm1Map_congr (G := G)
      (A := E p G m i j ⊗[ZMod p] N) (B := E p G l i j ⊗[ZMod p] N)
      (f := (LinearMap.rTensor N (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
        (E p G m i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N)))
      (f' := ((LinearMap.rTensor N (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
        (E p G n i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N))).comp
        (LinearMap.rTensor N (gradedMapLin p Φ.toHom Φ.surjective i j) :
        (E p G m i j ⊗[ZMod p] N) →+ (E p G n i j ⊗[ZMod p] N)))
      _ hfe hcomp).trans
    (Work.CohomologicalShrinking.tate.Hm1Map_comp (G := G)
      (A := E p G m i j ⊗[ZMod p] N) (B := E p G n i j ⊗[ZMod p] N) (C := E p G l i j ⊗[ZMod p] N)
      (e := (LinearMap.rTensor N (gradedMapLin p Φ.toHom Φ.surjective i j) :
        (E p G m i j ⊗[ZMod p] N) →+ (E p G n i j ⊗[ZMod p] N)))
      (f := (LinearMap.rTensor N (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
        (E p G n i j ⊗[ZMod p] N) →+ (E p G l i j ⊗[ZMod p] N)))
      _ _ hfe)

end Work.CohomologicalShrinking.operator
