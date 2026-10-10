import Mathlib.Tactic.Have
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.TensorProduct.Map
import Submission.Work.CohomologicalShrinking.Corollaries
import Submission.Work.CohomologicalShrinking.operator.hm1Map_comp
import Submission.Work.CohomologicalShrinking.tate.Hm2Map_comp

open scoped TensorProduct

namespace Work.CohomologicalShrinking.operator

open Work.CohomologicalShrinking

/-- The map induced on `Ĥ⁻²` by a `G`-equivariant additive map depends only on the underlying
map, not on the proof of equivariance. -/
theorem Hm2Map_congr {G A B : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] {f f' : A →+ B}
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (hf' : ∀ (g : G) (a : A), f' (g • a) = g • f' a) (h : f = f') :
    Work.Tate.Hm2Map (A := A) (B := B) f hf = Work.Tate.Hm2Map (A := A) (B := B) f' hf' := by
  subst h
  rfl

theorem hm2Map_comp (p : ℕ) [NeZero p] (G : Type*) [Group G] [Fintype G] (i j : ℕ) (T : Type*)
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T]
    {m n l : ℕ} (Φ : Work.CohomologicalShrinking.OperatorMap G m n)
    (Ψ : Work.CohomologicalShrinking.OperatorMap G n l) :
    Work.CohomologicalShrinking.OperatorMap.hm2Map (p := p) (G := G) (i := i) (j := j) (T := T)
        (Ψ.comp Φ)
      = (Work.CohomologicalShrinking.OperatorMap.hm2Map (p := p) (G := G) (i := i) (j := j) (T := T) Ψ).comp
          (Work.CohomologicalShrinking.OperatorMap.hm2Map (p := p) (G := G) (i := i) (j := j) (T := T) Φ) := by
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
  simp only [Work.CohomologicalShrinking.OperatorMap.hm2Map]
  exact (Hm2Map_congr (G := G)
      (A := E p G m i j ⊗[ZMod p] T) (B := E p G l i j ⊗[ZMod p] T)
      (f := (LinearMap.rTensor T (gradedMapLin p (Ψ.comp Φ).toHom (Ψ.comp Φ).surjective i j) :
        (E p G m i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T)))
      (f' := ((LinearMap.rTensor T (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
        (E p G n i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T))).comp
        (LinearMap.rTensor T (gradedMapLin p Φ.toHom Φ.surjective i j) :
        (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)))
      _ hfe hcomp).trans
    (Work.CohomologicalShrinking.tate.Hm2Map_comp (G := G)
      (A := E p G m i j ⊗[ZMod p] T) (B := E p G n i j ⊗[ZMod p] T) (C := E p G l i j ⊗[ZMod p] T)
      (e := (LinearMap.rTensor T (gradedMapLin p Φ.toHom Φ.surjective i j) :
        (E p G m i j ⊗[ZMod p] T) →+ (E p G n i j ⊗[ZMod p] T)))
      (f := (LinearMap.rTensor T (gradedMapLin p Ψ.toHom Ψ.surjective i j) :
        (E p G n i j ⊗[ZMod p] T) →+ (E p G l i j ⊗[ZMod p] T)))
      _ _ hfe)

end Work.CohomologicalShrinking.operator
