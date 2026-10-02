import Mathlib
import Submission.Work.ThomBordism.degenerateFamily

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Dropping the empty pieces of a null-bordism family

A `Work.ThomBordism.NullBordismFamily ι F` is an oriented bordism whose boundary is identified with
the disjoint union `Σ i, (F i).pt` of the pieces of the family `F : ι → Man8`.  The `Σ`-type does
not see the pieces whose underlying space is *empty*: if `i` has `(F i).pt = ∅` then the `i`-th
summand contributes nothing to the disjoint union, so the families with index type `Fin N × ι` and
with index type `Fin N × {i : ι // Nonempty (F i).pt}` describe essentially the same bordisms.

This file makes that precise (`nullBordismFamily_subtype`): a null-bordism family with the
*nonempty* indices only (`Fin N × {i // Nonempty (F i).pt}`) yields one with all indices
(`Fin N × ι`).  The bounding manifold `W`, its relative fundamental class `w` and the
local-generator condition `w_fund` are untouched; only the identification `∂W ≃ₜ Σ (F i).pt` of the
boundary changes, through the homeomorphism

  `Σ x : Fin N × {i // Nonempty (F i).pt}, (F x.2.1).pt  ≃ₜ  Σ x : Fin N × ι, (F x.2).pt`

which is the identity on the fibres, with the index transported along `Subtype.val` in one
direction and along the canonical section `i ↦ ⟨i, ·⟩` (using the point itself as the witness) in the
other.

The boundary equation `w ↦ ∑ i, [F i]` then has to be transported as well: the summand attached to
an *empty* index `i` vanishes, because the fundamental class of an empty `Man8` is `0`
(`Work.ThomBordism.Man8.c_eq_zero_of_isEmpty`), and the `Finset` bookkeeping that removes these
vanishing summands is `Work.ThomBordism.Finset.sum_prod_subtype_eq_sum_of_eq_zero`.  For the surviving
indices the two summands are *equal*, not merely homologous: the two parametrisations of the boundary
differ only in the proof component of the index, where the two witnesses of `Nonempty (F i).pt` are
identified by proof irrelevance.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

attribute [local instance] Classical.propDecidable

namespace Work.ThomBordism

noncomputable section

open Work.Cohomology

/-! ## The two disjoint-union models of the boundary -/

section Sigma

variable {ι : Type} [Fintype ι] (F : ι → Man8) (N : ℕ)

/-- The map that remembers only the *index* `i` of a term `⟨n, ⟨i, h⟩⟩ ↦ ⟨n, i⟩` and is the
identity on the fibres: the inclusion of the disjoint union over the nonempty indices into the
disjoint union over all indices. -/
abbrev subSigmaToFun : (Σ x : Fin N × {i : ι // Nonempty (F i).pt}, (F x.2.1).pt) →
    (Σ x : Fin N × ι, (F x.2).pt) :=
  fun z => ⟨⟨z.1.1, z.1.2.1⟩, z.2⟩

/-- Its inverse: a point `⟨⟨n, i⟩, y⟩` of the right-hand side *is* a witness that `F i` is
nonempty, so the index can be lifted to the subtype of nonempty indices. -/
abbrev subSigmaInvFun : (Σ x : Fin N × ι, (F x.2).pt) →
    (Σ x : Fin N × {i : ι // Nonempty (F i).pt}, (F x.2.1).pt) :=
  fun w => ⟨⟨w.1.1, ⟨w.1.2, ⟨w.2⟩⟩⟩, w.2⟩

@[simp] lemma subSigmaToFun_apply (z :
    (Σ x : Fin N × {i : ι // Nonempty (F i).pt}, (F x.2.1).pt)) :
    subSigmaToFun F N z = ⟨⟨z.1.1, z.1.2.1⟩, z.2⟩ := rfl

@[simp] lemma subSigmaInvFun_apply (w : (Σ x : Fin N × ι, (F x.2).pt)) :
    subSigmaInvFun F N w = ⟨⟨w.1.1, ⟨w.1.2, ⟨w.2⟩⟩⟩, w.2⟩ := rfl

lemma subSigmaInvFun_subSigmaToFun (z :
    (Σ x : Fin N × {i : ι // Nonempty (F i).pt}, (F x.2.1).pt)) :
    subSigmaInvFun F N (subSigmaToFun F N z) = z := by
  rcases z with ⟨⟨n, i, hi⟩, y⟩
  apply Sigma.ext
  · apply Prod.ext rfl
    exact Subtype.ext rfl
  · exact HEq.refl y

lemma subSigmaToFun_subSigmaInvFun (w : (Σ x : Fin N × ι, (F x.2).pt)) :
    subSigmaToFun F N (subSigmaInvFun F N w) = w := by
  rcases w with ⟨⟨n, i⟩, y⟩
  rfl

lemma continuous_subSigmaToFun : Continuous (subSigmaToFun F N) :=
  @Continuous.sigma_map (Fin N × {i : ι // Nonempty (F i).pt}) (Fin N × ι)
    (fun x : Fin N × {i : ι // Nonempty (F i).pt} => (F x.2.1).pt)
    (fun x : Fin N × ι => (F x.2).pt)
    (fun x => Man8.topologicalSpace (F x.2.1)) (fun x => Man8.topologicalSpace (F x.2))
    (fun x => (x.1, x.2.1)) (fun _ y => y) (fun _ => continuous_id)

lemma isEmbedding_subSigmaToFun : Topology.IsEmbedding (subSigmaToFun F N) := by
  refine (@Topology.isEmbedding_sigmaMap (Fin N × {i : ι // Nonempty (F i).pt}) (Fin N × ι)
    (fun x : Fin N × {i : ι // Nonempty (F i).pt} => (F x.2.1).pt)
    (fun x : Fin N × ι => (F x.2).pt)
    (fun x => Man8.topologicalSpace (F x.2.1)) (fun x => Man8.topologicalSpace (F x.2))
    (fun x => (x.1, x.2.1)) (fun _ y => y) ?_).mpr (fun _ => ?_)
  · intro x y hxy
    obtain ⟨h1, h2⟩ := Prod.mk.inj hxy
    exact Prod.ext h1 (Subtype.ext h2)
  · exact Topology.IsEmbedding.id

/-- The inverse map is continuous: `subSigmaToFun` is an embedding and the two are mutually inverse. -/
lemma continuous_subSigmaInvFun : Continuous (subSigmaInvFun F N) := by
  rw [(isEmbedding_subSigmaToFun F N).continuous_iff]
  have hcomp : (subSigmaToFun F N) ∘ (subSigmaInvFun F N) = id := funext (subSigmaToFun_subSigmaInvFun F N)
  rw [hcomp]
  exact continuous_id

/-- **The two models of the boundary are homeomorphic**: the disjoint union over the nonempty
indices is the disjoint union over all indices, with the empty pieces dropped. -/
def subHomeo : (Σ x : Fin N × {i : ι // Nonempty (F i).pt}, (F x.2.1).pt) ≃ₜ
    (Σ x : Fin N × ι, (F x.2).pt) where
  toFun := subSigmaToFun F N
  invFun := subSigmaInvFun F N
  left_inv := subSigmaInvFun_subSigmaToFun F N
  right_inv := subSigmaToFun_subSigmaInvFun F N
  continuous_toFun := continuous_subSigmaToFun F N
  continuous_invFun := continuous_subSigmaInvFun F N

@[simp] lemma subHomeo_apply (z :
    (Σ x : Fin N × {i : ι // Nonempty (F i).pt}, (F x.2.1).pt)) :
    subHomeo F N z = ⟨⟨z.1.1, z.1.2.1⟩, z.2⟩ := rfl

@[simp] lemma subHomeo_symm_apply (w : (Σ x : Fin N × ι, (F x.2).pt)) :
    (subHomeo F N).symm w = ⟨⟨w.1.1, ⟨w.1.2, ⟨w.2⟩⟩⟩, w.2⟩ := rfl

end Sigma

/-! ## The boundary summands -/

section Summand

variable {ι : Type} (F : ι → Man8) {W : Type} [TopologicalSpace W] (b : Set W)

/-- The parametrisation of the `i`-th piece of the boundary induced by `∂W ≃ₜ Σ i, (F i).pt`. -/
def subBdryMor (bdry : b ≃ₜ (Σ i : ι, (F i).pt)) (i : ι) : (F i).X ⟶ TopCat.of b :=
  TopCat.ofHom ⟨fun y => bdry.symm ⟨i, y⟩, bdry.continuous_invFun.comp continuous_sigmaMk⟩

@[simp] lemma subBdryMor_apply (bdry : b ≃ₜ (Σ i : ι, (F i).pt)) (i : ι) (y : (F i).pt) :
    (subBdryMor F b bdry i) y = bdry.symm ⟨i, y⟩ := rfl

/-- The `i`-th summand of the boundary equation of a null-bordism family: the push-forward of the
fundamental class of the piece `F i` into the homology of the boundary.  (The field
`NullBordismFamily.hw` states that `hPairδ` is the sum of these summands.) -/
def subBdrySummand (bdry : b ≃ₜ (Σ i : ι, (F i).pt)) (i : ι) :
    (chainC ℤ (TopCat.toSSet.obj (TopCat.of b))).homology 8 :=
  HomologicalComplex.homologyMap (chainMap ℤ (F i).X (TopCat.of b) (subBdryMor F b bdry i)) 8
    (F i).c

end Summand

/-! ## The transported boundary parametrisation -/

section Bdry

variable {ι : Type} [Fintype ι] (F : ι → Man8) (N : ℕ)

/-- The boundary parametrisation of the family with the empty pieces dropped: compose the given
one with the homeomorphism `subHomeo` of the two disjoint-union models. -/
def subBdry (W : NullBordismFamily (Fin N × {i : ι // Nonempty (F i).pt}) (fun x => F x.2.1)) :
    ((modelWithCornersEuclideanHalfSpace 9).boundary W.W) ≃ₜ
      (Σ x : Fin N × ι, (F x.2).pt) where
  toFun := fun z => subHomeo F N (W.bdry z)
  invFun := fun w => W.bdry.symm ((subHomeo F N).symm w)
  left_inv := by
    intro z
    show W.bdry.symm ((subHomeo F N).symm (subHomeo F N (W.bdry z))) = z
    rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
  right_inv := by
    intro w
    show subHomeo F N (W.bdry (W.bdry.symm ((subHomeo F N).symm w))) = w
    rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  continuous_toFun := (subHomeo F N).continuous_toFun.comp W.bdry.continuous_toFun
  continuous_invFun := W.bdry.continuous_invFun.comp (subHomeo F N).continuous_invFun

@[simp] lemma subBdry_apply
    (W : NullBordismFamily (Fin N × {i : ι // Nonempty (F i).pt}) (fun x => F x.2.1))
    (z : (modelWithCornersEuclideanHalfSpace 9).boundary W.W) :
    subBdry F N W z = subHomeo F N (W.bdry z) := rfl

@[simp] lemma subBdry_symm_apply
    (W : NullBordismFamily (Fin N × {i : ι // Nonempty (F i).pt}) (fun x => F x.2.1))
    (w : (Σ x : Fin N × ι, (F x.2).pt)) :
    (subBdry F N W).symm w = W.bdry.symm ((subHomeo F N).symm w) := rfl

end Bdry

end

end Work.ThomBordism
