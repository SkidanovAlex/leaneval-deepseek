import Submission.Work.ThomBordism.chainSetup_cone

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The interface between the cochain-level Thom map `psiAbs` and the local Thom map

`Work.ThomBordism.psiAbs Z n U τ W hW m a` is the cochain-level cup of the pullback of the base
cochain `a : C^m(W)` with the chosen relative cocycle representative `tauRepAt` of `τ` on the piece
`W ⊆ U`.  Its class, in `PieceCoh Z W (m + n)`, is — by construction of the honest mixed cup product
(`Work.Cohomology.mixedRelCupH`) — the local Thom map of the restricted class `τ|_W` applied to the
class of `a`.

This file only fixes the *statement* of that identification (`PsiClassHyp`), which is the interface
between the cochain-level (cone, tower) side of the argument and the abstract Thom side.
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **The `psiAbs`/`localThomMap` interface.**  For every degree `m` and every **cocycle**
`a : C^m(W)`, the relative cohomology class of the cochain-level cup `psiAbs … a` is the local Thom
map of the restricted class `τ|_W` applied to the class of `a`.

(The cocycle condition on `a` is what makes `psiAbs … a` a cocycle — `psiAbs_diff` — and the
cohomology class of `a` an element of `H^m(W;ℤ)`.  The extra hypothesis `hcyc` is a proof that
`psiAbs … a` is a relative cocycle, which the caller will supply from `psiAbs_diff` and `ha`.) -/
def PsiClassHyp (Z : RealBundle B F ι) (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (W : Set B) (hW : W ⊆ U) : Prop :=
  ∀ (m : ℕ) (a : BaseC W m) (ha : cochainDiff ℤ (baseSSet W) a = 0)
    (hcyc : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (m + n)
      (psiAbs Z n U τ W hW m a) = 0),
    relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (psiAbs Z n U τ W hW m a) hcyc
      = Work.Thom.localThomMap Z n W
          ((pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' U)
            (Z.proj ⁻¹' W) (Set.preimage_mono hW) n).hom τ) m
          (cohomologyClassOf ℤ (baseSSet W) a ha)

end

end Work.ThomBordism
