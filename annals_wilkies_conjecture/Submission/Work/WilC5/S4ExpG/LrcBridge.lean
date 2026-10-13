import Mathlib
import Submission.Work.WilC5.S4OnePoint
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_add_of_model
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.S4ExpF.logclosure_exp
import Submission.Work.WilC5.S4ExpF.logFun_zpow
import Submission.Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.tr_leE_axioms
import Submission.Work.WilC2.Dcl

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilC5.S4ExpG

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder
/-! ## 1. The `LRc`-symbols of a model of the `rexp`-reduct, in field notation

`LRc = (ring ⊕ rexp)[[ℝ]]`, and in the whole development the `LRc`-structure of a model of `TE`
is the canonical one synthesised from the `Ring.CompatibleRing` structure, the `rexp` structure and
the real constants (`S4Setup.lean`'s `reductStruct`, which coincides with
`LR.withConstantsStructure ℝ`).  Hence the `LRc`-symbols for `+, *,-,0,1` are the field operations
and the `rexp` symbol is `rexpFromExp`.  The lemmas below record this in a form usable in a
`rw`. -/

section LrcBridge

variable {M : Type} [LEc.Structure M] [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
  [(FirstOrder.Language.constantsOn ℝ).Structure M]

theorem lpLrcFunMap_add (x y : M) :
    @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 2
      (Sum.inl (Sum.inl Ring.addFunc)) ![x, y] = x + y := by
  rw [show (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 2
        (Sum.inl (Sum.inl Ring.addFunc)) ![x, y])
      = (@FirstOrder.Language.Structure.funMap FirstOrder.Language.ring M _ 2 Ring.addFunc
          ![x, y]) from rfl,
    FirstOrder.Ring.CompatibleRing.funMap_add]
  rfl

theorem lpLrcFunMap_mul (x y : M) :
    @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 2
      (Sum.inl (Sum.inl Ring.mulFunc)) ![x, y] = x * y := by
  rw [show (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 2
        (Sum.inl (Sum.inl Ring.mulFunc)) ![x, y])
      = (@FirstOrder.Language.Structure.funMap FirstOrder.Language.ring M _ 2 Ring.mulFunc
          ![x, y]) from rfl,
    FirstOrder.Ring.CompatibleRing.funMap_mul]
  rfl

theorem lpLrcFunMap_neg (x : M) :
    @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 1
      (Sum.inl (Sum.inl Ring.negFunc)) ![x] = -x := by
  rw [show (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 1
        (Sum.inl (Sum.inl Ring.negFunc)) ![x])
      = (@FirstOrder.Language.Structure.funMap FirstOrder.Language.ring M _ 1 Ring.negFunc
          ![x]) from rfl,
    FirstOrder.Ring.CompatibleRing.funMap_neg]
  rfl

theorem lpLrcFunMap_zero :
    @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 0
      (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → M) = (0 : M) := by
  rw [show (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 0
        (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → M))
      = (@FirstOrder.Language.Structure.funMap FirstOrder.Language.ring M _ 0 Ring.zeroFunc
          (![] : Fin 0 → M)) from rfl,
    FirstOrder.Ring.CompatibleRing.funMap_zero]

theorem lpLrcFunMap_one :
    @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 0
      (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → M) = (1 : M) := by
  rw [show (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 0
        (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → M))
      = (@FirstOrder.Language.Structure.funMap FirstOrder.Language.ring M _ 0 Ring.oneFunc
          (![] : Fin 0 → M)) from rfl,
    FirstOrder.Ring.CompatibleRing.funMap_one]

theorem lpLrcFunMap_rexp
    (hrexp : ∀ x : M, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL M _ 1
      WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x) (x : M) :
    @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 1
      (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![x] = Work.WilC5.rexpFromExp x := by
  rw [show (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 1
        (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![x])
      = (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL M _ 1
          WilkiesDesign.CG.rexpFunc.rexp ![x]) from rfl,
    hrexp]

/-! ## 2. The same, for the induced structure of a substructure -/

/-- The value in `M` of the `LRc`-addition of a substructure. -/
theorem lpSubFunMap_add (T : WilkiesDesign.CG.LRc.Substructure M) (x y : ↥T) :
    ((@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
        (Sum.inl (Sum.inl Ring.addFunc)) ![x, y] : ↥T) : M) = (x : M) + (y : M) := by
  change T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
      (Sum.inl (Sum.inl Ring.addFunc)) ![x, y]) = (x : M) + (y : M)
  have h3 : T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
        (Sum.inl (Sum.inl Ring.addFunc)) ![x, y])
      = @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 2
          (Sum.inl (Sum.inl Ring.addFunc)) ![(x : M), (y : M)] := by
    have h := @FirstOrder.Language.Embedding.map_fun' WilkiesDesign.CG.LRc ↥T M _ _
      (Substructure.subtype T) 2 (Sum.inl (Sum.inl Ring.addFunc)) (![x, y])
    have h2 : (T.subtype.toFun ∘ ![x, y]) = ![(x : M), (y : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2] at h
    exact h
  rw [h3, lpLrcFunMap_add]

theorem lpSubFunMap_mul (T : WilkiesDesign.CG.LRc.Substructure M) (x y : ↥T) :
    ((@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
        (Sum.inl (Sum.inl Ring.mulFunc)) ![x, y] : ↥T) : M) = (x : M) * (y : M) := by
  change T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
      (Sum.inl (Sum.inl Ring.mulFunc)) ![x, y]) = (x : M) * (y : M)
  have h3 : T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
        (Sum.inl (Sum.inl Ring.mulFunc)) ![x, y])
      = @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 2
          (Sum.inl (Sum.inl Ring.mulFunc)) ![(x : M), (y : M)] := by
    have h := @FirstOrder.Language.Embedding.map_fun' WilkiesDesign.CG.LRc ↥T M _ _
      (Substructure.subtype T) 2 (Sum.inl (Sum.inl Ring.mulFunc)) (![x, y])
    have h2 : (T.subtype.toFun ∘ ![x, y]) = ![(x : M), (y : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2] at h
    exact h
  rw [h3, lpLrcFunMap_mul]

theorem lpSubFunMap_neg (T : WilkiesDesign.CG.LRc.Substructure M) (x : ↥T) :
    ((@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
        (Sum.inl (Sum.inl Ring.negFunc)) ![x] : ↥T) : M) = -(x : M) := by
  change T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
      (Sum.inl (Sum.inl Ring.negFunc)) ![x]) = -(x : M)
  have h3 : T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
        (Sum.inl (Sum.inl Ring.negFunc)) ![x])
      = @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 1
          (Sum.inl (Sum.inl Ring.negFunc)) ![(x : M)] := by
    have h := @FirstOrder.Language.Embedding.map_fun' WilkiesDesign.CG.LRc ↥T M _ _
      (Substructure.subtype T) 1 (Sum.inl (Sum.inl Ring.negFunc)) (![x])
    have h2 : (T.subtype.toFun ∘ ![x]) = ![(x : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2] at h
    exact h
  rw [h3, lpLrcFunMap_neg]

theorem lpSubFunMap_zero (T : WilkiesDesign.CG.LRc.Substructure M) :
    ((@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
        (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → ↥T) : ↥T) : M) = (0 : M) := by
  change T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
      (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → ↥T)) = (0 : M)
  have h3 : T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
        (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → ↥T))
      = @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 0
          (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → M) := by
    have h := @FirstOrder.Language.Embedding.map_fun' WilkiesDesign.CG.LRc ↥T M _ _
      (Substructure.subtype T) 0 (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → ↥T)
    have h2 : (T.subtype.toFun ∘ (![] : Fin 0 → ↥T)) = (![] : Fin 0 → M) := by
      funext i; exact Fin.elim0 i
    rw [h2] at h
    exact h
  rw [h3, lpLrcFunMap_zero]

theorem lpSubFunMap_one (T : WilkiesDesign.CG.LRc.Substructure M) :
    ((@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
        (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → ↥T) : ↥T) : M) = (1 : M) := by
  change T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
      (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → ↥T)) = (1 : M)
  have h3 : T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
        (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → ↥T))
      = @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 0
          (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → M) := by
    have h := @FirstOrder.Language.Embedding.map_fun' WilkiesDesign.CG.LRc ↥T M _ _
      (Substructure.subtype T) 0 (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → ↥T)
    have h2 : (T.subtype.toFun ∘ (![] : Fin 0 → ↥T)) = (![] : Fin 0 → M) := by
      funext i; exact Fin.elim0 i
    rw [h2] at h
    exact h
  rw [h3, lpLrcFunMap_one]

theorem lpSubFunMap_rexp
    (hrexp : ∀ x : M, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL M _ 1
      WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (T : WilkiesDesign.CG.LRc.Substructure M) (y : ↥T) :
    ((@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
        (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![y] : ↥T) : M)
      = Work.WilC5.rexpFromExp (y : M) := by
  change T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
      (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![y]) = Work.WilC5.rexpFromExp (y : M)
  have h3 : T.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
        (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![y])
      = @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 1
          (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![(y : M)] := by
    have h := @FirstOrder.Language.Embedding.map_fun' WilkiesDesign.CG.LRc ↥T M _ _
      (Substructure.subtype T) 1 (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) (![y])
    have h2 : (T.subtype.toFun ∘ ![y]) = ![(y : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2] at h
    exact h
  rw [h3, lpLrcFunMap_rexp hrexp]

/-! ## 3. Identifying an element of a substructure given by its value with a symbol -/

/-- Changing the membership proof of an element of a substructure. -/
theorem lpSubtype_mem_congr {T : WilkiesDesign.CG.LRc.Substructure M} {x : M} (h₁ h₂ : x ∈ T) :
    (⟨x, h₁⟩ : ↥T) = ⟨x, h₂⟩ := Subtype.ext rfl

theorem lpSubElem_add (T : WilkiesDesign.CG.LRc.Substructure M) (x y : ↥T)
    (h : (x : M) + (y : M) ∈ T) :
    (⟨(x : M) + (y : M), h⟩ : ↥T) =
      @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
        (Sum.inl (Sum.inl Ring.addFunc)) ![x, y] := by
  apply Subtype.ext
  rw [lpSubFunMap_add]

theorem lpSubElem_mul (T : WilkiesDesign.CG.LRc.Substructure M) (x y : ↥T)
    (h : (x : M) * (y : M) ∈ T) :
    (⟨(x : M) * (y : M), h⟩ : ↥T) =
      @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
        (Sum.inl (Sum.inl Ring.mulFunc)) ![x, y] := by
  apply Subtype.ext
  rw [lpSubFunMap_mul]

theorem lpSubElem_neg (T : WilkiesDesign.CG.LRc.Substructure M) (x : ↥T) (h : -(x : M) ∈ T) :
    (⟨-(x : M), h⟩ : ↥T) =
      @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
        (Sum.inl (Sum.inl Ring.negFunc)) ![x] := by
  apply Subtype.ext
  rw [lpSubFunMap_neg]

theorem lpSubElem_zero (T : WilkiesDesign.CG.LRc.Substructure M) (h : (0 : M) ∈ T) :
    (⟨(0 : M), h⟩ : ↥T) =
      @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
        (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → ↥T) := by
  apply Subtype.ext
  rw [lpSubFunMap_zero]

theorem lpSubElem_one (T : WilkiesDesign.CG.LRc.Substructure M) (h : (1 : M) ∈ T) :
    (⟨(1 : M), h⟩ : ↥T) =
      @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
        (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → ↥T) := by
  apply Subtype.ext
  rw [lpSubFunMap_one]

/-- A `Dcl`-closed-style substructure whose `rexp` symbol is `rexpFromExp` is closed under
`rexpFromExp`. -/
theorem lpMem_rexp
    (hrexp : ∀ x : M, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL M _ 1
      WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    {T : WilkiesDesign.CG.LRc.Substructure M} {y : M} (hy : y ∈ T) :
    Work.WilC5.rexpFromExp y ∈ T := by
  have h : Work.WilC5.rexpFromExp y =
      @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M _ 1
        (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![y] :=
    (lpLrcFunMap_rexp hrexp y).symm
  rw [h]
  exact T.fun_mem _ _ (fun i => by fin_cases i; exact hy)

end LrcBridge

end Work.WilC5.S4ExpG
