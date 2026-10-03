/-
# The transfer of vanishing from the small model

The decoding `S.dec : S.Vx ⤳ V` of a skeleton induces a monoid homomorphism
`decode v : VertexGroup (S.encObj v) →* VertexGroup v` on the vertex groups (the casting of
vertices along `S.decObj (S.encObj v) = v` composed with the path-level decoding), and the encoding
`S.enc` induces an inverse `encVG v : VertexGroup v →* VertexGroup (S.encObj v)`; `decode` is a left
inverse of `encVG`, hence injective.

The main result of this file is that the decode of the relator normal closure of the small
presentation is contained in that of `P`: the relators of the small presentation are the encodings
of the relators of `P` occurring in the datum, and the decode of a conjugate of such a relator is a
conjugate of the corresponding relator of `P`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.Case1.Skeleton
import Submission.Work.Case1.CastVG
import Submission.Work.Case1.SmallPresentation
import Submission.Work.ORLocInd.Howie.conjPathHom_mem_relatorNormalClosure

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Work.Case1

open Quiver

namespace SmallTransfer

variable {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V] {W : Type u}
variable (S : Skel V W)

/-- The decoding homomorphism `VertexGroup p →* VertexGroup (S.decObj p)`. -/
noncomputable def decVG (p : S.Vx) :
    Work.ORLocInd.Howie.VertexGroup p →*
      Work.ORLocInd.Howie.VertexGroup (S.decObj p) where
  toFun x := ⟨S.dec.mapPath x.1, (PrefunctorAux.mapPath_isReduced_iff S.dec S.decObj_injective
    (fun _ _ => S.dec_map_injective) x.1).mpr x.2⟩
  map_one' := Subtype.ext (Prefunctor.mapPath_nil S.dec p)
  map_mul' x y := Subtype.ext (PrefunctorAux.mapPath_pmul S.dec S.decObj_injective
    (fun _ _ => S.dec_map_injective) x.1 y.1)

@[simp] theorem decVG_apply (p : S.Vx) (x : Work.ORLocInd.Howie.VertexGroup p) :
    (decVG S p x).1 = S.dec.mapPath x.1 := rfl

/-- The encoding homomorphism `VertexGroup x →* VertexGroup (S.encObj x)`. -/
noncomputable def encVG (x : V) :
    Work.ORLocInd.Howie.VertexGroup x →*
      Work.ORLocInd.Howie.VertexGroup (S.encObj x) where
  toFun y := ⟨S.enc.mapPath y.1, (PrefunctorAux.mapPath_isReduced_iff S.enc S.encObj_injective
    (fun _ _ => S.enc_map_injective) y.1).mpr y.2⟩
  map_one' := Subtype.ext (Prefunctor.mapPath_nil S.enc x)
  map_mul' y z := Subtype.ext (PrefunctorAux.mapPath_pmul S.enc S.encObj_injective
    (fun _ _ => S.enc_map_injective) y.1 z.1)

@[simp] theorem encVG_apply (x : V) (y : Work.ORLocInd.Howie.VertexGroup x) :
    (encVG S x y).1 = S.enc.mapPath y.1 := rfl

/-- The decoding homomorphism `VertexGroup (S.encObj v) →* VertexGroup v`. -/
noncomputable def decode (v : V) :
    Work.ORLocInd.Howie.VertexGroup (S.encObj v) →*
      Work.ORLocInd.Howie.VertexGroup v :=
  (castVG (Skel.decObj_encObj S v)).comp (decVG S (S.encObj v))

@[simp] theorem decode_apply (v : V) (x : Work.ORLocInd.Howie.VertexGroup (S.encObj v)) :
    decode S v x = castVG (Skel.decObj_encObj S v) (decVG S (S.encObj v) x) := rfl

/-- `decode` is a left inverse of `encVG`. -/
theorem decode_encVG (v : V) (x : Work.ORLocInd.Howie.VertexGroup v) :
    decode S v (encVG S v x) = x := by
  apply Subtype.ext
  show (castVG (Skel.decObj_encObj S v)
    (decVG S (S.encObj v) (encVG S v x))).1 = x.1
  rw [castVG_coe, decVG_apply, encVG_apply, Skel.dec_mapPath_enc_mapPath,
    Quiver.Path.cast_cast, PathCast.cast_self]

/-- The relator `P.path i`, as an element of the vertex group at its base vertex, lies in the
normal closure of the relators. -/
theorem relatorLoop_mem (P : Work.ORLocInd.Howie.Presentation V) (i : P.ι) :
    (⟨P.path i, P.reduced i⟩ : Work.ORLocInd.Howie.VertexGroup (P.base i)) ∈
      P.relatorNormalClosure (P.base i) := by
  refine Subgroup.subset_normalClosure
    ⟨i, Quiver.Path.nil, Quiver.Path.IsReduced.nil _, ?_⟩
  apply Subtype.ext
  show P.path i = Work.ORLocInd.Howie.pmul (Quiver.Path.nil : Quiver.Path (P.base i) (P.base i))
    (Work.ORLocInd.Howie.pmul (P.path i) Quiver.Path.nil)
  rw [Work.ORLocInd.Howie.pmul_nil_left, Work.ORLocInd.Howie.pmul_nil_right,
    Work.ORLocInd.Howie.red_eq_self (P.reduced i)]
  exact (Work.ORLocInd.Howie.red_eq_self (P.reduced i)).symm

/-- The relator normal closure of the small presentation is carried into that of `P` by the
decoding. -/
theorem decode_relatorNormalClosure (P : Work.ORLocInd.Howie.Presentation V) {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n)
    (hrel : ∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i) :
    (SmallPres.smallPresentation S P D hrel).relatorNormalClosure (S.encObj v) ≤
      Subgroup.comap (decode S v) (P.relatorNormalClosure v) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨r, δ', hδ', rfl⟩
  let i : P.ι := SmallPres.rel P D r.down
  set Dd : Quiver.Path (S.decObj (S.encObj v)) (S.decObj (S.encObj (P.base i))) :=
    S.dec.mapPath δ' with hDd
  have hloop : (⟨P.path i, P.reduced i⟩ : Work.ORLocInd.Howie.VertexGroup (P.base i)) ∈
      P.relatorNormalClosure (P.base i) := relatorLoop_mem P i
  have hA : castVG (Skel.dO S (P.base i))
      (⟨P.path i, P.reduced i⟩ : Work.ORLocInd.Howie.VertexGroup (P.base i)) ∈
      P.relatorNormalClosure (S.decObj (S.encObj (P.base i))) :=
    castVG_mem_relatorNormalClosure (P := P) (Skel.dO S (P.base i)) hloop
  have hAval : (castVG (Skel.dO S (P.base i))
      (⟨P.path i, P.reduced i⟩ : Work.ORLocInd.Howie.VertexGroup (P.base i))).1 =
      (P.path i).cast (Skel.dO S (P.base i)) (Skel.dO S (P.base i)) :=
    castVG_coe _ _
  have hconj : Work.ORLocInd.Howie.conjPathHom Dd (castVG (Skel.dO S (P.base i))
      (⟨P.path i, P.reduced i⟩ : Work.ORLocInd.Howie.VertexGroup (P.base i))) ∈
      P.relatorNormalClosure (S.decObj (S.encObj v)) :=
    Work.ORLocInd.Howie.conjPathHom_mem_relatorNormalClosure P Dd hA
  change decode S v (⟨Work.ORLocInd.Howie.pmul δ'
      (Work.ORLocInd.Howie.pmul ((SmallPres.smallPresentation S P D hrel).path r) δ'.reverse),
      Work.ORLocInd.Howie.pmul_isReduced _ _⟩ :
        Work.ORLocInd.Howie.VertexGroup (S.encObj v)) ∈ P.relatorNormalClosure v
  rw [decode_apply]
  refine castVG_mem_relatorNormalClosure (P := P) (Skel.decObj_encObj S v) ?_
  have hval : decVG S (S.encObj v) ⟨Work.ORLocInd.Howie.pmul δ'
      (Work.ORLocInd.Howie.pmul ((SmallPres.smallPresentation S P D hrel).path r) δ'.reverse),
      Work.ORLocInd.Howie.pmul_isReduced _ _⟩ = Work.ORLocInd.Howie.conjPathHom Dd
        (castVG (Skel.dO S (P.base i))
          (⟨P.path i, P.reduced i⟩ : Work.ORLocInd.Howie.VertexGroup (P.base i))) := by
    apply Subtype.ext
    show S.dec.mapPath (Work.ORLocInd.Howie.pmul δ'
        (Work.ORLocInd.Howie.pmul ((SmallPres.smallPresentation S P D hrel).path r) δ'.reverse))
      = Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul Dd
          ((P.path i).cast (Skel.dO S (P.base i)) (Skel.dO S (P.base i)))) Dd.reverse
    rw [hDd]
    calc S.dec.mapPath (Work.ORLocInd.Howie.pmul δ'
          (Work.ORLocInd.Howie.pmul ((SmallPres.smallPresentation S P D hrel).path r)
            δ'.reverse))
        = Work.ORLocInd.Howie.pmul (S.dec.mapPath δ')
            (S.dec.mapPath (Work.ORLocInd.Howie.pmul
              ((SmallPres.smallPresentation S P D hrel).path r) δ'.reverse)) :=
          PrefunctorAux.mapPath_pmul S.dec S.decObj_injective
            (fun _ _ => S.dec_map_injective) _ _
      _ = Work.ORLocInd.Howie.pmul (S.dec.mapPath δ')
            (Work.ORLocInd.Howie.pmul
              (S.dec.mapPath ((SmallPres.smallPresentation S P D hrel).path r))
              (S.dec.mapPath δ'.reverse)) := by
          rw [PrefunctorAux.mapPath_pmul S.dec S.decObj_injective
            (fun _ _ => S.dec_map_injective) _ _]
      _ = Work.ORLocInd.Howie.pmul (S.dec.mapPath δ')
            (Work.ORLocInd.Howie.pmul
              ((P.path i).cast (Skel.dO S (P.base i)) (Skel.dO S (P.base i)))
              (S.dec.mapPath δ').reverse) := by
          rw [PrefunctorAux.mapPath_reverse S.dec, SmallPres.smallPresentation_path,
            Skel.dec_mapPath_enc_mapPath]
      _ = Work.ORLocInd.Howie.pmul
            (Work.ORLocInd.Howie.pmul (S.dec.mapPath δ')
              ((P.path i).cast (Skel.dO S (P.base i)) (Skel.dO S (P.base i))))
            (S.dec.mapPath δ').reverse :=
          (Work.ORLocInd.Howie.pmul_assoc _ _ _).symm
  rw [hval]
  exact hconj

end SmallTransfer

end Work.Case1
