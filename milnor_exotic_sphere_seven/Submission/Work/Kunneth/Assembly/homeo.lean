import Mathlib
import Submission.Work.Kunneth.Assembly.Defs
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_trivial
import Submission.Work.LerayHirsch.bijective_lhMap_fibre_of_trivCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The homeomorphism `P(ε^m) ≃ₜ B × ℂP^{m-1}` with the explicit map `(projMap, qTriv)`

`Work.Kunneth.Asm.hMap m B : P(ε^m over B) → B × Qb m` is the map sending the class of a punctured
vector `(b,v)` to `(b, [v])`.  It is a homeomorphism: this is the port of the proof of
`Work.LerayHirsch.nonempty_homeo_projSpace_trivial` (which produces a homeomorphism onto
`B × ℙ ℂ (ℂ^m)` without recording its formula) composed with the canonical homeomorphism
`ℙ ℂ (ℂ^m) ≃ₜ Qb m = P(ε^m over the point)`.

The result is the stated form of the homeomorphism, with the underlying map *equal* to
`Work.Kunneth.Asm.hMap m B`, which is what the naturality of the Leray–Hirsch comparison needs.
-/

namespace Work.Kunneth.Asm

open CategoryTheory Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization MonoidalCategory TensorProduct

noncomputable section

variable {B : Type} [TopologicalSpace B] {m : ℕ}

theorem nonempty_homeo_hMap (m : ℕ) (B : Type) [TopologicalSpace B] :
    ∃ e : Pb m B ≃ₜ (B × Qb m),
      (↑e : Pb m B → B × Qb m) = fun x =>
        (Work.LerayHirsch.projMap (Zb m B) x, Work.Kunneth.qTriv m B x) := by
  classical
  let Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit := Zb m B
  -- the class map on the punctured total space
  set projProd' : ↥(zeroComplement (realification Z))
      → B × Qb m := fun p => (p.1.proj, Work.LerayHirsch.mkProj
        (Work.LerayHirsch.trivCore m)
        ⟨(⟨PUnit.unit, (show EuclideanSpace ℂ (Fin m) from p.1.2)⟩ :
            (realification (Work.LerayHirsch.trivCore m)).TotalSpace),
          by rw [mem_zeroComplement]; exact (mem_zeroComplement p.1).mp p.2⟩) with hprojProd'
  obtain ⟨φ, hφ⟩ := Work.LerayHirsch.exists_punctTrivHomeo m B
  have hcomp : projProd' = (fun q : B × {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} =>
      (q.1, Work.LerayHirsch.projUniv m (Work.LerayHirsch.mkP m q.2))) ∘
      (φ : ↥(zeroComplement (realification Z)) →
        B × {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) := by
    funext p
    rw [Function.comp_apply, hφ p]
    rfl
  have hcont : Continuous projProd' := by
    rw [hcomp]
    exact (continuous_fst.comp φ.continuous).prodMk
      ((Work.LerayHirsch.projUniv m).continuous.comp
        ((Work.LerayHirsch.continuous_mkP m).comp (continuous_snd.comp φ.continuous)))
  have hopen : IsOpenMap projProd' := by
    rw [hcomp]
    exact ((IsOpenMap.id : IsOpenMap (id : B → B)).prodMap
        ((Work.LerayHirsch.projUnivHomeo m).isOpenMap.comp
          (Work.LerayHirsch.isOpenMap_mkP m))).comp φ.isOpenMap
  have hsurj : Function.Surjective projProd' := by
    rw [hcomp]
    exact (Work.LerayHirsch.surjective_prodMap_id ((Work.LerayHirsch.projUnivHomeo m).surjective.comp
      (Work.LerayHirsch.surjective_mkP m))).comp φ.surjective
  have hQ : Topology.IsQuotientMap projProd' :=
    hopen.isQuotientMap hcont hsurj
  let F : Pb m B → B × Qb m := fun x => (Work.LerayHirsch.projMap Z x,
    Work.Kunneth.qTriv m B x)
  have hFmk : ∀ p, F (Work.LerayHirsch.mkProj Z p) = projProd' p := by
    intro p
    simp only [F, projProd', hprojProd', Work.LerayHirsch.projMap_mkProj]
    rw [Work.Kunneth.qTriv_mkProj]
  have hQ' : Topology.IsQuotientMap F := by
    refine Topology.IsQuotientMap.of_comp_isQuotientMap (isQuotientMap_quotient_mk') ?_
    change Topology.IsQuotientMap projProd'
    exact hQ
  have hinj : Function.Injective F := by
    intro x y hxy
    have h1 : Work.LerayHirsch.projMap Z x = Work.LerayHirsch.projMap Z y :=
      congrArg Prod.fst hxy
    have h2 : Work.Kunneth.qTriv m B x = Work.Kunneth.qTriv m B y := congrArg Prod.snd hxy
    have h3 : Work.LerayHirsch.projClass Z x = Work.LerayHirsch.projClass Z y :=
      (Work.LerayHirsch.projUnivHomeo m).injective (show Work.LerayHirsch.projUniv m
        (Work.LerayHirsch.projClass Z x) = Work.LerayHirsch.projUniv m
          (Work.LerayHirsch.projClass Z y) from h2)
    have hx : (Work.LerayHirsch.fibreMap Z (Work.LerayHirsch.projMap Z x)
        (Work.LerayHirsch.projClass Z x)).1 = x :=
      congrArg Subtype.val (Work.LerayHirsch.fibreMap_projClass Z
        (Work.LerayHirsch.projMap Z x) x rfl)
    have hy : (Work.LerayHirsch.fibreMap Z (Work.LerayHirsch.projMap Z y)
        (Work.LerayHirsch.projClass Z y)).1 = y :=
      congrArg Subtype.val (Work.LerayHirsch.fibreMap_projClass Z
        (Work.LerayHirsch.projMap Z y) y rfl)
    rw [← hx, h1, h3, hy]
  refine ⟨(Equiv.ofBijective F ⟨hinj, hQ'.surjective⟩).toHomeomorph
    (fun s => hQ'.isCoinducing.isOpen_preimage), ?_⟩
  exact funext fun x => rfl

end

end Work.Kunneth.Asm
