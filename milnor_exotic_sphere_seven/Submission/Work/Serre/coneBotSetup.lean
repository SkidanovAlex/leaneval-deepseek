import Mathlib
import Submission.Work.Serre.ConePairDefs
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Thom.ATools
import Submission.Work.Serre.DiscPair.cylEqvGenEmb
import Submission.Work.Serre.DiscPair.cylPreimageLift_range
import Submission.Work.RatHurewicz.cylPullBase
import Submission.Work.Serre.relCoh_concentrated_of_ratAcyclic
import Submission.Work.Serre.DiscPair.centreConePair

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

variable {X B : Type} [TopologicalSpace X] [TopologicalSpace B]


/-! ## The bottom part of a cone-fibre, and its identification with the fibre -/

theorem cylRetract_cylIncl_apply (q : C(X, B)) (x : X) :
    cylRetract q (cylIncl q x) = q x :=
  congrFun (congrArg DFunLike.coe (cylRetract_cylIncl q)) x

/-- **The part of the bottom copy lying over `b` is the fibre `q ⁻¹' {b}`**, through the explicit
homeomorphism of the bottom copy of the mapping cylinder. -/
def rangeBotHomeoFibre (q : C(X, B)) (b : B) (e : X ≃ₜ ↥(Set.range (cylIncl q)))
    (he : ∀ x : X, (e x : cyl q) = cylIncl q x) :
    ↥{y : ↥(Set.range (cylIncl q)) | cylRetract q (y : cyl q) = b} ≃ₜ {x : X // q x = b} where
  toFun y := ⟨e.symm y.1, by
    have h1 : cylIncl q (e.symm y.1) = (y.1 : cyl q) := by
      rw [← he (e.symm y.1), Homeomorph.apply_symm_apply]
    rw [← cylRetract_cylIncl_apply q (e.symm y.1), h1]
    exact y.2⟩
  invFun z := ⟨⟨e z.1, ⟨z.1, (he z.1).symm⟩⟩, by
    show cylRetract q (e z.1 : cyl q) = b
    rw [he z.1, cylRetract_cylIncl_apply q z.1]
    exact z.2⟩
  left_inv := fun y => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (Homeomorph.apply_symm_apply e y.1)
  right_inv := fun z => Subtype.ext (by
    show e.symm (⟨e z.1, ⟨z.1, (he z.1).symm⟩⟩ : ↥(Set.range (cylIncl q))) = z.1
    have h : (⟨e z.1, ⟨z.1, (he z.1).symm⟩⟩ : ↥(Set.range (cylIncl q))) = e z.1 :=
      Subtype.ext rfl
    rw [h, Homeomorph.symm_apply_apply])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) (by
    intro y
    have h1 : cylIncl q (e.symm y.1) = (y.1 : cyl q) := by
      rw [← he (e.symm y.1), Homeomorph.apply_symm_apply]
    rw [← cylRetract_cylIncl_apply q (e.symm y.1), h1]
    exact y.2)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk (by fun_prop) (by
      intro z
      exact ⟨z.1, (he z.1).symm⟩)) (by
    intro z
    show cylRetract q (e z.1 : cyl q) = b
    rw [he z.1, cylRetract_cylIncl_apply q z.1]
    exact z.2)

@[simp] theorem rangeBotHomeoFibre_val (q : C(X, B)) (b : B) (e : X ≃ₜ ↥(Set.range (cylIncl q)))
    (he : ∀ x : X, (e x : cyl q) = cylIncl q x)
    (y : ↥{y : ↥(Set.range (cylIncl q)) | cylRetract q (y : cyl q) = b}) :
    ((rangeBotHomeoFibre q b e he y : {x : X // q x = b}) : X)
      = e.symm (y.1 : ↥(Set.range (cylIncl q))) := rfl

@[simp] theorem rangeBotHomeoFibre_symm_val (q : C(X, B)) (b : B) (e : X ≃ₜ ↥(Set.range (cylIncl q)))
    (he : ∀ x : X, (e x : cyl q) = cylIncl q x) (z : {x : X // q x = b}) :
    (((rangeBotHomeoFibre q b e he).symm z :
        ↥{y : ↥(Set.range (cylIncl q)) | cylRetract q (y : cyl q) = b})
      : ↥(Set.range (cylIncl q))) = e (z.1 : X) := rfl

/-- **The bottom part of a cone-fibre, presented as the part of the bottom copy of the mapping
cylinder lying over `b`.** -/
def coneBotSwap (q : C(X, B)) (b : B) :
    ↥{y : ↥(Set.range (cylIncl q)) | cylRetract q (y : cyl q) = b} ≃ₜ ↥(coneFibreBot q b) where
  toFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv y := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2))
    (fun y => y.1.2)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2))
    (fun y => y.1.2)

@[simp] theorem coneBotSwap_val (q : C(X, B)) (b : B)
    (y : ↥{y : ↥(Set.range (cylIncl q)) | cylRetract q (y : cyl q) = b}) :
    ((coneBotSwap q b y : ↥(coneFibreBot q b)) : cyl q) = (y.1 : cyl q) := rfl

@[simp] theorem coneBotSwap_symm_val (q : C(X, B)) (b : B) (a : ↥(coneFibreBot q b)) :
    (((coneBotSwap q b).symm a :
        ↥{y : ↥(Set.range (cylIncl q)) | cylRetract q (y : cyl q) = b}) : cyl q)
      = (a.1.1 : cyl q) := rfl

/-- **The map of mapping cylinders along the pullback square is `cylIncl` on the bottom copies.** -/
theorem pathPsi_cylIncl (q : C(X, B)) (p : C(unitInterval, B))
    (z₀ : Work.StemsB.Pullback q p) :
    pathPsi q p (cylIncl (Work.StemsB.pullbackSnd q p) z₀)
      = cylIncl q (Work.StemsB.pullbackFst q p z₀) := by
  show (Work.StemsB.cylMapGen (Work.StemsB.pullbackSnd q p) q (Work.StemsB.pullbackFst q p) p
      (fun z => z.2.symm))
      (Quotient.mk'' (Sum.inl (z₀, (0 : unitInterval))
        : (Work.StemsB.Pullback q p × unitInterval) ⊕ unitInterval))
      = Quotient.mk'' (Sum.inl (Work.StemsB.pullbackFst q p z₀, (0 : unitInterval))
        : (X × unitInterval) ⊕ B)
  exact Work.StemsB.cylMapGen_apply_inl (Work.StemsB.pullbackSnd q p) q
    (Work.StemsB.pullbackFst q p) p (fun z => z.2.symm) (z₀, 0)

/-- The fibre of `pullbackSnd q p` over `t` is the fibre of `q` over `p t`, by `pullbackFst`. -/
def fibrePullbackHomeo (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval) :
    {z : Work.StemsB.Pullback q p // Work.StemsB.pullbackSnd q p z = t} ≃ₜ
      {x : X // q x = p t} where
  toFun z := ⟨(z.1.1).1, by
    have h1 : q (z.1.1).1 = p (z.1.1).2 := z.1.2
    rw [h1]
    have h2 : (z.1.1).2 = t := z.2
    rw [h2]⟩
  invFun w := ⟨⟨(w.1, t), w.2⟩, rfl⟩
  left_inv := fun z => by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl z.2.symm
  right_inv := fun w => Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk (by fun_prop) (by
    intro z
    have h1 : q (z.1.1).1 = p (z.1.1).2 := z.1.2
    rw [h1]
    have h2 : (z.1.1).2 = t := z.2
    rw [h2])
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk (by fun_prop) (by
      intro w
      exact w.2)) (by intro w; rfl)

@[simp] theorem fibrePullbackHomeo_val (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval)
    (z : {z : Work.StemsB.Pullback q p // Work.StemsB.pullbackSnd q p z = t}) :
    ((fibrePullbackHomeo q p t z : {x : X // q x = p t}) : X) = (z.1.1).1 := rfl

@[simp] theorem fibrePullbackHomeo_symm_val (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval)
    (w : {x : X // q x = p t}) :
    (((fibrePullbackHomeo q p t).symm w :
        {z : Work.StemsB.Pullback q p // Work.StemsB.pullbackSnd q p z = t})
      : Work.StemsB.Pullback q p) = ⟨(w.1, t), w.2⟩ := rfl

/-- **The bottom parts of the two cone-fibres are homeomorphic**, by the fibre transport along the
pullback square of the path. -/
def coneBotHomeo (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval) :
    ↥(coneFibreBot (Work.StemsB.pullbackSnd q p) t) ≃ₜ ↥(coneFibreBot q (p t)) :=
  (((coneBotSwap (Work.StemsB.pullbackSnd q p) t).symm.trans
      (rangeBotHomeoFibre (Work.StemsB.pullbackSnd q p) t
        (Classical.choose (cylHomeoExplicit (Work.StemsB.pullbackSnd q p)))
        (Classical.choose_spec (cylHomeoExplicit (Work.StemsB.pullbackSnd q p))))).trans
    (fibrePullbackHomeo q p t)).trans
  ((rangeBotHomeoFibre q (p t) (Classical.choose (cylHomeoExplicit q))
      (Classical.choose_spec (cylHomeoExplicit q))).symm.trans (coneBotSwap q (p t)))


end

end Work.Serre
