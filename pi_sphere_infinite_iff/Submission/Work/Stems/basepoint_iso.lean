import Mathlib
import Submission.Work.Stems.Pi
import Submission.Work.Stems.Collar.Defs
import Submission.Work.Stems.Collar.collar_collapse
import Submission.Work.Stems.Collar.collar_collapse_symm
import Submission.Work.Stems.Collar.collar_release
import Submission.Work.Stems.dense_boundary
import Submission.Work.Stems.subsingleton_of_infinite
import Submission.Work.Stems.functor_bijective_of_natIso

/-!
# Homotopy groups are independent of the base point, along a path

For a path `p : Path x y` and a nonempty index type `N`, the homotopy groups
`HomotopyGroup N X x` and `HomotopyGroup N X y` are isomorphic as groups.

The proof passes through Mathlib's identification of `HomotopyGroup N X z` with the fundamental
group of the iterated loop space `Ω^{N \ {i}} X z`.  The geometric input is the collar map
`Work.Stems.Collar.collar p : Ω^M X x → Ω^M X y`, which fills the collar `{delta ≤ 1/4}` of the
cube `I^M` with the path `p` and shrinks the loop into the inner cube; the two collapsing
homotopies (`Submission/Work/Stems/Collar/collar_collapse*.lean`) show that it is a homotopy
inverse of `collar p.symm`, hence it induces a bijection on fundamental groups by the general
categorical lemma `Work.Stems.functor_bijective_of_natIso`.

For an infinite index type both sides are trivial: the boundary of the cube is dense, so every
generalized loop is constant.
-/

open scoped Topology Topology.Homotopy unitInterval
open CategoryTheory

namespace Work.Stems

/-- Mathlib's comparison between the homotopy group and the fundamental group of the iterated
loop space, upgraded to a `MulEquiv` (the group structure on `HomotopyGroup N X x` is *defined*
as the pullback of the fundamental group structure along this equivalence). -/
noncomputable def homotopyGroupMulEquivFundamentalGroup (N X : Type*) [TopologicalSpace X]
    [DecidableEq N] [Nonempty N] (x : X) :
    HomotopyGroup N X x ≃*
      FundamentalGroup (GenLoop {j : N // j ≠ Classical.arbitrary N} X x) GenLoop.const :=
  MulEquiv.mk (homotopyGroupEquivFundamentalGroup (Classical.arbitrary N)) fun a b => by
    change (homotopyGroupEquivFundamentalGroup (Classical.arbitrary N))
      ((homotopyGroupEquivFundamentalGroup (Classical.arbitrary N)).symm
        ((homotopyGroupEquivFundamentalGroup (Classical.arbitrary N)) a *
         (homotopyGroupEquivFundamentalGroup (Classical.arbitrary N)) b)) = _
    rw [Equiv.apply_symm_apply]
    rfl

/-- A homeomorphism of spaces induces an isomorphism of fundamental groups. -/
noncomputable def mulEquivOfHomeomorph {Z Z' : Type*} [TopologicalSpace Z] [TopologicalSpace Z']
    (h : Z ≃ₜ Z') (z : Z) : FundamentalGroup Z z ≃* FundamentalGroup Z' (h z) := by
  have hcf : (h.symm : C(Z', Z)).comp (h : C(Z, Z')) = ContinuousMap.id Z := by
    ext w
    exact congrFun (Homeomorph.symm_comp_self h) w
  have hcf' : (h : C(Z, Z')).comp (h.symm : C(Z', Z)) = ContinuousMap.id Z' := by
    ext w
    exact congrFun (Homeomorph.self_comp_symm h) w
  have h1 : (FundamentalGroupoid.map (h : C(Z, Z'))) ⋙
      (FundamentalGroupoid.map (h.symm : C(Z', Z))) = 𝟭 (FundamentalGroupoid Z) := by
    rw [← FundamentalGroupoid.map_comp, hcf, FundamentalGroupoid.map_id]
  have h2 : (FundamentalGroupoid.map (h.symm : C(Z', Z))) ⋙
      (FundamentalGroupoid.map (h : C(Z, Z'))) = 𝟭 (FundamentalGroupoid Z') := by
    rw [← FundamentalGroupoid.map_comp, hcf', FundamentalGroupoid.map_id]
  have hbij := functor_bijective_of_natIso (FundamentalGroupoid.map (h : C(Z, Z')))
    (FundamentalGroupoid.map (h.symm : C(Z', Z))) (eqToIso h1) (eqToIso h2)
    (FundamentalGroupoid.mk z)
  exact MulEquiv.ofBijective (FundamentalGroup.map (h : C(Z, Z')) z) hbij

namespace BasepointIso

/-- The main (finite index type with at least two elements) case: the collar at the path `p`
induces a group isomorphism, via the loop space. -/
theorem mulEquivOfCollar {N X : Type*} [TopologicalSpace X] [DecidableEq N] [Fintype N]
    [Nonempty N] {x y : X} (p : Path x y)
    (hM : Nonempty {j : N // j ≠ Classical.arbitrary N}) :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N X y) := by
  classical
  let i := Classical.arbitrary N
  letI : Nonempty {j : N // j ≠ i} := hM
  haveI : Fintype {j : N // j ≠ i} := inferInstance
  let Zx := GenLoop {j : N // j ≠ i} X x
  let Zy := GenLoop {j : N // j ≠ i} X y
  -- the functors on fundamental groupoids induced by the two collar maps
  let A : FundamentalGroupoid Zx ⥤ FundamentalGroupoid Zy :=
    FundamentalGroupoid.map (Collar.collar p)
  let B : FundamentalGroupoid Zy ⥤ FundamentalGroupoid Zx :=
    FundamentalGroupoid.map (Collar.collar p.symm)
  have hAB : A ⋙ B = FundamentalGroupoid.map
      ((Collar.collar p.symm).comp (Collar.collar p)) :=
    (FundamentalGroupoid.map_comp (Collar.collar p.symm) (Collar.collar p)).symm
  have hBA : B ⋙ A = FundamentalGroupoid.map
      ((Collar.collar p).comp (Collar.collar p.symm)) :=
    (FundamentalGroupoid.map_comp (Collar.collar p) (Collar.collar p.symm)).symm
  -- the two collapsing homotopies produce the natural isomorphisms
  obtain ⟨Hα⟩ := (Collar.collar_collapse (M := {j : N // j ≠ i}) p)
  obtain ⟨Hβ⟩ := (Collar.collar_collapse_symm (M := {j : N // j ≠ i}) p)
  have α : A ⋙ B ≅ 𝟭 (FundamentalGroupoid Zx) :=
    (eqToIso hAB).trans
      ((asIso (FundamentalGroupoidFunctor.homotopicMapsNatIso Hα)).trans
        (eqToIso (FundamentalGroupoid.map_id (X := Zx))))
  have β : B ⋙ A ≅ 𝟭 (FundamentalGroupoid Zy) :=
    (eqToIso hBA).trans
      ((asIso (FundamentalGroupoidFunctor.homotopicMapsNatIso Hβ)).trans
        (eqToIso (FundamentalGroupoid.map_id (X := Zy))))
  -- hence the collar induces a bijection on the vertex group
  have hbij : Function.Bijective
      (fun f : Quiver.Hom (FundamentalGroupoid.mk GenLoop.const)
        (FundamentalGroupoid.mk GenLoop.const) => A.map f) :=
    functor_bijective_of_natIso A B α β (FundamentalGroupoid.mk GenLoop.const)
  have hbij' : Function.Bijective
      (FundamentalGroup.map (Collar.collar p) (GenLoop.const : Zx)) := hbij
  -- the base point change at the target
  obtain ⟨q⟩ := (Collar.collar_release (M := {j : N // j ≠ i}) p)
  refine ⟨(homotopyGroupMulEquivFundamentalGroup N X x).trans
    (((MulEquiv.ofBijective (FundamentalGroup.map (Collar.collar p) GenLoop.const)
        hbij').trans
      (FundamentalGroup.fundamentalGroupMulEquivOfPath q)).trans
      (homotopyGroupMulEquivFundamentalGroup N X y).symm)⟩

/-- The case of a singleton index type: the loop space is (homeomorphic to) `X` itself, so this
reduces to Mathlib's base point change for the fundamental group. -/
theorem mulEquivOfUnique {N X : Type*} [TopologicalSpace X] [DecidableEq N] [Nonempty N]
    (huniq : Subsingleton N) {x y : X} (p : Path x y) :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N X y) := by
  classical
  let i := Classical.arbitrary N
  haveI : IsEmpty {j : N // j ≠ i} := ⟨fun j => j.2 (huniq.elim j.1 i)⟩
  have hx0 : (genLoopHomeoOfIsEmpty {j : N // j ≠ i} x) GenLoop.const = x := rfl
  have hy0 : (genLoopHomeoOfIsEmpty {j : N // j ≠ i} y) GenLoop.const = y := rfl
  exact ⟨(homotopyGroupMulEquivFundamentalGroup N X x).trans
    (((mulEquivOfHomeomorph (genLoopHomeoOfIsEmpty {j : N // j ≠ i} x) GenLoop.const).trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath
        (Path.cast p hx0 hy0)).trans
        (mulEquivOfHomeomorph (genLoopHomeoOfIsEmpty {j : N // j ≠ i} y)
          GenLoop.const).symm)).trans
      (homotopyGroupMulEquivFundamentalGroup N X y).symm)⟩

end BasepointIso

theorem basepoint_iso {N X : Type*} [TopologicalSpace X] [DecidableEq N] [Nonempty N] {x y : X}
    (p : Path x y) : Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N X y) := by
  classical
  by_cases hfin : Finite N
  · by_cases huniq : Subsingleton N
    · exact BasepointIso.mulEquivOfUnique huniq p
    · haveI : Fintype N := Fintype.ofFinite N
      have hex : ∃ j : N, j ≠ Classical.arbitrary N := by
        by_contra h
        refine huniq ⟨fun a b => ?_⟩
        have ha : a = Classical.arbitrary N := by
          by_contra hne; exact h ⟨a, hne⟩
        have hb : b = Classical.arbitrary N := by
          by_contra hne; exact h ⟨b, hne⟩
        rw [ha, hb]
      obtain ⟨j, hj⟩ := hex
      exact BasepointIso.mulEquivOfCollar p ⟨⟨j, hj⟩⟩
  · haveI : Infinite N := ⟨hfin⟩
    refine ⟨MulEquiv.ofBijective (1 : HomotopyGroup N X x →* HomotopyGroup N X y)
      ⟨fun a b _ => (subsingleton_of_infinite (N := N) (X := X) x).elim a b, fun b =>
        ⟨1, (subsingleton_of_infinite (N := N) (X := X) y).elim 1 b⟩⟩⟩

end Work.Stems
