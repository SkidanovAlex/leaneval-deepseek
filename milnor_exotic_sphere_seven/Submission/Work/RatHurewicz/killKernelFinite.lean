import Mathlib
import Submission.Work.StemsB.PiMap
import Submission.Work.RatHurewicz.killFamily_subsingleton
import Submission.Work.Serre.CWModel.piOneSurjective
import Submission.Work.RatHurewicz.attachCells_extension
import Submission.Work.Serre.CWModel.sphereExtend
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.CWModel.killSub
import Submission.Work.RatHurewicz.ConnectivityBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

/-- **An attaching loop whose class lies in the kernel of `π₁` becomes null-homotopic after the
map.**  If `α : π₁(A,a₀)` is killed by `g : A → B`, then the sphere map representing `α`
(`Work.RatHurewicz.killFamily 0 A a₀ α`) becomes null-homotopic after composing with `g`.

The class of `killFamily 0 A a₀ α` is `α`: its descent to the cube is a representative cube of
`α` (`Work.Stems.cubeLift_comp`), so the class of `g ∘ killFamily 0 A a₀ α` is
`πmap g 0 a₀ α = 1`, and a based cube whose class is trivial is homotopic to the constant cube,
which descends (`Work.Serre.CWModel.cubeLift_homotopic`) to a homotopy of sphere maps. -/
theorem homotopic_const_of_piMap_eq_one {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (g : C(A, B)) (a₀ : A) (α : HomotopyGroup (Fin 1) A a₀)
    (h : Work.StemsB.πmap g 0 a₀ α = 1) :
    (g.comp (Work.RatHurewicz.killFamily 0 A a₀ α)).Homotopic
      (ContinuousMap.const (Work.RatHurewicz.cellSphere 0) (g a₀)) := by
  have hcube : GenLoop.Homotopic (Work.StemsB.genLoopMap g 1 (Quotient.out α))
      (GenLoop.const (N := Fin 1) (X := B) (x := g a₀)) := by
    have h1 : (Quotient.mk _ (Work.StemsB.genLoopMap g 1 (Quotient.out α)) :
          HomotopyGroup (Fin 1) B (g a₀))
        = Quotient.mk (GenLoop.Homotopic.setoid (Fin 1) (g a₀))
            (GenLoop.const (N := Fin 1) (X := B) (x := g a₀)) := by
      rw [← Work.StemsB.πmap_apply_mk, Quotient.out_eq α, h]
      exact HomotopyGroup.one_def (N := Fin 1) (X := B) (x := g a₀)
    exact Quotient.exact h1
  have h2 := Work.Serre.CWModel.cubeLift_homotopic (n := 1) le_rfl hcube
  rw [Work.RatHurewicz.cubeLift_genLoopMap, Work.Serre.CWModel.cubeLift_const] at h2
  simpa [Work.RatHurewicz.killFamily_apply] using h2

/-- **Killing the kernel of `π₁(Y) → π₁(X)` produces a space with finite `π₁`.**

If `Y` is path connected and `φ : Y → X` is a based map whose image on `π₁` is *finite*, then there
is a space `Y'` (path connected) with a map `ψ : Y' → X` and a map `χ : Y → Y'` with `ψ ∘ χ = φ`,
such that `π₁(Y')` is finite and the induced map `π₁(Y') → π₁(X)` is injective.

Intended route: let `K := ker(π₁(Y) → π₁(X))` (normal, of finite index because the image is
finite).  Let `ι := K` and `f := fun k : K => Work.RatHurewicz.killFamily 0 Y y₀ k`, so that
`Y' := Work.RatHurewicz.attachCells 0 Y K f` attaches one 2-cell per element of the kernel along a
representative loop.  Each attaching loop is nullhomotopic in `X` (its class lies in `K`), so `φ`
extends over the cells: use `Work.Serre.CWModel.sphereExtend` cell by cell (the pattern of
`Work.StemsB.killFamily_extend`), giving `ψ` with `ψ ∘ χ = φ` for `χ := attachIncl 0 Y K f`.  Then
`χ_*` is surjective on `π₁` (`Work.Serre.CWModel.piOneSurjective`, from the compression property of
a cell attachment) with kernel exactly the normal closure of the classes of the attaching loops,
i.e. `K` (port the argument of `Work.RatHurewicz.killFamily_subsingleton` to the sub-family `K`), so
`π₁(Y') ≅ π₁(Y)/K ≅ im(π₁ φ)`, which is finite, and `ψ_*` is that isomorphism followed by the
inclusion of the image, hence injective.  Path connectedness is preserved because `attachCells`
glues cells of dimension 2 to a path-connected space. -/
theorem killKernelFinite (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (X : Type) [TopologicalSpace X] (φ : C(Y, X))
    (hY0 : Subsingleton (HomotopyGroup (Fin 0) Y y₀))
    (himg : (Set.range (Work.StemsB.πmap φ 0 y₀)).Finite) :
    ∃ (Y' : Type) (_ : TopologicalSpace Y') (y₀' : Y') (ψ : C(Y', X)) (χ : C(Y, Y')),
      ψ.comp χ = φ ∧ Finite (HomotopyGroup (Fin 1) Y' y₀') ∧
      Function.Injective (Work.StemsB.πmap ψ 0 y₀') ∧
      Subsingleton (HomotopyGroup (Fin 0) Y' y₀') := by
  classical
  haveI hYpc : PathConnectedSpace Y :=
    pathConnectedSpace_of_subsingleton_pi_zero y₀ hY0
  -- the kernel of `π₁(φ)` as an index type
  let ι := {α : HomotopyGroup (Fin 1) Y y₀ // Work.StemsB.πmap φ 0 y₀ α = 1}
  let f : ι → C(cellSphere 0, Y) := fun k => killFamily 0 Y y₀ (k : HomotopyGroup (Fin 1) Y y₀)
  -- each attaching loop becomes null-homotopic after `φ`
  have hnull : ∀ k : ι, (φ.comp (f k)).Homotopic
      (ContinuousMap.const (cellSphere 0) (φ y₀)) :=
    fun k => homotopic_const_of_piMap_eq_one φ y₀ (k : HomotopyGroup (Fin 1) Y y₀) k.2
  -- extend `φ` over the 2-cells
  let G : ι → C(cellDisk 0, X) := fun k =>
    Classical.choose (Work.Serre.CWModel.sphereExtend (φ.comp (f k))
      (hnull k).some.toContinuousMap (φ y₀)
      (hnull k).some.map_zero_left (hnull k).some.map_one_left)
  have hG : ∀ (k : ι) (z : cellSphere 0), G k (cellSphereToDisk 0 z) = φ (f k z) := by
    intro k z
    have hspec := Classical.choose_spec (Work.Serre.CWModel.sphereExtend (φ.comp (f k))
      (hnull k).some.toContinuousMap (φ y₀)
      (hnull k).some.map_zero_left (hnull k).some.map_one_left)
    exact congrFun (congrArg DFunLike.coe hspec) z
  let Y' : Type := attachCells 0 Y ι f
  letI : TopologicalSpace Y' := inferInstance
  let χ : C(Y, Y') := attachIncl 0 Y ι f
  let ψ : C(Y', X) := Work.Serre.CWModel.attachG 0 Y ι f φ G hG
  have hψχ : ψ.comp χ = φ := by
    ext y
    exact Work.Serre.CWModel.attachG_incl 0 Y ι f φ G hG y
  -- `π₁` of the inclusion is surjective
  have hsurj : Function.Surjective (Work.StemsB.πmap χ 0 y₀) :=
    surjective_πmap_attachIncl 0 Y ι f y₀
  -- functoriality: `π₁(ψ) ∘ π₁(χ) = π₁(φ)`
  have hcomp : ∀ a : HomotopyGroup (Fin 1) Y y₀,
      Work.StemsB.πmap φ 0 y₀ a
        = Work.StemsB.πmap ψ 0 (χ y₀) (Work.StemsB.πmap χ 0 y₀ a) := fun a =>
    Work.StemsB.πmap_comp_apply χ ψ 0 y₀ a
  -- every class in the kernel of `π₁(φ)` dies in `Y'`
  have hkill : ∀ a : HomotopyGroup (Fin 1) Y y₀, Work.StemsB.πmap φ 0 y₀ a = 1 →
      Work.StemsB.πmap χ 0 y₀ a = 1 :=
    fun a ha => Work.Serre.CWModel.killSub (n := 0) Y y₀ ι
      (fun k : ι => (k : HomotopyGroup (Fin 1) Y y₀)) ⟨a, ha⟩
  -- `π₁(ψ)` is injective
  have hinj : Function.Injective (Work.StemsB.πmap ψ 0 (χ y₀)) := by
    intro u v huv
    obtain ⟨a, rfl⟩ := hsurj u
    obtain ⟨b, rfl⟩ := hsurj v
    have hab : Work.StemsB.πmap φ 0 y₀ a = Work.StemsB.πmap φ 0 y₀ b := by
      rw [hcomp a, hcomp b]
      exact huv
    have hker : Work.StemsB.πmap φ 0 y₀ (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h1 := hkill (a * b⁻¹) hker
    have h2 : Work.StemsB.πmap χ 0 y₀ (a * b⁻¹)
        = Work.StemsB.πmap χ 0 y₀ a * (Work.StemsB.πmap χ 0 y₀ b)⁻¹ := by
      rw [map_mul, map_inv]
    rw [h2] at h1
    exact mul_inv_eq_one.mp h1
  -- the range of `π₁(ψ)` is the (finite) range of `π₁(φ)`
  have hrange : Set.range (Work.StemsB.πmap ψ 0 (χ y₀))
      = Set.range (Work.StemsB.πmap φ 0 y₀) := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj v
      exact ⟨a, hcomp a⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Work.StemsB.πmap χ 0 y₀ a, (hcomp a).symm⟩
  have hfin : Finite (HomotopyGroup (Fin 1) Y' (χ y₀)) := by
    haveI : Finite ↥(Set.range (Work.StemsB.πmap ψ 0 (χ y₀))) :=
      (hrange ▸ himg).to_subtype
    exact Finite.of_injective
      (fun a => (⟨Work.StemsB.πmap ψ 0 (χ y₀) a, Set.mem_range_self a⟩ :
        ↥(Set.range (Work.StemsB.πmap ψ 0 (χ y₀)))))
      (fun a b hab => hinj (Subtype.ext_iff.mp hab))
  -- `Y'` is path connected, hence `π₀ (Y')` is trivial
  haveI hpc : PathConnectedSpace Y' :=
    Work.Serre.CWModel.pathConnectedSpace_attachCells 0 Y ι f
  have hsub0 : Subsingleton (HomotopyGroup (Fin 0) Y' (χ y₀)) := by
    haveI hZ : Subsingleton (ZerothHomotopy Y') :=
      (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
    refine ⟨fun a b => ?_⟩
    exact (HomotopyGroup.pi0EquivZerothHomotopy (X := Y') (x := χ y₀)).injective
      (Subsingleton.elim _ _)
  exact ⟨Y', inferInstance, χ y₀, ψ, χ, hψχ, hfin, hinj, hsub0⟩

end

end Work.RatHurewicz
