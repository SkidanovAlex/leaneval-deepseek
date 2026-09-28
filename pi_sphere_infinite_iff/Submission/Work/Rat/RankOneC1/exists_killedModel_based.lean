import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.Serre.SPC.piOne_killStep
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.attachCells_extension
import Submission.Work.RatHurewicz.killKernelFinite
import Submission.Work.StemsB.killToFgModel
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.CWModel.Defs
import Submission.Work.Serre.CWModel.killSub
import Submission.Work.Serre.CWModel.sphereExtend
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Rat.RankOneC1.killTowerFgBased

set_option synthInstance.maxHeartbeats 400000


/-!
# A based model of `X` with the same `π₁`-image and no homotopy above `π₁`

This is the *based* form of `Work.Rat.RankOneC1.exists_killedModel`: given a based map
`φ : Y → X` with `φ y₀ = x₀`, `Y` path connected with finitely generated `π₁(Y)`, and a target `X`
whose homotopy groups `π_i(X)`, `2 ≤ i ≤ N`, all vanish, it produces `W`, `ψ : W → X`,
`κ : Y → W` with `ψ ∘ κ = φ`, with the *base point chosen so that* `ψ w₀ = x₀` (namely
`w₀ := κ y₀`), such that `W` is path connected, `π₁(W)` is finitely generated, `π₁(ψ)` is
injective, and `π_i(W) = 0` for `2 ≤ i ≤ N`.

The construction is the classical one, in two stages, each of which records the base point:

1. `killKernelFgBased`: attach one `2`-cell per element of `ker π₁(φ)` (each attaching loop is
   null-homotopic in `X`, so `φ` extends over the cells); the resulting space `Y'` has
   `π₁(Y') ≅ π₁(Y)/ker ≅ im π₁(φ)` — a quotient of a finitely generated group — and `π₁(ψ)` is
   injective.
2. `killTowerFgBased` with `k = 1`: kill `π_2, …, π_N` of `Y'` by attaching cells of dimension
   `≥ 3` along representatives of those groups (they are null-homotopic in `X` because
   `π_i(X) = 0` for `2 ≤ i ≤ N`).  Cells of dimension `≥ 3` change neither `π₀` nor `π₁`, and the
   new base point is the image of the old one, so `ψ w₀ = ψ(κ y₀) = φ y₀ = x₀`.
-/


namespace Work.Rat.RankOneC1

noncomputable section

open scoped Topology Topology.Homotopy unitInterval

set_option linter.style.haveILetI false

/-! ## Step 1: killing the kernel of `π₁(φ)`, with the base point recorded -/

theorem killKernelFgBased {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X] (y₀ : Y)
    (φ : C(Y, X)) [PathConnectedSpace Y] (hfg : Group.FG (HomotopyGroup (Fin 1) Y y₀)) :
    ∃ (Y' : Type) (_ : TopologicalSpace Y') (y₀' : Y') (ψ : C(Y', X)) (χ : C(Y, Y')),
      ψ.comp χ = φ ∧ χ y₀ = y₀' ∧ PathConnectedSpace Y' ∧
      Group.FG (HomotopyGroup (Fin 1) Y' y₀') ∧
      Function.Injective (Work.Serre.piMapN ψ 1 y₀') := by
  classical
  let ι := {α : HomotopyGroup (Fin 1) Y y₀ // Work.Serre.piMapN φ 1 y₀ α = 1}
  let f : ι → C(Work.RatHurewicz.cellSphere 0, Y) :=
    fun k => Work.RatHurewicz.killFamily 0 Y y₀ (k : HomotopyGroup (Fin 1) Y y₀)
  have hnull : ∀ k : ι, (φ.comp (f k)).Homotopic
      (ContinuousMap.const (Work.RatHurewicz.cellSphere 0) (φ y₀)) :=
    fun k => Work.RatHurewicz.homotopic_const_of_piMap_eq_one φ y₀
      (k : HomotopyGroup (Fin 1) Y y₀) k.2
  let G : ι → C(Work.RatHurewicz.cellDisk 0, X) := fun k =>
    Classical.choose (Work.Serre.CWModel.sphereExtend (φ.comp (f k))
      (hnull k).some.toContinuousMap (φ y₀)
      (hnull k).some.map_zero_left (hnull k).some.map_one_left)
  have hG : ∀ (k : ι) (z : Work.RatHurewicz.cellSphere 0),
      G k (Work.RatHurewicz.cellSphereToDisk 0 z) = φ (f k z) := by
    intro k z
    have hspec := Classical.choose_spec (Work.Serre.CWModel.sphereExtend (φ.comp (f k))
      (hnull k).some.toContinuousMap (φ y₀)
      (hnull k).some.map_zero_left (hnull k).some.map_one_left)
    exact congrFun (congrArg DFunLike.coe hspec) z
  let Y' : Type := Work.RatHurewicz.attachCells 0 Y ι f
  letI : TopologicalSpace Y' := inferInstance
  let χ : C(Y, Y') := Work.RatHurewicz.attachIncl 0 Y ι f
  let ψ : C(Y', X) := Work.Serre.CWModel.attachG 0 Y ι f φ G hG
  have hψχ : ψ.comp χ = φ := by
    ext y
    exact Work.Serre.CWModel.attachG_incl 0 Y ι f φ G hG y
  have hsurj : Function.Surjective (Work.StemsB.πmap χ 0 y₀) :=
    Work.RatHurewicz.surjective_πmap_attachIncl 0 Y ι f y₀
  have hcomp : ∀ a : HomotopyGroup (Fin 1) Y y₀,
      Work.StemsB.πmap φ 0 y₀ a = Work.StemsB.πmap ψ 0 (χ y₀) (Work.StemsB.πmap χ 0 y₀ a) :=
    fun a => Work.StemsB.πmap_comp_apply χ ψ 0 y₀ a
  have hkill : ∀ a : HomotopyGroup (Fin 1) Y y₀, Work.StemsB.πmap φ 0 y₀ a = 1 →
      Work.StemsB.πmap χ 0 y₀ a = 1 :=
    fun a ha => Work.Serre.CWModel.killSub (n := 0) Y y₀ ι
      (fun k : ι => (k : HomotopyGroup (Fin 1) Y y₀)) ⟨a, ha⟩
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
  have hpc : PathConnectedSpace Y' := Work.Serre.CWModel.pathConnectedSpace_attachCells 0 Y ι f
  have hfg' : Group.FG (HomotopyGroup (Fin 1) Y' (χ y₀)) := by
    haveI := hfg
    exact Group.fg_of_surjective (f := Work.StemsB.πmap χ 0 y₀) hsurj
  exact ⟨Y', inferInstance, χ y₀, ψ, χ, hψχ, rfl, hpc, hfg', hinj⟩

/-! ## Step 2: the tower and the assembly -/

theorem exists_killedModel_based {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X]
    (y₀ : Y) (x₀ : X) (φ : C(Y, X)) (hφ : φ y₀ = x₀) (N : ℕ) [PathConnectedSpace Y]
    (hX : ∀ i : ℕ, 2 ≤ i → i ≤ N → ∀ x : X, Subsingleton (HomotopyGroup (Fin i) X x))
    (hfg : Group.FG (HomotopyGroup (Fin 1) Y y₀)) :
    ∃ (W : Type) (_ : TopologicalSpace W) (w₀ : W) (ψ : C(W, X)) (κ : C(Y, W)),
      PathConnectedSpace W ∧
      (∀ y : Y, ψ (κ y) = φ y) ∧
      ψ w₀ = x₀ ∧
      Group.FG (HomotopyGroup (Fin 1) W w₀) ∧
      Function.Injective (Work.Serre.piMapN ψ 1 w₀) ∧
      (∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) W w₀)) := by
  obtain ⟨Y', instY', y₀', ψ, χ, hψχ, hχ₀, hpc', hfg', hinj'⟩ := killKernelFgBased y₀ φ hfg
  letI : TopologicalSpace Y' := instY'
  haveI : PathConnectedSpace Y' := hpc'
  obtain ⟨W, instW, w₀, ψ', χ', hψ'χ', hχ'₀, hpcW, hfgW, hinjW, hkilledW⟩ :=
    killTowerFgBased (N - 1) 1 (le_refl 1) y₀' ψ
      (fun i hi2 hiN x => hX i hi2 (by omega) x) hfg' hinj'
      (fun j hj2 hj1 => absurd hj2 (by omega))
  letI : TopologicalSpace W := instW
  refine ⟨W, instW, w₀, ψ', χ'.comp χ, hpcW, ?_, ?_, hfgW, hinjW, ?_⟩
  · intro y
    have h1 : ψ' (χ' (χ y)) = ψ (χ y) := congrFun (congrArg DFunLike.coe hψ'χ') (χ y)
    have h2 : ψ (χ y) = φ y := congrFun (congrArg DFunLike.coe hψχ) y
    exact h1.trans h2
  · have hcomp : ψ'.comp (χ'.comp χ) = φ := by
      rw [← ContinuousMap.comp_assoc, hψ'χ', hψχ]
    have h1 : ψ' w₀ = (ψ'.comp (χ'.comp χ)) y₀ := by
      rw [← hχ'₀, ← hχ₀]
      rfl
    rw [h1, hcomp, hφ]
  · intro i hi2 hiN
    exact hkilledW i hi2 (by omega)

end

end Work.Rat.RankOneC1
