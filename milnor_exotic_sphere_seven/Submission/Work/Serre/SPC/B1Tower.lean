import Mathlib
import Submission.Work.Serre.SPC.B1Propagate
import Submission.Work.Serre.SPC.attachFibreData
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.Assembly.pullbackFst_serre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cellular tower of the `b = 1` model

Starting from a stage of the model with `π₁` bijective (`Work.Serre.CWModel.StA B b₀ 0`), the
generator and killing steps of `Submission/Work/Serre/CWModel/` attach cells of dimension `≥ 2`,
so the propagation `Work.Serre.SPC.Propagate` transports `GoodN` along the whole tower, and the
`π`-facts come from `Work.Serre.CWModel.genStep`/`killStep`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

/-- The tower of the model, starting at level `0`. -/
def towerB {B : Type} [TopologicalSpace B] (b₀ : B) (s₀ : Work.Serre.CWModel.StA B b₀ 0) :
    (k : ℕ) → Work.Serre.CWModel.StA B b₀ k
  | 0 => s₀
  | (k + 1) => Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))

/-- The index type of the generator step at level `n`. -/
abbrev GenIdx {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) : Type :=
  HomotopyGroup (Fin (n + 2)) B (s.g s.y₀)

/-- The attaching maps of the generator step (all constant at the base point). -/
abbrev GenFr {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) :
    GenIdx s → C(Work.RatHurewicz.cellSphere n, s.Y) :=
  fun _ => ContinuousMap.const _ s.y₀

/-- The index type of the killing step at level `n`. -/
abbrev KillIdx2 {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StG B b₀ n) : Type :=
  {α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀ // Work.Serre.piMapN s.g (n + 2) s.y₀ α = 1}

/-- The attaching maps of the killing step. -/
abbrev KillFr {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StG B b₀ n) :
    KillIdx2 s → C(Work.RatHurewicz.cellSphere (n + 1), s.Y) :=
  fun k => Work.RatHurewicz.killFamily (n + 1) s.Y s.y₀ k.1

/-- **The fibre data of the pullback along the structure map of a stage.** -/
theorem attachFibreData_stage {B : Type} [TopologicalSpace B] (b₀ : B) {E : Type}
    [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E)
    (he₀ : p e₀ = b₀) (f : ℕ)
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j))
    (htr : FibreTransport) {Γ : Type} [TopologicalSpace Γ] [PathConnectedSpace Γ]
    (γ : Γ) (g : C(Γ, B)) (hbase : g γ = b₀) :
    (∀ y : Γ, ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y))).homology j)) ∧
      (∀ y : Γ, CategoryTheory.IsIso (TopCat.singularHomology₀ε
        (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y)) (ModuleCat.of ℤ ℤ))) :=
  attachFibreData p hp b₀ e₀ he₀ f htr hfib hfib0 γ g hbase

/-- The embedding of the old stage into the new one, for the generator step. -/
theorem isEmbedding_attachIncl_gen {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) :
    Topology.IsEmbedding (Work.RatHurewicz.attachIncl n s.Y (GenIdx s) (GenFr s)) :=
  Topology.IsEmbedding.mk (Work.RatHurewicz.isInducing_attachIncl n s.Y (GenIdx s) (GenFr s))
    (Work.RatHurewicz.AttachRange.attachIncl_injective n s.Y (GenIdx s) (GenFr s))

/-- The embedding of the old stage into the new one, for the killing step. -/
theorem isEmbedding_attachIncl_kill {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StG B b₀ n) :
    Topology.IsEmbedding (Work.RatHurewicz.attachIncl (n + 1) s.Y (KillIdx2 s) (KillFr s)) :=
  Topology.IsEmbedding.mk
    (Work.RatHurewicz.isInducing_attachIncl (n + 1) s.Y (KillIdx2 s) (KillFr s))
    (Work.RatHurewicz.AttachRange.attachIncl_injective (n + 1) s.Y (KillIdx2 s) (KillFr s))

/-- **The propagation of `GoodN` along the tower.** -/
theorem towerB_good {B : Type} [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) (he₀ : p e₀ = b₀) (f : ℕ)
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j))
    (hcell : CellStepHyp) (htr : FibreTransport) (hprop2 : Propagate2 b₀ p (1 + f))
    (s₀ : Work.Serre.CWModel.StA B b₀ 0) (h₀ : GoodN b₀ p (1 + f) s₀.y₀ s₀.g) (k : ℕ) :
    GoodN b₀ p (1 + f) (towerB b₀ s₀ k).y₀ (towerB b₀ s₀ k).g := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    haveI hpc : PathConnectedSpace (towerB b₀ s₀ k).Y := (towerB b₀ s₀ k).conn
    -- the generator step
    haveI hpcG : PathConnectedSpace (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).Y :=
      (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).conn
    have hrelG : ∀ x : (towerB b₀ s₀ k).Y,
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g
            (Work.RatHurewicz.attachIncl k (towerB b₀ s₀ k).Y
              (GenIdx (towerB b₀ s₀ k)) (GenFr (towerB b₀ s₀ k)) x) = (towerB b₀ s₀ k).g x :=
      fun x => rfl
    haveI hpcAG : PathConnectedSpace (Work.RatHurewicz.attachCells k (towerB b₀ s₀ k).Y
        (GenIdx (towerB b₀ s₀ k)) (GenFr (towerB b₀ s₀ k))) :=
      Work.Serre.CWModel.pathConnectedSpace_attachCells k (towerB b₀ s₀ k).Y
        (GenIdx (towerB b₀ s₀ k)) (GenFr (towerB b₀ s₀ k))
    have hstepG : ∀ i : ℕ, i < (1 + f) + 1 → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (pairStepMap p (Work.RatHurewicz.attachIncl k (towerB b₀ s₀ k).Y
            (GenIdx (towerB b₀ s₀ k)) (GenFr (towerB b₀ s₀ k)))
          (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g (towerB b₀ s₀ k).g hrelG) i) := by
      intro i hi
      have hdata := attachFibreData_stage b₀ p hp e₀ he₀ f hfib0 hfib htr
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).y₀
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).gbase
      exact (hcell (k + 2) (by omega) (towerB b₀ s₀ k).Y (GenIdx (towerB b₀ s₀ k))
        (GenFr (towerB b₀ s₀ k))
        (Work.StemsB.Pullback (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g p)
        (Work.StemsB.pullbackFst (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g p)
        (fun n => Work.Serre.Assembly.hasHLP_pullbackFst _ p (hp n)) f hdata.1 hdata.2).1 i
        (by omega)
    have hgoodG : GoodN b₀ p (1 + f) (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).y₀
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g :=
      hprop2 (towerB b₀ s₀ k).y₀ (towerB b₀ s₀ k).g ih
        (Work.RatHurewicz.attachIncl k (towerB b₀ s₀ k).Y (GenIdx (towerB b₀ s₀ k))
          (GenFr (towerB b₀ s₀ k)))
        (isEmbedding_attachIncl_gen (towerB b₀ s₀ k))
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g hrelG hstepG
    -- the killing step
    haveI hpcK : PathConnectedSpace
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).Y :=
      (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).conn
    have hrelK : ∀ x : (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).Y,
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).g
            (Work.RatHurewicz.attachIncl (k + 1) (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).Y
              (KillIdx2 (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)))
              (KillFr (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))) x)
          = (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g x :=
      fun x => rfl
    haveI hpcAK : PathConnectedSpace (Work.RatHurewicz.attachCells (k + 1)
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).Y
        (KillIdx2 (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)))
        (KillFr (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)))) :=
      Work.Serre.CWModel.pathConnectedSpace_attachCells (k + 1)
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).Y
        (KillIdx2 (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)))
        (KillFr (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)))
    have hstepK : ∀ i : ℕ, i < (1 + f) + 1 → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (pairStepMap p (Work.RatHurewicz.attachIncl (k + 1)
            (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).Y
            (KillIdx2 (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)))
            (KillFr (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))))
          (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).g
          (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g hrelK) i) := by
      intro i hi
      have hdata := attachFibreData_stage b₀ p hp e₀ he₀ f hfib0 hfib htr
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).y₀
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).g
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).gbase
      exact (hcell (k + 2 + 1) (by omega)
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).Y
        (KillIdx2 (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)))
        (KillFr (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)))
        (Work.StemsB.Pullback (Work.Serre.CWModel.killStep
          (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).g p)
        (Work.StemsB.pullbackFst (Work.Serre.CWModel.killStep
          (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).g p)
        (fun n => Work.Serre.Assembly.hasHLP_pullbackFst _ p (hp n)) f hdata.1 hdata.2).1 i
        (by omega)
    change GoodN b₀ p (1 + f)
      (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).y₀
      (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).g
    exact hprop2 (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).y₀
      (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g hgoodG
      (Work.RatHurewicz.attachIncl (k + 1) (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).Y
        (KillIdx2 (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)))
        (KillFr (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))))
      (isEmbedding_attachIncl_kill (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)))
      (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).g hrelK hstepK

/-- **The `π`-facts of the top stage of the tower**, at every base point. -/
theorem towerB_piMapN_bijective {B : Type} [TopologicalSpace B] (b₀ : B)
    (s₀ : Work.Serre.CWModel.StA B b₀ 0) (N : ℕ) [PathConnectedSpace B] :
    ∀ i : ℕ, i ≤ N → ∀ x : (towerB b₀ s₀ (N + 1)).Y,
      Function.Bijective (Work.Serre.piMapN (towerB b₀ s₀ (N + 1)).g i x) := by
  set s := towerB b₀ s₀ (N + 1) with hs
  haveI hΓ : PathConnectedSpace s.Y := s.conn
  intro i hi x
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    haveI h1 : Subsingleton (HomotopyGroup (Fin 0) s.Y x) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := s.Y) (x := x)).injective.subsingleton
    haveI hZB : Subsingleton (ZerothHomotopy B) := ⟨fun a c => by
      obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective a
      obtain ⟨z, rfl⟩ := ZerothHomotopy.mk_surjective c
      obtain ⟨p⟩ := PathConnectedSpace.joined y z
      exact ZerothHomotopy.sound p⟩
    have h2 : Subsingleton (HomotopyGroup (Fin 0) B (s.g x)) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := s.g x)).injective.subsingleton
    exact ⟨fun a c _ => h1.elim a c, fun y => ⟨default, h2.elim _ _⟩⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact Work.Serre.bijective_piMapN_of_joined s.g (PathConnectedSpace.joined s.y₀ x) (j + 1)
      (s.bij j (by omega))

end

end Work.Serre.SPC
