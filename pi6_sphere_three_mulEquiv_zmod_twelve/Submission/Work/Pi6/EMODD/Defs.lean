import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Serre.serreAttachKillPi
import Submission.Work.Serre.MapPathDefs
import Submission.Work.RatHurewicz.RelHomotopy
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The "kill `π₃, …, π_M`" tower and the mapping-path fibration of the `K(ℤ/2,2)` area (EMODD)

`kTower Y k` is `Y` with cells attached (via `Work.Serre.KillCells (j+2)`) so that `π_i` is unchanged
for `i ≤ 2` and trivial for `3 ≤ i ≤ k+2`.  It is the tower used to build a `K(ℤ,2)` range model `Kℤ`
out of `S²`: `Kℤ := kTower (Sph 2) (M-2)`.

`mpathFibre r k₀` is the strict fibre of the Serre fibration `Work.Serre.mpathQ r : mpath r → X`
over the base point `r k₀`; it is homeomorphic to `Work.RatHurewicz.homotopyFibre r k₀`
(`Work.Serre.mpathQ_fibreHomeo`).

The definitions are collected here so that the lemmas about them (delegated) can be stated with a
short statement referring to this module.
-/

open scoped Topology

namespace Work.Pi6.EMODD

noncomputable section

/-- A type bundled with its topology. -/
abbrev Bundled : Type 1 := Σ T : Type, TopologicalSpace T

/-- The iterated "kill `π₃, …, π_{k+2}`" tower, as bundled spaces:
`kTowerB Y 0 = Y`, `kTowerB Y (k+1) = KillCells (k+2) (kTowerB Y k)`. -/
noncomputable def kTowerB : Bundled → ℕ → Bundled
  | Y, 0 => Y
  | Y, (k + 1) => ⟨@Work.Serre.KillCells (k + 2) (kTowerB Y k).1 (kTowerB Y k).2, by
      letI : TopologicalSpace (kTowerB Y k).1 := (kTowerB Y k).2
      exact inferInstance⟩

/-- The iterated "kill `π₃, …, π_{k+2}`" tower over `Y`. -/
abbrev kTower (Y : Type) [tY : TopologicalSpace Y] (k : ℕ) : Type :=
  (kTowerB ⟨Y, tY⟩ k).1

instance kTowerTop (Y : Type) [tY : TopologicalSpace Y] (k : ℕ) :
    TopologicalSpace (kTower Y k) :=
  (kTowerB ⟨Y, tY⟩ k).2

attribute [instance] kTowerTop

/-- The one-step inclusion `kTower Y k → kTower Y (k+1)` (killing `π_{k+3}`). -/
noncomputable def kTowerIncl (Y : Type) [tY : TopologicalSpace Y] (k : ℕ) :
    C(kTower Y k, kTower Y (k + 1)) :=
  Work.Serre.killIncl (k + 2) (kTower Y k)

/-- The inclusion `Y → kTower Y k`. -/
noncomputable def kTowerUp (Y : Type) [tY : TopologicalSpace Y] : ∀ k, C(Y, kTower Y k)
  | 0 => ContinuousMap.id Y
  | (k + 1) => (kTowerIncl Y k).comp (kTowerUp Y k)

@[simp]
theorem kTowerUp_zero (Y : Type) [tY : TopologicalSpace Y] :
    kTowerUp Y 0 = ContinuousMap.id Y := rfl

theorem kTowerUp_succ_apply (Y : Type) [tY : TopologicalSpace Y] (k : ℕ) (y : Y) :
    kTowerUp Y (k + 1) y = kTowerIncl Y k (kTowerUp Y k y) := rfl

/-- The base point of the total space `mpath r` of the mapping-path fibration of `r`. -/
abbrev mpathPt {T X : Type} [TopologicalSpace T] [TopologicalSpace X] (r : C(T, X)) (k₀ : T) :
    Work.Serre.mpath r :=
  Work.Serre.mpathOf r k₀

/-- The strict fibre of the mapping-path fibration `Work.Serre.mpathQ r : mpath r → X` over `r k₀`. -/
abbrev mpathFibre {T X : Type} [TopologicalSpace T] [TopologicalSpace X] (r : C(T, X)) (k₀ : T) :
    Type :=
  Work.StemsB.fibre (Work.Serre.mpathQ r) (Work.Serre.mpathQ r (mpathPt r k₀))

/-- The base point of the strict fibre `mpathFibre r k₀`. -/
abbrev mpathFibrePt {T X : Type} [TopologicalSpace T] [TopologicalSpace X] (r : C(T, X))
    (k₀ : T) : mpathFibre r k₀ :=
  Work.StemsB.fibrePoint (Work.Serre.mpathQ r) (mpathPt r k₀)

end

end Work.Pi6.EMODD
