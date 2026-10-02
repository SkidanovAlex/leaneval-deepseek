import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.StemsB.hasHLP_pullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hurewicz fibrations

`Work.StemsB.HasHLP p Z` is the homotopy lifting property of `p : E → B` with respect to a *single*
test space `Z` (`Submission/Work/StemsB/Fibrations.lean`).  Mathlib has no fibrations at all, so the
vocabulary has to be built here.

* `Work.StemsB.IsHurewiczFibration p` — the HLP with respect to **every** test space (in the
  universe of the total space).  This is the strong notion (a "fibration" in the sense of Hurewicz),
  and it is the one under which all the constructions of fibration theory (fibre transport along a
  path, triviality over a contractible base, and hence the identification of the first page of the
  Serre spectral sequence) are available *without* any cofibration theory: everything is proved by
  applying the HLP to the space one is interested in (`Z = fibre p b`, `Z = I^n`, ...).

* **The path–loop fibration is a Hurewicz fibration** (`isHurewiczFibration_evalOne`), by the
  explicit reparametrisation of `Submission/Work/StemsB/isSerreFibration_evalOne.lean`
  (`hasHLP_evalOne`, which is the HLP of `evalOne` for *every* test space).  This is the fibration
  whose Serre spectral sequence relates `H_*(X)` and `H_*(ΩX)` and which is the input of the
  refined route to `Work.StemsB.RatHurewiczRange` (`CONTRACTS.md` §D).  In particular the relative
  homotopy lifting property (`Work.StemsB.exists_lift_rel`, i.e. the cell-by-cell argument needed
  for a general Serre fibration) is *not* needed for it.

* Closure under composition, products and base change.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

universe uH

/-- A map `p : E → B` is a **Hurewicz fibration** if it has the homotopy lifting property with
respect to every topological space (in the same universe as the total space). -/
def IsHurewiczFibration {E : Type uH} {B : Type uH} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) : Prop := ∀ (Z : Type uH) [TopologicalSpace Z], HasHLP p Z

variable {E B : Type uH} [TopologicalSpace E] [TopologicalSpace B]

/-- The defining property, packaged. -/
theorem IsHurewiczFibration.hasHLP {p : C(E, B)} (hp : IsHurewiczFibration p) (Z : Type uH)
    [TopologicalSpace Z] : HasHLP p Z := hp Z

/-- Every Hurewicz fibration (in the universe of small test spaces) is a Serre fibration: the
cubes `I^n` are among the test spaces. -/
theorem IsHurewiczFibration.isSerreFibration {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : IsHurewiczFibration p) : IsSerreFibration p := fun n => hp (Fin n → I)

/-- The identity is a Hurewicz fibration. -/
theorem isHurewiczFibration_id : IsHurewiczFibration (ContinuousMap.id E) := by
  intro Z _ f b H
  exact ⟨b, H, by ext x; rfl⟩

/-- **The path–loop fibration `PX → X` is a Hurewicz fibration.**  This is
`Work.StemsB.hasHLP_evalOne` (the HLP of the endpoint evaluation for every test space), repackaged.
-/
theorem isHurewiczFibration_evalOne (X : Type uH) [TopologicalSpace X] (x₀ : X) :
    IsHurewiczFibration (evalOne X x₀) := fun Z _ => hasHLP_evalOne X x₀ Z

section Comp

variable {C : Type uH} [TopologicalSpace C]

/-- A composite of Hurewicz fibrations is a Hurewicz fibration. -/
theorem IsHurewiczFibration.comp {p : C(E, B)} {q : C(C, E)}
    (hp : IsHurewiczFibration p) (hq : IsHurewiczFibration q) :
    IsHurewiczFibration (p.comp q) :=
  fun Z _ => (hp Z).comp (hq Z)

end Comp

section Prod

variable {E' : Type uH} [TopologicalSpace E'] {B' : Type uH} [TopologicalSpace B']

/-- A product of Hurewicz fibrations is a Hurewicz fibration. -/
theorem IsHurewiczFibration.prodMap {p : C(E, B)} {p' : C(E', B')}
    (hp : IsHurewiczFibration p) (hp' : IsHurewiczFibration p') :
    IsHurewiczFibration (p.prodMap p') :=
  fun Z _ => (hp Z).prodMap (hp' Z)

end Prod

/-- **Base change of a Hurewicz fibration** along any map `q : E' → B`. -/
theorem IsHurewiczFibration.pullbackSnd {E' : Type uH} [TopologicalSpace E'] {p : C(E, B)}
    (q : C(E', B)) (hp : IsHurewiczFibration p) :
    IsHurewiczFibration (pullbackSnd p q) :=
  fun Z _ => hasHLP_pullback p q (hp Z)

end

end Work.StemsB
