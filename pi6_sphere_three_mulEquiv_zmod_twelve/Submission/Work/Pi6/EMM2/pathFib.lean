import Mathlib
import Submission.Work.Pi6.EMM2.Statements
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Area EMM2 — the path fibration of a range model

The **path–loop fibration** of a based space `(X, x₀)` is the map
`mpathQ (const x₀) : mpath (const x₀) → X` of the mapping path space of the constant map
`PUnit → X`.  The mapping path space of the constant map is the based path space of `X`, and
`mpathQ` is evaluation at the endpoint, so this is the usual path fibration `PX → X`.

Three facts are collected here (the statement `Work.Pi6.EMM2.PathFibStatement`):

* the total space is contractible (`Work.FGThm.mpathHomotopyEquiv` with `E = PUnit`,
  contractibility of the mapping path space of every map `mpath p ≃ₕ E`);
* `mpathQ` is a Serre fibration (`Work.Serre.mpathQ_isSerreFibration`);
* the fibre over `x₀` is a range model of the same Eilenberg–MacLane space with degree lowered by
  one and range lowered by one: the fibre of `mpathQ (const x₀)` over `x₀` is the loop space
  `Ω X = Path x₀ x₀` up to homeomorphism, and the loop shift
  `Work.Stems.isEMSpaceUpTo_loop'` lowers `K(A,m)` to `K(A,m-1)` with range `M - 1`.

The homeomorphism between the fibre and the loop space is assembled from
`Work.StemsB.fibreEvalOneHomeo` (the fibre of the path–loop fibration `evalOne` is the loop space)
and `Homeomorph.subtype` applied to the identification `mpath (const x₀) ≃ₜ PathSpace X x₀` of the
total spaces.
-/

open scoped Topology unitInterval
open ContinuousMap

namespace Work.Pi6.EMM2

noncomputable section

/-- The mapping path space of the constant map `PUnit → X` at `x₀` is the based path space of `X`:
the `PUnit` coordinate is dropped by `Homeomorph.punitProd`, and the subspace conditions agree. -/
def mpathConstHomeo (X : Type) [TopologicalSpace X] (x₀ : X) :
    Work.Serre.mpath (ContinuousMap.const PUnit x₀) ≃ₜ Work.StemsB.PathSpace X x₀ :=
  Homeomorph.subtype (p := fun z : PUnit × C(I, X) =>
      z.2 0 = (ContinuousMap.const PUnit x₀ : C(PUnit, X)) z.1)
    (q := fun γ : C(I, X) => γ 0 = x₀)
    (Homeomorph.punitProd (C(I, X))) (fun _ => Iff.rfl)

/-- **The fibre of the path fibration `mpathQ (const x₀)` over `x₀` is the loop space
`Ω X = Path x₀ x₀`.**  This is `Work.StemsB.fibreEvalOneHomeo` transported along the homeomorphism
`mpathConstHomeo` of total spaces (under which `mpathQ (const x₀)` becomes `Work.StemsB.evalOne`). -/
def fibreMpathQConstHomeo (X : Type) [TopologicalSpace X] (x₀ : X) :
    Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit x₀)) x₀ ≃ₜ Path x₀ x₀ :=
  (Homeomorph.subtype
    (p := fun y => Work.Serre.mpathQ (ContinuousMap.const PUnit x₀) y = x₀)
    (q := fun γ : Work.StemsB.PathSpace X x₀ => Work.StemsB.evalOne X x₀ γ = x₀)
    (mpathConstHomeo X x₀) (fun _ => Iff.rfl)).trans (Work.StemsB.fibreEvalOneHomeo X x₀)

/-- The inverse homeomorphism sends the constant loop to the canonical base point of the fibre. -/
@[simp]
theorem fibreMpathQConstHomeo_symm_refl (X : Type) [TopologicalSpace X] (x₀ : X) :
    (fibreMpathQConstHomeo X x₀).symm (Path.refl x₀) =
      Work.StemsB.fibrePoint (Work.Serre.mpathQ (ContinuousMap.const PUnit x₀))
        (Work.Serre.mpathOf (ContinuousMap.const PUnit x₀) PUnit.unit) :=
  rfl

/-- **The path fibration of a range model** (`Pi6/EMM2/pathFib`): for a range model `X` of `K(A,m)`
through degree `M` with `2 ≤ m`, the mapping path space of the constant map `PUnit → X` is
contractible, `mpathQ (const x₀)` is a Serre fibration, and its fibre over `x₀` is a range model of
`K(A,m-1)` through degree `M - 1`. -/
theorem pathFib : Work.Pi6.EMM2.PathFibStatement := by
  intro A _ m M hm X _ x₀ hX
  refine ⟨?_, ?_, ?_⟩
  · -- the mapping path space of `const x₀ : PUnit → X` is homotopy equivalent to `PUnit`
    exact ((Work.FGThm.mpathHomotopyEquiv (ContinuousMap.const PUnit x₀)).some).contractibleSpace
  · exact Work.Serre.mpathQ_isSerreFibration (ContinuousMap.const PUnit x₀)
  · -- the fibre is the loop space, whose range model structure is the loop shift
    have hloop : Work.Serre.IsEMSpaceUpTo A (m - 1) (by omega) (M - 1)
        (Path x₀ x₀) (Path.refl x₀) :=
      Work.Stems.isEMSpaceUpTo_loop' (A := A) (m := m) (M := M) hm x₀ hX
    have h := Work.RatHurewicz.isEMSpaceUpTo_of_homeomorph (A := A) (k := m - 1) (N := M - 1)
      (by omega) (fibreMpathQConstHomeo X x₀).symm (Path.refl x₀) hloop
    simpa using h

end

end Work.Pi6.EMM2
