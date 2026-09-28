import Mathlib
import Submission.Work.Serre.SweepDefs
import Submission.Work.Serre.SweepRelDefs
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.RatHurewicz.DomeMap
import Submission.Work.Serre.sweepRelOfHasHLPRel
import Submission.Work.Serre.domeHomeo
import Submission.Work.Serre.sweepBdryOne
import Submission.Work.Serre.sweepBdrySucc

/-!
# The three-face lifting property for the cube and for its boundary

`Work.Serre.Sweep Z p` (see `Submission/Work/Serre/SweepDefs.lean`) is the statement that for a
Serre fibration `p : E → B` and a test space `Z`, every lift of a base map `H : Z × I × I → B`
which is prescribed on the union of the three faces `{s = 0}`, `{t = 0}`, `{t = 1}` of the prism
`Z × I_s × I_t` extends to a lift of `H`.

The main theorem `Work.Serre.sweepCube_bdry` proves `Sweep` for the cube `Z = I^m` and for its
boundary `Z = ∂I^m`, for every `m`, and for every Serre fibration.  The proof is an induction on
`m`, using

* `Work.StemsB.exists_lift_rel`, i.e. the relative homotopy lifting property `HasHLPRel p k` of a
  Serre fibration for the pair `(I^k × {0} ∪ ∂I^k × I) ⊂ I^k × I`, packaged as the "disk step"
  `Work.Serre.SweepRel m` (`Submission/Work/Serre/SweepRelDefs.lean`);
* the decomposition `∂I^{m+1} = F ∪ D` of the boundary of the cube into the bottom face
  `F = {z | z (Fin.last m) = 0} ≅ I^m` and the dome `D = ∂I^{m+1} ∖ int F ≅ I^m`, parametrised by
  `Work.RatHurewicz.domePt` (see `Work.Serre.IsDomeHomeo`).

The pieces of the induction are proved in the sibling files `Serre/sweepRelOfHasHLPRel.lean`,
`Serre/domeHomeo.lean`, `Serre/sweepBdryOne.lean` and `Serre/sweepBdrySucc.lean`.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `∂I^0 = ∅`, so `Sweep ↥(∂I^0)` is vacuously true. -/
theorem sweepBdryZero (p : C(E, B)) : Sweep ↥(Cube.boundary (Fin 0)) E B p := by
  intro H f₀ h₀ f₁ h₁ f₂ h₂ c₀ c₁
  haveI : IsEmpty ↥(Cube.boundary (Fin 0)) := by
    rw [show Cube.boundary (Fin 0) = (∅ : Set (Fin 0 → unitInterval)) from by
      ext x; simp [Cube.boundary]]
    infer_instance
  refine ⟨⟨fun x => isEmptyElim x.1, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact continuous_of_const (fun a b => isEmptyElim a.1)
  · ext x; exact isEmptyElim x.1
  · intro z t; exact isEmptyElim z
  · intro z s; exact isEmptyElim z
  · intro z s; exact isEmptyElim z

/-- The cube and its boundary, in every dimension, satisfy the three-face lifting property. -/
theorem sweepCube_bdry_aux (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) :
    ∀ m : ℕ, Sweep ↥(Cube.boundary (Fin m)) E B p ∧ Sweep (Fin m → unitInterval) E B p := by
  have hrel : ∀ k : ℕ, Work.StemsB.HasHLPRel p k := fun k => Work.StemsB.exists_lift_rel p hp k
  have hSR : ∀ m : ℕ, SweepRel m E B p := fun m => sweepRelOfHasHLPRel p (hrel (m + 1))
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | m
    · -- `m = 0`: the boundary is empty and the cube is a point
      exact ⟨sweepBdryZero p, Sweep.of_sweepRel (hSR 0) (sweepBdryZero p)⟩
    rcases m with _ | k
    · -- `m = 1`: `∂I¹ = {0,1}`, and the cube `I¹` is the disk step for `m = 1`
      have h0 : Sweep (Fin 0 → unitInterval) E B p := (ih 0 (by omega)).2
      exact ⟨sweepBdryOne p h0, Sweep.of_sweepRel (hSR 1) (sweepBdryOne p h0)⟩
    · -- `m = k + 2`: split `∂I^{k+2}` into the bottom face and the dome
      have hk : Sweep ↥(Cube.boundary (Fin (k + 1))) E B p := (ih (k + 1) (by omega)).1
      obtain ⟨e, he⟩ := domeHomeo (m := k + 1) (by omega)
      have hb : Sweep ↥(Cube.boundary (Fin (k + 1 + 1))) E B p :=
        sweepBdrySucc (m := k + 1) (by omega) p (hSR (k + 1)) hk e he
      exact ⟨hb, Sweep.of_sweepRel (hSR (k + 1 + 1)) hb⟩

-- `Work.Serre.sweepCube_bdry`: the "three faces" lifting property `Work.Serre.Sweep`
-- (see `Submission/Work/Serre/SweepDefs.lean`) holds for the cube `Fin m → I` and for its
-- boundary `↥(Cube.boundary (Fin m))`, for every `m`, for every Serre fibration.
--
-- PROOF PLAN (induction on `m`; everything is `Work.StemsB.exists_lift_rel p hp k`
-- = `Work.StemsB.HasHLPRel p k`, the relative HLP for the "L-shaped" prism
-- `(Fin k → I) × I` with the lift prescribed on `(Fin k → I) × {0} ∪ ∂(Fin k → I) × I`):
--
-- * `Sweep (↥(Cube.boundary (Fin 0)))`: trivial, since `Cube.boundary (Fin 0) = ∅`.
--   (`sweepBdryZero`)
-- * `Sweep (↥(Cube.boundary (Fin 1)))`: `∂I¹ = {0,1}`, so the domain is two squares; each is the
--   prism over the cube `Fin 1 → I` in the `s`-direction, and `HasHLPRel p 1` applies to each.
--   (`sweepBdryOne`)
-- * `Sweep (Fin m → I)` from `Sweep (↥(Cube.boundary (Fin m)))`: the prism over the cube
--   `(Fin m → I) × I` in the `s`-direction has L-boundary
--   `(Fin m → I) × I × {0} ∪ ((∂(Fin m → I)) × I ∪ (Fin m → I) × {0,1}) × I`,
--   i.e. the three prescribed faces together with `∂(Fin m → I) × I × I`; the latter is
--   supplied by `Sweep (↥(Cube.boundary (Fin m)))` applied to the restriction of the data.
--   Use `HasHLPRel p (m+1)`.  (`SweepRel`, `sweepRelOfHasHLPRel`, `Sweep.of_sweepRel`)
-- * `Sweep (↥(Cube.boundary (Fin (m+1))))` from `Sweep (↥(Cube.boundary (Fin m)))` and
--   `HasHLPRel p (m+1)` (for `m ≥ 1`), via the decomposition `∂I^{m+1} = F ∪ D` into the bottom
--   face `F = {x | x (Fin.last m) = 0} ≅ I^m` and the *dome* `D = ∂I^{m+1} ∖ int F`, which
--   `Work.RatHurewicz.domePt (hm : 1 ≤ m) : C(Fin m → I, ↥(Cube.boundary (Fin (m+1))))`
--   parametrises homeomorphically with `domePt (∂I^m) ⊆` the rim `∂F`.  (`IsDomeHomeo`,
--   `domeHomeo`, `sweepBdrySucc`)
theorem sweepCube_bdry {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) :
    (∀ m : ℕ, Work.Serre.Sweep (Fin m → unitInterval) E B p) ∧
    (∀ m : ℕ, Work.Serre.Sweep ↥(Cube.boundary (Fin m)) E B p) := by
  have h := sweepCube_bdry_aux p hp
  exact ⟨fun m => (h m).2, fun m => (h m).1⟩

end

end Work.Serre
