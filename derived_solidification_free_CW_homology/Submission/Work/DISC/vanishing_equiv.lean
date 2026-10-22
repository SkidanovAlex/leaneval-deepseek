import Mathlib
import Submission.Work.DISC.Defs
import Submission.Work.DISC.uniform_tail_of_open
import Submission.Work.DISC.isLocallyConstant_glue

/-!
# AREA DISC — vanishing-at-infinity functions on `S × (ℕ∪{∞})` are null sequences

Locally constant functions on the light profinite set `↥S × (ℕ∪{∞})` which vanish on the slice
`↥S × {∞}` are the same thing as null sequences of locally constant functions `↥S → M`, and the
shift-difference `f ↦ f - f ∘ (id × shift)` corresponds to the difference `a_n ↦ a_n - a_{n+1}`
of consecutive terms.

The two topological inputs are:

* `Work.DISC.uniform_tail_of_open`: an open set containing the slice `↥S × {∞}` contains all
  slices `↥S × {n}` for `n ≥ N` (compactness of `↥S` plus the fact that neighbourhoods of `∞`
  in `ℕ∪{∞}` are cofinite);
* `Work.DISC.isLocallyConstant_glue`: an eventually zero sequence of locally constant functions
  on `↥S` glues to a locally constant function on `↥S × (ℕ∪{∞})`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.DISC

/-! ## Slices -/

/-- The `n`-th slice `s ↦ f (s, n)` of a locally constant function on `↥S × (ℕ∪{∞})`. -/
def vanishingSlice (S : LightProfinite.{0}) {M : ModuleCat.{0} ℤ}
    (f : LocallyConstant (↥S × OnePoint ℕ) ↥M) (n : ℕ) : LocallyConstant ↥S ↥M :=
  f.comap ⟨fun s => (s, (n : OnePoint ℕ)), by fun_prop⟩

lemma vanishingSlice_apply (S : LightProfinite.{0}) {M : ModuleCat.{0} ℤ}
    (f : LocallyConstant (↥S × OnePoint ℕ) ↥M) (n : ℕ) (s : ↥S) :
    vanishingSlice S f n s = f (s, (n : OnePoint ℕ)) := rfl

/-! ## The two directions of the equivalence -/

/-- A locally constant function on `↥S × (ℕ∪{∞})` vanishing on the slice at infinity gives the
null sequence of its slices. -/
def vanishingToNull (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ)
    (f : Vanishing S M) : NullSeq S M :=
  ⟨fun n => vanishingSlice S f.1 n, by
    obtain ⟨N, hN⟩ := uniform_tail_of_open S
      (f.1 ⁻¹' ({0} : Set ↥M) : Set (↥S × OnePoint ℕ))
      (f.1.isLocallyConstant {0}) (fun s => by simpa using f.2 s)
    refine ⟨N, fun n hn => ?_⟩
    ext s
    simpa [vanishingSlice_apply] using hN n hn s⟩

/-- A null sequence glues to a locally constant function on `↥S × (ℕ∪{∞})` vanishing at
infinity. -/
def vanishingOfNull (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ)
    (a : NullSeq S M) : Vanishing S M :=
  ⟨⟨fun p => OnePoint.elim p.2 (0 : ↥M) (fun n => a.1 n p.1),
    isLocallyConstant_glue S M a.1 a.bound (fun n hn => by
      ext s
      exact congrArg (fun g : LocallyConstant ↥S ↥M => g s) (a.bound_spec n hn))⟩,
   fun s => rfl⟩

lemma vanishingOfNull_toNull (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ)
    (f : Vanishing S M) : vanishingOfNull S M (vanishingToNull S M f) = f := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro p
  obtain ⟨s, x⟩ := p
  show OnePoint.elim x (0 : ↥M) (fun n => vanishingSlice S f.1 n s) = f.1 (s, x)
  induction x using OnePoint.rec with
  | infty => exact (f.2 s).symm
  | coe n => rfl

lemma vanishingToNull_ofNull (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ)
    (a : NullSeq S M) : vanishingToNull S M (vanishingOfNull S M a) = a := by
  apply Subtype.ext
  funext n
  apply LocallyConstant.ext
  intro s
  show vanishingSlice S (vanishingOfNull S M a).1 n s = a.1 n s
  rfl

lemma vanishingToNull_shiftDiff (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ)
    (f : Vanishing S M) :
    vanishingToNull S M (Vanishing.shiftDiff f) = NullSeq.diff (vanishingToNull S M f) := by
  apply Subtype.ext
  funext n
  apply LocallyConstant.ext
  intro s
  show vanishingSlice S (Vanishing.shiftDiff f).1 n s =
    vanishingSlice S f.1 n s - vanishingSlice S f.1 (n + 1) s
  rw [show vanishingSlice S (Vanishing.shiftDiff f).1 n s =
      f.1 (s, (n : OnePoint ℕ)) - f.1 (s, (n + 1 : ℕ)) from by
    show f.1 (s, (n : OnePoint ℕ)) -
      f.1 (shiftProd S (s, (n : OnePoint ℕ))) = f.1 (s, (n : OnePoint ℕ)) -
        f.1 (s, (n + 1 : ℕ))
    rw [shiftProd_apply]
    rfl]
  simp only [vanishingSlice_apply]

theorem vanishing_equiv (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) :
    ∃ e : Work.DISC.Vanishing S M ≃ Work.DISC.NullSeq S M,
      ∀ f : Work.DISC.Vanishing S M,
        e (Work.DISC.Vanishing.shiftDiff f) = Work.DISC.NullSeq.diff (e f) :=
  ⟨{ toFun := vanishingToNull S M
     invFun := vanishingOfNull S M
     left_inv := vanishingOfNull_toNull S M
     right_inv := vanishingToNull_ofNull S M },
   vanishingToNull_shiftDiff S M⟩

end Work.DISC
