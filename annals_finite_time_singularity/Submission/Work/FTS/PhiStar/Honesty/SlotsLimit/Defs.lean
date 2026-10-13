/-
# `FTS/PhiStar/Honesty/SlotsLimit/Defs` — test functions on the open quadrant and the
formal transposes of the operators occurring in the three elliptic slots

The route to `Work.FTS.PhiStar.Honesty.hkMem_slots_of_approx` is a *limit passage*: the three
slots `z²∂_z²Ψ`, `∂_θ²Ψ`, `z∂_z∂_θ²Ψ` of the approximating class data `Ψ_n = psiSeries α (G n)`
are Cauchy in the weighted `L²`-spaces (this is the a priori estimate `EllEstUnif` applied to
the differences) and the values `Ψ_n` converge to `Φ` in `L²(Q0)`.  Passing to the limit
requires two things:

* the *pointwise almost-everywhere* limits of the slots (and of all their sub-slots) are the
  **classical** derivatives of `Φ`.  This is the content of the "integration by parts against
  test functions" step: for every smooth compactly supported `φ` on the open quadrant `Q0` and
  every smooth `f` on `Q0`,
  `∫_{Q0} T f · φ = ∫_{Q0} f · T* φ`, where `T*` is the formal transpose of `T`;
* the limit inherits the `L²`-bound (Fatou).

This file fixes the vocabulary of that step: the class `TestQ0` of test functions, and the
explicit transposes `pzIterStar`, `pthIterStar`, `DzStar`, `DthStar`, `DzIterStar`,
`DthIterStar`, `mixedStar` together with the transposes of the three slot operators
(`slot1`, `slot2`, `slot3`).  The identities themselves are proved in the sibling modules.

Everything in this file is a definition or a syntactic re-statement; no analysis is involved.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## Test functions on the open quadrant -/

/-- **A test function on the open quadrant**: globally `C^∞`, compactly supported, with support
inside `Q0 = (0,∞) × (0,π/2)`.  (The support is *strictly* inside the open quadrant, so every
`θ`-derivative of a test function also vanishes at the angular endpoints and at `z = 0`.) -/
def TestQ0 (φ : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ)
    ∧ HasCompactSupport (Function.uncurry φ)
    ∧ tsupport (Function.uncurry φ) ⊆ Q0

theorem TestQ0.smooth {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry φ) := h.1

theorem TestQ0.cpt {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) : HasCompactSupport (Function.uncurry φ) :=
  h.2.1

theorem TestQ0.tsupp {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    tsupport (Function.uncurry φ) ⊆ Q0 := h.2.2

theorem TestQ0.continuous {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    Continuous (Function.uncurry φ) := h.smooth.continuous

theorem TestQ0.continuousOn {φ : ℝ → ℝ → ℝ} (h : TestQ0 φ) :
    ContinuousOn (Function.uncurry φ) Q0 := h.continuous.continuousOn

/-! ## The formal transposes of the elementary operators

For a test function `φ`, `∫_{Q0} (z ∂_z f)·φ = ∫_{Q0} f·(DzStar φ)` with
`DzStar φ = -(z ∂_z φ + φ)`, because the boundary term at `z = 0` carries the factor `z` while
the one at `z = ∞` dies from the compact support.  Likewise
`∫_{Q0} (sin 2θ ∂_θ f)·φ = ∫_{Q0} f·(DthStar φ)` with `DthStar φ = -(sin 2θ ∂_θ φ + 2 cos 2θ φ)`,
both angular boundary terms vanishing because `sin 2θ = 0` at the endpoints.  Iterating gives
the transposes of `D_z^j`, `D_θ^i` and of their compositions, and the plain derivatives have
transposes `±` themselves (two dimensions of integration by parts with compactly supported
test functions, no boundary terms at all). -/

/-- The transpose of `∂_z^j`: `pzIterStar j φ = (-1)^j ∂_z^j φ`. -/
def pzIterStar (j : ℕ) (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-1 : ℝ) ^ j * Work.Spaces.pzIter j φ z θ

/-- The transpose of `∂_θ^i`: `pthIterStar i φ = (-1)^i ∂_θ^i φ`. -/
def pthIterStar (i : ℕ) (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-1 : ℝ) ^ i * Work.Spaces.pthIter i φ z θ

/-- The transpose of `D_z = z ∂_z`: `DzStar φ = -(D_z φ + φ)`. -/
def DzStar (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Spaces.Dz φ z θ + φ z θ)

/-- The transpose of `D_θ = sin 2θ ∂_θ`: `DthStar φ = -(D_θ φ + 2 cos 2θ · φ)`. -/
def DthStar (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Spaces.Dth φ z θ + 2 * Real.cos (2 * θ) * φ z θ)

/-- The transpose of `D_z^j`: iterate `DzStar`. -/
def DzIterStar : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, φ => φ
  | n + 1, φ => DzIterStar n (DzStar φ)

/-- The transpose of `D_θ^i`: iterate `DthStar`. -/
def DthIterStar : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, φ => φ
  | n + 1, φ => DthIterStar n (DthStar φ)

/-- The transpose of `mixed j i = D_z^j D_θ^i`: `(D_θ^i)*` after `(D_z^j)*`. -/
def mixedStar (j i : ℕ) (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  DthIterStar i (DzIterStar j φ)

/-! ## The three slot operators and their transposes -/

/-- The first slot operator `f ↦ z² ∂_z² f`. -/
def slot1 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ

/-- The second slot operator `f ↦ ∂_θ² f`. -/
def slot2 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 f

/-- The third slot operator `f ↦ z ∂_z ∂_θ² f`. -/
def slot3 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.Dz (Work.Spaces.pthIter 2 f)

/-- The transpose of the first slot: the multiplication by `z²` is self-adjoint, so it stays on
the test function. -/
def slot1Star (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  pzIterStar 2 (fun z θ => z ^ 2 * φ z θ)

/-- The transpose of the second slot. -/
def slot2Star (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := pthIterStar 2 φ

/-- The transpose of the third slot. -/
def slot3Star (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := pthIterStar 2 (DzStar φ)

/-- The weight of the `(j,i)`-term of `HkIntegrand`: the pure weight `w/√sin^η` of the first
sum when `i = 0`, and `Wt = w·sin(2θ)^{-γ/2}` of the mixed double sum when `i ≥ 1`. -/
def termWeight (α : ℝ) (i : ℕ) : ℝ → ℝ → ℝ :=
  if i = 0 then fun z θ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
  else Work.Spaces.Wt α

/-- The pairs `(j,i)` indexing the terms of `HkIntegrand`: the pure terms `(j,0)` with `j ≤ k`
and the mixed terms `(j,i)` with `1 ≤ i` and `i + j ≤ k`. -/
def HkActivePairs (k : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.range (k + 1)).product (Finset.range (k + 1))).filter
    (fun p : ℕ × ℕ => p.2 = 0 ∧ p.1 ≤ k ∨ 1 ≤ p.2 ∧ p.2 + p.1 ≤ k))

/-- The three slot operators, indexed by `ℕ` (indices `≥ 2` repeat the third one). -/
def slot : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0 => slot1
  | 1 => slot2
  | _ => slot3

theorem slot_zero (f : ℝ → ℝ → ℝ) : slot 0 f = slot1 f := rfl
theorem slot_one (f : ℝ → ℝ → ℝ) : slot 1 f = slot2 f := rfl
theorem slot_two (f : ℝ → ℝ → ℝ) : slot 2 f = slot3 f := rfl

/-- The operator of the `(j,i)`-th sub-slot of the `r`-th slot, `f ↦ mixed j i (slot_r f)`. -/
def subSlot (r : ℕ) (j i : ℕ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Spaces.mixed j i (slot r f)

/-- The transpose of the `(j,i)`-th sub-slot of the `r`-th slot: the transpose of a composition
reverses the order, so the slot transpose acts *last*. -/
def subSlotStar (r : ℕ) (j i : ℕ) (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  match r with
  | 0 => slot1Star (mixedStar j i φ)
  | 1 => slot2Star (mixedStar j i φ)
  | _ => slot3Star (mixedStar j i φ)

theorem slot1_apply (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    slot1 f z θ = z ^ 2 * Work.Spaces.pzIter 2 f z θ := rfl

theorem slot2_apply (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    slot2 f z θ = Work.Spaces.pthIter 2 f z θ := rfl

theorem slot3_apply (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    slot3 f z θ = Work.Spaces.Dz (Work.Spaces.pthIter 2 f) z θ := rfl

@[simp] theorem subSlot_zero (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    subSlot 0 j i f = Work.Spaces.mixed j i (slot1 f) := by
  rw [subSlot, slot_zero]

@[simp] theorem subSlot_one (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    subSlot 1 j i f = Work.Spaces.mixed j i (slot2 f) := by
  rw [subSlot, slot_one]

@[simp] theorem subSlot_two (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    subSlot 2 j i f = Work.Spaces.mixed j i (slot3 f) := by
  rw [subSlot, slot_two]

theorem subSlot_eq_mixed (r : ℕ) (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    subSlot r j i f = match r with
      | 0 => Work.Spaces.mixed j i (slot1 f)
      | 1 => Work.Spaces.mixed j i (slot2 f)
      | _ => Work.Spaces.mixed j i (slot3 f) := by
  rw [subSlot]
  cases r with
  | zero => rfl
  | succ r =>
    cases r with
    | zero => rfl
    | succ r => rfl

end Work.FTS.PhiStar.Honesty.SlotsLimit
