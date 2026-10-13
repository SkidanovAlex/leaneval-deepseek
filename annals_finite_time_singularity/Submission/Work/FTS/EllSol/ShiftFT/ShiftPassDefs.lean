/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# Slot vocabulary for the truncation passage `ShiftFT/shiftedFlat_of_nice`

`Work.FTS.EllSol.ShiftedFlatAux` is the shifted Agmon estimate
`∫∫ (∂_θL_b u)² σ_a ≤ C (∫∫ (L_b u)² σ_η + √(∫∫ (L_b²u)² σ_η · ∫∫ (u_{θθ})² σ_η))` on the
strip, where `L_b = ∂_t - b`.  The passage from the compactly-supported ("nice") case
`ShiftFT/shiftedFlatNice` to the general `C²`-on-the-strip case is done by truncating the
*junk-free* quantity `v = L_b u` and solving `L_b G = chi N · v` exactly
(`ShiftFT/ShiftPrimDefs.lean`); the approximants are `uTr N b u` (used for `b ≥ 0`) and
`uTrFwd N b u` (used for `b ≤ 0`).

This file only fixes the four slot functionals of the statement, so that the sub-lemmas of the
passage can be stated without repeating the unwieldy expressions:

* `slotE1 b f`  — the heavy first-order slot `(L_b f)² σ_η`;
* `slotE2 b f`  — the heavy second-order slot `(L_b²f)² σ_η`;
* `slotE3 f`    — the heavy angular slot `(∂_θ²f)² σ_η`;
* `slotAa α b f`— the light mixed slot `(∂_θL_b f)² σ_a`.

They are *definitionally* the expressions of `Work.FTS.EllSol.ShiftedFlatAux`, so that a
statement phrased with `slotE1` etc. can be used where the explicit expression is expected
(and conversely).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.Trunc.PassAux2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The integration domain `ℝ × Iθ` (the same set as `Work.FTS.EllSol.Trunc.SI`). -/
abbrev passSI : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ

/-- The scale sequence `Nf n = n + 2` along which the truncation parameter tends to `∞`. -/
def Nf (n : ℕ) : ℝ := (n : ℝ) + 2

/-- The heavy first-order slot `(L_b f)² σ_η`, `L_b f = ∂_t f - b f`. -/
def slotE1 (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pz f p.1 p.2 - b * f p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2

/-- The heavy second-order slot `(L_b²f)² σ_η`. -/
def slotE2 (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2 - 2 * b * Work.Spaces.pz f p.1 p.2
      + b ^ 2 * f p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2

/-- The heavy angular slot `(∂_θ²f)² σ_η`. -/
def slotE3 (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2

/-- The light mixed slot `(∂_θL_b f)² σ_a`. -/
def slotAa (α b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2 - b * Work.Spaces.pth f p.1 p.2) ^ 2
    * Work.FTS.EllSol.FlatFT.wA α p.2

@[simp] theorem slotE1_apply (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotE1 b f p = (Work.Spaces.pz f p.1 p.2 - b * f p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2 := rfl

@[simp] theorem slotE2_apply (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotE2 b f p = (Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2
        - 2 * b * Work.Spaces.pz f p.1 p.2 + b ^ 2 * f p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2 := rfl

@[simp] theorem slotE3_apply (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotE3 f p = (Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2 := rfl

@[simp] theorem slotAa_apply (α b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotAa α b f p = (Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2
        - b * Work.Spaces.pth f p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wA α p.2 := rfl

theorem slotE1_nonneg_of_mem {b : ℝ} {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ passSI) :
    0 ≤ slotE1 b f p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)

theorem slotE2_nonneg_of_mem {b : ℝ} {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ passSI) :
    0 ≤ slotE2 b f p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)

theorem slotE3_nonneg_of_mem {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ passSI) :
    0 ≤ slotE3 f p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)

theorem slotAa_nonneg_of_mem {α b : ℝ} {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ passSI) :
    0 ≤ slotAa α b f p :=
  mul_nonneg (sq_nonneg _)
    (Work.FTS.EllSol.FlatFT.wA_nonneg hp.2)

theorem measurableSet_passSI : MeasurableSet passSI :=
  MeasurableSet.prod MeasurableSet.univ measurableSet_Icc

/-- `passSI` is `Trunc.SI`. -/
theorem passSI_eq_SI : passSI = Work.FTS.EllSol.Trunc.SI := rfl

end

end Work.FTS.EllSol.ShiftFT
