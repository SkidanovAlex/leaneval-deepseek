import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotPairRowsAux
import Submission.Work.BoseBoxFock.fibre_kernel_free
import Submission.Work.BoseBoxFock.fibre_kernel_two
import Submission.Work.BoseBoxFock.pinQ_kernel_expansion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowGDefs` — the fibre functions `G` of the FS `Q₂` row

Each of the five triple integrals of `potPairRows_kernelExpanded` has the form

    ∫_x ∫_y ∫_u (state) · K (kernel arguments) · (state),

and the step (S2) of `FINDING_PotPairRows_exists.md` rewrites it as `∫_w ∫_y K w y · G w y`,
where `G` is the *fibre* function obtained by freezing the two kernel arguments and integrating out
the remaining coordinates.  This module names those fibre functions (`pairG13`, `pairG23`,
`pairG21`, `slotG`) so that the error lemmas are readable, and records the `rfl` bridges to the
inline shapes used by `block13_fibre` / `blockTwo3_fibre` / `block13_fibre_L2` etc.

Everything here is definitional (`sorry`-free).
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Insert the value `w` in the coordinate `j` of the fibre `x'`. -/
def insertCoord {n : ℕ} (j : Fin n) (w : E3) (x' : {k : Fin n // k ≠ j} → E3) :
    Fin n → E3 :=
  fun k => if h : k = j then w else x' ⟨k, h⟩

/-- Insert the values `w₀`, `w₁` in the coordinates `p.1`, `p.2` of the fibre `x'`. -/
def insertCoord2 {n : ℕ} (p : Fin n × Fin n) (w₀ w₁ : E3)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) : Fin n → E3 :=
  fun k => if h : k = p.1 then w₀ else if h' : k = p.2 then w₁ else x' ⟨k, h, h'⟩

@[simp] lemma insertCoord_eq {n : ℕ} (j : Fin n) (w : E3)
    (x' : {k : Fin n // k ≠ j} → E3) :
    insertCoord j w x' = fun k => if h : k = j then w else x' ⟨k, h⟩ := rfl

@[simp] lemma insertCoord2_eq {n : ℕ} (p : Fin n × Fin n) (w₀ w₁ : E3)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) :
    insertCoord2 p w₀ w₁ x'
      = fun k => if h : k = p.1 then w₀
                 else if h' : k = p.2 then w₁ else x' ⟨k, h, h'⟩ := rfl

/-- **The block I / III.1 fibre**: the kernel sits at `(x p.2, y)` and at the free variable `y`
(which is substituted into slot `p.1`); `A` is the slot-`p.1` state factor and `B` the free factor
attached to the `u`-integral. -/
noncomputable def pairG13 {n : ℕ} (p : Fin n × Fin n) (Θ : Work.BoseDict.Xn n → ℂ)
    (A B : E3 → ℂ) (w y : E3) : ℂ :=
  ∫ x' : {k : Fin n // k ≠ p.2} → E3, ∫ u : E3,
    star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1) * star (B u)
      * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)

/-- **The block II.2 fibre**: the kernel sits at the two configuration slots `p.1`, `p.2`; `A`, `B`
are the free factors attached to `y`, `u`. -/
noncomputable def pairG23 {n : ℕ} (p : Fin n × Fin n) (Θ : Work.BoseDict.Xn n → ℂ)
    (A B : E3 → ℂ) (w₀ w₁ : E3) : ℂ :=
  ∫ x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3, ∫ y : E3, ∫ u : E3,
    star (Θ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
      * Θ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u)

/-- **The block II.1 fibre**: the kernel sits at the two *free* variables `(u,y)`; `A` is the state
factor at both configuration slots `p.1`, `p.2`. -/
noncomputable def pairG21 {n : ℕ} (p : Fin n × Fin n) (Θ : Work.BoseDict.Xn n → ℂ)
    (A : E3 → ℂ) (u y : E3) : ℂ :=
  ∫ x : Work.BoseDict.Xn n, star (Θ x) * A (x p.1) * A (x p.2)
    * Θ (Function.update (Function.update x p.1 y) p.2 u)

/-- **The block III.2 (one-slot) fibre**: the kernel sits at `(x j, y)`. -/
noncomputable def slotG {n : ℕ} (j : Fin n) (Θ : Work.BoseDict.Xn n → ℂ)
    (w y : E3) : ℂ :=
  ∫ x' : {k : Fin n // k ≠ j} → E3,
    star (Θ (insertCoord j w x')) * Θ (Function.update (insertCoord j w x') j y)

end Work.BoseBoxFock
