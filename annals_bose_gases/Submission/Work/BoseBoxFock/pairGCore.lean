import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSmooth_fibres
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGCore` — the clean (box-restricted) representatives of the row fibres,
and the slice vocabulary of the `pairG_dir_leB` estimate

The step (S2)/D2 estimate of `FINDING_PotPairRows_exists.md` §10.7–§10.9 bounds the Dirichlet
energy `pairEnergy ℓ (pairG13 p Θ A B)` of a row fibre by
`C·cA²cB²·pinL2(Θ₀)·(pinDir(Θ₀) + pinL2(Θ₀))` where `Θ = 1_{abox}·Θ₀` is the honest state pin.

On the box squared the fibre agrees with the **clean** representative obtained by replacing `Θ` by
`Θ₀` and restricting the inner integration to the *compact* boxes (`pairEnergy` only sees the values
of the fibre on `boxL ℓ × boxL ℓ`, `pairEnergy_congr_box`), which is what makes the parametric
differentiation and the Cauchy–Schwarz estimates available.

This module fixes that vocabulary:

* `confY13` — the `Y`-configuration of `pairG13`;
* `pairGc13`, `pairGc23`, `pairGc21` — the clean fibres;
* `memX13`, `dirX13`, `memY13`, `memX23`, `dirX23`, `memY23`, `memX21`, `memY21`, `dirY21` — the
  slice masses and slice Dirichlet contents by which the estimates are stated.

`sorry`-free (definitions only).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- The one-particle box `boxL ℓ` of the corpus. -/
scoped notation "boxLQ" => Work.BoseK15.corpusBox.boxL

/-- **The `Y`-configuration of the block I/III.1 fibre `pairG13`**: slots `p.1`, `p.2` receive
the values `y`, `u`, all other slots are taken from `x'`. -/
def confY13 {n : ℕ} (p : Fin n × Fin n) (y u : E3) (x' : {k : Fin n // k ≠ p.2} → E3) : Xn n :=
  fun k => if _ : k = p.1 then y else if h' : k = p.2 then u else x' ⟨k, h'⟩

/-- **The clean representative of the `pairG13` fibre.**  The state factor is the smooth `Θ₀`, the
inner integration runs over the compact boxes `boxPiSet ({k ≠ p.2}) ℓ × boxL ℓ`, and the slot-`p.1`
factor `A` is evaluated at the slot value `x' p.1` (the `w`-dependence drops out because
`insertCoord p.2 w x'` does not change slot `p.1`). -/
noncomputable def pairGc13 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (Θ : Xn n → ℂ) (A B : E3 → ℂ) (w y : E3) : ℂ :=
  ∫ z in (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) ×ˢ (boxLQ ℓ),
    star (Θ (insertCoord p.2 w z.1)) * A (z.1 ⟨p.1, hp⟩) * star (B z.2)
      * Θ (confY13 p y z.2 z.1)

/-- **The clean representative of the `pairG23` fibre** (both slots `p.1`, `p.2` receive the kernel
variables `w₀`, `w₁`; `y'`, `u` are the free factors). -/
noncomputable def pairGc23 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (Θ : Xn n → ℂ) (A B : E3 → ℂ) (w₀ w₁ : E3) : ℂ :=
  ∫ z in (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ) ×ˢ ((boxLQ ℓ) ×ˢ (boxLQ ℓ)),
    star (Θ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2)
      * Θ (insertCoord2 p z.2.1 z.2.2 z.1)

/-- **The clean representative of the `pairG21` fibre**, in the parametrisation in which the two
*configurations* of the integrand are built by `insertCoord2` from the box coordinates
`(a, b, x'')` and `(y, u, x'')`.  (The equality with `pairG21` on the box squared is exactly the
coordinate identity `∫_{abox} f = ∫_{boxL² × P12} f ∘ insertCoord2`.) -/
noncomputable def pairGc21 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (Θ : Xn n → ℂ) (A : E3 → ℂ) (u y : E3) : ℂ :=
  ∫ z in ((boxLQ ℓ) ×ˢ (boxLQ ℓ)) ×ˢ (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ),
    star (Θ (insertCoord2 p z.1.1 z.1.2 z.2)) * A z.1.1 * A z.1.2
      * Θ (insertCoord2 p y u z.2)

/-! ## The slice vocabulary -/

/-- The `w`-slice mass of the state at slot `p.2` (the X-factor of `pairG13`). -/
noncomputable def memX13 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ : Xn n → ℂ) (w : E3) : ℝ :=
  ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ, ‖Θ (insertCoord p.2 w x')‖ ^ 2

/-- The `w`-slice Dirichlet content at slot `p.2` (the derivative factor of `pairG13`). -/
noncomputable def dirX13 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ : Xn n → ℂ) (w : E3) : ℝ :=
  ∑ j : Fin 3, ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
    ‖fderiv ℝ Θ (insertCoord p.2 w x') (slotDirVec p.2 j)‖ ^ 2

/-- The `y`-slice mass of the `Y`-factor of `pairG13`. -/
noncomputable def memY13 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ : Xn n → ℂ) (y : E3) : ℝ :=
  ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ, ∫ u in boxLQ ℓ, ‖Θ (confY13 p y u x')‖ ^ 2

/-- The two-slot mass of the state at slots `(p.1, p.2) = (w₀, w₁)` (the X-factor of `pairG23`). -/
noncomputable def memX23 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ : Xn n → ℂ)
    (w₀ w₁ : E3) : ℝ :=
  ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
    ‖Θ (insertCoord2 p w₀ w₁ x'')‖ ^ 2

/-- The two-slot Dirichlet content at slot `p.1` (the derivative factor of `pairG23`). -/
noncomputable def dirX23 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ : Xn n → ℂ)
    (w₀ w₁ : E3) : ℝ :=
  ∑ j : Fin 3, ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
    ‖fderiv ℝ Θ (insertCoord2 p w₀ w₁ x'') (slotDirVec p.1 j)‖ ^ 2

/-- The two-slot mass of the `Y`-factor of `pairG23`. -/
noncomputable def memY23 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ : Xn n → ℂ)
    (y : E3) : ℝ :=
  ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ, ∫ u in boxLQ ℓ,
    ‖Θ (insertCoord2 p y u x'')‖ ^ 2

/-- The two-slot mass of the state at slots `(p.1, p.2) = (a, b)` (the X-factor of `pairG21`). -/
noncomputable def memX21 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ : Xn n → ℂ)
    (a b : E3) : ℝ :=
  ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
    ‖Θ (insertCoord2 p a b x'')‖ ^ 2

/-- The two-slot mass of the `Y`-factor of `pairG21`. -/
noncomputable def memY21 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ : Xn n → ℂ)
    (y u : E3) : ℝ :=
  ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
    ‖Θ (insertCoord2 p y u x'')‖ ^ 2

/-- The two-slot Dirichlet content at slot `p.2` (the derivative factor of `pairG21`). -/
noncomputable def dirY21 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ : Xn n → ℂ)
    (y u : E3) : ℝ :=
  ∑ j : Fin 3, ∫ x'' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
    ‖fderiv ℝ Θ (insertCoord2 p y u x'') (slotDirVec p.2 j)‖ ^ 2

end Work.BoseBoxFock
