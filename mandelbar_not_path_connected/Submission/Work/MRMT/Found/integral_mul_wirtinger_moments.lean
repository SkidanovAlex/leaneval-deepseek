import Mathlib
import Submission.Work.MRMT.Sobolev.dzbar_mul
import Submission.Work.MRMT.Sobolev.integral_dzbar_eq_zero_of_contDiff
import Submission.Work.MRMT.QC.WirtingerCalc
import Submission.Work.MRMT.Beltrami.energy_identity
import Submission.Work.MRMT.Beltrami.integral_mul_dz_eq_neg
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The four Wirtinger "moments" of a compactly supported `C¹` function

Let `h : ℂ → ℂ` be of class `C¹` (real differentiability with continuous Fréchet derivative)
and compactly supported.  Integrating the two Wirtinger derivatives `∂h` and `∂̄h`
(`Work.MRMT.dz`, `Work.MRMT.dzbar`) against the two coordinate functions `z` and `z̄`
gives the four `L¹` identities

  `∫ z ∂̄h = 0`,   `∫ z̄ ∂̄h = -∫ h`,   `∫ z ∂h = -∫ h`,   `∫ z̄ ∂h = 0`.

These are the boundary terms of Cauchy's theorem: they assert that, in the distributional
sense, `∂̄ (1/z) = π δ₀` (`∫ (1/z̄) ∂̄φ = -π φ 0` after the substitution `z̄`), i.e. that the
Cauchy kernel has distributional `∂̄` equal to a multiple of the Dirac mass, and dually
`∂(1/z)` is the same mass.  Equivalently they say that the "second derivatives" of the
distributions `1/z` and `1/z̄` are zero away from the origin.

They are the analytic input for the classical representation
`h(z) = -(1/π) ∫ (∂̄h)(w) / (z - w) dm(w)`
(and its `∂̄`-analogue), which is the starting point of the Ahlfors–Bers / Cauchy-transform
machinery used in the Mandelbar project.

## Proof

Every identity is an instance of integration by parts for the Fréchet derivative in the two
real directions `1` and `i`:

* `Work.MRMT.QC.integral_mul_dzbar_eq_neg : ∫ f ∂̄g = -∫ (∂̄f) g`  (`f, g ∈ C¹`, `g` compactly
  supported), the `∂̄` case;
* `Work.MRMT.Beltrami.integral_mul_dz_eq_neg : ∫ f ∂g = -∫ (∂f) g`, the `∂` case.

Taking `f = id` gives the moments against `z`, and `f = conj` (`starRingEnd ℂ`) the moments
against `z̄`; the two `f`-derivatives are then the constants

  `∂ id = 1`,  `∂̄ id = 0`,  `∂ conj = 0`,  `∂̄ conj = 1`,

which is exactly the asserted pattern of values.
-/

namespace Work.MRMT.Found

open MeasureTheory Complex Function

/-- `∂̄` of complex conjugation: conjugation is anti-holomorphic, so `∂̄ (starRingEnd ℂ) = 1`.
Stated for the `RingHom`-coercion `starRingEnd ℂ` (the form in which the ambient
statements use conjugation). -/
lemma dzbar_starRingEnd (u : ℂ) : Work.MRMT.dzbar (starRingEnd ℂ) u = 1 :=
  Work.MRMT.Wirtinger.dzbar_star u

/-- `∂` of complex conjugation: conjugation is anti-holomorphic, so `∂ (starRingEnd ℂ) = 0`. -/
lemma dz_starRingEnd (u : ℂ) : Work.MRMT.dz (starRingEnd ℂ) u = 0 :=
  Work.MRMT.Wirtinger.dz_star u

/-- Complex conjugation is of class `C¹` as a real map of `ℂ` (it is `ℝ`-linear). -/
lemma contDiff_starRingEnd : ContDiff ℝ 1 (starRingEnd ℂ) :=
  Complex.conjCLE.contDiff

theorem integral_mul_wirtinger_moments {h : ℂ → ℂ} (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    (∫ u, u * Work.MRMT.dzbar h u = 0) ∧
    (∫ u, (starRingEnd ℂ) u * Work.MRMT.dzbar h u = -∫ u, h u) ∧
    (∫ u, u * Work.MRMT.dz h u = -∫ u, h u) ∧
    (∫ u, (starRingEnd ℂ) u * Work.MRMT.dz h u = 0) := by
  have hcid : ContDiff ℝ 1 (id : ℂ → ℂ) := contDiff_id
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `∫ z ∂̄h = -∫ (∂̄id) h = 0`, since `∂̄id = 0`.
    have key := Work.MRMT.QC.integral_mul_dzbar_eq_neg (f := (id : ℂ → ℂ)) (g := h)
      hcid hh hs
    calc ∫ u, u * Work.MRMT.dzbar h u
        = ∫ u, (id : ℂ → ℂ) u * Work.MRMT.dzbar h u := rfl
      _ = -∫ u, Work.MRMT.dzbar (id : ℂ → ℂ) u * h u := key
      _ = 0 := by simp
  · -- `∫ z̄ ∂̄h = -∫ (∂̄conj) h = -∫ h`, since `∂̄conj = 1`.
    have key := Work.MRMT.QC.integral_mul_dzbar_eq_neg (f := (starRingEnd ℂ : ℂ → ℂ)) (g := h)
      contDiff_starRingEnd hh hs
    rw [key]
    simp [dzbar_starRingEnd]
  · -- `∫ z ∂h = -∫ (∂id) h = -∫ h`, since `∂id = 1`.
    have key := Work.MRMT.Beltrami.integral_mul_dz_eq_neg (f := (id : ℂ → ℂ)) (g := h)
      hcid hh hs
    calc ∫ u, u * Work.MRMT.dz h u
        = ∫ u, (id : ℂ → ℂ) u * Work.MRMT.dz h u := rfl
      _ = -∫ u, Work.MRMT.dz (id : ℂ → ℂ) u * h u := key
      _ = -∫ u, h u := by simp
  · -- `∫ z̄ ∂h = -∫ (∂conj) h = 0`, since `∂conj = 0`.
    have key := Work.MRMT.Beltrami.integral_mul_dz_eq_neg (f := (starRingEnd ℂ : ℂ → ℂ)) (g := h)
      contDiff_starRingEnd hh hs
    rw [key]
    simp [dz_starRingEnd]

end Work.MRMT.Found
