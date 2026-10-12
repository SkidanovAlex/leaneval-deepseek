import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.KinRowQuant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tauDefs` — the vocabulary of the lattice/continuum kinetic comparison

This module fixes the notation shared by the target
`Work.BoseBoxFock.tauLattice_le_tauContinuumChi` and its two exact reductions
(`tauLhs_eq`, `tauRhs_eq`):

* `tauLatPow ℓ j g = Σ_n ℓ⁻³ ‖k_n‖^j ‖kinFT g k_n‖²`,  `k_n = kmomInt ℓ n = (2π/ℓ) n`
  (the *lattice* momentum moments; `j = 0, 1, 2` are the quantities `S0, S1, S2`);
* `tauLatZero ℓ g = ℓ⁻³‖kinFT g 0‖²` (the lattice mass at the zero momentum, `a₀`);
* `tauContPow j g = (2π)⁻³ ∫_p ‖p‖^j ‖kinFT g p‖²` (the *continuum* moments `R0, R1, R2`);
* `tauLowMass c g = (2π)⁻³ ∫_{‖p‖<c} (c−‖p‖)² ‖kinFT g p‖²` (the low-momentum integral
  `I_<(c)` of the target's aliasing analysis).

The two identities that turn the target into the single *aliasing-deficit* inequality
`3 S1 − 2 R1 ≥ c[(5/4+c₀)S0 − (9/4+c₀)a₀] + c⁻¹ I_<(c)` are

`tauLhs_eq` :  the lattice sum with the *smoothed* profile equals
  `S2 − 3c S1 + (9/4+c₀)c²(S0 − a₀)`   (for `c ≤ π/ℓ`), and
`tauRhs_eq` :  the continuum integral with FS's sharp kinetic coefficient `fsKinCoeff c`
  equals `R2 − 2c R1 + c² R0 − I_<(c)`.

The first is exact because for `c ≤ π/ℓ` every *non-zero* lattice momentum has
`‖k_n‖ ≥ 2π/ℓ ≥ 2c`, so the quadratic tail `tauProf r = (r−3/2)² + c₀` of the profile applies
to it (`tauChi_tail`), while the `n = 0` term of the profile is `0`.  The second is the
elementary splitting of `[r−c]₊² = r² − 2cr + c² − (c−r)²1_{r<c}`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The **lattice momentum moment** `S_j = Σ_n ℓ⁻³‖k_n‖^j‖kinFT g k_n‖²`,
`k_n = kmomInt ℓ n`. -/
def tauLatPow (ℓ : ℝ) (j : ℕ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ j
    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- The **lattice mass at the zero momentum** `a₀ = ℓ⁻³‖kinFT g 0‖²`. -/
def tauLatZero (ℓ : ℝ) (g : E3 → ℂ) : ℝ :=
  (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g 0‖ ^ 2

/-- The **continuum momentum moment** `R_j = (2π)⁻³∫_p ‖p‖^j ‖kinFT g p‖²`. -/
def tauContPow (j : ℕ) (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : E3, ‖p‖ ^ j * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- The **low-momentum integral** `I_<(c) = (2π)⁻³∫_{‖p‖<c}(c−‖p‖)²‖kinFT g p‖²`, the mass the
lattice cannot see (every non-zero lattice momentum exceeds the cut-off `c ≤ π/ℓ`). -/
def tauLowMass (c : ℝ) (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p in {p : E3 | ‖p‖ < c}, (c - ‖p‖) ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2

lemma tauLatPow_zero (ℓ : ℝ) (g : E3 → ℂ) :
    tauLatPow ℓ 0 g
      = ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
  unfold tauLatPow
  exact tsum_congr fun n => by rw [pow_zero, mul_one]

/-! ## The two profile facts used by `tauLhs_eq`

`tauProf` is `tauProf`, so the only usable properties are the six
recorded in `exists_tauProf`.  In particular the constant `c₀` of the quadratic tail is *not*
`∫t²tauKer` (that is not available); we extract it with `Classical.choose`. -/

/-- The (opaque) constant `c₀` of the profile: `tauProf r = (r − 3/2)² + c₀` for `r ≥ 2`. -/
noncomputable def tauC0 : ℝ := Classical.choose tauProf_spec.2.2.2.2.2

lemma tauC0_nonneg : 0 ≤ tauC0 :=
  (Classical.choose_spec tauProf_spec.2.2.2.2.2).1

/-- The quadratic tail of the profile, valid for `r ≥ 2`. -/
lemma tauProf_quad {r : ℝ} (hr : 2 ≤ r) : tauProf r = (r - 3 / 2) ^ 2 + tauC0 :=
  (Classical.choose_spec tauProf_spec.2.2.2.2.2).2 r hr

/-- **The exact quadratic tail of the rescaled profile.**  For `r ≥ 2c` the rescaled profile is
*exactly* the quadratic `ρ_c(r) = (r − 3c/2)² + c₀c²`; this is the identity that turns the
target's left-hand side into lattice moments for `c ≤ π/ℓ` (where every non-zero lattice momentum
satisfies `‖k_n‖ ≥ 2π/ℓ ≥ 2c`). -/
theorem tauChi_tail {c r : ℝ} (hc : 0 < c) (hr : 2 * c ≤ r) :
    c ^ 2 * tauProf (r / c) = (r - 3 * c / 2) ^ 2 + tauC0 * c ^ 2 := by
  have h2 : (2 : ℝ) ≤ r / c := by
    rw [le_div_iff₀ hc]; linarith
  rw [tauProf_quad h2]
  field_simp

/-- **The profile defect** `δ_c(r) = r² − 3cr + (9/4+c₀)c² − c²τ̃(r/c)`, the difference between
the quadratic and the smoothed symbol at the momentum `r = ‖p‖`.  By `tauChi_tail` it vanishes
for `r ≥ 2c`; it is the correction produced by the lattice momenta below the smoothing window
`2c` (the only points where the quadratic tail of `tauProf` does **not** apply). -/
noncomputable def tauDelta (c r : ℝ) : ℝ :=
  r ^ 2 - 3 * c * r + (9 / 4 + tauC0) * c ^ 2 - c ^ 2 * tauProf (r / c)

/-- `δ_c(r) = 0` for `r ≥ 2c`. -/
lemma tauDelta_eq_zero_of {c r : ℝ} (hc : 0 < c) (hr : 2 * c ≤ r) : tauDelta c r = 0 := by
  have h := tauChi_tail hc hr
  unfold tauDelta
  rw [h]
  ring

/-- At the zero momentum, `δ_c(0) = (9/4+c₀)c²`: the `a₀`-credit of the reduction. -/
lemma tauDelta_zero {c : ℝ} (hc : 0 < c) : tauDelta c 0 = (9 / 4 + tauC0) * c ^ 2 := by
  have h0 : tauProf (0 / c) = 0 := by
    have h := tauProf_spec.2.2.2.2.1 (0 / c) (by simp)
    simpa only [tauProf] using h
  unfold tauDelta
  rw [h0]
  ring

end Work.BoseBoxFock
