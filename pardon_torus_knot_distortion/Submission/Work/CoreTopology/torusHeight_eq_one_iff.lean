import Mathlib
import Submission.Work.CoreTopology.TorusDichotomyDefs
import Submission.Work.CoreTopology.horizVec_ne_zero_of_disc

/-!
# The level set `{1}` of the height function is the standard torus

For `P = (x, y, z) ∈ ℝ³` with `r = √(x² + y²)` the height function is

  `torusHeight P = (r - 2)² + z²`,

so that `{torusHeight = 1}` is the torus of revolution with major radius `2` and minor
radius `1`.  Here we identify this level set with the image of the standard parametrisation
`torusMap`, i.e. with the carrier `standard.carrier` of the standard parametrised torus.

The easy inclusion (`torusHeight = 1` on the image of `torusMap`, hence on `standard.carrier`)
is already available as `torusHeight_eq_one_of_mem_carrier`.  The content of the present file is
the converse: every point of height `1` is of the form

  `P = ((2 + cos φ) cos θ, (2 + cos φ) sin θ, sin φ)`,

with

  `cos φ = r - 2`,  `sin φ = z`,  `cos θ = x / r`,  `sin θ = y / r`.

The two triples `(r - 2, z)` and `(x / r, y / r)` are points of the unit circle of `ℂ` — this is
exactly the equation `torusHeight P = 1` and the identity `r² = x² + y²` — so they are
`(cos t, sin t)` for suitable `t`, which is the elementary trigonometric input
`exists_cos_sin_of_normSq_eq_one`.

As a corollary we obtain the polynomial description of the torus used elsewhere in the
development: `P ∈ standard.carrier ↔ (x² + y² + z² + 3)² = 16 (x² + y²)`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- **Trigonometry of the unit circle.**  Every complex number `z` with `normSq z = 1` is
`(cos t, sin t)` for some real `t`. -/
lemma exists_cos_sin_of_normSq_eq_one (z : ℂ) (h : Complex.normSq z = 1) :
    ∃ t : ℝ, Real.cos t = z.re ∧ Real.sin t = z.im := by
  have hnorm : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by rw [Complex.sq_norm, h]
    rcases sq_eq_one_iff.mp h2 with h1 | h1
    · exact h1
    · exfalso
      have := norm_nonneg z
      linarith
  obtain ⟨t, ht⟩ := (Complex.norm_eq_one_iff z).mp hnorm
  exact ⟨t, by rw [← Complex.exp_ofReal_mul_I_re t, ht],
    by rw [← Complex.exp_ofReal_mul_I_im t, ht]⟩

/-- **The level set `{1}` of the height function is exactly the standard torus.**  For a point
`P = (x, y, z)` of `ℝ³` with `r = √(x² + y²)` (so that `torusHeight P = (r - 2)² + z²`), we have
`torusHeight P = 1` if and only if `P` lies on the standard torus of revolution of major radius
`2` and minor radius `1`, whose equation is `(x² + y² + z² + 3)² = 16 (x² + y²)`. -/
theorem torusHeight_eq_one_iff (P : LeanEval.KnotTheory.PardonDistortion.R3) :
    Work.CoreTopology.torusHeight P = 1 ↔ P ∈ Work.CoreTopology.standard.carrier := by
  refine ⟨?_, torusHeight_eq_one_of_mem_carrier⟩
  intro h
  rw [standard_carrier, Set.mem_range]
  have hsq : horizRadius P ^ 2 = P 0 ^ 2 + P 1 ^ 2 := by rw [horizRadius_sq, horizRadiusSq]
  have hh : (horizRadius P - 2) ^ 2 + P 2 ^ 2 = 1 := by
    rw [← torusHeight_apply]
    exact h
  -- `r = 1` would already force `z = 0`; in particular `r ≠ 0`, so the divisions below make sense.
  have hr1 : 1 ≤ horizRadius P := by nlinarith [sq_nonneg (horizRadius P - 2)]
  have hrne : horizRadius P ≠ 0 := by linarith
  -- the meridian angle: `(r - 2, z)` lies on the unit circle
  obtain ⟨φ, hφc, hφs⟩ := exists_cos_sin_of_normSq_eq_one (⟨horizRadius P - 2, P 2⟩ : ℂ) (by
    rw [Complex.normSq_apply]
    simp
    nlinarith [hh])
  -- the longitude angle: `(x / r, y / r)` lies on the unit circle
  obtain ⟨θ, hθc, hθs⟩ := exists_cos_sin_of_normSq_eq_one
    (⟨P 0 / horizRadius P, P 1 / horizRadius P⟩ : ℂ) (by
    rw [Complex.normSq_apply]
    simp
    field_simp
    nlinarith [hsq])
  have hφc' : Real.cos φ = horizRadius P - 2 := hφc
  have hφs' : Real.sin φ = P 2 := hφs
  have hθc' : Real.cos θ = P 0 / horizRadius P := hθc
  have hθs' : Real.sin θ = P 1 / horizRadius P := hθs
  refine ⟨(θ, φ), ?_⟩
  ext i
  fin_cases i
  · show (2 + Real.cos φ) * Real.cos θ = P 0
    rw [hφc', hθc']
    field_simp
    ring
  · show (2 + Real.cos φ) * Real.sin θ = P 1
    rw [hφc', hθs']
    field_simp
    ring
  · show Real.sin φ = P 2
    rw [hφs']

/-- **Polynomial form of the standard torus.**  A point `P = (x, y, z)` of `ℝ³` lies on the
standard torus of revolution (major radius `2`, minor radius `1`) if and only if
`(x² + y² + z² + 3)² = 16 (x² + y²)`.  Indeed, with `r² = x² + y²`, the equation
`torusHeight P = 1` is `r² - 4r + 4 + z² = 1`, i.e. `r² + z² + 3 = 4r`, whose square is the
polynomial equation (and conversely, since `r² + z² + 3 ≥ 3 > 0`). -/
theorem standard_carrier_iff_polynomial (P : R3) :
    P ∈ standard.carrier ↔ (P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + 3) ^ 2 = 16 * (P 0 ^ 2 + P 1 ^ 2) := by
  rw [← torusHeight_eq_one_iff]
  have hsq : horizRadius P ^ 2 = P 0 ^ 2 + P 1 ^ 2 := by rw [horizRadius_sq, horizRadiusSq]
  constructor
  · intro h
    have hh : (horizRadius P - 2) ^ 2 + P 2 ^ 2 = 1 := by
      rw [← torusHeight_apply]
      exact h
    rw [← hsq]
    nlinarith [hh]
  · intro h
    rw [torusHeight_apply]
    rw [← hsq] at h
    nlinarith [h, sq_nonneg (horizRadius P), sq_nonneg (P 2), horizRadius_nonneg P]

end

end Work.CoreTopology
