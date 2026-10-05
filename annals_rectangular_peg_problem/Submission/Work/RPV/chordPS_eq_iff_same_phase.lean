import Mathlib
import Submission.Work.RPV.Defs

/-!
# `chordPS` is injective up to the data of the phase point

`chordPS z w a` records, for the chord `(z,w)` of `ℂ²` with chosen phase `a`,
* `u = e^{-ia}(z+w)/√2` (split into `q₁ = Im u`, `p₁ = Re u`),
* the angle `q₂ = a`,
* `p₂ = (‖z‖² + ‖w‖²)/2 - 1`.

Since `e^{-ia} ≠ 0`, the pair `(q₁,p₁)` determines `z + w`; and because
`‖z‖² + ‖w‖² = (‖z+w‖² + ‖z-w‖²)/2` (parallelogram law, written with the
individual norms), the value of `p₂` determines `‖z - w‖` once `z + w` is known.
Hence two chords give the same point of `PS` (at the same phase `a`) exactly
when they have the same midpoint and the same length:

`chordPS z w a = chordPS z' w' a ↔ z + w = z' + w' ∧ ‖z - w‖ = ‖z' - w'‖`.

The forward direction uses the parallelogram law `parallelogram_law_with_norm`
to convert `‖z‖² + ‖w‖² = ‖z'‖² + ‖w'‖²` (with `z+w = z'+w'`) into
`‖z-w‖ = ‖z'-w'‖`; the backward direction is the same computation read
backwards.
-/

namespace Work.RPV

theorem chordPS_eq_iff_same_phase {z w z' w' : ℂ} {a : ℝ} :
    Work.RPV.chordPS z w a = Work.RPV.chordPS z' w' a ↔
      z + w = z' + w' ∧ ‖z - w‖ = ‖z' - w'‖ := by
  constructor
  · intro h
    -- Reading off the two real coordinates of `u = e^{-ia}(z+w)/√2` from the
    -- first pair of the `PS`-point identifies `u` and hence `z + w`.
    have hre : (Complex.exp (-(a : ℂ) * Complex.I) * ((z + w) / (Real.sqrt 2 : ℂ))).re =
               (Complex.exp (-(a : ℂ) * Complex.I) * ((z' + w') / (Real.sqrt 2 : ℂ))).re := by
      have := congrArg (fun x : PS => x.2.1) h
      simpa only [chordPS] using this
    have him : (Complex.exp (-(a : ℂ) * Complex.I) * ((z + w) / (Real.sqrt 2 : ℂ))).im =
               (Complex.exp (-(a : ℂ) * Complex.I) * ((z' + w') / (Real.sqrt 2 : ℂ))).im := by
      have := congrArg (fun x : PS => x.1.1) h
      simpa only [chordPS] using this
    have hu : Complex.exp (-(a : ℂ) * Complex.I) * ((z + w) / (Real.sqrt 2 : ℂ)) =
              Complex.exp (-(a : ℂ) * Complex.I) * ((z' + w') / (Real.sqrt 2 : ℂ)) :=
      Complex.ext hre him
    have h1 : (z + w) / (Real.sqrt 2 : ℂ) = (z' + w') / (Real.sqrt 2 : ℂ) :=
      mul_left_cancel₀ (Complex.exp_ne_zero _) hu
    have hsne : (Real.sqrt 2 : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact (Real.sqrt_ne_zero').mpr (by norm_num)
    have hsum : z + w = z' + w' := mul_right_cancel₀ (inv_ne_zero hsne) h1
    -- The final coordinate gives `‖z‖² + ‖w‖² = ‖z'‖² + ‖w'‖²`.
    have hp : (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 - 1 = (‖z'‖ ^ 2 + ‖w'‖ ^ 2) / 2 - 1 := by
      have := congrArg (fun x : PS => x.2.2) h
      simpa only [chordPS] using this
    have hn : ‖z‖ ^ 2 + ‖w‖ ^ 2 = ‖z'‖ ^ 2 + ‖w'‖ ^ 2 := by linarith
    refine ⟨hsum, ?_⟩
    -- Parallelogram law: `‖z+w‖² + ‖z-w‖² = 2(‖z‖² + ‖w‖²)`.
    have hpar := parallelogram_law_with_norm ℂ z w
    have hpar' := parallelogram_law_with_norm ℂ z' w'
    have hsumnorm : ‖z + w‖ = ‖z' + w'‖ := by rw [hsum]
    have hsq : ‖z - w‖ ^ 2 = ‖z' - w'‖ ^ 2 := by
      rw [hsumnorm] at hpar
      linarith
    exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp (by
      simpa only [pow_two] using hsq)
  · rintro ⟨hsum, hnorm⟩
    have hu : Complex.exp (-(a : ℂ) * Complex.I) * ((z + w) / (Real.sqrt 2 : ℂ)) =
              Complex.exp (-(a : ℂ) * Complex.I) * ((z' + w') / (Real.sqrt 2 : ℂ)) := by
      rw [hsum]
    have hp : (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 - 1 = (‖z'‖ ^ 2 + ‖w'‖ ^ 2) / 2 - 1 := by
      have hpar := parallelogram_law_with_norm ℂ z w
      have hpar' := parallelogram_law_with_norm ℂ z' w'
      rw [hsum, hnorm] at hpar
      linarith
    simp only [chordPS]
    rw [hu, hp]

end Work.RPV
