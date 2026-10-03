import Mathlib
import Submission.Work.FIArea7.exists_squareWave_fourier

namespace Work.FIArea7

/-- **FI (20.16)–(20.19) in separated form.**  There is an absolute constant `C` such that for
every `R ≥ 2` there are Fourier coefficients `ĉ : ℤ → ℂ` of `ℓ¹`-norm at most `C log 2R` (supplied
by `Work.FIArea7.exists_squareWave_fourier`, the expansion of the smoothed square wave
`t(α) = sign(cos α)`) such that for all non-zero `w z : ℂ` with `|Re(wz)| ≥ ‖w‖‖z‖/R` (the "room"
of *FI* (20.18): `wz` stays `1/R` away from the imaginary axis)

  `sign(Re(wz)) = Σ_k ĉ_k (w/‖w‖)^k (z/‖z‖)^k`,

in the `HasSum` sense.  The point is the *separation*: the `k`-th summand is a product of a
function of `w` alone with a function of `z` alone, which is what §§20, 22–23 need in order to put
the multiplier sign `ε(w,z)` into bilinear forms. -/
theorem sign_re_separation :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R → ∃ ĉ : ℤ → ℂ,
      (∀ s : Finset ℤ, ∑ k ∈ s, ‖ĉ k‖ ≤ C * Real.log (2 * (R : ℝ))) ∧
      ∀ (w z : ℂ), w ≠ 0 → z ≠ 0 → ‖w‖ * ‖z‖ ≤ (R : ℝ) * |(w * z).re| →
        HasSum (fun k : ℤ => ĉ k * ((w / (‖w‖ : ℂ)) ^ k * (z / (‖z‖ : ℂ)) ^ k))
          (if 0 < (w * z).re then (1 : ℂ) else -1) := by
  obtain ⟨C, hC0, hC⟩ := exists_squareWave_fourier
  refine ⟨C, hC0, fun R hR => ?_⟩
  obtain ⟨ĉ, hcoeff, hsum⟩ := hC R hR
  refine ⟨ĉ, hcoeff, ?_⟩
  intro w z hw hz hroom
  -- the unit modulus point at which we evaluate the (single-variable) square-wave expansion
  have ha : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hb : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hden : (0 : ℝ) < ‖w‖ * ‖z‖ := mul_pos ha hb
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  set u : ℂ := (w / (‖w‖ : ℂ)) * (z / (‖z‖ : ℂ)) with hu
  -- the separated summands are the powers of the single point `u`
  have hu_eq : u = (w * z) / ((‖w‖ * ‖z‖ : ℝ) : ℂ) := by
    rw [hu]; push_cast; field_simp
  -- `u` lies on the unit circle
  have hunorm : ‖u‖ = 1 := by
    rw [hu_eq, norm_div]
    have h1 : ‖(((‖w‖ * ‖z‖ : ℝ)) : ℂ)‖ = ‖w‖ * ‖z‖ := by
      rw [show ‖(((‖w‖ * ‖z‖ : ℝ)) : ℂ)‖ = |‖w‖ * ‖z‖| by simp,
        abs_of_nonneg hden.le]
    rw [h1, norm_mul, div_self (ne_of_gt hden)]
  -- and the real part is the real part of `w * z` normalised by `‖w‖‖z‖`
  have hure : u.re = (w * z).re / (‖w‖ * ‖z‖) := by
    rw [hu_eq, Complex.div_ofReal_re]
  -- the room hypothesis gives the `1 / R` separation for `u`
  have hrele : (1 : ℝ) / (R : ℝ) ≤ |u.re| := by
    rw [hure, abs_div, abs_of_pos hden, le_div_iff₀ hden]
    have hh : (1 : ℝ) / (R : ℝ) * (‖w‖ * ‖z‖) = (‖w‖ * ‖z‖) / (R : ℝ) := by ring
    rw [hh, div_le_iff₀ hR0]
    linarith [hroom]
  -- the sign of the value is the sign of `Re (w * z)`
  have hsign : 0 < u.re ↔ 0 < (w * z).re := by
    rw [hure, div_pos_iff]
    constructor
    · rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
      · exact h1
      · linarith
    · intro h1; exact Or.inl ⟨h1, hden⟩
  have hval : (if 0 < u.re then (1 : ℂ) else -1)
      = (if 0 < (w * z).re then (1 : ℂ) else -1) := by
    by_cases h : 0 < u.re
    · rw [if_pos h, if_pos (hsign.mp h)]
    · rw [if_neg h, if_neg (fun hh => h (hsign.mpr hh))]
  have hmain : HasSum
      (fun k : ℤ => ĉ k * ((w / (‖w‖ : ℂ)) ^ k * (z / (‖z‖ : ℂ)) ^ k))
      (if 0 < u.re then (1 : ℂ) else -1) := by
    apply HasSum.congr_fun (hsum u hunorm hrele)
    intro k
    rw [hu, mul_zpow]
  rw [← hval]
  exact hmain

end Work.FIArea7
