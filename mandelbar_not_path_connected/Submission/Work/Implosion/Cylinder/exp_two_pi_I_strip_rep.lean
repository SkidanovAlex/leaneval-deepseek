/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The Écalle cylinder: representatives of `u ↦ exp (2πi u)` in the unit strip

The Écalle coordinate `u` of `Ecalle.lean` is only defined up to the action of
the period lattice: the projection

  `u  ↦  exp (2πi u)`

is invariant under `u ↦ u + 1`, because `exp (2πi) = 1`.  Consequently the
*Écalle cylinder* is the quotient of `ℂ` by the additive group `ℤ ⊂ ℂ`, and the
standard fundamental domain is the vertical strip

  `{u : ℂ | 0 ≤ Re u ∧ Re u < 1}`.

This file records the elementary covering-set fact that makes the cylinder
useful: every nonzero complex number has **exactly one** representative in that
strip, i.e. `u ↦ exp (2πi u)` restricts to a bijection `strip → ℂ \ {0}`.

This is used downstream whenever a point of the cylinder has to be lifted to a
concrete value of the Écalle coordinate.
-/
import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Cylinder

open Complex

/-! ## The kernel of the cylinder projection -/

/-- The kernel of the projection `u ↦ exp (2πi u)` is exactly `ℤ ⊂ ℂ`:
`exp (2πi u) = 1` holds if and only if `u` is an integer (viewed in `ℂ`). -/
theorem exp_two_pi_I_eq_one_iff (u : ℂ) :
    Complex.exp (2 * Real.pi * I * u) = 1 ↔ ∃ n : ℤ, u = n := by
  rw [show (2 * (Real.pi : ℂ) * I * u) = (2 * Real.pi * I) * u by ring,
    Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, mul_left_cancel₀ Complex.two_pi_I_ne_zero (by rw [hn, mul_comm])⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

/-! ## Existence of a strip representative -/

/-- Every nonzero complex number is `exp (2πi u)` for some `u` with
`0 ≤ Re u < 1`.  The construction uses `Complex.range_exp` to write `z = exp s`
and then shifts the preimage `s / (2πi)` of `s` by the integer `-⌊Re (s/(2πi))⌋`,
which moves its real part into `[0,1)` and does not change `exp (2πi ·)`. -/
theorem exists_exp_two_pi_I_strip (z : ℂ) (hz : z ≠ 0) :
    ∃ u : ℂ, 0 ≤ u.re ∧ u.re < 1 ∧ Complex.exp (2 * Real.pi * I * u) = z := by
  have hzr : z ∈ Set.range Complex.exp := by rw [Complex.range_exp]; simpa using hz
  obtain ⟨s, rfl⟩ := hzr
  set w : ℂ := -I * s / (2 * (Real.pi : ℂ)) with hw
  refine ⟨w - (⌊w.re⌋ : ℂ), ?_, ?_, ?_⟩
  · rw [Complex.sub_re]
    have hc : ((⌊w.re⌋ : ℤ) : ℂ).re = ((⌊w.re⌋ : ℤ) : ℝ) := by simp
    rw [hc]
    have := Int.floor_le w.re
    linarith
  · rw [Complex.sub_re]
    have hc : ((⌊w.re⌋ : ℤ) : ℂ).re = ((⌊w.re⌋ : ℤ) : ℝ) := by simp
    rw [hc]
    have := Int.lt_floor_add_one w.re
    linarith
  · have hw2 : 2 * (Real.pi : ℂ) * I * w = s := by
      rw [hw]; field_simp; rw [Complex.I_sq]; ring
    rw [show 2 * (Real.pi : ℂ) * I * (w - (⌊w.re⌋ : ℂ))
          = 2 * (Real.pi : ℂ) * I * w + (-(⌊w.re⌋)) * (2 * (Real.pi : ℂ) * I) by ring]
    have hone : Complex.exp ((-(⌊w.re⌋)) * (2 * (Real.pi : ℂ) * I)) = 1 :=
      Complex.exp_eq_one_iff.mpr ⟨-(⌊w.re⌋), by simp⟩
    rw [Complex.exp_add, hw2, hone, mul_one]

/-! ## Uniqueness of the strip representative -/

/-- Two points of the strip `{u : ℂ | 0 ≤ Re u ∧ Re u < 1}` with the same image
under `u ↦ exp (2πi u)` are equal.  Indeed their difference is an integer (kernel
computation), but it also has absolute value `< 1`. -/
theorem exp_two_pi_I_strip_inj (u v : ℂ)
    (hu : 0 ≤ u.re) (hu1 : u.re < 1) (hv : 0 ≤ v.re) (hv1 : v.re < 1)
    (h : Complex.exp (2 * Real.pi * I * u) = Complex.exp (2 * Real.pi * I * v)) :
    u = v := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hsub : u - v = (n : ℂ) := by
    have h2 : (2 * (Real.pi : ℂ) * I) * (u - v) = (2 * (Real.pi : ℂ) * I) * (n : ℂ) := by
      rw [mul_sub, hn]; ring
    exact mul_left_cancel₀ Complex.two_pi_I_ne_zero h2
  have hre : u.re - v.re = (n : ℝ) := by
    have := congrArg Complex.re hsub
    simpa using this
  have hn1 : (n : ℝ) < 1 := by linarith
  have hn2 : (-1 : ℝ) < (n : ℝ) := by linarith
  have hnz : n = 0 := by
    have h1 : n < 1 := by exact_mod_cast hn1
    have h2 : -1 < n := by exact_mod_cast hn2
    omega
  exact sub_eq_zero.mp (by rw [hsub, hnz]; simp)

/-! ## The main statement -/

/-- **Unique strip representative.**  Every nonzero complex number `z` is the
image under `u ↦ exp (2πi u)` of exactly one `u` in the fundamental strip
`{u : ℂ | 0 ≤ Re u ∧ Re u < 1}` of the Écalle cylinder. -/
theorem exp_two_pi_I_strip_rep (z : ℂ) (hz : z ≠ 0) :
    ∃! u : ℂ, 0 ≤ u.re ∧ u.re < 1 ∧ Complex.exp (2 * Real.pi * I * u) = z := by
  obtain ⟨u, hu, hu1, hue⟩ := exists_exp_two_pi_I_strip z hz
  refine ⟨u, ⟨hu, hu1, hue⟩, ?_⟩
  intro v hv
  exact exp_two_pi_I_strip_inj v u hv.1 hv.2.1 hu hu1 (by rw [hv.2.2, hue])

end Work.Implosion.Cylinder
