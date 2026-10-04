import Mathlib
import Submission.Work.Diff.Alg.Q2PR.unit_sqrt
import Submission.Work.Diff.Alg.Q2PR.quad_root_real
import Submission.Work.Diff.Alg.Q2PR.nondegen_key

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Q2PR

/-- For any `p q r : ℂ` the Hermitian-type quadratic expression
`-p α β̄ + q (α ᾱ - β β̄) + r β ᾱ` has a nonzero zero.

Proof: set `α = 1` and look for `β = t` with `r t - p t̄ - q (t t̄ - 1) = 0`.

* If `q = 0` then `β = 0` works.
* If `‖p‖ = ‖r‖`, then (unless `p = r = 0`, where `α = β = 1` works) `p/r` is a unit
  complex number; choosing a unit square root `t` of it (`t² = p/r`, `t t̄ = 1`) makes the
  `q`-term vanish and `r t = p t̄`.
* If `‖p‖ ≠ ‖r‖` the ℝ-linear map `t ↦ r t - p t̄` is invertible: writing
  `A = (r̄ q + p q̄)/(‖r‖² - ‖p‖²)` one has `r A - p Ā = q`, and taking `t = A s` where the real
  `s` solves `‖A‖² s² - s - 1 = 0` gives `t t̄ - 1 = s`, whence `r t - p t̄ = q (t t̄ - 1)`. -/
theorem root_quad (p q r : ℂ) : ∃ α β : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧
    -p * α * star β + q * (α * star α - β * star β) + r * β * star α = 0 := by
  by_cases hq : q = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hq]⟩
  · by_cases hpr : ‖p‖ = ‖r‖
    · by_cases hp : p = 0
      · have hr : r = 0 := by
          have h : ‖r‖ = 0 := by rw [← hpr, hp]; simp
          simpa using norm_eq_zero.mp h
        refine ⟨1, 1, Or.inl one_ne_zero, ?_⟩
        simp [hp, hr]
      · have hr : r ≠ 0 := by
          intro hr0
          apply hp
          have h : ‖p‖ = 0 := by rw [hpr, hr0]; simp
          simpa using norm_eq_zero.mp h
        have hω : ‖p / r‖ = 1 := by
          rw [norm_div, hpr]
          exact div_self (norm_ne_zero_iff.mpr hr)
        obtain ⟨t, ht2, ht1⟩ := unit_sqrt (p / r) hω
        refine ⟨1, t, Or.inl one_ne_zero, ?_⟩
        have hp_eq : p = (p / r) * r := (div_mul_cancel₀ p hr).symm
        have hpt : p * star t = r * t := by
          rw [hp_eq, ← ht2]
          calc t ^ 2 * r * star t = r * (t * star t) * t := by ring
            _ = r * 1 * t := by rw [ht1]
            _ = r * t := by ring
        simp only [star_one, mul_one, ht1, sub_self, mul_zero, add_zero]
        rw [neg_mul, hpt]
        ring
    · set A : ℂ := (star r * q + p * star q) / ((‖r‖^2 - ‖p‖^2 : ℝ) : ℂ) with hA
      have hAkey : r * A - p * star A = q := by rw [hA]; exact nondegen_key p q r hpr
      have hA_ne : A ≠ 0 := by
        intro h0
        apply hq
        have h : (0:ℂ) = q := by
          have := hAkey
          rw [h0] at this
          simpa using this
        exact h.symm
      set c : ℝ := Complex.normSq A with hc
      have hcpos : 0 < c := by rw [hc]; exact Complex.normSq_pos.mpr hA_ne
      obtain ⟨s, hs⟩ := quad_root_real c hcpos
      set t : ℂ := A * (s:ℂ) with ht
      have hstar_s : star (s:ℂ) = (s:ℂ) := Complex.conj_ofReal s
      have ht_ts : t * star t = ((s + 1 : ℝ) : ℂ) := by
        have hnt : Complex.normSq t = s + 1 := by
          have h1 : Complex.normSq t = Complex.normSq A * s^2 := by
            rw [ht, Complex.normSq_mul, Complex.normSq_ofReal]; ring
          rw [h1, ← hc]
          linarith [hs]
        have h2 : t * star t = (Complex.normSq t : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj]
        rw [h2, hnt]
      have hst : star t = star A * (s:ℂ) := by rw [ht, star_mul, hstar_s, mul_comm]
      have hmain : r * t - p * star t = q * (s:ℂ) := by
        rw [hst, ht]
        have : r * (A * (s:ℂ)) - p * (star A * (s:ℂ)) = (r * A - p * star A) * (s:ℂ) := by ring
        rw [this, hAkey]
      refine ⟨1, t, Or.inl one_ne_zero, ?_⟩
      simp only [star_one, mul_one]
      have hgoal : -p * star t + q * (1 - t * star t) + r * t
          = (r * t - p * star t) + q * (1 - t * star t) := by ring
      rw [hgoal, hmain, ht_ts]
      have h3 : (1:ℂ) - ((s + 1 : ℝ) : ℂ) = -(s:ℂ) := by push_cast; ring
      rw [h3]
      ring

end Work.Diff.Alg.Q2PR
