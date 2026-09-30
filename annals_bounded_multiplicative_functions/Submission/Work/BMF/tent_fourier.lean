import Mathlib
import Submission.Work.BMF.tent_fourier_defs
import Submission.Work.BMF.bernoulli_eZ_sum
import Submission.Work.BMF.tentCoeff_eq
import Submission.Work.BMF.tent_secondDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Fourier series of the tent function

For `0 < B ≤ 1/2` the tent (hat) function
`tent B x = max (1 - nint x / B) 0` (where `nint` is the distance to the nearest integer)
equals its Fourier series
`tent B x = ∑_{r ∈ ℤ} tentCoeff B r · e(r x)`,
with the (non-negative) Fourier coefficients
`tentCoeff B r = sin²(π r B)/(π² r² B)` (and `tentCoeff B 0 = B`).

The proof writes both factors in terms of the additive character `eZ` and reduces to the
Fourier series of the second Bernoulli polynomial:
`∑_{n ∈ ℤ} e(n t)/n² = 2π² ({t}² - {t} + 1/6)` (`bernoulli_eZ_sum`), multiplied out with the
`r = 0` term treated separately.  The resulting value is identified with `tent B x` through the
finite-difference identity `tent_secondDiff`.
-/

namespace Work.BMF

/-- The `t`-th "character sum" summand `e(r t)/r²`, kept as a named function so that the
Bernoulli Fourier series can be applied at the three arguments `x`, `x + B`, `x - B`. -/
noncomputable def Tp (t : ℝ) (r : ℤ) : ℂ := (1 : ℂ) / (r : ℂ) ^ 2 * eZ ((r : ℝ) * t)

theorem tent_fourier (B x : ℝ) (hB : 0 < B) (hB2 : B ≤ 1 / 2) :
    HasSum (fun r : ℤ => (tentCoeff B r : ℂ) * eZ ((r : ℝ) * x)) (tent B x : ℂ) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  set Kc : ℂ := ((1 / (4 * Real.pi ^ 2 * B) : ℝ) : ℂ) with hKc
  -- the three Bernoulli Fourier series
  have h1 : HasSum (Tp x) (2 * Real.pi ^ 2 * phiC x) := bernoulli_eZ_sum x
  have h2 : HasSum (Tp (x + B)) (2 * Real.pi ^ 2 * phiC (x + B)) := bernoulli_eZ_sum (x + B)
  have h3 : HasSum (Tp (x - B)) (2 * Real.pi ^ 2 * phiC (x - B)) := bernoulli_eZ_sum (x - B)
  -- their linear combination
  have hA : HasSum (fun r : ℤ => Kc * (2 * Tp x r - Tp (x + B) r - Tp (x - B) r))
      (Kc * (2 * (2 * Real.pi ^ 2 * phiC x) - 2 * Real.pi ^ 2 * phiC (x + B)
        - 2 * Real.pi ^ 2 * phiC (x - B))) := by
    have h := ((h1.mul_left (2 : ℂ)).sub h2).sub h3
    exact h.mul_left Kc
  -- the summands agree, up to the `r = 0` term
  have hpt : ∀ r : ℤ, (tentCoeff B r : ℂ) * eZ ((r : ℝ) * x)
      = Kc * (2 * Tp x r - Tp (x + B) r - Tp (x - B) r)
        + (if r = 0 then (B : ℂ) else 0) := by
    intro r
    by_cases hr : r = 0
    · subst hr
      simp only [tentCoeff, Tp]
      norm_num
    · have hkey : Kc * (1 / (r : ℂ) ^ 2)
          = 1 / ((4 * Real.pi ^ 2 * (r : ℝ) ^ 2 * B : ℝ) : ℂ) := by
        rw [hKc]
        push_cast
        field_simp
      have hmain : Kc * (2 * Tp x r - Tp (x + B) r - Tp (x - B) r)
          = (2 - eZ ((r : ℝ) * B) - eZ (-((r : ℝ) * B)))
              / ((4 * Real.pi ^ 2 * (r : ℝ) ^ 2 * B : ℝ) : ℂ) * eZ ((r : ℝ) * x) := by
        simp only [Tp]
        rw [show (r : ℝ) * (x + B) = (r : ℝ) * x + (r : ℝ) * B by ring, eZ_add,
            show (r : ℝ) * (x - B) = (r : ℝ) * x + (-((r : ℝ) * B)) by ring, eZ_add]
        rw [show Kc * (2 * ((1 : ℂ) / (r : ℂ) ^ 2 * eZ ((r : ℝ) * x))
              - (1 : ℂ) / (r : ℂ) ^ 2 * (eZ ((r : ℝ) * x) * eZ ((r : ℝ) * B))
              - (1 : ℂ) / (r : ℂ) ^ 2 * (eZ ((r : ℝ) * x) * eZ (-((r : ℝ) * B))))
            = Kc * (1 / (r : ℂ) ^ 2) * (2 * eZ ((r : ℝ) * x)
              - eZ ((r : ℝ) * x) * eZ ((r : ℝ) * B)
              - eZ ((r : ℝ) * x) * eZ (-((r : ℝ) * B))) by ring, hkey]
        ring
      rw [ite_eq_right hr, add_zero, hmain, tentCoeff_eq B hB r hr]
  -- the `r = 0` correction and its sum
  have hC : HasSum (fun r : ℤ => (if r = 0 then (B : ℂ) else 0)) (B : ℂ) :=
    hasSum_ite_eq (0 : ℤ) (B : ℂ)
  have hsum1 : HasSum (fun r : ℤ => Kc * (2 * Tp x r - Tp (x + B) r - Tp (x - B) r)
      + (if r = 0 then (B : ℂ) else 0))
      (Kc * (2 * (2 * Real.pi ^ 2 * phiC x) - 2 * Real.pi ^ 2 * phiC (x + B)
        - 2 * Real.pi ^ 2 * phiC (x - B)) + (B : ℂ)) := hA.add hC
  -- evaluation of the limiting value
  have hval : Kc * (2 * (2 * Real.pi ^ 2 * phiC x) - 2 * Real.pi ^ 2 * phiC (x + B)
      - 2 * Real.pi ^ 2 * phiC (x - B)) + (B : ℂ) = (tent B x : ℂ) := by
    have hΦ : (2 * (2 * Real.pi ^ 2 * phiC x) - 2 * Real.pi ^ 2 * phiC (x + B)
        - 2 * Real.pi ^ 2 * phiC (x - B))
        = (2 * (Real.pi : ℂ) ^ 2) * (2 * phiC x - phiC (x + B) - phiC (x - B)) := by ring
    have hK : Kc * (2 * (Real.pi : ℂ) ^ 2) = 1 / (2 * (B : ℂ)) := by
      rw [hKc]; push_cast; field_simp; ring
    have hΦR : (2 * phiC x - phiC (x + B) - phiC (x - B))
        = ((2 * phiR x - phiR (x + B) - phiR (x - B) : ℝ) : ℂ) := by
      unfold phiC; push_cast; ring
    rw [hΦ, ← mul_assoc, hK, hΦR]
    rw [show (1 / (2 * (B : ℂ)) : ℂ) = ((1 / (2 * B) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
    congr 1
    rw [tent_secondDiff B x hB hB2]; ring
  rw [← hval]
  exact hsum1.congr_fun (fun r => hpt r)

end Work.BMF
