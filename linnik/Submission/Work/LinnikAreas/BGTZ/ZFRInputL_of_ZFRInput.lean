import Mathlib
import Submission.Work.LinnikAreas.BGTZZFR
import Submission.Work.LinnikAreas.BGTZ.ZFRInput_exists
import Submission.Work.LinnikAreas.BGTZ.LFunction_eq_zero_imp_zeroMult
import Submission.Work.LinnikAreas.BGTZ.zetaZFR_working
import Submission.Work.LinnikAreas.Density4.LFunction_one_apply_one
import Submission.Work.ZeroDensity.Ingham.zetaZeroBridge

open DirichletCharacter Complex

namespace Work.LinnikAreas.BGTZ

/-!
# `ZFRInputL` from `ZFRInput`

`ZFRInput cZ` (see `Submission/Work/LinnikAreas/BGTZZFR.lean`) is the uniform zero-free region
phrased with `zeroMult`-zeros: for every character `χ` mod `q` and every zero `ρ` of the
*completed* `L`-function of `χ` (`zeroMult χ ρ ≠ 0`, `Re ρ > 1/2`, `ρ ≠ β₁`) one has
`1 - Re ρ ≥ cZ / log (q · max 4 |Im ρ|)`.

`ZFRInputL cZ` is the same statement with the hypothesis `L(ρ,χ) = 0 ∨ L(ρ,χχ₁) = 0` on the
ordinary `L`-function.  The two differ only in the hypothesis, and the bridge is provided by
`LFunction_eq_zero_imp_zeroMult` (non-principal `χ`) together with the principal-character
reduction `principalL_zero_imp_zeta` below: a zero of an ordinary `L`-function in `Re > 1/2` is a
`zeroMult`-zero of the *same* character, so `ZFRInput` applies directly (its conclusion does not
depend on the character).  Hence `ZFRInput cZ` implies `ZFRInputL cZ` — in particular the constant
is preserved.
-/

/-- A zero of `L(·,χ₀)` (`χ₀` the principal character mod `q ≥ 4`) with `Re ρ > 1/2` is a zero of
`ζ`.  Away from `ρ = 1` this is `L(s,χ₀) = ζ(s)·∏_{p ∣ q}(1 - p^{-s})`
(`LFunctionTrivChar_eq_mul_riemannZeta`, every factor non-zero for `Re s > 0`); at `ρ = 1`
Mathlib's value `L(1,χ₀)` is non-zero (`LFunction_one_apply_one`, its two factors being a non-zero
Euler product and a positive real number). -/
theorem principalL_zero_imp_zeta {q : ℕ} [NeZero q] (hq : 4 ≤ q) {ρ : ℂ}
    (hre : (1 / 2 : ℝ) < ρ.re)
    (h : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ = 0) :
    riemannZeta ρ = 0 := by
  classical
  rcases eq_or_ne ρ 1 with hρ1 | hρ1
  · -- `ρ = 1`: the value of `L(·,χ₀)` at its pole is non-zero
    exfalso
    subst hρ1
    have hval := Work.LinnikAreas.Density4.LFunction_one_apply_one q (by omega : 2 ≤ q)
    rw [hval] at h
    rcases mul_eq_zero.mp h with h2 | h3
    · -- the Euler product is non-zero
      refine (Finset.prod_ne_zero_iff.mpr ?_) h2
      intro p hp
      have hp1 : (p : ℂ) ≠ 1 := by
        have hne : p ≠ 1 := (Nat.prime_of_mem_primeFactors hp).ne_one
        exact_mod_cast hne
      intro hc
      exact hp1 (inv_eq_one.mp (sub_eq_zero.mp hc).symm)
    · -- the bracket is a positive real
      have hpos : (0 : ℝ) < Real.log (q : ℝ)
            + (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2
            + ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
        have hLq : Real.log 4 ≤ Real.log (q : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hq)
        have hγ : (0 : ℝ) < Real.eulerMascheroniConstant := by
          linarith [Real.one_half_lt_eulerMascheroniConstant]
        have hsum : 0 ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
          refine Finset.sum_nonneg fun p hp => ?_
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
          exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
        have hlog4π : Real.log (4 * Real.pi) = Real.log 4 + Real.log Real.pi :=
          Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)
        have hlogπ : Real.log Real.pi < Real.log 4 :=
          Real.log_lt_log Real.pi_pos Real.pi_lt_four
        nlinarith [hLq, hγ, hsum, hlog4π, hlogπ]
      have hbr : ((Real.log (q : ℝ) : ℂ) + riemannZeta 1
          + ∑ p ∈ q.primeFactors, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)) ≠ 0 := by
        have hζ1 : riemannZeta 1
            = (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 : ℝ) : ℂ) := by
          rw [riemannZeta_one]
          have hlog : Complex.log ((4 : ℂ) * (Real.pi : ℂ))
              = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
            rw [show (4 : ℂ) * (Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring]
            exact (Complex.ofReal_log (by positivity)).symm
          rw [hlog]
          simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat]
        have hrw : ((Real.log (q : ℝ) : ℂ) + riemannZeta 1
            + ∑ p ∈ q.primeFactors, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ))
            = ((Real.log (q : ℝ) + (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2
                + ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) := by
          rw [hζ1]
          push_cast
          ring
        rw [hrw]
        exact_mod_cast (ne_of_gt hpos)
      exact hbr h3
  · -- `ρ ≠ 1`: the Euler product
    have hEP := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) (s := ρ) hρ1
    have hthis : DirichletCharacter.LFunctionTrivChar q ρ = 0 := h
    rw [hEP] at hthis
    refine (mul_eq_zero.mp hthis).resolve_left ?_
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
    have hnorm : ‖(p : ℂ) ^ (-ρ)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re,
        Real.rpow_neg (by positivity : (0 : ℝ) ≤ (p : ℝ))]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp1r (by linarith : (0 : ℝ) < ρ.re))
    intro hc
    have h1p : (p : ℂ) ^ (-ρ) = 1 := (sub_eq_zero.mp hc).symm
    rw [h1p, norm_one] at hnorm
    exact absurd hnorm (lt_irrefl 1)

/-- **The `zeroMult`/`L`-bridge in `Re > 1/2`, all characters** (the principal character
included).  A zero of the ordinary `L`-function of any character `χ` mod `q ≥ 4` with
`1/2 < Re ρ` is a `zeroMult`-zero of that same character.

* `χ = 1`: `principalL_zero_imp_zeta` turns `L(ρ,χ₀) = 0` into `riemannZeta ρ = 0`; hence
  `Re ρ < 1` (`riemannZeta_ne_zero_of_one_le_re`) and `zetaZeroBridge` identifies the zeros of the
  completed zeta function with those of `ζ` in the closed strip, giving
  `analyticOrderNatAt completedRiemannZeta ρ ≠ 0`, i.e. `zeroMult 1 ρ ≠ 0`
  (`zeroMult_principal_eq`).
* `χ ≠ 1`: `LFunction_eq_zero_imp_zeroMult`, with `Re ρ < 1` from
  `LFunction_ne_zero_of_one_le_re`. -/
theorem LFunction_eq_zero_imp_zeroMult_half {q : ℕ} [NeZero q] (hq : 4 ≤ q)
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hre : (1 / 2 : ℝ) < ρ.re)
    (h : DirichletCharacter.LFunction χ ρ = 0) :
    Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
  rcases eq_or_ne χ 1 with hχ | hχ
  · rw [hχ] at h ⊢
    have hζ : riemannZeta ρ = 0 := principalL_zero_imp_zeta hq hre h
    have hre1 : ρ.re < 1 :=
      lt_of_not_ge fun hc => riemannZeta_ne_zero_of_one_le_re hc hζ
    rw [Work.LinnikAreas.zeroMult_principal_eq]
    exact (Work.ZeroDensity.Ingham.zetaZeroBridge ρ (le_of_lt hre) hre1.le).mpr hζ
  · have hρ1 : ρ.re < 1 := by
      by_contra hc
      rw [not_lt] at hc
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hc) h
    exact LFunction_eq_zero_imp_zeroMult χ hχ (by linarith) hρ1 h

/-- **`ZFRInputL` from `ZFRInput`, with the same constant.**  Given the `zeroMult`-form of the
uniform zero-free region with constant `cZ > 0`, the `L`-function form holds with the same
constant: the `ZFRInput` bound does not depend on the character, so it suffices to convert an
`L`-function zero (of `χ` or of `χχ₁`) in `Re > 1/2` into a `zeroMult`-zero of the same character
(`LFunction_eq_zero_imp_zeroMult_half`).  The threshold `q₀` is raised to `max q₀ 4` so that the
principal-character reduction applies. -/
theorem ZFRInputL_of_ZFRInput (cZ : ℝ) (hcZ : 0 < cZ)
    (h : Work.LinnikAreas.BGTZ.ZFRInput cZ) :
    ∃ cZ' : ℝ, 0 < cZ' ∧ Work.LinnikAreas.BGTZ.ZFRInputL cZ' := by
  obtain ⟨q₀, hq⟩ := h
  refine ⟨cZ, hcZ, max q₀ 4, ?_⟩
  intro q hqle hqne χ₁ β₁ hχ₁ hsq hβ₁ hz₁ hβ₁' χ ρ hdisj hre hne
  haveI : NeZero q := hqne
  have hq₀ : q₀ ≤ q := le_trans (le_max_left _ _) hqle
  have hq4 : 4 ≤ q := le_trans (le_max_right _ _) hqle
  rcases hdisj with hL | hL
  · exact hq q hq₀ χ₁ β₁ hχ₁ hsq hβ₁ hz₁ hβ₁' χ ρ
      (LFunction_eq_zero_imp_zeroMult_half hq4 χ hre hL) hre hne
  · exact hq q hq₀ χ₁ β₁ hχ₁ hsq hβ₁ hz₁ hβ₁' (χ * χ₁) ρ
      (LFunction_eq_zero_imp_zeroMult_half hq4 (χ * χ₁) hre hL) hre hne

end Work.LinnikAreas.BGTZ
