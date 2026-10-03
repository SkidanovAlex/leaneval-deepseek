/-
# Shared vocabulary for the inverse Weyl estimate in the interval (`Icc`) form
(`Work.KMTAreas.A4.lip2GenWeyl`)

The target `Work.KMTAreas.A4.WeylIccStatement P` (the conclusion of
`Work.KMTAreas.A4.lip2WeylIcc`) is proved here along this route:

1. **The `Icc` reduction** (`Work.KMTAreas.A4.lip2IccReduce`).  The windowed sum
   `winSumIcc M γ ξ P s a b = ∑_{n ∈ Icc a b} win M γ (n-s) e (ξ P n)` is written, via the
   sliding-window decomposition of the window (`boxDecomp`), as an `ℓ¹`-combination of *sharp
   interval* sums of the unimodular sequence
   `winPhase γ ξ P s n = e ((n - s) γ) · e (ξ P n)`.  Hence a large windowed sum produces an
   interval `[c,d]` of length `≤ C M` on which `‖∑_{n ∈ Icc c d} winPhase γ ξ P s n‖ ≥ ε M / C`.

2. **The inverse Weyl estimate with a real linear term** (`IWPtr`).  On `[c,d]` the sequence
   `winPhase` is a unimodular constant times the phase `n ↦ e (τ n + ξ Q(n))` with `τ = γ₀` a real
   representative of `γ`.  The estimate `IWPtr d` (proved from the τ-free cascade `IWP_allG`, see
   `Work.KMTAreas.A4.lip2IWPtrStep`) inverts a large sum of such a phase into a rational
   approximation of `ξ · Q.coeff d`.

3. **Assembly.**  If the length hypothesis `C ε' ^ (-K) ≤ L` of `IWPtr` is available we are done;
   if not, the two inequalities `L ≥ εM/C` (amplitude) and `L ≤ C M` (length) together with the
   theorem's hypothesis `ε ^ (-K') ≤ M` force `M` to be bounded, and then the trivial estimate
   `q = 1`, `a' = round (ξ · lc P)` closes the argument.

The real-linear-term phase is unavoidable: the modulation `e ((n-s) γ)` of the window is a
*linear* phase whose coefficient is an arbitrary real, and the differencing (van der Corput) step
of the cascade cancels it exactly, so it never reappears at lower degree.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2IccBasic
import Submission.Work.KMTAreas.A4.lip2GenDefs
import Submission.Work.KMTAreas.A4.invWeylSucc
import Submission.Work.KMTAreas.A4.invWeylDense
import Submission.Work.KMTAreas.A4.invWeylVdc
import Submission.Work.KMTAreas.A4.invWeyl_one
import Submission.Work.KMTAreas.A4.lip2AmplifyStatement
import Submission.Work.KMTAreas.A4.winBox
import Submission.Work.KMTAreas.A4.winZero_classSum_vanish
import Submission.Work.KMTAreas.A4.window_extract

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Phases with a real linear term -/

/-- The phase `n ↦ e (τ n + ξ Q(n))` of an integer polynomial `Q` with an extra *real* linear
term `τ n`.  This is the phase produced by the `Icc` reduction: `τ = γ₀` is a real representative
of the modulation `γ` of the window. -/
noncomputable def phLin (Q : Polynomial ℤ) (ξ τ : ℝ) : ℤ → ℂ :=
  fun n => ee (τ * (n : ℝ) + ξ * ((Q.eval n : ℤ) : ℝ))

theorem phLin_norm (Q : Polynomial ℤ) (ξ τ : ℝ) (n : ℤ) : ‖phLin Q ξ τ n‖ = 1 := by
  rw [phLin, ee_norm]

/-- The linear term factors out: `phLin Q ξ τ n = e (τ n) · ph Q ξ n`. -/
theorem fourier_coe_eq_ee (n : ℤ) (t : ℝ) :
    (fourier n ((t : ℝ) : FreqCircle) : ℂ) = ee (t * (n : ℝ)) := by
  rw [fourier_coe_apply]
  rw [ee]
  congr 1
  push_cast
  ring

theorem phLin_eq_mul (Q : Polynomial ℤ) (ξ τ : ℝ) (n : ℤ) :
    phLin Q ξ τ n = ee (τ * (n : ℝ)) * ph Q ξ n := by
  rw [phLin, ee_add]
  rfl

/-- With `τ = 0` the phase `phLin` is the `ph` of `Work.KMTAreas.A4.invWeylDefs`. -/
theorem phLin_zero (Q : Polynomial ℤ) (ξ : ℝ) (n : ℤ) : phLin Q ξ 0 n = ph Q ξ n := by
  rw [phLin_eq_mul, zero_mul, ee_zero, one_mul]

/-- **The correlation identity.**  Differencing the phase `phLin Q ξ τ` at the shift `h` removes
the linear term and leaves the unit constant `e (-τ h)` times the phase of the differenced
polynomial `Q - Q (X + h)`.  This is why the cascade only ever needs the τ-free estimate `IWP`. -/
theorem phLin_corr (Q : Polynomial ℤ) (ξ τ : ℝ) (n h : ℤ) :
    phLin Q ξ τ n * star (phLin Q ξ τ (n + h))
      = ee (-(τ * (h : ℝ))) * ph (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ n := by
  rw [phLin_eq_mul, phLin_eq_mul, star_mul, star_ee]
  calc ee (τ * (n : ℝ)) * ph Q ξ n * (star (ph Q ξ (n + h)) * ee (-(τ * ((n + h : ℤ) : ℝ))))
      = ee (τ * (n : ℝ)) * (ph Q ξ n * star (ph Q ξ (n + h)))
          * ee (-(τ * ((n + h : ℤ) : ℝ))) := by ring
    _ = ee (τ * (n : ℝ)) * ph (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ n
          * ee (-(τ * ((n + h : ℤ) : ℝ))) := by rw [ph_mul_conj_ph]
    _ = ee (-(τ * (h : ℝ))) * ph (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ n := by
        have hee : ee (τ * (n : ℝ)) * ee (-(τ * ((n + h : ℤ) : ℝ))) = ee (-(τ * (h : ℝ))) := by
          rw [← ee_add]
          congr 1
          push_cast
          ring
        calc ee (τ * (n : ℝ)) * ph (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ n
              * ee (-(τ * ((n + h : ℤ) : ℝ)))
            = (ee (τ * (n : ℝ)) * ee (-(τ * ((n + h : ℤ) : ℝ))))
                * ph (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ n := by ring
          _ = ee (-(τ * (h : ℝ))) * ph (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ n := by
              rw [hee]

/-! ## The inverse Weyl estimate with a real linear term -/

/-- **The inverse Weyl estimate at degree `d` with a real linear term.**  If the sum of the phase
`n ↦ e (τ n + ξ Q(n))` over an interval `[a,b]` of length `L` is at least `ε L` and `L` is at least
`C ε ^ (-K)`, then `ξ · Q.coeff d` has a rational approximation with denominator at most
`C ε ^ (-K)` and error at most `C ε ^ (-K) / L ^ d`.

This is `Work.KMTAreas.A4.IWP` with the extra real linear term `τ n`; the linear term cancels at
the first van der Corput step (`phLin_corr`), so the estimate follows from the τ-free cascade
`Work.KMTAreas.A4.IWP_allG`.

**Proof route** (the induction step `Work.KMTAreas.A4.IWPtr_succ`): copy the proof of
`Work.KMTAreas.A4.iwW_succ` in `Submission/Work/KMTAreas/A4/invWeylWindow.lean` (that module is not
importable -- it depends on the broken `winSumReduceProved` -- but its text is readable and the
proof is a verbatim transcription with these changes):

* the unimodular sequence of the outer sum is `u n = phLin Q ξ τ n` instead of `c * ph Q ξ n` (its
  unit modulus is `phLin_norm`); the amplitude parameter `c` disappears;
* the pigeonholed correlation sums are rewritten with `phLin_corr`:
  `u n * conj (u (n + h)) = e (-τ h) * ph (Q - Q (X+h)) ξ n`, so the inner (τ-free) instance
  `IWP d C K` is applied with the unit amplitude `c := ee (-(τ * h))` (`ee_norm`);
* everything else -- the derivation of `8 ≤ ε ^ 2 L` from the length hypothesis, the constants
  `C' = max (max C₁ (64 ^ (K+1) * C)) 8`, `K' = max (max K₁ (2*K+2)) 2`, and the final call
  `invWeylStep d hd C K hC hK hAmp hDense Q hQ ξ a b ε H ...` (which never mentions `τ`) -- is
  unchanged.  The instances `invWeylVdc`, `lip2AmplifyStatement`, `invWeylDense` are imported by
  this module. -/
def IWPtr (d : ℕ) (C K : ℝ) : Prop :=
  ∀ (Q : Polynomial ℤ) (hQ : Q.natDegree = d) (ξ τ : ℝ) (a b : ℤ) (ε : ℝ),
    a ≤ b → 0 < ε → ε ≤ 1 → C * ε ^ (-K) ≤ (((b - a : ℤ) : ℝ) + 1) →
    ε * (((b - a : ℤ) : ℝ) + 1) ≤ ‖∑ n ∈ Finset.Icc a b, phLin Q ξ τ n‖ →
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C * ε ^ (-K) ∧
      ∃ m : ℤ, |(q : ℝ) * ξ * ((Q.coeff d : ℤ) : ℝ) - (m : ℝ)|
        ≤ C * ε ^ (-K) / ((((b - a : ℤ) : ℝ) + 1) ^ d)

/-- `IWPtr` for every degree `d ≥ 2`. -/
def IWPtrAll : Prop := ∀ d : ℕ, 2 ≤ d → ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ IWPtr d C K

/-! ## The integrand of the windowed `Icc` sum -/

/-- The unimodular integrand of `winSumIcc`: the modulation `e ((n - s) γ)` of the window times
the phase `e (ξ P(n))` of the polynomial. -/
noncomputable def winPhase (γ : FreqCircle) (ξ : ℝ) (P : Polynomial ℤ) (s n : ℤ) : ℂ :=
  (fourier (n - s) γ : ℂ) * ee (ξ * ((P.eval n : ℤ) : ℝ))

theorem winPhase_norm (γ : FreqCircle) (ξ : ℝ) (P : Polynomial ℤ) (s n : ℤ) :
    ‖winPhase γ ξ P s n‖ = 1 := by
  rw [winPhase, norm_mul, ee_norm, mul_one, fourier_apply, Circle.norm_coe]

/-- **The reduced form of the integrand.**  For a real representative `γ₀` of the modulation `γ`,
`winPhase γ ξ P s n` is the unit constant `e (-γ₀ s)` times the phase `phLin P ξ γ₀ n`. -/
theorem winPhase_eq_const_mul_phLin (γ : FreqCircle) (ξ : ℝ) (P : Polynomial ℤ) (s n : ℤ)
    {γ₀ : ℝ} (hγ : ((γ₀ : ℝ) : FreqCircle) = γ) :
    winPhase γ ξ P s n = ee (-(γ₀ * (s : ℝ))) * phLin P ξ γ₀ n := by
  have hf : (fourier (n - s) γ : ℂ) = ee (γ₀ * ((n - s : ℤ) : ℝ)) := by
    rw [← hγ]
    exact fourier_coe_eq_ee (n - s) γ₀
  rw [winPhase, hf, phLin]
  rw [← ee_add, ← ee_add]
  congr 1
  push_cast
  ring

/-! ## The τ-free cascade (copied from `Work.KMTAreas.A4.invWeylWindow`) -/

/-- The degree-`1` base case of the inverse Weyl estimate (the wrapper of
`Work.KMTAreas.A4.invWeyl_one`). -/
theorem IWP_oneG : ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ IWP 1 C K := by
  obtain ⟨C, K, hC, hK, hmain⟩ := invWeyl_one
  refine ⟨C, K, hC, hK, ?_⟩
  intro Q ξ c hQ hc a b ε hab hε0 hε1 hlen hampl
  have hsum : (∑ n ∈ Finset.Icc a b, c * ph Q ξ n)
      = ∑ n ∈ Finset.Icc a b, c *
          Complex.exp (2 * Real.pi * Complex.I * (ξ * ((Q.eval n : ℤ) : ℝ))) := by
    apply Finset.sum_congr rfl
    intro n _
    simp only [ph, Complex.ofReal_mul]
  rw [hsum] at hampl
  exact hmain Q hQ ξ c hc a b ε hab hε0 hε1 hampl

/-- The τ-free inverse Weyl estimate for every degree `d ≥ 1` (the copy of
`Work.KMTAreas.A4.IWP_all` that does not depend on the windowed chapter). -/
theorem IWP_allG : ∀ d : ℕ, 1 ≤ d → ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ IWP d C K := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases eq_or_lt_of_le hd with h1 | h2
    · subst h1
      exact IWP_oneG
    · obtain ⟨C, K, hC, hK, hIW⟩ := ih (d - 1) (by omega) (by omega)
      obtain ⟨C', K', hC', hK', hIW'⟩ :=
        invWeylSucc (d - 1) (by omega) C K hC hK hIW invWeylVdc lip2AmplifyStatement
          invWeylDense
      have hcast : (d - 1) + 1 = d := by omega
      have hgoal : IWP d C' K' := by rwa [hcast] at hIW'
      exact ⟨C', K', hC', hK', hgoal⟩

end Work.KMTAreas.A4
