import Submission.CDT.LogHadamard
import Submission.CDT.SympDenom

/-!
# Item 3 of the Theorem-C route: the unlikely `G`-function `P` (paper eq. (defP))

This module formalises the missing *step 3* of the route map of
`Submission.cdt_theoremC_li` (CDT Theorem `logsmain`, part 2,
arXiv:2408.15403 §"Products of two logarithms"): the construction of the
**unlikely `G`-function** `P` from an assumed `ℤ`-linear relation

```lean
r_a·η_a + r_b·η_b + r_ab·η_aη_b = r_0        -- paper eq. (rabc)
```

between `η_a := ½·log((a+1)/(a−1))` and `η_b` (`a = 1+2m`, `b = 1+2n`).

The paper defines (eq. (defP))

```lean
P := r_a·P_a + r_b·P_b + r_ab·P_ab,      P_a := (H(a) − η_a·A(a)) ⋆ A(b),
                                          P_b := A(a) ⋆ (H(b) − η_b·A(b)),
                                          P_ab := H(a) ⋆ H(b) − η_aη_b·(A(a) ⋆ A(b)),
```

and observes that **under (rabc) the coefficients of `P` become rational**,
with denominator type `[1,…,n]²`, and that `P` is *overconvergent* beyond the
smallest cusp (`a − √(a²−1))·(b − √(b²−1))`.  That is what is proved here:

* the cancellation `logPCoeff_eq_rat` — `r_a·P_a + r_b·P_b + r_ab·P_ab` has
  coefficients `r_a·vₙ(a)uₙ(b) + r_b·uₙ(a)vₙ(b) + r_ab·vₙ(a)vₙ(b) − r₀·uₙ(a)uₙ(b)`
  (a pure `ring` computation once (rabc) is substituted);
* the denominator type `logPCoeffQ_denom` — `[1,…,n]²·cₙ ∈ ℤ` for odd
  integer `a, b`, from the Beukers-pair integrality `uₙ ∈ ℤ` and
  `[1,…,n]·vₙ ∈ ℤ` (`Beukers.beukersU_int_of_odd`,
  `Beukers.beukersV_lcm_int_of_odd`);
* overconvergence `logPCoeff_beyond_cusp`, from the three beyond-cusp bounds
  of `LogHadamard`;
* the packaged statement `logP_unlikely`: under (rabc), the power series
  `logP` has rational coefficients of denominator type `[1,…,n]²` which are
  overconvergent beyond the smallest cusp.

**Still missing (recorded here and in the ledger of `Submission.lean`)**: the
three `M`-identities of the paper (the second display of §"The overconvergent
space")

```lean
M(H(a) ⋆ A(b)) = −b + 3aX − 3bX² + aX³,
M(A(a) ⋆ H(b)) = −a + 3bX − 3aX² + bX³,
M(H(a) ⋆ H(b)) = −1 + 2X² − X⁴
```

(with `M = logPAODE a b` the paper's order-2 operator `(ODE)`), which refine
`LogHadamard.logPA_ode` (`M(P_A) = 0`) to the non-homogeneous case and give
`M(P) ∈ ℚ[X]`; together with the `Sym⁺`-symmetrisation `G = Sym⁺P` of the
paper's Remark `PtoG` (their Lemma `bdenominators`/Proposition `fictive G`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace Submission.CDT

noncomputable section

/-! ## The coefficients of the combination `P` -/

/-- The coefficients `cₙ` of the paper's combination
`r_a·P_a + r_b·P_b + r_ab·P_ab` (real form, before imposing (rabc)). -/
def logPCoeff (ã₁ ã₂ : ℝ) (ra rb rab : ℤ) (n : ℕ) : ℝ :=
  (ra : ℝ) * beukersPaCoeff ã₁ ã₂ n + (rb : ℝ) * beukersPbCoeff ã₁ ã₂ n
    + (rab : ℝ) * beukersPabCoeff ã₁ ã₂ n

/-- The *rational* expression which the coefficients `cₙ` take once the
relation `r_a·η_a + r_b·η_b + r_ab·η_aη_b = r₀` is imposed. -/
def logPCoeffQ (ã₁ ã₂ : ℚ) (ra rb rab r0 : ℤ) (n : ℕ) : ℚ :=
  (ra : ℚ) * (beukersV ã₁ n * beukersU ã₂ n)
    + (rb : ℚ) * (beukersU ã₁ n * beukersV ã₂ n)
    + (rab : ℚ) * (beukersV ã₁ n * beukersV ã₂ n)
    - (r0 : ℚ) * (beukersU ã₁ n * beukersU ã₂ n)

/-- **The cancellation of the transcendentals.**  Assuming the relation
`r_a·η_a + r_b·η_b + r_ab·η_aη_b = r₀`, the `n`-th coefficient of
`r_a·P_a + r_b·P_b + r_ab·P_ab` is the rational number `logPCoeffQ`. -/
theorem logPCoeff_eq_rat (ã₁ ã₂ : ℚ) (ra rb rab r0 : ℤ)
    (hrel : (ra : ℝ) * beukersEta (ã₁ : ℝ) + (rb : ℝ) * beukersEta (ã₂ : ℝ)
      + (rab : ℝ) * (beukersEta (ã₁ : ℝ) * beukersEta (ã₂ : ℝ)) = (r0 : ℝ))
    (n : ℕ) :
    logPCoeff (ã₁ : ℝ) (ã₂ : ℝ) ra rb rab n
      = (logPCoeffQ ã₁ ã₂ ra rb rab r0 n : ℝ) := by
  unfold logPCoeff logPCoeffQ beukersPaCoeff beukersPbCoeff beukersPabCoeff beukersD
  rw [beukersUR_eq_cast ã₁, beukersVR_eq_cast ã₁, beukersUR_eq_cast ã₂, beukersVR_eq_cast ã₂]
  push_cast
  linear_combination
    (-((beukersU ã₁ n : ℝ) * (beukersU ã₂ n : ℝ))) * hrel

/-! ## Denominator type `[1,…,n]²` -/

/-- **The denominator type of the coefficients**: for odd integers `a`, `b`,
`[1,…,n]²·cₙ ∈ ℤ`. -/
theorem logPCoeffQ_denom (z₁ z₂ : ℤ) (hz₁ : Odd z₁) (hz₂ : Odd z₂)
    (ra rb rab r0 : ℤ) (n : ℕ) :
    ∃ t : ℤ, (t : ℚ) = (((Finset.Icc 1 n).lcm id : ℕ) : ℚ) ^ 2
      * logPCoeffQ (z₁ : ℚ) (z₂ : ℚ) ra rb rab r0 n := by
  obtain ⟨t₁, ht₁⟩ := beukersU_int_of_odd z₁ hz₁ n
  obtain ⟨s₁, hs₁⟩ := beukersV_lcm_int_of_odd z₁ hz₁ n
  obtain ⟨t₂, ht₂⟩ := beukersU_int_of_odd z₂ hz₂ n
  obtain ⟨s₂, hs₂⟩ := beukersV_lcm_int_of_odd z₂ hz₂ n
  have hL : ((((Finset.Icc 1 n).lcm id : ℕ) : ℤ) : ℚ)
      = (((Finset.Icc 1 n).lcm id : ℕ) : ℚ) := by norm_num
  refine ⟨ra * (s₁ * (((Finset.Icc 1 n).lcm id : ℕ) : ℤ) * t₂)
    + rb * ((((Finset.Icc 1 n).lcm id : ℕ) : ℤ) * t₁ * s₂)
    + rab * (s₁ * s₂)
    - r0 * ((((Finset.Icc 1 n).lcm id : ℕ) : ℤ) * t₁
        * ((((Finset.Icc 1 n).lcm id : ℕ) : ℤ) * t₂)), ?_⟩
  unfold logPCoeffQ
  push_cast
  rw [hs₁, hs₂, ht₁, ht₂]
  ring

/-! ## Overconvergence beyond the smallest cusp -/

/-- **Overconvergence**: the coefficients of the combination are bounded by
`C·sⁿ` with `s·(a − √(a²−1))·(b − √(b²−1)) < 1`. -/
theorem logPCoeff_beyond_cusp (ã₁ ã₂ : ℚ) (h₁ : 3 ≤ ã₁) (h₂ : 3 ≤ ã₂)
    (ra rb rab : ℤ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
      s * ((ã₁ - Real.sqrt (ã₁ ^ 2 - 1)) * (ã₂ - Real.sqrt (ã₂ ^ 2 - 1))) < 1 ∧
      ∀ n : ℕ, |logPCoeff (ã₁ : ℝ) (ã₂ : ℝ) ra rb rab n| ≤ C * s ^ n := by
  have h₁' : (3 : ℝ) ≤ (ã₁ : ℝ) := by exact_mod_cast h₁
  have h₂' : (3 : ℝ) ≤ (ã₂ : ℝ) := by exact_mod_cast h₂
  obtain ⟨C₁, s₁, hC₁, hs₁, hsc₁, hb₁⟩ := beukersPaCoeff_beyond_cusp (ã₁ : ℝ) (ã₂ : ℝ) h₁' h₂'
  obtain ⟨C₂, s₂, hC₂, hs₂, hsc₂, hb₂⟩ := beukersPbCoeff_beyond_cusp (ã₁ : ℝ) (ã₂ : ℝ) h₁' h₂'
  obtain ⟨C₃, s₃, hC₃, hs₃, hsc₃, hb₃⟩ := beukersPabCoeff_beyond_cusp (ã₁ : ℝ) (ã₂ : ℝ) h₁' h₂'
  have hρ₁ : (0 : ℝ) < (ã₁ : ℝ) - Real.sqrt ((ã₁ : ℝ) ^ 2 - 1) := by
    have := beukers_rho_pos (ã₁ : ℝ) h₁'
    simpa [beukersRho] using this
  have hρ₂ : (0 : ℝ) < (ã₂ : ℝ) - Real.sqrt ((ã₂ : ℝ) ^ 2 - 1) := by
    have := beukers_rho_pos (ã₂ : ℝ) h₂'
    simpa [beukersRho] using this
  have hprod : 0 < (ã₁ - Real.sqrt (ã₁ ^ 2 - 1)) * (ã₂ - Real.sqrt (ã₂ ^ 2 - 1)) :=
    mul_pos hρ₁ hρ₂
  refine ⟨|(ra : ℝ)| * C₁ + |(rb : ℝ)| * C₂ + |(rab : ℝ)| * C₃ + 1,
    max s₁ (max s₂ s₃), ?_, ?_, ?_, ?_⟩
  · positivity
  · exact lt_of_lt_of_le (lt_max_of_lt_left hs₁) (le_refl _)
  · have hmax : max s₁ (max s₂ s₃)
        < 1 / ((ã₁ - Real.sqrt (ã₁ ^ 2 - 1)) * (ã₂ - Real.sqrt (ã₂ ^ 2 - 1))) := by
      refine max_lt ?_ (max_lt ?_ ?_)
      · rw [lt_div_iff₀ hprod]; exact hsc₁
      · rw [lt_div_iff₀ hprod]; exact hsc₂
      · rw [lt_div_iff₀ hprod]; exact hsc₃
    rw [lt_div_iff₀ hprod] at hmax
    exact hmax
  · intro n
    have h1 := hb₁ n
    have h2 := hb₂ n
    have h3 := hb₃ n
    have hs1 : s₁ ^ n ≤ max s₁ (max s₂ s₃) ^ n :=
      pow_le_pow_left₀ (le_of_lt hs₁) (le_max_left _ _) n
    have hs2 : s₂ ^ n ≤ max s₁ (max s₂ s₃) ^ n :=
      pow_le_pow_left₀ (le_of_lt hs₂) (le_trans (le_max_left _ _) (le_max_right _ _)) n
    have hs3 : s₃ ^ n ≤ max s₁ (max s₂ s₃) ^ n :=
      pow_le_pow_left₀ (le_of_lt hs₃) (le_trans (le_max_right _ _) (le_max_right _ _)) n
    have hsmax : 0 ≤ max s₁ (max s₂ s₃) ^ n := by positivity
    have hC1 : 0 ≤ |(ra : ℝ)| * C₁ := by positivity
    have hC2 : 0 ≤ |(rb : ℝ)| * C₂ := by positivity
    have hC3 : 0 ≤ |(rab : ℝ)| * C₃ := by positivity
    have hmain : |logPCoeff (ã₁ : ℝ) (ã₂ : ℝ) ra rb rab n|
        ≤ (|(ra : ℝ)| * C₁ + |(rb : ℝ)| * C₂ + |(rab : ℝ)| * C₃)
            * max s₁ (max s₂ s₃) ^ n := by
      calc |logPCoeff (ã₁ : ℝ) (ã₂ : ℝ) ra rb rab n|
          = |(ra : ℝ) * beukersPaCoeff (ã₁ : ℝ) (ã₂ : ℝ) n
              + (rb : ℝ) * beukersPbCoeff (ã₁ : ℝ) (ã₂ : ℝ) n
              + (rab : ℝ) * beukersPabCoeff (ã₁ : ℝ) (ã₂ : ℝ) n| := rfl
        _ ≤ |(ra : ℝ) * beukersPaCoeff (ã₁ : ℝ) (ã₂ : ℝ) n|
              + |(rb : ℝ) * beukersPbCoeff (ã₁ : ℝ) (ã₂ : ℝ) n|
              + |(rab : ℝ) * beukersPabCoeff (ã₁ : ℝ) (ã₂ : ℝ) n| := by
            exact abs_add_three _ _ _
        _ = |(ra : ℝ)| * |beukersPaCoeff (ã₁ : ℝ) (ã₂ : ℝ) n|
              + |(rb : ℝ)| * |beukersPbCoeff (ã₁ : ℝ) (ã₂ : ℝ) n|
              + |(rab : ℝ)| * |beukersPabCoeff (ã₁ : ℝ) (ã₂ : ℝ) n| := by
            rw [abs_mul, abs_mul, abs_mul]
        _ ≤ |(ra : ℝ)| * (C₁ * s₁ ^ n) + |(rb : ℝ)| * (C₂ * s₂ ^ n)
              + |(rab : ℝ)| * (C₃ * s₃ ^ n) := by
            exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
              (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)))
              (mul_le_mul_of_nonneg_left h3 (abs_nonneg _))
        _ ≤ (|(ra : ℝ)| * C₁ + |(rb : ℝ)| * C₂ + |(rab : ℝ)| * C₃)
              * max s₁ (max s₂ s₃) ^ n := by
            have e1 : |(ra : ℝ)| * (C₁ * s₁ ^ n) = |(ra : ℝ)| * C₁ * s₁ ^ n := by ring
            have e2 : |(rb : ℝ)| * (C₂ * s₂ ^ n) = |(rb : ℝ)| * C₂ * s₂ ^ n := by ring
            have e3 : |(rab : ℝ)| * (C₃ * s₃ ^ n) = |(rab : ℝ)| * C₃ * s₃ ^ n := by ring
            rw [e1, e2, e3]
            nlinarith [mul_le_mul_of_nonneg_left hs1 hC1, mul_le_mul_of_nonneg_left hs2 hC2,
              mul_le_mul_of_nonneg_left hs3 hC3, hsmax]
    calc |logPCoeff (ã₁ : ℝ) (ã₂ : ℝ) ra rb rab n|
        ≤ (|(ra : ℝ)| * C₁ + |(rb : ℝ)| * C₂ + |(rab : ℝ)| * C₃)
            * max s₁ (max s₂ s₃) ^ n := hmain
      _ ≤ (|(ra : ℝ)| * C₁ + |(rb : ℝ)| * C₂ + |(rab : ℝ)| * C₃ + 1)
            * max s₁ (max s₂ s₃) ^ n := by nlinarith [hsmax]

/-! ## The unlikely `G`-function -/

/-- The power series `P = Σ cₙ xⁿ` of the paper's eq. (defP), whose
coefficients are the rational numbers `logPCoeffQ`. -/
def logP (ã₁ ã₂ : ℚ) (ra rb rab r0 : ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (logPCoeffQ ã₁ ã₂ ra rb rab r0)

/-- Under (rabc), the coefficient of the *formal combination of real series*
`r_a·P_a + r_b·P_b + r_ab·P_ab` is the rational coefficient of `logP`. -/
theorem logPCoeff_logP (ã₁ ã₂ : ℚ) (ra rb rab r0 : ℤ)
    (hrel : (ra : ℝ) * beukersEta (ã₁ : ℝ) + (rb : ℝ) * beukersEta (ã₂ : ℝ)
      + (rab : ℝ) * (beukersEta (ã₁ : ℝ) * beukersEta (ã₂ : ℝ)) = (r0 : ℝ))
    (n : ℕ) :
    logPCoeff (ã₁ : ℝ) (ã₂ : ℝ) ra rb rab n
      = ((PowerSeries.coeff n (logP ã₁ ã₂ ra rb rab r0) : ℚ) : ℝ) := by
  rw [logPCoeff_eq_rat ã₁ ã₂ ra rb rab r0 hrel n, logP, PowerSeries.coeff_mk]

/-- **Paper step 3 (`defP`), packaged.**  Assume the absurd `ℤ`-relation
`r_a·η_a + r_b·η_b + r_ab·η_aη_b = r₀` between the two logarithms, with
`a = 1 + 2m`, `b = 1 + 2n` odd integers `≥ 3`.  Then the unlikely `G`-function
`P` of (defP) is a power series with

* *rational coefficients*, equal to the coefficients of the real combination
  `r_a·P_a + r_b·P_b + r_ab·P_ab` (`logPCoeff_logP`);
* *denominator type* `[1,…,n]²`;
* *overconvergence* beyond the smallest cusp
  `(a − √(a²−1))·(b − √(b²−1))`. -/
theorem logP_unlikely (z₁ z₂ : ℤ) (hz₁ : Odd z₁) (hz₂ : Odd z₂)
    (h₁ : 3 ≤ z₁) (h₂ : 3 ≤ z₂) (ra rb rab r0 : ℤ)
    (hrel : (ra : ℝ) * beukersEta ((z₁ : ℚ) : ℝ) + (rb : ℝ) * beukersEta ((z₂ : ℚ) : ℝ)
      + (rab : ℝ) * (beukersEta ((z₁ : ℚ) : ℝ) * beukersEta ((z₂ : ℚ) : ℝ)) = (r0 : ℝ)) :
    (∀ n : ℕ, ∃ t : ℤ, (t : ℚ) = (((Finset.Icc 1 n).lcm id : ℕ) : ℚ) ^ 2
        * PowerSeries.coeff n (logP (z₁ : ℚ) (z₂ : ℚ) ra rb rab r0))
    ∧ (∃ C s : ℝ, 0 < C ∧ 0 < s ∧
        s * (((z₁ : ℚ) : ℝ) - Real.sqrt (((z₁ : ℚ) : ℝ) ^ 2 - 1))
            * (((z₂ : ℚ) : ℝ) - Real.sqrt (((z₂ : ℚ) : ℝ) ^ 2 - 1)) < 1
        ∧ ∀ n : ℕ, |((PowerSeries.coeff n (logP (z₁ : ℚ) (z₂ : ℚ) ra rb rab r0) : ℚ) : ℝ)|
            ≤ C * s ^ n) := by
  constructor
  · intro n
    obtain ⟨t, ht⟩ := logPCoeffQ_denom z₁ z₂ hz₁ hz₂ ra rb rab r0 n
    refine ⟨t, ?_⟩
    rw [ht, logP, PowerSeries.coeff_mk]
  · obtain ⟨C, s, hC, hs, hsc, hbnd⟩ :=
      logPCoeff_beyond_cusp (z₁ : ℚ) (z₂ : ℚ) (by exact_mod_cast h₁) (by exact_mod_cast h₂) ra rb rab
    refine ⟨C, s, hC, hs, ?_, ?_⟩
    · simpa only [mul_assoc] using hsc
    · intro n
      rw [← logPCoeff_logP (z₁ : ℚ) (z₂ : ℚ) ra rb rab r0 hrel n]
      exact hbnd n

/-! ## Denominator types in the project's `lcmRange` normal form

`EichlerInput.HasDenomTypeSq` is phrased with the recursive `lcmRange`, while
`Beukers.beukersV_lcm_int_of_odd` supplies the equivalent `Finset` lcm. -/

/-- `lcmRange n = lcm(1,…,n)` -/
lemma lcmRange_eq_Icc_lcm (n : ℕ) : lcmRange n = (Finset.Icc 1 n).lcm id := by
  induction n with
  | zero => simp [lcmRange]
  | succ n ih =>
    rw [lcmRange, ih]
    rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) from by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.lcm_insert]
    exact Nat.lcm_comm _ _

/-- The power series `P` has denominator type `[1,…,n]²`. -/
theorem logP_denomTypeSq (z₁ z₂ : ℤ) (hz₁ : Odd z₁) (hz₂ : Odd z₂)
    (ra rb rab r0 : ℤ) :
    HasDenomTypeSq (fun n => PowerSeries.coeff n (logP (z₁ : ℚ) (z₂ : ℚ) ra rb rab r0)) := by
  intro n
  obtain ⟨t, ht⟩ := logPCoeffQ_denom z₁ z₂ hz₁ hz₂ ra rb rab r0 n
  refine ⟨t, ?_⟩
  rw [lcmRange_eq_Icc_lcm]
  simp only [logP, PowerSeries.coeff_mk]
  exact ht.symm

/-! ## The symmetrisation `G = Sym⁺P` (paper Remark `PtoG`) -/

/-- **Paper Proposition `fictive G` (arithmetic part).**  Under the absurd
relation (rabc) and with `a = 1+2m`, `b = 1+2n` odd, the symmetrised
unlikely `G`-function `G(y) = Sym⁺P` has denominator type `[1,…,2n]²`, while
`G_A(y) = Sym⁺P_A` has *integer* coefficients (denominator type `1`). -/
theorem logP_symm_denomType (z₁ z₂ : ℤ) (hz₁ : Odd z₁) (hz₂ : Odd z₂)
    (ra rb rab r0 : ℤ) :
    (∀ n : ℕ, ∃ z : ℤ, ((lcmRange (2 * n) : ℚ)) ^ 2
        * PowerSeries.coeff n (sympSym (logP (z₁ : ℚ) (z₂ : ℚ) ra rb rab r0)) = z)
    ∧ (∀ n : ℕ, ∃ z : ℤ, (z : ℚ) = PowerSeries.coeff n (sympSym (PA (z₁ : ℚ) (z₂ : ℚ)))) := by
  constructor
  · exact sympSym_denomType _ (logP_denomTypeSq z₁ z₂ hz₁ hz₂ ra rb rab r0)
  · exact sympSym_int _ (fun n => PA_coeff_int_of_odd z₁ z₂ hz₁ hz₂ n)

end

end Submission.CDT
