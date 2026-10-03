import Mathlib
import Submission.Work.KMTPlan.A6Clean.AdelicClausesAt

namespace Work.KMTPlan.A6Clean

open scoped ENNReal NNReal BigOperators

/-- **The loss weight is monotone in its exponent**, with *no* sign hypothesis on `c`.

The clause list `AdelicClausesAt` carries the exponent `A` of the loss weight without requiring
`0 ≤ A`, so the monotonicity used to pass from `A` to `A' ≥ A` must hold for arbitrary reals.
This is the case: `c ↦ (1 + L)^c` is increasing for `c ≤ c'` because its base `1 + L` is `≥ 1`
(and `L ≥ 0`), and `c ↦ 2^{cρL}` is increasing because `ρL ≥ 0` makes the exponent increasing.
(Compare `Work.KMTAreas.A7Hi.lossWeight_mono`, which carries the redundant hypothesis `0 ≤ c`.) -/
theorem lossWeight_mono_local {c c' ρ : ℝ} (hcc : c ≤ c') (hρ : 0 ≤ ρ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂
      ≤ Work.KMTAreas.A7.lossWeight c' ρ l₁ l₂ k₁ k₂ := by
  have hL : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR]
    have h : (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      rw [Work.Analysis.EndVar.lmax]; omega
    exact_mod_cast h
  have h1 : (1 : ℝ) ≤ 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by linarith
  have hA : (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ c
      ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ c' :=
    Real.rpow_le_rpow_of_exponent_le h1 hcc
  have hB : (2 : ℝ) ^ (c * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)
      ≤ (2 : ℝ) ^ (c' * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    have hsub : (0 : ℝ) ≤ (c' - c) * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hcc) hρ) hL
    nlinarith [hsub]
  unfold Work.KMTAreas.A7.lossWeight
  exact mul_le_mul hA hB (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by linarith) _)

/-- **Monotonicity of the §8 adelic clause list in its three constants.**  The clause list
`AdelicClausesAt` has the same `∃ F, ∃ u, ∃ v, ∃ M, ∃ Ku, ∃ Kv` witnesses at `(c', A', Cin')` as at
`(c, A, Cin)` (all the clauses above the last three are independent of the constants), and the
three constant-dependent clauses only *weaken* when `c` decreases to `c' ≤ c`, `A` increases to
`A' ≥ A` and `Cin` increases pointwise to `Cin'`:

* the `M`-clause uses `2^{-c·max l₁ l₂}`, which is *increasing* in the exponent, hence increasing
  as `c` decreases;
* the `Ku`/`Kv`-clauses use `lossWeight A`, which is monotone in the exponent `A`
  (`lossWeight_mono_local`, requiring only `ρ ≥ 0`).

This is the arithmetic needed to compare producers stated at different constant triples (e.g. to
take the `max` of two exponents, or to absorb extra constants into `Cin`). -/
theorem adelicClausesAt_mono (P : Polynomial ℤ) (ρ R : ℝ) (hρ : 0 ≤ ρ) (r : NNReal) (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (j₁ j₂ : ℤ) (f g : ℤ → ℂ) (C₀ : ℕ) {c c' A A' : ℝ} {Cin Cin' : NNReal → NNReal} (h : Work.KMTPlan.A6Clean.AdelicClausesAt P ρ R r a Λ l₁ l₂ k₁ k₂ t j₁ j₂ f g C₀ c A Cin) (hcc : c' ≤ c) (hAA : A ≤ A') (hCin : ∀ L : NNReal, Cin L ≤ Cin' L) : Work.KMTPlan.A6Clean.AdelicClausesAt P ρ R r a Λ l₁ l₂ k₁ k₂ t j₁ j₂ f g C₀ c' A' Cin' := by
  obtain ⟨F, u, v, M, Ku, Kv, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine ⟨F, u, v, M, Ku, Kv, h1, h2, h3, ⟨h4.1, ?_⟩, ⟨h5.1, ?_⟩, ⟨h6.1, ?_⟩,
    h7, h8, h9, h10, h11, h12, h13⟩
  · -- the `M`-clause: `2^{-c·max l₁ l₂}` increases as `c` decreases, and `Cin ≤ Cin'`
    have hmax : (0 : ℝ) ≤ max (l₁ : ℝ) (l₂ : ℝ) := by positivity
    have hcm : c' * max (l₁ : ℝ) (l₂ : ℝ) ≤ c * max (l₁ : ℝ) (l₂ : ℝ) :=
      mul_le_mul_of_nonneg_right hcc hmax
    have hneg : -(c * max (l₁ : ℝ) (l₂ : ℝ)) ≤ -(c' * max (l₁ : ℝ) (l₂ : ℝ)) :=
      neg_le_neg hcm
    have hpow : (2 : ℝ) ^ (-(c * max (l₁ : ℝ) (l₂ : ℝ)))
        ≤ (2 : ℝ) ^ (-(c' * max (l₁ : ℝ) (l₂ : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hneg
    exact le_trans h4.2 (mul_le_mul (ENNReal.coe_le_coe.mpr (hCin Λ))
      (ENNReal.ofReal_le_ofReal hpow) zero_le zero_le)
  · -- the `Ku`-clause: `lossWeight` is monotone in the exponent, and `Cin ≤ Cin'`
    have hlw := lossWeight_mono_local hAA hρ l₁ l₂ k₁ k₂
    exact le_trans h5.2 (mul_le_mul (mul_le_mul (ENNReal.coe_le_coe.mpr (hCin Λ))
      (ENNReal.ofReal_le_ofReal hlw) zero_le zero_le) le_rfl zero_le zero_le)
  · -- the `Kv`-clause: same
    have hlw := lossWeight_mono_local hAA hρ l₁ l₂ k₁ k₂
    exact le_trans h6.2 (mul_le_mul (mul_le_mul (ENNReal.coe_le_coe.mpr (hCin Λ))
      (ENNReal.ofReal_le_ofReal hlw) zero_le zero_le) le_rfl zero_le zero_le)

end Work.KMTPlan.A6Clean
