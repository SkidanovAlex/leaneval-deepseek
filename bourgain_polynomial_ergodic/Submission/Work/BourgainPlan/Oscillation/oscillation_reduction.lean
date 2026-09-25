import Mathlib
import Submission.BourgainPlan.Interfaces
import Submission.Work.BourgainPlan.Oscillation.oscillation_core

/-!
# The `o(J)` reduction for the ℓ² oscillation inequality

`Submission.BourgainPlan.OscillationStatement` asks for the block-oscillation sum

  `Σ_{j<J} ∫⁻_n (sup_{k_j ≤ i < k_{j+1}} |discAvg P ⌊ρ^i⌋ g n − discAvg P ⌊ρ^{k_j}⌋ g n|)²`

to be at most `ε J ‖g‖²` for `J ≥ J₀`, uniformly in the strictly increasing `k`.  Since `ε` is
arbitrary, it is enough to prove *any* power bound `C J^s` with `s < 1` — in particular the
uniform `O(1)` bound (`s = 0`), or Bourgain's `C J^{1/2}` (`s = 1/2`) which is what his §6
square-function argument yields.  This file isolates that analytic statement as
`SublinearOscillation` and proves the reduction `oscillation_statement_of_sublinear`.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

/-- The ℓ² block-oscillation functional of Bourgain's inequality, for fixed `P`, `ρ`, a block
sequence `k` and length `J`. -/
noncomputable def oscFunctional (P : Polynomial ℤ) (ρ : ℝ) (J : ℕ) (k : ℕ → ℕ)
    (g : ℕ → ℝ) : ENNReal :=
  ∑ j ∈ Finset.range J,
    ∫⁻ n, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
        ‖Submission.BourgainPlan.discAvg P ⌊ρ ^ i⌋₊ g n
          - Submission.BourgainPlan.discAvg P ⌊ρ ^ (k j)⌋₊ g n‖ₑ) ^ (2 : ℝ) ∂Measure.count

/-- A finite-support hypothesis, in the form used by the interfaces. -/
def Finsupp (g : ℕ → ℝ) : Prop := ∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0

/-- **The sublinear oscillation bound**: the block oscillation is at most `C J^s ‖g‖²` for some
`C ≥ 0` and some *exponent* `s < 1`.  This is the analytic content of Bourgain's inequality; it
is strictly weaker than the uniform `O(1)` bound and includes his `J^{1/2}` estimate. -/
def SublinearOscillation (P : Polynomial ℤ) (ρ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ s : ℝ, s < 1 ∧
    ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k → ∀ g : ℕ → ℝ, Finsupp g →
      oscFunctional P ρ J k g
        ≤ ENNReal.ofReal (C * (J : ℝ) ^ s)
            * ∫⁻ n, ‖g n‖ₑ ^ (2 : ℝ) ∂Measure.count

/-- The same, uniformly over the polynomial (the hypothesis the final assembly consumes). -/
def SublinearOscillationStatement : Prop :=
  ∀ P : Polynomial ℤ, Submission.BourgainPlan.NonnegOnNat P →
    ∀ ρ : ℝ, 1 < ρ → SublinearOscillation P ρ

/-- **A sublinear bound implies the `o(J)` conclusion.**  If the oscillation functional is at
most `C J^s ‖g‖²` with `s < 1`, then for every `ε > 0` and every `J ≥ J₀` it is at most
`ε J ‖g‖²`: eventually `C J^s ≤ ε J` because `J^{1-s} → ∞`. -/
theorem oscillation_sublinear_form (P : Polynomial ℤ) (ρ : ℝ)
    (h : SublinearOscillation P ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ k : ℕ → ℕ, StrictMono k → ∀ g : ℕ → ℝ, Finsupp g →
      oscFunctional P ρ J k g
        ≤ ENNReal.ofReal (ε * (J : ℝ)) * ∫⁻ n, ‖g n‖ₑ ^ (2 : ℝ) ∂Measure.count := by
  obtain ⟨C, hC, s, hs, hbd⟩ := h
  have h1s : 0 < 1 - s := by linarith
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · refine ⟨1, fun J _ k hk g hg => ?_⟩
    have h1 := hbd J k hk g hg
    rw [← hC0, zero_mul, ENNReal.ofReal_zero, zero_mul] at h1
    exact le_trans h1 bot_le
  -- the threshold `J₀ = max 1 ⌈(C/ε)^(1/(1-s))⌉`
  refine ⟨max 1 ⌈(C / ε) ^ (1 / (1 - s))⌉₊, fun J hJ k hk g hg => ?_⟩
  have hJ1 : 1 ≤ J := le_trans (le_max_left 1 _) hJ
  have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ1)
  have h1 := hbd J k hk g hg
  refine le_trans h1 ?_
  have hCε_nonneg : 0 ≤ C / ε := div_nonneg hC hε.le
  have hJge : max 1 ((C / ε) ^ (1 / (1 - s))) ≤ (J : ℝ) := by
    refine max_le ?_ ?_
    · exact_mod_cast hJ1
    · refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast (le_trans (le_max_right 1 _) hJ)
  have hpow : (C / ε) ≤ (J : ℝ) ^ (1 - s) := by
    calc (C / ε) = ((C / ε) ^ (1 / (1 - s))) ^ (1 - s) := by
          rw [← Real.rpow_mul hCε_nonneg, one_div, inv_mul_cancel₀ (ne_of_gt h1s),
            Real.rpow_one]
      _ ≤ (J : ℝ) ^ (1 - s) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hCε_nonneg _) (le_trans (le_max_right 1 _) hJge)
            h1s.le
  have hkey : C * (J : ℝ) ^ s ≤ ε * (J : ℝ) := by
    calc C * (J : ℝ) ^ s = ε * ((C / ε) * (J : ℝ) ^ s) := by field_simp
      _ ≤ ε * ((J : ℝ) ^ (1 - s) * (J : ℝ) ^ s) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hJpos.le _)) hε.le
      _ = ε * ((J : ℝ) ^ ((1 - s) + s)) := by rw [Real.rpow_add hJpos]
      _ = ε * (J : ℝ) := by rw [sub_add_cancel, Real.rpow_one]
  calc ENNReal.ofReal (C * (J : ℝ) ^ s) * ∫⁻ n, ‖g n‖ₑ ^ (2 : ℝ) ∂Measure.count
      ≤ ENNReal.ofReal (ε * (J : ℝ)) * ∫⁻ n, ‖g n‖ₑ ^ (2 : ℝ) ∂Measure.count :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hkey) _

/-- **The `o(J)` oscillation statement follows from the sublinear bound.** -/
theorem oscillation_statement_of_sublinear (h : SublinearOscillationStatement) :
    Submission.BourgainPlan.OscillationStatement := by
  intro P hP ρ hρ ε hε
  exact oscillation_sublinear_form P ρ (h P hP ρ hρ) ε hε

end Work.BourgainPlan.Oscillation
