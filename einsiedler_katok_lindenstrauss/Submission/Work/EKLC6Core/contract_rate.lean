import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.box_facts
import Submission.Work.EKLC6Core.shape_pastSig_eq
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLComp.FlowerDefs
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.contract_rate` — the exponential contraction rate of `aDiag t` on `U`

For a horospherical subgroup `U ≤ SL₃(ℝ)` contracted by `aDiag t`, the conjugation
`u ↦ aDiag t ^ n · u · (aDiag t ^ n)⁻¹` shrinks the entrywise ball `Uball U ρ` into
`Uball U (ρ * λⁿ)` with a constant `λ ∈ (0,1)` depending only on `t`.

This refines `Work.EKLC6Core.uniform_contraction_horo` (which only says that every ball shrinks
into every other ball *eventually*) to the *exponential* statement needed to compare the
contraction of the diagonal flow with the decay of the thin-boundary shells: the shell argument
produces a margin of size `c μⁿ` with `μ ∈ (λ, 1)`, and the nesting of the plaque constraints
follows precisely because `λⁿ ≪ μⁿ`.

The mathematical content is the entry formula `(aDiag t ^ n · u · (aDiag t ^ n)⁻¹)ᵢⱼ
= e^{n (tᵢ - tⱼ)} uᵢⱼ` (`boxi_conj_pow_apply`) together with the entry pattern
`uᵢⱼ = δᵢⱼ` whenever `t i ≥ t j` (`box_facts_entry_eq_one`).
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The contraction rate of `aDiag t`.**  If some direction `t i < t j` is strictly contracted
then there is `λ ∈ (0,1)` dominating all the contraction factors `e^{t i - t j}`; if there is no
such direction, any `λ ∈ (0,1)` does. -/
theorem exists_contract_rate (t : Fin 3 → ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ ∀ i j : Fin 3, t i < t j → Real.exp (t i - t j) ≤ lam := by
  classical
  set S : ℝ := (Finset.univ : Finset (Fin 3 × Fin 3)).sup' Finset.univ_nonempty
    (fun p : Fin 3 × Fin 3 => if t p.1 < t p.2 then Real.exp (t p.1 - t p.2) else 1 / 2) with hS
  have hSlt : S < 1 := by
    rw [hS]
    obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
      Finset.univ_nonempty
      (fun p : Fin 3 × Fin 3 => if t p.1 < t p.2 then Real.exp (t p.1 - t p.2) else 1 / 2)
    rw [hp]
    by_cases h : t p.1 < t p.2
    · rw [if_pos h]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    · rw [if_neg h]; norm_num
  refine ⟨max (1 / 2) S, lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    max_lt (by norm_num) hSlt, ?_⟩
  intro i j hij
  have hle : Real.exp (t i - t j) ≤ S := by
    rw [hS]
    calc Real.exp (t i - t j)
        = (if t i < t j then Real.exp (t i - t j) else 1 / 2) := by rw [if_pos hij]
      _ ≤ _ := Finset.le_sup' (fun p : Fin 3 × Fin 3 =>
            if t p.1 < t p.2 then Real.exp (t p.1 - t p.2) else 1 / 2) (Finset.mem_univ (i, j))
  exact le_trans hle (le_max_right _ _)

/-- Conjugation by a power of the diagonal flow preserves a horospherical subgroup. -/
theorem conj_pow_mem_U {U : Subgroup SL3} (hU : IsHoro U) {t : Fin 3 → ℝ} {u : SL3}
    (hu : u ∈ U) (n : ℕ) : aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ U := by
  induction n with
  | zero => simpa using hu
  | succ k ih =>
    rw [pow_succ']
    have key : aDiag t * aDiag t ^ k * u * (aDiag t * aDiag t ^ k)⁻¹
        = aDiag t * (aDiag t ^ k * u * (aDiag t ^ k)⁻¹) * (aDiag t)⁻¹ := by group
    rw [key]
    exact hU.2.1 t _ ih

/-- **The exponential contraction of the balls `Uball U ρ`.**  Conjugation by the `n`-th power of
`aDiag t` shrinks `Uball U ρ` into `Uball U (ρ λⁿ)`. -/
theorem conj_pow_mem_Uball {U : Subgroup SL3} {t : Fin 3 → ℝ} (hU : IsHoro U)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (nhds 1))
    {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : ∀ i j : Fin 3, t i < t j → Real.exp (t i - t j) ≤ lam)
    {ρ : ℝ} {u : SL3} (hu : u ∈ Work.EKLComp.Uball U ρ) (n : ℕ) :
    aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ Work.EKLComp.Uball U (ρ * lam ^ n) := by
  have hρ : 0 < ρ := lt_of_le_of_lt (abs_nonneg _) (hu.2 0 0)
  have hpos : 0 < ρ * lam ^ n := mul_pos hρ (pow_pos hlam0 n)
  refine ⟨conj_pow_mem_U hU hu.1 n, fun i j => ?_⟩
  rw [boxi_conj_pow_apply]
  by_cases h : t i < t j
  · have hij : i ≠ j := fun h' => by rw [h'] at h; exact lt_irrefl _ h
    have h0 : (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := Matrix.one_apply_ne hij
    have h2 : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| < ρ := by
      have hh := hu.2 i j
      rwa [h0, sub_zero] at hh
    have h1 : Real.exp ((n : ℝ) * (t i - t j)) ≤ lam ^ n := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_nonneg _) (hlam i j h) n
    rw [h0, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
    have step1 : Real.exp ((n : ℝ) * (t i - t j)) * |(u : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ lam ^ n * |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
      mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have step2 : lam ^ n * |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| < lam ^ n * ρ :=
      mul_lt_mul_of_pos_left h2 (pow_pos hlam0 n)
    calc Real.exp ((n : ℝ) * (t i - t j)) * |(u : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ lam ^ n * |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| := step1
      _ < lam ^ n * ρ := step2
      _ = ρ * lam ^ n := by ring
  · push Not at h
    have hzero : (u : Matrix (Fin 3) (Fin 3) ℝ) i j
        = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
      simpa using box_facts_entry_eq_one hcontr hu.1 h
    rw [hzero]
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.one_apply_eq, sub_self, mul_zero, Real.exp_zero, one_mul, sub_self, abs_zero]
      exact hpos
    · have h1 : (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := Matrix.one_apply_ne hij
      rw [h1, mul_zero, sub_zero, abs_zero]
      exact hpos

end Work.EKLC6Core
