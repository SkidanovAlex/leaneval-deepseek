import Mathlib
import Submission.Work.NN.Core.DbarCnPertAux
import Submission.Work.NN.Ratio.Setup
import Submission.Work.NN.Core.famMul_holderNorm_bound
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Core

/-- **A cutoff for the Beltrami coefficient.**  For `0 < α < 1` and radii `ρ' < ρ` (componentwise)
there is a constant `C > 0` and, for every perturbation `A` with `C^{0,α}`-small coefficients on
`polydisc 0 ρ` (of size `ε`), a function `χ` which is `1` on the closed polydisc of radius `ρ'`,
vanishes outside `polydisc 0 ρ`, and such that the products `χ · betaCoef A i j` have
`C^{0,α}`-norm on all of `ℂⁿ` bounded by `C ε`. -/
theorem exists_betaCut_small {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ'0 : ∀ j, 0 < ρ' j) (hρ' : ∀ j, ρ' j < ρ j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (ε : ℝ), 0 ≤ ε →
        (∀ i j, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
            (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
        ∃ χ : Work.NN.Core.Cn n → ℂ,
          (∀ z, (∀ i, ‖z i‖ ≤ ρ' i) → χ z = 1) ∧
          (∀ z, χ z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) ∧
          (∀ i j, Work.CR.Flat.holderNorm 0 α
              (fun z => χ z * Work.NN.Core.betaCoef A i j z) Set.univ
            ≤ ENNReal.ofReal (C * ε)) := by
  classical
  -- geometric data: a polydisc strictly between `ρ'` and `ρ`
  obtain ⟨b, hρ'b, hbρ⟩ : ∃ b : Fin n → ℝ, (∀ j, ρ' j < b j) ∧ (∀ j, b j < ρ j) :=
    ⟨fun j => (ρ' j + ρ j) / 2, fun j => by linarith [hρ' j], fun j => by linarith [hρ' j]⟩
  have hρ'nn : ∀ j, 0 ≤ ρ' j := fun j => le_of_lt (hρ'0 j)
  -- boundedness radius for the polydisc `polydisc 0 ρ`
  set R : ℝ := ∑ j, ρ j with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef]; exact Finset.sum_nonneg fun j _ => le_of_lt (hρ0 j)
  have hbdd : ∀ x ∈ Work.CR.Flat.polydisc 0 ρ, ‖x‖ ≤ R := by
    intro x hx
    rw [pi_norm_le_iff_of_nonneg hR0]
    intro j
    have h1 : ‖x j‖ ≤ ρ j := le_of_lt (by simpa using hx j)
    rw [hRdef]
    exact le_trans h1 (Finset.single_le_sum (fun i _ => le_of_lt (hρ0 i)) (Finset.mem_univ j))
  -- the norm of the cutoff on the polydisc is finite
  let Nχ : ℝ≥0∞ :=
    Work.CR.Flat.holderNorm 0 α (Work.NN.Ratio.polydiscCut ρ' b) (Work.CR.Flat.polydisc 0 ρ)
  have hχne : Nχ ≠ ⊤ :=
    Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded (Ω := Work.CR.Flat.polydisc 0 ρ)
      (Work.CR.Flat.isOpen_polydisc 0 ρ) hbdd hα0 (le_of_lt hα1)
      ((Work.NN.Ratio.contDiff_polydiscCut ρ' b).of_le (by exact_mod_cast le_top))
  have hNχle : Nχ ≤ ENNReal.ofReal (Nχ.toReal + 1) := by
    calc Nχ = ENNReal.ofReal Nχ.toReal := (ENNReal.ofReal_toReal hχne).symm
      _ ≤ ENNReal.ofReal (Nχ.toReal + 1) :=
          ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by norm_num))
  refine ⟨Nχ.toReal + 1, ?_, ?_⟩
  · have := ENNReal.toReal_nonneg (a := Nχ); linarith
  · intro A ε hε hA
    -- the constant `‖-(I/2)‖ = 1/2`
    have hc : ‖(-(Complex.I / 2) : ℂ)‖ = 1 / 2 := by
      rw [norm_neg, norm_div, Complex.norm_I]
      norm_num
    -- the `C^{0,α}`-norm of each Beltrami coefficient is at most `ε`
    have hβ : ∀ i j, Work.CR.Flat.holderNorm 0 α (betaCoef A i j) (Work.CR.Flat.polydisc 0 ρ)
        ≤ ENNReal.ofReal ε := by
      intro i j
      have hsm := Work.NN.Core.BTheta.holderNorm_zero_const_mul_le (α := α) (-(Complex.I / 2))
        (fun z => (A z (Pi.single i (1 : ℂ))) j) (Work.CR.Flat.polydisc 0 ρ)
      calc Work.CR.Flat.holderNorm 0 α (betaCoef A i j) (Work.CR.Flat.polydisc 0 ρ)
          = Work.CR.Flat.holderNorm 0 α
              (fun z => (-(Complex.I / 2)) *
                ((fun z => (A z (Pi.single i (1 : ℂ))) j) z)) (Work.CR.Flat.polydisc 0 ρ) := rfl
        _ ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal ε := by
              rw [← hc]
              exact hsm.trans (mul_le_mul' le_rfl (hA i j))
        _ ≤ ENNReal.ofReal ε := by
              rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
              exact ENNReal.ofReal_le_ofReal (by linarith)
    refine ⟨Work.NN.Ratio.polydiscCut ρ' b, ?_, ?_, ?_⟩
    · intro z hz
      exact Work.NN.Ratio.polydiscCut_eq_one hρ'nn hρ'b hz
    · intro z hz j
      have h1 := Work.NN.Ratio.polydiscCut_ne_zero_imp hρ'nn hρ'b hz j
      simpa using lt_of_lt_of_le h1 (le_of_lt (hbρ j))
    · intro i j
      -- the product vanishes on the closed complement of `polydisc 0 b`
      have hvan : ∀ z : Work.NN.Core.Cn n,
          (∃ k, b k ≤ ‖z k - (0 : Work.NN.Core.Cn n) k‖) →
          (fun z => Work.NN.Ratio.polydiscCut ρ' b z * betaCoef A i j z) z = 0 := by
        intro z hz
        obtain ⟨k, hk⟩ := hz
        have hk' : b k ≤ ‖z k‖ := by simpa using hk
        show Work.NN.Ratio.polydiscCut ρ' b z * betaCoef A i j z = 0
        rw [Work.NN.Ratio.polydiscCut_eq_zero hρ'nn hρ'b ⟨k, hk'⟩, zero_mul]
      calc Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Ratio.polydiscCut ρ' b z * betaCoef A i j z) Set.univ
          ≤ Work.CR.Flat.holderNorm 0 α
              (fun z => Work.NN.Ratio.polydiscCut ρ' b z * betaCoef A i j z)
              (Work.CR.Flat.polydisc 0 ρ) :=
            Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
              (c := 0) hbρ (le_of_lt hα0) hvan
        _ ≤ Work.CR.Flat.holderNorm 0 α (Work.NN.Ratio.polydiscCut ρ' b)
              (Work.CR.Flat.polydisc 0 ρ)
            * Work.CR.Flat.holderNorm 0 α (betaCoef A i j) (Work.CR.Flat.polydisc 0 ρ) :=
            Work.NN.Core.holderNorm_zero_mul_le _ _ _
        _ ≤ Nχ * ENNReal.ofReal ε := mul_le_mul' le_rfl (hβ i j)
        _ ≤ ENNReal.ofReal (Nχ.toReal + 1) * ENNReal.ofReal ε := mul_le_mul' hNχle le_rfl
        _ = ENNReal.ofReal ((Nχ.toReal + 1) * ε) := by
            rw [ENNReal.ofReal_mul (by have := ENNReal.toReal_nonneg (a := Nχ); linarith)]

end Work.NN.Core
