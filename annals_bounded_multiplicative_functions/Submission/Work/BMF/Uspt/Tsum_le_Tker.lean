import Mathlib
import Submission.Work.BMF.Uspt.base
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.one_le_kern
import Submission.Work.BMF.kern_summable
import Submission.Work.BMF.tsum_pi_prod
import Submission.Work.BMF.TentDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The box sum `Tsum` is dominated by the kernel sum `Tker`

Ford's Lemma 5.1 replaces the weighted `2s`-th moment of the inner `b`-sum

  `Tsum r s M₁ M₂ k γ ε = Σ_{c ∈ Cbox r M₁ k} ‖Xsum k M₂ γ ε c‖ ^ (2s)`

over the *finite* frequency box `Cbox r M₁ k = ∏_j [1, r M₁^{j+1}]` by the sum

  `Tker r s M₁ M₂ k γ ε = Σ'_c (∏_j kern (r M₁^{j+1}) (c_j)) · ‖Xsum k M₂ γ ε c‖ ^ (2s)`

over the whole lattice `Fin k → ℤ`, where `kern K` is the Fourier kernel
`kern K c = (π²K/2) · tentCoeff (1/(2K)) c`.

The point of the passage is that `kern K c ≥ 1` on the box frequencies (`one_le_kern`) and
`kern K ≥ 0` everywhere, while `kern K` is summable over `ℤ` (`kern_summable`).  Hence the
lattice sum `Tker` dominates the box sum term by term: this is the content of
`Tsum_le_Tker`.
-/

namespace Work.BMF.Uspt

open Finset
open scoped BigOperators

noncomputable section

/-- The Ford kernel `kern K` is non-negative for every `K` and every frequency `c`. -/
lemma kern_nonneg (K : ℕ) (c : ℤ) : 0 ≤ Work.BMF.kern K c := by
  unfold Work.BMF.kern
  exact mul_nonneg (by positivity) (Work.BMF.tentCoeff_nonneg (by positivity) c)

/-- Membership in the frequency box `Cbox r M₁ k`: the coordinates of `c` lie in the
intervals `[1, r M₁^{j+1}]`. -/
lemma mem_Cbox_iff {r M₁ k : ℕ} {c : Fin k → ℤ} :
    c ∈ Work.BMF.Cbox r M₁ k ↔
      ∀ j : Fin k, (1 : ℤ) ≤ c j ∧ c j ≤ ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℤ) := by
  rw [Work.BMF.Cbox, Finset.mem_image]
  constructor
  · rintro ⟨f, hf, hfe⟩ j
    rw [Finset.mem_pi] at hf
    have hmem := hf j (Finset.mem_univ j)
    rw [Finset.mem_Icc] at hmem
    have hcj : c j = ((f j (Finset.mem_univ j) : ℕ) : ℤ) := by rw [← hfe]
    rw [hcj]
    exact_mod_cast hmem
  · intro h
    refine ⟨fun j _ => (c j).toNat, ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro j _
      rw [Finset.mem_Icc]
      have h1 := (h j).1
      have h2 := (h j).2
      constructor <;> omega
    · funext j
      simp only
      exact Int.toNat_of_nonneg (le_trans (by norm_num) (h j).1)

/-- The inner `b`-sum is bounded by the sum of the moduli of the coefficients. -/
lemma norm_Xsum_le (k M₂ : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) (c : Fin k → ℤ) :
    ‖Work.BMF.Xsum k M₂ γ ε c‖ ≤ ∑ b ∈ Finset.Icc 1 M₂, ‖ε b‖ := by
  rw [Work.BMF.Xsum]
  calc ‖∑ b ∈ Finset.Icc 1 M₂,
          ε b * Work.BMF.eZ (∑ j : Fin k, γ j * (b : ℝ) ^ ((j : ℕ) + 1) * (c j : ℝ))‖
      ≤ ∑ b ∈ Finset.Icc 1 M₂,
          ‖ε b * Work.BMF.eZ (∑ j : Fin k, γ j * (b : ℝ) ^ ((j : ℕ) + 1) * (c j : ℝ))‖ :=
        norm_sum_le _ _
    _ = ∑ b ∈ Finset.Icc 1 M₂, ‖ε b‖ := by
        apply Finset.sum_congr rfl
        intro b _
        rw [norm_mul, Work.BMF.Uspt.eZ_norm, mul_one]

/-- The product of the kernels over the frequency lattice `Fin k → ℤ` is summable. -/
lemma summable_prod_kern (r M₁ k : ℕ) (hr : 1 ≤ r) (hM₁ : 1 ≤ M₁) :
    Summable (fun c : Fin k → ℤ =>
      ∏ j : Fin k, Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) (c j)) := by
  have hKj : ∀ j : Fin k, 1 ≤ r * M₁ ^ ((j : ℕ) + 1) := by
    intro j
    calc 1 = 1 * 1 := by ring
      _ ≤ r * M₁ ^ ((j : ℕ) + 1) := Nat.mul_le_mul hr (one_le_pow₀ hM₁)
  have h1 : ∀ j : Fin k,
      HasSum (fun c : ℤ => ((Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) c : ℝ) : ℂ))
        (∑' c, ((Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) c : ℝ) : ℂ)) :=
    fun j => ((Complex.summable_ofReal).mpr (Work.BMF.kern_summable _ (hKj j))).hasSum
  have h2 : ∀ j : Fin k,
      Summable (fun c : ℤ =>
        ‖((Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) c : ℝ) : ℂ)‖) := by
    intro j
    refine (Work.BMF.kern_summable _ (hKj j)).congr (fun c => ?_)
    rw [show ‖((Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) c : ℝ) : ℂ)‖
          = |Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) c| by simp,
      abs_of_nonneg (kern_nonneg _ _)]
  obtain ⟨hsumm, _⟩ := Work.BMF.tsum_pi_prod h1 h2
  refine hsumm.congr (fun c => ?_)
  apply Finset.prod_congr rfl
  intro j _
  rw [show ‖((Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) (c j) : ℝ) : ℂ)‖
        = |Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) (c j)| by simp,
    abs_of_nonneg (kern_nonneg _ _)]

theorem Tsum_le_Tker (r s M₁ M₂ k : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (γ : Fin k → ℝ) (ε : ℕ → ℂ) :
    Work.BMF.Tsum r s M₁ M₂ k γ ε ≤ Work.BMF.Tker r s M₁ M₂ k γ ε := by
  have _ : 1 ≤ s := hs
  have _ : 1 ≤ M₂ := hM₂
  have hKj : ∀ j : Fin k, 1 ≤ r * M₁ ^ ((j : ℕ) + 1) := by
    intro j
    calc 1 = 1 * 1 := by ring
      _ ≤ r * M₁ ^ ((j : ℕ) + 1) := Nat.mul_le_mul hr (one_le_pow₀ hM₁)
  have hprod := summable_prod_kern r M₁ k hr hM₁
  have hf_summ : Summable (fun c : Fin k → ℤ =>
      (∏ j : Fin k, Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) (c j))
        * ‖Work.BMF.Xsum k M₂ γ ε c‖ ^ (2 * s)) := by
    refine Summable.of_nonneg_of_le
      (f := fun c : Fin k → ℤ =>
        (∏ j : Fin k, Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) (c j))
          * (∑ b ∈ Finset.Icc 1 M₂, ‖ε b‖) ^ (2 * s)) ?_ ?_ ?_
    · intro c
      exact mul_nonneg (Finset.prod_nonneg (fun j _ => kern_nonneg _ _))
        (pow_nonneg (norm_nonneg _) _)
    · intro c
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_Xsum_le k M₂ γ ε c) (2 * s))
        (Finset.prod_nonneg (fun j _ => kern_nonneg _ _))
    · exact hprod.mul_right _
  calc Work.BMF.Tsum r s M₁ M₂ k γ ε
      = ∑ c ∈ Work.BMF.Cbox r M₁ k, ‖Work.BMF.Xsum k M₂ γ ε c‖ ^ (2 * s) := rfl
    _ ≤ ∑ c ∈ Work.BMF.Cbox r M₁ k,
          (∏ j : Fin k, Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) (c j))
            * ‖Work.BMF.Xsum k M₂ γ ε c‖ ^ (2 * s) := by
        apply Finset.sum_le_sum
        intro c hc
        have hk1 : 1 ≤ ∏ j : Fin k, Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) (c j) := by
          apply Finset.one_le_prod₀
          intro j _
          obtain ⟨h1j, h2j⟩ := mem_Cbox_iff.mp hc j
          have hc1 : 1 ≤ (c j).toNat := by omega
          have hc2 : (c j).toNat ≤ r * M₁ ^ ((j : ℕ) + 1) := by
            rw [Int.toNat_le]; omega
          have h := one_le_kern (r * M₁ ^ ((j : ℕ) + 1)) (hKj j) (c := (c j).toNat) hc1 hc2
          rwa [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ c j)] at h
        calc ‖Work.BMF.Xsum k M₂ γ ε c‖ ^ (2 * s)
            = 1 * ‖Work.BMF.Xsum k M₂ γ ε c‖ ^ (2 * s) := (one_mul _).symm
          _ ≤ (∏ j : Fin k, Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) (c j))
                * ‖Work.BMF.Xsum k M₂ γ ε c‖ ^ (2 * s) :=
              mul_le_mul_of_nonneg_right hk1 (pow_nonneg (norm_nonneg _) _)
    _ ≤ ∑' c : Fin k → ℤ,
          (∏ j : Fin k, Work.BMF.kern (r * M₁ ^ ((j : ℕ) + 1)) (c j))
            * ‖Work.BMF.Xsum k M₂ γ ε c‖ ^ (2 * s) :=
        hf_summ.sum_le_tsum _
          (fun c _ => mul_nonneg (Finset.prod_nonneg (fun j _ => kern_nonneg _ _))
            (pow_nonneg (norm_nonneg _) _))
    _ = Work.BMF.Tker r s M₁ M₂ k γ ε := rfl

end

end Work.BMF.Uspt
