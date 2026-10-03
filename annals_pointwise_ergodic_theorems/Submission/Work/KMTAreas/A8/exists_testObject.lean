/-
# A test object for the clamped variational norm (area A8)

This module proves `Work.KMTAreas.A8.exists_testObject`: for every `r ≥ 1`, every `K` and every
sequence `a : ℕ → ℂ` there is a finitely supported coefficient vector `Ψ K a` such that the pairing
`pair · (Ψ K a)` is a contraction for the clamped variational norm `vNormK r K` and realises
`vNormK r K a` at `a`:

  `∀ x, ‖pair x (Ψ K a)‖ ≤ vNormK r K x`,   `pair a (Ψ K a) = vNormK r K a`.

It is the "linearisation" of the clamped variational norm: `vNormK r K = supK K + varK r K` is the
sum of a norm (`supK`, the sup norm of the first `K+1` coordinates) and a seminorm (`varK`, the
maximal `ℓʳ`-norm of the increments along a monotone chain of indices `≤ K`), so it is a norm on
the finite-dimensional space of the first `K+1` coordinates, and a norming functional exists.

The two summands are treated separately.

* `exists_supK_testObject`: choose an index `n₀ ≤ K` with `‖a n₀‖ = supK K a` and take the
  functional `x ↦ x n₀ · c` where `‖c‖ ≤ 1` and `a n₀ · c = ‖a n₀‖` (`exists_mul_eq_norm`).
* `exists_varK_testObject`: choose a chain realising `varK r K a`, and on the increment vector `v`
  of `a` along that chain apply the finite `ℓʳ`-duality lemma `exists_dual_lp` (Hölder), producing
  coefficients `c` with `∑ vᵢ cᵢ = ‖v‖ᵣ` and `‖∑ xᵢ cᵢ‖ ≤ ‖x‖ᵣ`; the Finsupp
  `∑ᵢ (single (w (i+1)) cᵢ + single (w i) (−cᵢ))` then has exactly the required pairing
  `∑ᵢ (x (w (i+1)) − x (w i)) cᵢ`.

The sum of the two functionals is the test object.
-/
import Mathlib
import Submission.Work.KMTAreas.A8Defs
import Submission.Work.KMTAreas.A8.exists_dual_lp

set_option autoImplicit false

namespace Work.KMTAreas.A8

open scoped BigOperators

noncomputable section

/-! ### Linearity of the pairing -/

lemma pair_add (x : ℕ → ℂ) (l₁ l₂ : ℕ →₀ ℂ) :
    Work.KMTAreas.pair x (l₁ + l₂) = Work.KMTAreas.pair x l₁ + Work.KMTAreas.pair x l₂ := by
  rw [Work.KMTAreas.pair, Work.KMTAreas.pair, Work.KMTAreas.pair]
  exact Finsupp.sum_add_index (fun a _ => mul_zero _) (fun a _ b₁ b₂ => mul_add _ _ _)

lemma pair_sum_univ {ι : Type*} [Fintype ι] (x : ℕ → ℂ) (g : ι → ℕ →₀ ℂ) :
    Work.KMTAreas.pair x (∑ i, g i) = ∑ i, Work.KMTAreas.pair x (g i) := by
  rw [Work.KMTAreas.pair]
  rw [← Finsupp.sum_finsetSum_index (h := fun n c => x n * c)]
  · simp [Work.KMTAreas.pair]
  · intro a
    simp
  · intro a b₁ b₂
    ring

lemma pair_single (x : ℕ → ℂ) (n : ℕ) (c : ℂ) :
    Work.KMTAreas.pair x (Finsupp.single n c) = x n * c := by
  rw [Work.KMTAreas.pair, Finsupp.sum_single_index]
  simp

/-! ### A single-index functional realising `‖z‖` -/

/-- For every `z : ℂ` there is `c` with `‖c‖ ≤ 1` and `z * c = ‖z‖` (as a complex number):
take `c = star z / ‖z‖`. -/
lemma exists_mul_eq_norm (z : ℂ) :
    ∃ c : ℂ, ‖c‖ ≤ 1 ∧ z * c = ((‖z‖ : ℝ) : ℂ) := by
  by_cases h : z = 0
  · exact ⟨0, by simp, by simp [h]⟩
  · have hz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h
    refine ⟨star z / ((‖z‖ : ℝ) : ℂ), ?_, ?_⟩
    · rw [norm_div, norm_star]
      simp [hz]
    · have hsq : z * star z = (((‖z‖ : ℝ) ^ 2 : ℝ) : ℂ) := by
        have h1 : star z * z = ((Complex.normSq z : ℝ) : ℂ) :=
          Complex.normSq_eq_conj_mul_self.symm
        rw [mul_comm, h1, Complex.normSq_eq_norm_sq]
      rw [← mul_div_assoc, hsq, ← Complex.ofReal_div]
      congr 1
      rw [pow_two, mul_div_cancel_left₀ _ hz]

/-! ### The `supK` part -/

/-- **The `supK` test object.**  There is a finitely supported coefficient vector whose pairing is
bounded by `supK K` and which realises `supK K a` at `a`. -/
lemma exists_supK_testObject (K : ℕ) (a : ℕ → ℂ) :
    ∃ l : ℕ →₀ ℂ,
      (∀ x : ℕ → ℂ, ‖Work.KMTAreas.pair x l‖ ≤ Work.KMTAreas.supK K x) ∧
      Work.KMTAreas.pair a l = ((Work.KMTAreas.supK K a : ℝ) : ℂ) := by
  have hattain : ∃ n ∈ Finset.range (K + 1), Work.KMTAreas.supK K a = ‖a n‖ := by
    rw [Work.KMTAreas.supK]
    exact Finset.exists_mem_eq_sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩ fun n => ‖a n‖
  obtain ⟨n₀, hn₀, hsup⟩ := hattain
  obtain ⟨c₀, hc₀, hc₀'⟩ := exists_mul_eq_norm (a n₀)
  refine ⟨Finsupp.single n₀ c₀, ?_, ?_⟩
  · intro x
    rw [pair_single]
    calc ‖x n₀ * c₀‖ = ‖x n₀‖ * ‖c₀‖ := norm_mul _ _
      _ ≤ ‖x n₀‖ * 1 := mul_le_mul_of_nonneg_left hc₀ (norm_nonneg _)
      _ = ‖x n₀‖ := mul_one _
      _ ≤ Work.KMTAreas.supK K x := by
          rw [Work.KMTAreas.supK]
          exact Finset.le_sup' (f := fun n => ‖x n‖) hn₀
  · rw [pair_single, hc₀', ← hsup]

/-! ### The `varK` part -/

/-- **The `varK` test object.**  There is a finitely supported coefficient vector whose pairing is
bounded by `varK r K` and which realises `varK r K a` at `a`. -/
lemma exists_varK_testObject (r : NNReal) (hr : 1 ≤ r) (K : ℕ) (a : ℕ → ℂ) :
    ∃ l : ℕ →₀ ℂ,
      (∀ x : ℕ → ℂ, ‖Work.KMTAreas.pair x l‖ ≤ Work.KMTAreas.varK r K x) ∧
      Work.KMTAreas.pair a l = ((Work.KMTAreas.varK r K a : ℝ) : ℂ) := by
  have hattain : ∃ p ∈ (Finset.univ : Finset (Work.KMTAreas.Chain K)),
      Work.KMTAreas.varK r K a
        = (∑ i : Fin p.1.1, ‖a ↑(p.2.1 i.succ) - a ↑(p.2.1 i.castSucc)‖ ^ (r : ℝ))
            ^ (1 / (r : ℝ)) := by
    rw [Work.KMTAreas.varK]
    exact Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun p : Work.KMTAreas.Chain K =>
        (∑ i : Fin p.1.1, ‖a ↑(p.2.1 i.succ) - a ↑(p.2.1 i.castSucc)‖ ^ (r : ℝ))
          ^ (1 / (r : ℝ)))
  obtain ⟨⟨J, w, hw⟩, -, hp₀⟩ := hattain
  obtain ⟨c, hc_eq, hc_bd⟩ :=
    exists_dual_lp r hr (fun i : Fin J.1 => a ↑(w i.succ) - a ↑(w i.castSucc))
  have hpair : ∀ x : ℕ → ℂ,
      Work.KMTAreas.pair x (∑ i : Fin J.1,
          (Finsupp.single (w i.succ).val (c i) + Finsupp.single (w i.castSucc).val (- c i)))
        = ∑ i : Fin J.1, (x ↑(w i.succ) - x ↑(w i.castSucc)) * c i := by
    intro x
    rw [pair_sum_univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pair_add, pair_single, pair_single]
    ring
  refine ⟨∑ i : Fin J.1,
      (Finsupp.single (w i.succ).val (c i) + Finsupp.single (w i.castSucc).val (- c i)), ?_, ?_⟩
  · intro x
    rw [hpair x]
    refine (hc_bd fun i => x ↑(w i.succ) - x ↑(w i.castSucc)).trans ?_
    rw [Work.KMTAreas.varK]
    exact Finset.le_sup'
      (f := fun p : Work.KMTAreas.Chain K =>
        (∑ i : Fin p.1.1, ‖x ↑(p.2.1 i.succ) - x ↑(p.2.1 i.castSucc)‖ ^ (r : ℝ))
          ^ (1 / (r : ℝ)))
      (Finset.mem_univ (⟨J, ⟨w, hw⟩⟩ : Work.KMTAreas.Chain K))
  · rw [hpair a, hc_eq, hp₀]

/-! ### The test object -/

theorem exists_testObject (r : NNReal) (hr : 1 ≤ r) :
    ∃ Ψ : ℕ → (ℕ → ℂ) → (ℕ →₀ ℂ),
      (∀ K a a', ‖Work.KMTAreas.pair a' (Ψ K a)‖ ≤ Work.KMTAreas.vNormK r K a') ∧
      (∀ K a, Work.KMTAreas.pair a (Ψ K a) = (Work.KMTAreas.vNormK r K a : ℂ)) := by
  have hex : ∀ K (a : ℕ → ℂ), ∃ l : ℕ →₀ ℂ,
      (∀ x : ℕ → ℂ, ‖Work.KMTAreas.pair x l‖ ≤ Work.KMTAreas.vNormK r K x) ∧
      Work.KMTAreas.pair a l = ((Work.KMTAreas.vNormK r K a : ℝ) : ℂ) := by
    intro K a
    obtain ⟨l₁, h₁, h₁'⟩ := exists_supK_testObject K a
    obtain ⟨l₂, h₂, h₂'⟩ := exists_varK_testObject r hr K a
    refine ⟨l₁ + l₂, ?_, ?_⟩
    · intro x
      rw [pair_add]
      calc ‖Work.KMTAreas.pair x l₁ + Work.KMTAreas.pair x l₂‖
          ≤ ‖Work.KMTAreas.pair x l₁‖ + ‖Work.KMTAreas.pair x l₂‖ := norm_add_le _ _
        _ ≤ Work.KMTAreas.supK K x + Work.KMTAreas.varK r K x := add_le_add (h₁ x) (h₂ x)
        _ = Work.KMTAreas.vNormK r K x := rfl
    · rw [pair_add, h₁', h₂']
      exact (Complex.ofReal_add _ _).symm
  exact ⟨fun K a => Classical.choose (hex K a), fun K a x => (Classical.choose_spec (hex K a)).1 x,
    fun K a => (Classical.choose_spec (hex K a)).2⟩

end

end Work.KMTAreas.A8
