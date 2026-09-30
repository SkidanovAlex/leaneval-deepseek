import Mathlib
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.ebound_defs
import Submission.Work.BMF.mr_direct.card_diff_natIcc_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The merged-coefficient `L²` bound on the range-extension error

The merged coefficient `ebD b c K P Q X` is supported (via `hrange`) on the two wings of the
slightly enlarged window `[X e^{-1/K}, 2 X e^{1/K}]` that lie outside `[X, 2X]`.  Since each
merged coefficient is bounded by `1` pointwise, the weighted sum
`Σ ‖ebD n‖² / n²` is at most `card(wings) · e²/X²`, and the two wings contain only
`O(X/K)` integers.  This gives the crude estimate `(8 X / K + 8) e² / X²`.

* `ebD_eq_zero_of_mem_natIcc` — `ebD` vanishes on the middle window `[X, 2X]`;
* `ebD_term_le_aux` — the per-term bound `‖ebD n‖²/n² ≤ e²/X²`;
* `ebD_sum_div_sq_le` — the assembled estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.BMF.mr_direct

open scoped BigOperators

noncomputable section

/-- On the middle window `[X, 2X]` the merged coefficient `ebD` vanishes: every index of the
underlying pair set `pSetB` has merged frequency `ebnn i ∉ [X, 2X]`, so the fibre over a point
of `[X, 2X]` is empty. -/
lemma ebD_eq_zero_of_mem_natIcc (b c : ℕ → ℂ) (K P Q X : ℝ)
    (hrange : ∀ i ∈ Work.BMF.mrDirect.pSetB K P Q X,
      Work.BMF.mr_direct.ebnn i ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)) ∧
        Work.BMF.mr_direct.ebnn i ∉ Work.BMF.natIcc X (2 * X))
    {n : ℕ} (hn : n ∈ Work.BMF.natIcc X (2 * X)) :
    Work.BMF.mr_direct.ebD b c K P Q X n = 0 := by
  have hempty : Work.BMF.mr_direct.ebFiber K P Q X n = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi heq
    have h2 := (hrange i hi).2
    rw [heq] at h2
    exact h2 hn
  simp [Work.BMF.mr_direct.ebD, hempty]

/-- Per-term bound: for every integer `n` of the enlarged window
`[X e^{-1/K}, 2 X e^{1/K}]` one has `‖ebD n‖² / n² ≤ e² / X²`, since `n ≥ X e^{-1/K}` and
`‖ebD n‖² ≤ 1`. -/
lemma ebD_term_le_aux (b c : ℕ → ℂ) (K P Q X : ℝ) (hX : 1 ≤ X) (hK : 1 ≤ K)
    (hnorm : ∀ n, ‖Work.BMF.mr_direct.ebD b c K P Q X n‖ ^ 2 ≤ 1) :
    ∀ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
      ‖Work.BMF.mr_direct.ebD b c K P Q X n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Real.exp 2 / X ^ 2 := by
  intro n hn
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hApos : 0 < X * Real.exp (-(1 / K)) := by positivity
  have hb : (0 : ℝ) ≤ 2 * X * Real.exp (1 / K) := by positivity
  have hn_ge : X * Real.exp (-(1 / K)) ≤ (n : ℝ) :=
    ((Work.BMF.mrDirect.mem_natIcc hb).mp hn).1
  have hsqq : (X * Real.exp (-(1 / K))) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ hApos.le hn_ge 2
  have h1 : ‖Work.BMF.mr_direct.ebD b c K P Q X n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (hnorm n) (by positivity)
  have h2 : 1 / (n : ℝ) ^ 2 ≤ 1 / (X * Real.exp (-(1 / K))) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hApos 2) hsqq
  have h3 : 1 / (X * Real.exp (-(1 / K))) ^ 2 = Real.exp (2 / K) / X ^ 2 := by
    have hexp : (Real.exp (-(1 / K))) ^ 2 = Real.exp (-(2 / K)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, hexp, Real.exp_neg]
    field_simp
  have h4 : Real.exp (2 / K) / X ^ 2 ≤ Real.exp 2 / X ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hKpos]
    nlinarith [hK]
  linarith [h1, h2, h3, h4]

theorem ebD_sum_div_sq_le (b c : ℕ → ℂ) (K P Q X : ℝ) (hX : 1 ≤ X) (hK : 1 ≤ K)
    (hnorm : ∀ n, ‖Work.BMF.mr_direct.ebD b c K P Q X n‖ ^ 2 ≤ 1)
    (hrange : ∀ i ∈ Work.BMF.mrDirect.pSetB K P Q X,
      Work.BMF.mr_direct.ebnn i ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)) ∧
        Work.BMF.mr_direct.ebnn i ∉ Work.BMF.natIcc X (2 * X)) :
    (∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
        ‖Work.BMF.mr_direct.ebD b c K P Q X n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ (8 * X / K + 8) * Real.exp 2 / X ^ 2 := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hterm0 := ebD_term_le_aux b c K P Q X hX hK hnorm
  set L : Finset ℕ := Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)) with hL
  set M : Finset ℕ := Work.BMF.natIcc X (2 * X) with hM
  -- the middle window sits inside the enlarged window
  have hsub : M ⊆ L := by
    rw [hM, hL]
    apply Work.BMF.mrDirect.natIcc_mono
    · exact mul_le_of_le_one_right hXpos.le (Real.exp_le_one_iff.mpr (by
        have : (0 : ℝ) ≤ 1 / K := by positivity
        linarith))
    · exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
  -- the summand vanishes on the middle window
  have hmidzero : ∀ n ∈ M, ‖Work.BMF.mr_direct.ebD b c K P Q X n‖ ^ 2 / (n : ℝ) ^ 2 = 0 := by
    intro n hn
    have hn' : n ∈ Work.BMF.natIcc X (2 * X) := by rw [hM] at hn; exact hn
    have h := ebD_eq_zero_of_mem_natIcc b c K P Q X hrange hn'
    simp [h]
  -- restrict the sum to the two wings
  have hsplit : (∑ n ∈ L, ‖Work.BMF.mr_direct.ebD b c K P Q X n‖ ^ 2 / (n : ℝ) ^ 2)
      = ∑ n ∈ L \ M, ‖Work.BMF.mr_direct.ebD b c K P Q X n‖ ^ 2 / (n : ℝ) ^ 2 := by
    have h := Finset.sum_sdiff hsub
      (f := fun n => ‖Work.BMF.mr_direct.ebD b c K P Q X n‖ ^ 2 / (n : ℝ) ^ 2)
    rw [Finset.sum_eq_zero hmidzero, add_zero] at h
    exact h.symm
  rw [hsplit]
  calc ∑ n ∈ L \ M, ‖Work.BMF.mr_direct.ebD b c K P Q X n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ (L \ M).card • (Real.exp 2 / X ^ 2) :=
        Finset.sum_le_card_nsmul (L \ M) _ (Real.exp 2 / X ^ 2)
          (fun n hn => hterm0 n (Finset.mem_sdiff.mp hn).1)
    _ = ((L \ M).card : ℝ) * (Real.exp 2 / X ^ 2) := by rw [nsmul_eq_mul]
    _ ≤ (8 * X / K + 8) * (Real.exp 2 / X ^ 2) := by
        apply mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h := card_diff_natIcc_le X K hX hK
        have : L \ M = (Work.BMF.natIcc (X * Real.exp (-(1 / K)))
              (2 * X * Real.exp (1 / K))).filter
              (fun n => n ∉ Work.BMF.natIcc X (2 * X)) := by
          rw [hL, hM, Finset.sdiff_eq_filter]
        rw [this]; exact h
    _ = (8 * X / K + 8) * Real.exp 2 / X ^ 2 := by ring

end

end Work.BMF.mr_direct
