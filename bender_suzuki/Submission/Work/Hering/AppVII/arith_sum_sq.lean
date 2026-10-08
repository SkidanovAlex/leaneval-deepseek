import Mathlib
import Submission.Work.Hering.AppVII.sum_sq_eq_of_config
import Submission.Work.Hering.AppVII.double_sum_sq_ge
import Submission.Work.Hering.AppVII.card_le_sum_sq_of_ne_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

/-- **Appendix VII, step 5 (p. 219).**

For `p ≥ 2` and a non-constant `n : Fin p → ℤ`, the sum of the squared pairwise differences
`∑ᵢ ∑ⱼ (n i - n j)^2` equals `2 (p - 1)` if and only if all the values `n i` are equal to a
single integer `m` except at one index `i₀`, where the value equals `m ± 1`.

(`∑ᵢ ∑ⱼ (n i - n j)^2 = 2 ∑_{i<j} (n i - n j)^2`, so the displayed equation says
`∑_{i<j} (n i - n j)^2 = p - 1`.)

* `⇐` is the direct computation `Work.Hering.AppVII.sum_sq_eq_of_config`.
* `⇒`: pick an index `i₀` at which `n` attains its minimum `μ`.  With `z = #{i | n i = μ}` the
  `2 (p - z) z` cross terms of the double sum already give `∑ᵢ ∑ⱼ (n i - n j)^2 ≥ 2 z S`, where
  `S = ∑_{n i > μ} (n i - μ)^2 ≥ p - z`; hence `z (p - z) ≤ p - 1`, i.e. `z = 1` or `p - z = 1`.
  In either case equality forces every gap `n i - μ` with `n i > μ` to be `1`, which is the
  stated structure. -/
theorem arith_sum_sq {p : ℕ} (hp : 2 ≤ p) {n : Fin p → ℤ} (hne : ∃ i j, n i ≠ n j) : (∑ i : Fin p, ∑ j : Fin p, (n i - n j) ^ 2 = 2 * ((p : ℤ) - 1)) ↔ ∃ i₀ : Fin p, ∃ m : ℤ, (∀ i : Fin p, i ≠ i₀ → n i = m) ∧ (n i₀ = m + 1 ∨ n i₀ = m - 1) := by
  classical
  constructor
  · intro hT
    -- an index at which `n` attains its minimum
    obtain ⟨i₀, -, hmin⟩ :=
      Finset.exists_min_image (Finset.univ : Finset (Fin p)) n ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    let f : Fin p → ℤ := fun i => n i - n i₀
    have hf : ∀ i, 0 ≤ f i := by
      intro i
      have h1 := hmin i (Finset.mem_univ i)
      show 0 ≤ n i - n i₀
      linarith
    let Z : Finset (Fin p) := Finset.univ.filter (fun i => f i = 0)
    let P : Finset (Fin p) := Finset.univ.filter (fun i => f i ≠ 0)
    let S : ℤ := ∑ i ∈ P, (f i) ^ 2
    -- the double sum only depends on `f`
    have hTf : (∑ i : Fin p, ∑ j : Fin p, (f i - f j) ^ 2)
        = ∑ i : Fin p, ∑ j : Fin p, (n i - n j) ^ 2 := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      simp only [f]; ring
    have hL2 : 2 * (Z.card : ℤ) * S ≤ 2 * ((p : ℤ) - 1) := by
      have h := double_sum_sq_ge f hf
      rw [hTf, hT] at h
      exact h
    have hcd : Z.card + P.card = p := by
      show (Finset.univ.filter (fun i => f i = 0)).card
          + (Finset.univ.filter (fun i => f i ≠ 0)).card = p
      rw [Finset.card_filter_add_card_filter_not (fun i => f i = 0)]
      simp
    have hc1 : 1 ≤ Z.card := by
      apply Finset.card_pos.mpr
      refine ⟨i₀, ?_⟩
      simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and, f]
      ring
    have hd1 : 1 ≤ P.card := by
      obtain ⟨i, j, hij⟩ := hne
      have hex : ∃ k, f k ≠ 0 := by
        by_cases hi : n i = n i₀
        · refine ⟨j, ?_⟩
          simp only [f]
          intro h
          exact hij (by rw [hi]; linarith)
        · refine ⟨i, ?_⟩
          simp only [f]
          exact sub_ne_zero.mpr hi
      obtain ⟨k, hk⟩ := hex
      apply Finset.card_pos.mpr
      exact ⟨k, by simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]; exact hk⟩
    have hSd : (P.card : ℤ) ≤ S := card_le_sum_sq_of_ne_zero f hf
    have hcS_le : (Z.card : ℤ) * S ≤ (p : ℤ) - 1 := by linarith
    have hcdz : (Z.card : ℤ) + (P.card : ℤ) = (p : ℤ) := by exact_mod_cast hcd
    have hcz : (1 : ℤ) ≤ (Z.card : ℤ) := by exact_mod_cast hc1
    have hdz : (1 : ℤ) ≤ (P.card : ℤ) := by exact_mod_cast hd1
    have hprod_le : ((Z.card : ℤ) - 1) * ((P.card : ℤ) - 1) ≤ 0 := by
      nlinarith [hcS_le, hSd, hcdz, hcz, hdz]
    have hZ0 : 0 ≤ (Z.card : ℤ) - 1 := by linarith
    have hP0 : 0 ≤ (P.card : ℤ) - 1 := by linarith
    have hprod0 : ((Z.card : ℤ) - 1) * ((P.card : ℤ) - 1) = 0 :=
      le_antisymm hprod_le (mul_nonneg hZ0 hP0)
    have hcase : Z.card = 1 ∨ P.card = 1 := by
      rcases mul_eq_zero.mp hprod0 with h | h
      · left
        have hZc1 : (Z.card : ℤ) = 1 := by linarith
        exact_mod_cast hZc1
      · right
        have hPc1 : (P.card : ℤ) = 1 := by linarith
        exact_mod_cast hPc1
    rcases hcase with hZc | hPc
    · -- `Z` is a singleton: one index attains the minimum, all others are `μ + 1`
      obtain ⟨i₁, hZ1⟩ := Finset.card_eq_one.mp hZc
      have hZc' : (Z.card : ℤ) = 1 := by exact_mod_cast hZc
      have hSle : S ≤ (P.card : ℤ) := by
        have h : (Z.card : ℤ) * S ≤ (p : ℤ) - 1 := hcS_le
        rw [hZc', one_mul] at h
        have hpc : (P.card : ℤ) = (p : ℤ) - 1 := by linarith [hcdz, hZc']
        linarith
      have hSeq : S = (P.card : ℤ) := le_antisymm hSle hSd
      have hall : ∀ i ∈ P, (f i) ^ 2 = 1 := by
        have hle : ∀ i ∈ P, (1 : ℤ) ≤ (f i) ^ 2 := by
          intro i hi
          have hne0 : f i ≠ 0 := by
            simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hi
          have h0 := hf i
          have h1 : 1 ≤ f i := by
            have hlt : 0 < f i := lt_of_le_of_ne h0 hne0.symm
            linarith
          nlinarith
        have hsum1 : (∑ i ∈ P, (1 : ℤ)) = (P.card : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        have hSeq' : (∑ i ∈ P, (f i) ^ 2) = (P.card : ℤ) := hSeq
        have hseq : (∑ i ∈ P, (f i) ^ 2) = ∑ i ∈ P, (1 : ℤ) := by rw [hSeq', hsum1]
        intro i hi
        exact ((Finset.sum_eq_sum_iff_of_le (s := P) (f := fun _ => (1 : ℤ))
          (g := fun i => (f i) ^ 2) hle).mp hseq.symm i hi).symm
      refine ⟨i₁, n i₀ + 1, ?_, ?_⟩
      · intro i hi
        have hiP : i ∈ P := by
          simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
          intro hfi0
          have hmem : i ∈ Z := by
            simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hfi0
          rw [hZ1] at hmem
          simp at hmem
          exact hi hmem
        have h1 := hall i hiP
        have hfi : f i = 1 := by
          have h0 := hf i
          rcases sq_eq_one_iff.mp h1 with h | h
          · exact h
          · linarith
        simp only [f] at hfi
        linarith
      · right
        have hi₁Z : i₁ ∈ Z := by rw [hZ1]; simp
        have hfi₁ : f i₁ = 0 := by
          simpa only [Z, Finset.mem_filter, Finset.mem_univ, true_and] using hi₁Z
        simp only [f] at hfi₁
        linarith
    · -- `P` is a singleton: all but one index are `μ`, the remaining one is `μ + 1`
      obtain ⟨i₁, hP1⟩ := Finset.card_eq_one.mp hPc
      have hPc' : (P.card : ℤ) = 1 := by exact_mod_cast hPc
      have hpz : (Z.card : ℤ) = (p : ℤ) - 1 := by linarith [hcdz, hPc']
      have hSval : S = (f i₁) ^ 2 := by
        show (∑ i ∈ P, (f i) ^ 2) = (f i₁) ^ 2
        rw [hP1, Finset.sum_singleton]
      have hsq1 : (f i₁) ^ 2 ≤ 1 := by
        have h := hcS_le
        rw [hSval, hpz] at h
        have hpz1 : (1 : ℤ) ≤ (p : ℤ) - 1 := by
          have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
          linarith
        nlinarith [h, hpz1]
      have hfi₁_mem : i₁ ∈ P := by rw [hP1]; simp
      have hfi₁_ne : f i₁ ≠ 0 := by
        simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hfi₁_mem
      have hsq : (f i₁) ^ 2 = 1 := by
        have h0 := hf i₁
        have hge : 1 ≤ (f i₁) ^ 2 := by
          have h1 : 1 ≤ f i₁ := by
            have hlt : 0 < f i₁ := lt_of_le_of_ne h0 hfi₁_ne.symm
            linarith
          nlinarith
        linarith
      have hf1 : f i₁ = 1 := by
        have h0 := hf i₁
        rcases sq_eq_one_iff.mp hsq with h | h
        · exact h
        · linarith
      refine ⟨i₁, n i₀, ?_, ?_⟩
      · intro i hi
        have hiZ : f i = 0 := by
          by_contra hcon
          have hmem : i ∈ P := by
            simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hcon
          rw [hP1] at hmem
          simp at hmem
          exact hi hmem
        simp only [f] at hiZ
        linarith
      · left
        simp only [f] at hf1
        linarith
  · -- the configuration case is a direct computation
    rintro ⟨i₀, m, hrest, hsp⟩
    exact sum_sq_eq_of_config hrest hsp

end Work.Hering.AppVII
