import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Integer coefficients of `ℓ²`-norm three with a prescribed entry `1`

If `c : ι → ℤ` is a finitely supported integer-valued function with `∑ i, c i ^ 2 = 3` and
`c i₀ = 1`, then `c` takes the value `1` on `i₀`, takes a value in `{±1}` on exactly two further
indices `i₁, i₂`, and vanishes everywhere else.

The proof: let `A` be the support of `c` and `B = A \ {i₀}`.  Then `∑_{i∈B} c i ^ 2 = 2`.  Every
term `c i ^ 2` with `i ∈ B` is a positive square bounded by `2`, hence equals `1`; consequently
`|B| = 2` and the two elements of `B` are the required `i₁, i₂`.  Any index outside
`{i₀} ∪ B = A` has value `0`.
-/

namespace Work.BrauerSuzuki.Characters

theorem sum_sq_three_coeffs {ι : Type*} [Fintype ι] (c : ι → ℤ)
    (h3 : ∑ i, c i ^ 2 = 3) (i₀ : ι) (h0 : c i₀ = 1) :
    ∃ i₁ i₂ : ι, i₁ ≠ i₀ ∧ i₂ ≠ i₀ ∧ i₁ ≠ i₂ ∧
      (c i₁ = 1 ∨ c i₁ = -1) ∧ (c i₂ = 1 ∨ c i₂ = -1) ∧
      ∀ i, i ≠ i₀ → i ≠ i₁ → i ≠ i₂ → c i = 0 := by
  classical
  -- `A` is the support of `c`, and `i₀` lies in it.
  set A : Finset ι := Finset.univ.filter (fun i => c i ≠ 0) with hA
  have hi0A : i₀ ∈ A := by rw [hA]; simp [h0]
  -- Summing over the support does not change the sum.
  have hsumA : ∑ i ∈ A, c i ^ 2 = 3 := by
    rw [hA, Finset.sum_filter, ← h3]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : c i = 0 <;> simp [h]
  -- `B` is the support with `i₀` removed; the remaining square-sum is `2`.
  set B : Finset ι := A.erase i₀ with hB
  have hsumB : ∑ i ∈ B, c i ^ 2 = 2 := by
    have h1 : c i₀ ^ 2 = 1 := by rw [h0]; norm_num
    have h := Finset.sum_erase_add A (fun i => c i ^ 2) hi0A
    rw [← hB] at h
    linarith [h, hsumA, h1]
  -- Every element of `B` contributes a positive square `≤ 2`, hence exactly `1`.
  have hsq : ∀ i ∈ B, c i ^ 2 = 1 := by
    intro i hi
    have hiA : i ∈ A := Finset.mem_of_mem_erase hi
    have hne : c i ≠ 0 := by
      have h := hiA; rw [hA] at h; simpa using h
    have hle : c i ^ 2 ≤ 2 := by
      have hnn : ∀ j ∈ B, (0 : ℤ) ≤ c j ^ 2 := fun j _ => sq_nonneg _
      have h := Finset.single_le_sum hnn hi
      linarith [h, hsumB]
    have hlt : c i ^ 2 < (2 : ℤ) ^ 2 := by nlinarith [hle]
    have habs : |c i| < 2 := by
      have h := (sq_lt_sq (a := c i) (b := (2 : ℤ))).mp hlt
      simpa using h
    rw [abs_lt] at habs
    obtain ⟨hl, hr⟩ := habs
    -- The only integers strictly between `-2` and `2` are `-1, 0, 1`, and `c i ≠ 0`.
    have hci : c i = 1 ∨ c i = -1 := by
      rcases lt_trichotomy (c i) 0 with h | h | h
      · right; omega
      · exact absurd h hne
      · left; omega
    rcases hci with h | h <;> rw [h] <;> norm_num
  -- The sum of the (all equal to `1`) squares over `B` equals its cardinality.
  have hcardB : B.card = 2 := by
    have hconst : ∑ i ∈ B, c i ^ 2 = ∑ i ∈ B, (1 : ℤ) :=
      Finset.sum_congr rfl fun i hi => hsq i hi
    rw [hsumB, Finset.sum_const, nsmul_eq_mul, mul_one] at hconst
    omega
  obtain ⟨i₁, i₂, hne12, hBeq⟩ := Finset.card_eq_two.mp hcardB
  have hi₁B : i₁ ∈ B := by rw [hBeq]; simp
  have hi₂B : i₂ ∈ B := by rw [hBeq]; simp
  have hne1₀ : i₁ ≠ i₀ := by
    have h := hi₁B; rw [hB] at h; exact (Finset.mem_erase.mp h).1
  have hne2₀ : i₂ ≠ i₀ := by
    have h := hi₂B; rw [hB] at h; exact (Finset.mem_erase.mp h).1
  refine ⟨i₁, i₂, hne1₀, hne2₀, hne12, ?_, ?_, ?_⟩
  · exact sq_eq_one_iff.mp (hsq i₁ hi₁B)
  · exact sq_eq_one_iff.mp (hsq i₂ hi₂B)
  · -- Indices outside `{i₀, i₁, i₂} = A` have value `0`.
    intro i hi0 hi1 hi2
    by_contra hci
    have hiA : i ∈ A := by rw [hA]; simp [hci]
    have hAeq : A = insert i₀ B := by rw [hB]; exact (Finset.insert_erase hi0A).symm
    rw [hAeq] at hiA
    rw [Finset.mem_insert] at hiA
    rcases hiA with h | h
    · exact hi0 h
    · rw [hBeq, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hi1 h
      · exact hi2 h

end Work.BrauerSuzuki.Characters
