import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.isVChar_iff_exists_int_coeffs
import Submission.Work.CharCore.CFun
import Submission.Work.CharCore.vchar_norm_one
import Submission.Work.CharCore.principalChar_mem_Irr
import Submission.Work.BrauerSuzuki.Characters.cfInner_vchar_eq_coeff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A virtual character of norm `4` with trivial multiplicity `1` is `1 + ε₁Λ + ε₂Θ + ε₃Υ`

Let `ν` be a virtual (integral) character of a finite group `G` with `cfInner ν ν = 4` and
`cfInner ν 1 = 1`.  Writing `ν = ∑_{χ ∈ Irr G} c χ • χ` with integer coefficients `c`
(`Work.CharCore.isVChar_iff_exists_int_coeffs`) and using orthonormality of `Irr G`
(`Work.CharCore.irr_orthonormal`),

* the norm identity `cfInner ν ν = 4` becomes `∑_χ (c χ)^2 = 4`
  (`Work.CharCore.cfInner_eq_sum_sq`), and
* the identity `cfInner ν 1 = 1` says that the coefficient of the principal character `1`
  is `1` (`Work.BrauerSuzuki.Characters.cfInner_vchar_eq_coeff`).

A sum of integer squares equal to `4` with one coefficient equal to `1` then consists of
exactly four nonzero coefficients `1, ±1, ±1, ±1`
(`Work.BrauerSuzuki.Characters.sum_sq_four_coeffs`): the principal character and three
further distinct non-principal irreducible characters, so that
`ν = 1 + ∑_{i : Fin 3} ε i • χ i` with `ε i ∈ {1, -1}`.
-/

noncomputable section

open Classical

namespace Work.BrauerSuzuki.Characters

/-- A sum of squares of integers equal to `4` with one coefficient equal to `1` has
exactly three further nonzero summands, all equal to `±1`, and vanishes elsewhere. -/
theorem sum_sq_four_coeffs {ι : Type*} [Fintype ι] (c : ι → ℤ)
    (h4 : ∑ i, c i ^ 2 = 4) (i₀ : ι) (h0 : c i₀ = 1) :
    ∃ i₁ i₂ i₃ : ι, i₁ ≠ i₀ ∧ i₂ ≠ i₀ ∧ i₃ ≠ i₀ ∧ i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧
      (c i₁ = 1 ∨ c i₁ = -1) ∧ (c i₂ = 1 ∨ c i₂ = -1) ∧ (c i₃ = 1 ∨ c i₃ = -1) ∧
      ∀ i, i ≠ i₀ → i ≠ i₁ → i ≠ i₂ → i ≠ i₃ → c i = 0 := by
  classical
  -- `A` is the support of `c` and `i₀` lies in it.
  set A : Finset ι := Finset.univ.filter (fun i => c i ≠ 0) with hA
  have hi0A : i₀ ∈ A := by rw [hA]; simp [h0]
  have hsumA : ∑ i ∈ A, c i ^ 2 = 4 := by
    rw [hA, Finset.sum_filter, ← h4]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : c i = 0 <;> simp [h]
  -- `B = A \ {i₀}` carries the remaining square-sum `3`.
  set B : Finset ι := A.erase i₀ with hB
  have hsumB : ∑ i ∈ B, c i ^ 2 = 3 := by
    have h1 : c i₀ ^ 2 = 1 := by rw [h0]; norm_num
    have h := Finset.sum_erase_add A (fun i => c i ^ 2) hi0A
    rw [← hB] at h
    linarith [h, hsumA, h1]
  -- every element of `B` contributes a positive square `≤ 3`, hence exactly `1`.
  have hsq : ∀ i ∈ B, c i ^ 2 = 1 := by
    intro i hi
    have hiA : i ∈ A := Finset.mem_of_mem_erase hi
    have hne : c i ≠ 0 := by
      have h := hiA; rw [hA] at h; simpa using h
    have hle : c i ^ 2 ≤ 3 := by
      have hnn : ∀ j ∈ B, (0 : ℤ) ≤ c j ^ 2 := fun j _ => sq_nonneg _
      have h := Finset.single_le_sum hnn hi
      linarith [h, hsumB]
    have hlt : c i ^ 2 < (2 : ℤ) ^ 2 := by nlinarith [hle]
    have habs : |c i| < 2 := by
      have h := (sq_lt_sq (a := c i) (b := (2 : ℤ))).mp hlt
      simpa using h
    rw [abs_lt] at habs
    obtain ⟨hl, hr⟩ := habs
    have hci : c i = 1 ∨ c i = -1 := by
      rcases lt_trichotomy (c i) 0 with h | h | h
      · right; omega
      · exact absurd h hne
      · left; omega
    rcases hci with h | h <;> rw [h] <;> norm_num
  -- the sum of the (all equal to `1`) squares over `B` equals its cardinality `3`.
  have hcardB : B.card = 3 := by
    have hconst : ∑ i ∈ B, c i ^ 2 = ∑ i ∈ B, (1 : ℤ) :=
      Finset.sum_congr rfl fun i hi => hsq i hi
    rw [hsumB, Finset.sum_const, nsmul_eq_mul, mul_one] at hconst
    omega
  obtain ⟨i₁, i₂, i₃, hne12, hne13, hne23, hBeq⟩ := Finset.card_eq_three.mp hcardB
  have hi₁B : i₁ ∈ B := by rw [hBeq]; simp
  have hi₂B : i₂ ∈ B := by rw [hBeq]; simp
  have hi₃B : i₃ ∈ B := by rw [hBeq]; simp
  have hne1₀ : i₁ ≠ i₀ := by
    have h := hi₁B; rw [hB] at h; exact (Finset.mem_erase.mp h).1
  have hne2₀ : i₂ ≠ i₀ := by
    have h := hi₂B; rw [hB] at h; exact (Finset.mem_erase.mp h).1
  have hne3₀ : i₃ ≠ i₀ := by
    have h := hi₃B; rw [hB] at h; exact (Finset.mem_erase.mp h).1
  refine ⟨i₁, i₂, i₃, hne1₀, hne2₀, hne3₀, hne12, hne13, hne23, ?_, ?_, ?_, ?_⟩
  · exact sq_eq_one_iff.mp (hsq i₁ hi₁B)
  · exact sq_eq_one_iff.mp (hsq i₂ hi₂B)
  · exact sq_eq_one_iff.mp (hsq i₃ hi₃B)
  · -- indices outside `{i₀, i₁, i₂, i₃} = A` have value `0`.
    intro i hi0 hi1 hi2 hi3
    by_contra hci
    have hiA : i ∈ A := by rw [hA]; simp [hci]
    have hAeq : A = insert i₀ B := by rw [hB]; exact (Finset.insert_erase hi0A).symm
    rw [hAeq] at hiA
    rw [Finset.mem_insert] at hiA
    rcases hiA with h | h
    · exact hi0 h
    · rw [hBeq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h
      · exact hi1 h
      · exact hi2 h
      · exact hi3 h

/-- A finite sum whose coefficient function is supported on four pairwise distinct indices
collapses to the four corresponding terms. -/
theorem sum_eq_four_of_support {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module ℂ M]
    (c : ι → ℂ) (F : ι → M) (i₀ i₁ i₂ i₃ : ι)
    (h01 : i₁ ≠ i₀) (h02 : i₂ ≠ i₀) (h03 : i₃ ≠ i₀) (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃)
    (h23 : i₂ ≠ i₃)
    (hzero : ∀ i, i ≠ i₀ → i ≠ i₁ → i ≠ i₂ → i ≠ i₃ → c i = 0) :
    ∑ i, c i • F i = c i₀ • F i₀ + c i₁ • F i₁ + c i₂ • F i₂ + c i₃ • F i₃ := by
  classical
  have hsum : ∑ i, c i • F i = ∑ i ∈ ({i₀, i₁, i₂, i₃} : Finset ι), c i • F i := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [hzero i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2, zero_smul]
  rw [hsum]
  rw [Finset.sum_insert (by simp [h01.symm, h02.symm, h03.symm]),
      Finset.sum_insert (by simp [h12, h13]),
      Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton]
  abel

theorem vchar_of_norm_four {G : Type*} [Group G] [Fintype G] {ν : G → ℂ}
    (hν : Work.CharCore.IsVChar ν) (hnorm : Work.CharCore.cfInner ν ν = 4)
    (h1 : Work.CharCore.cfInner ν (fun _ => (1 : ℂ)) = 1) :
    ∃ (χ : Fin 3 → G → ℂ) (ε : Fin 3 → ℂ),
      (∀ i, χ i ∈ Work.CharCore.Irr G) ∧
      (∀ i, χ i ≠ (fun _ => (1 : ℂ))) ∧
      (∀ i j, i ≠ j → χ i ≠ χ j) ∧
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ν = (fun _ => (1 : ℂ)) + ∑ i, ε i • χ i := by
  classical
  obtain ⟨c, hc⟩ := Work.CharCore.isVChar_iff_exists_int_coeffs.mp hν
  -- the index of the principal (trivial) character in `Irr G`
  let iP : ↥(Work.CharCore.Irr G) :=
    ⟨fun _ => (1 : ℂ), Work.CharCore.principalChar_mem_Irr⟩
  have hiP : (iP : G → ℂ) = (fun _ => (1 : ℂ)) := rfl
  -- the multiplicity of the principal character is `1`
  have hcoeff : (c iP : ℂ) = 1 := by
    have h := cfInner_vchar_eq_coeff c iP
    rw [← hc] at h
    rw [← h]
    exact h1
  have hcint : c iP = 1 := by exact_mod_cast hcoeff
  -- the norm identity turns into a sum of squares of the coefficients
  have hsum4 : ∑ χ : ↥(Work.CharCore.Irr G), (c χ) ^ 2 = 4 := by
    have hsq := Work.CharCore.cfInner_eq_sum_sq (s := Work.CharCore.Irr G)
      (fun _ hx => hx) c
    rw [← hc] at hsq
    rw [hnorm] at hsq
    have : ((∑ χ : ↥(Work.CharCore.Irr G), (c χ) ^ 2 : ℤ) : ℂ) = ((4 : ℤ) : ℂ) := by
      push_cast
      exact hsq.symm
    exact Int.cast_injective this
  obtain ⟨i₁, i₂, i₃, h10, h20, h30, h12, h13, h23, hc1, hc2, hc3, hzero⟩ :=
    sum_sq_four_coeffs c hsum4 iP hcint
  -- only the four coefficients at `iP`, `i₁`, `i₂`, `i₃` survive
  have key : ν = (fun _ => (1 : ℂ)) + (c i₁ : ℂ) • (i₁ : G → ℂ) + (c i₂ : ℂ) • (i₂ : G → ℂ)
      + (c i₃ : ℂ) • (i₃ : G → ℂ) := by
    rw [hc]
    rw [sum_eq_four_of_support (c := fun χ : ↥(Work.CharCore.Irr G) => (c χ : ℂ))
      (F := fun χ : ↥(Work.CharCore.Irr G) => (χ : G → ℂ)) iP i₁ i₂ i₃ h10 h20 h30 h12 h13 h23
      (fun i h0 h1' h2' h3' => by rw [hzero i h0 h1' h2' h3']; simp)]
    rw [hcoeff, hiP]
    simp
  refine ⟨![(i₁ : G → ℂ), (i₂ : G → ℂ), (i₃ : G → ℂ)],
    ![(c i₁ : ℂ), (c i₂ : ℂ), (c i₃ : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using i₁.2
    · simpa using i₂.2
    · simpa using i₃.2
  · intro i
    fin_cases i
    · intro hh
      exact h10 (Subtype.ext (by rw [hiP]; simpa using hh))
    · intro hh
      exact h20 (Subtype.ext (by rw [hiP]; simpa using hh))
    · intro hh
      exact h30 (Subtype.ext (by rw [hiP]; simpa using hh))
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using h12
    · simpa using h13
    · simpa using h12.symm
    · exact absurd rfl hij
    · simpa using h23
    · simpa using h13.symm
    · simpa using h23.symm
    · exact absurd rfl hij
  · intro i
    fin_cases i
    · rcases hc1 with h | h
      · left; rw [h]; norm_num
      · right; rw [h]; norm_num
    · rcases hc2 with h | h
      · left; rw [h]; norm_num
      · right; rw [h]; norm_num
    · rcases hc3 with h | h
      · left; rw [h]; norm_num
      · right; rw [h]; norm_num
  · rw [key, Fin.sum_univ_three]
    simp
    abel

end Work.BrauerSuzuki.Characters
