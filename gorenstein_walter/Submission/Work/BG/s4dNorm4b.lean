import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.normFourPmIrr

namespace Work.BG

open OddOrder.RepresentationTheory

/-- Finite integer-vector combinatorics: if the nonzero integer coefficients attached to a
finite set have squares summing to `3`, then there are exactly three of them, and each
carries the coefficient `±1`.

This is the combinatorial core of the norm-`4`/`⟨1,δ⟩ = 1` decomposition: writing
`δ = ∑_a (c a) • a` over its support in `Irr K` with `‖δ‖² = ∑_a (c a)² = 4` and the
trivial-character coefficient equal to `1`, the remaining coefficients have squares
summing to `3`, so they are three signs `±1`. -/
lemma s4dNorm4b_sum_sq_three {ι : Type*} [DecidableEq ι] {s : Finset ι} {c : ι → ℤ}
    (hne : ∀ a ∈ s, c a ≠ 0) (hsum : ∑ a ∈ s, c a ^ 2 = 3) :
    ∃ b₁ b₂ b₃ : ι, b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ ∧ s = {b₁, b₂, b₃} ∧
      (c b₁ = 1 ∨ c b₁ = -1) ∧ (c b₂ = 1 ∨ c b₂ = -1) ∧ (c b₃ = 1 ∨ c b₃ = -1) := by
  classical
  -- Every nonzero square is at least `1`, hence `s` has at most three elements.
  have hge : ∀ a ∈ s, (1 : ℤ) ≤ c a ^ 2 := fun a ha => by
    have h := Int.one_le_abs (hne a ha)
    calc (1 : ℤ) = 1 ^ 2 := by ring
      _ ≤ |c a| ^ 2 := by gcongr
      _ = c a ^ 2 := sq_abs (c a)
  -- Every nonzero square is either `1` or at least `4`.
  have hsq : ∀ a ∈ s, c a ^ 2 = 1 ∨ 4 ≤ c a ^ 2 :=
    fun a ha => int_sq_eq_one_or_four_le (c a) (hne a ha)
  have hcard_le : s.card ≤ 3 := by
    have h := Finset.sum_le_sum hge
    rw [hsum] at h
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h
  have hcard_pos : 1 ≤ s.card := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · exfalso
      have hs : s = ∅ := Finset.card_eq_zero.mp h
      rw [hs] at hsum
      simp at hsum
    · exact h
  have hcard3 : s.card = 3 := by
    rcases Nat.lt_or_ge s.card 3 with hlt | hge3
    · have hcases : s.card = 1 ∨ s.card = 2 := by omega
      rcases hcases with hc | hc
      · -- a single square cannot equal `3`
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
        rw [Finset.sum_singleton] at hsum
        rcases hsq a (Finset.mem_singleton_self a) with h | h <;> omega
      · -- two nonzero squares cannot sum to `3`
        obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
        rw [Finset.sum_pair hab] at hsum
        rcases hsq a (by simp) with ha | ha <;> rcases hsq b (by simp) with hb | hb <;> omega
    · omega
  obtain ⟨b₁, b₂, b₃, hb12, hb13, hb23, rfl⟩ := Finset.card_eq_three.mp hcard3
  have hsum' : c b₁ ^ 2 + (c b₂ ^ 2 + c b₃ ^ 2) = 3 := by
    rw [Finset.sum_insert (by simp [hb12, hb13]), Finset.sum_insert (by simp [hb23]),
      Finset.sum_singleton] at hsum
    exact hsum
  have hs1 : c b₁ ^ 2 = 1 := by
    have h1 := hge b₁ (by simp); have h2 := hge b₂ (by simp); have h3 := hge b₃ (by simp)
    omega
  have hs2 : c b₂ ^ 2 = 1 := by
    have h1 := hge b₁ (by simp); have h2 := hge b₂ (by simp); have h3 := hge b₃ (by simp)
    omega
  have hs3 : c b₃ ^ 2 = 1 := by
    have h1 := hge b₁ (by simp); have h2 := hge b₂ (by simp); have h3 := hge b₃ (by simp)
    omega
  exact ⟨b₁, b₂, b₃, hb12, hb13, hb23, rfl,
    sq_eq_one_iff.mp hs1, sq_eq_one_iff.mp hs2, sq_eq_one_iff.mp hs3⟩

open OddOrder.RepresentationTheory Work.BG in
theorem s4dNorm4b {K : Type} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    {δ : ClassFunction K ℂ} (hZ : δ ∈ ZIrr K)
    (hnorm : ClassFunction.inner δ δ = 4)
    (h1 : ClassFunction.inner (trivialClassFunction K) δ = 1) :
    ∃ φ₁ φ₂ φ₃ : ClassFunction K ℂ,
      IsPmIrr φ₁ ∧ IsPmIrr φ₂ ∧ IsPmIrr φ₃ ∧
      ClassFunction.inner δ φ₁ = 1 ∧ ClassFunction.inner δ φ₂ = 1 ∧
      ClassFunction.inner δ φ₃ = 1 ∧
      δ = trivialClassFunction K + φ₁ + φ₂ + φ₃ := by
  classical
  -- Fourier expansion of the virtual character `δ` over its support in `Irr K`.
  obtain ⟨c, hsupp, hrepr, hnorm_sum⟩ := mem_ZIrr_inner_self_eq_sum_sq hZ
  -- Parseval in integer form.
  have hsum_int : ∑ a ∈ c.support, c a ^ 2 = 4 := by
    have hc : ((∑ a ∈ c.support, c a ^ 2 : ℤ) : ℂ) = 4 := by
      push_cast
      rw [← hnorm_sum, hnorm]
    exact_mod_cast hc
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  have hsupp' : ∀ a ∈ c.support, IsIrreducibleCharacter a :=
    fun a ha => mem_irreducibleCharacters.mp (hsupp ha)
  -- Fourier coefficient of `δ` at an irreducible.
  have hcoeff : ∀ b : ClassFunction K ℂ, IsIrreducibleCharacter b →
      ClassFunction.inner δ b = (c b : ℂ) := by
    intro b hb
    rw [hrepr]
    exact inner_eq_coeff_of_repr (⟨b, hb⟩ : IrreducibleCharacter K) hsupp
  -- `⟨1, δ⟩ = 1` forces the trivial character to occur with coefficient `1`.
  have htriv_irr : IsIrreducibleCharacter (trivialClassFunction K) :=
    trivialClassFunction_isIrreducible
  have hc_triv : c (trivialClassFunction K) = 1 := by
    have hst : star (ClassFunction.inner δ (trivialClassFunction K)) = 1 := by
      rw [← ClassFunction.inner_star_comm (trivialClassFunction K) δ]
      exact h1
    rw [hcoeff (trivialClassFunction K) htriv_irr, star_intCast] at hst
    exact_mod_cast hst
  have hmem_triv : trivialClassFunction K ∈ c.support :=
    Finsupp.mem_support_iff.mpr (by rw [hc_triv]; norm_num)
  -- The remaining coefficients have squares summing to `3`.
  have hsum3 : ∑ a ∈ c.support.erase (trivialClassFunction K), c a ^ 2 = 3 := by
    have h := Finset.sum_erase_add c.support (fun a => c a ^ 2) hmem_triv
    rw [hsum_int, hc_triv] at h
    norm_num at h
    omega
  have hne3 : ∀ a ∈ c.support.erase (trivialClassFunction K), c a ≠ 0 :=
    fun a ha => hne a (Finset.mem_of_mem_erase ha)
  obtain ⟨b₁, b₂, b₃, hb12, hb13, hb23, hset, hc1, hc2, hc3⟩ :=
    s4dNorm4b_sum_sq_three hne3 hsum3
  have hb₁s : b₁ ∈ c.support.erase (trivialClassFunction K) := by rw [hset]; simp
  have hb₂s : b₂ ∈ c.support.erase (trivialClassFunction K) := by rw [hset]; simp
  have hb₃s : b₃ ∈ c.support.erase (trivialClassFunction K) := by rw [hset]; simp
  have hb₁c : b₁ ∈ c.support := Finset.mem_of_mem_erase hb₁s
  have hb₂c : b₂ ∈ c.support := Finset.mem_of_mem_erase hb₂s
  have hb₃c : b₃ ∈ c.support := Finset.mem_of_mem_erase hb₃s
  have hs1 : c b₁ * c b₁ = 1 := by rcases hc1 with h | h <;> rw [h] <;> norm_num
  have hs2 : c b₂ * c b₂ = 1 := by rcases hc2 with h | h <;> rw [h] <;> norm_num
  have hs3 : c b₃ * c b₃ = 1 := by rcases hc3 with h | h <;> rw [h] <;> norm_num
  refine ⟨(c b₁ : ℂ) • b₁, (c b₂ : ℂ) • b₂, (c b₃ : ℂ) • b₃,
    isPmIrr_zsmul_of_sq_eq_one (hsupp' b₁ hb₁c) hc1,
    isPmIrr_zsmul_of_sq_eq_one (hsupp' b₂ hb₂c) hc2,
    isPmIrr_zsmul_of_sq_eq_one (hsupp' b₃ hb₃c) hc3, ?_, ?_, ?_, ?_⟩
  · rw [ClassFunction.inner_smul_right, hcoeff b₁ (hsupp' b₁ hb₁c), star_intCast,
      ← Int.cast_mul, hs1]
    norm_num
  · rw [ClassFunction.inner_smul_right, hcoeff b₂ (hsupp' b₂ hb₂c), star_intCast,
      ← Int.cast_mul, hs2]
    norm_num
  · rw [ClassFunction.inner_smul_right, hcoeff b₃ (hsupp' b₃ hb₃c), star_intCast,
      ← Int.cast_mul, hs3]
    norm_num
  · rw [hrepr, ← Finset.insert_erase hmem_triv,
      Finset.sum_insert (Finset.notMem_erase (trivialClassFunction K) c.support), hset,
      Finset.sum_insert (by simp [hb12, hb13]), Finset.sum_pair hb23,
      hc_triv, Int.cast_one, one_smul]
    abel

end Work.BG
