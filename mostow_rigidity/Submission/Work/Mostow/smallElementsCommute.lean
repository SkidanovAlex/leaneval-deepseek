import Mathlib
import Submission.Work.Mostow.orthSmallCommute

namespace Work.Mostow

open Submission.Mostow

noncomputable section

set_option maxHeartbeats 1000000

/-- **Small elements of a finite subgroup of `O(m)` commute at the explicit constant `1/4`.**

This is the constant-explicit form of `Work.Mostow.orthSmallCommute`, obtained by running the same
Engel-sequence argument directly with `c₀ = 1/4`: put `B₀ := b`, `B_{i+1} := [a, B_i]`.  Buser's
estimate `mOf [a, x] ≤ 2 * mOf a * mOf x` gives `mOf B_i ≤ (1/2)^i * (1/4) → 0`, so finiteness of
`A` produces `N` with `B_N = 1`; the descent step `B_{i+2} = 1 ⇒ B_{i+1} = 1` uses
Engel–Frobenius (`Work.Mostow.Margulis.engel_frobenius_orthogonal`), whence `B_1 = [a,b] = 1`. -/
theorem smallElementsCommute (m : ℕ) (A : Subgroup (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m))
    [Finite A] (a b : A)
    (ha : Work.Mostow.mOf (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) ≤ 1 / 4)
    (hb : Work.Mostow.mOf (b : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) ≤ 1 / 4) :
    (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) * (b : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
      = (b : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  have hshrink : ∀ i : ℕ, mOf (engelSeq A a b i : E m ≃ₗᵢ[ℝ] E m) ≤ (1 / 2 : ℝ) ^ i * (1 / 4) :=
    fun i => osc.engelSeq_mOf_le A a b ha hb i
  have hbound : ∀ i : ℕ, mOf (engelSeq A a b i : E m ≃ₗᵢ[ℝ] E m) ≤ 1 / 2 := by
    intro i
    have h1 := hshrink i
    have h2 : (1 / 2 : ℝ) ^ i * (1 / 4) ≤ 1 / 2 := by
      have h3 : (1 / 2 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    linarith
  by_cases hb1 : b = 1
  · have hb1' : (b : E m ≃ₗᵢ[ℝ] E m) = 1 := by
      have := congrArg (fun x : A => (x : E m ≃ₗᵢ[ℝ] E m)) hb1
      simpa using this
    rw [hb1']
    simp
  · have hfin : (Set.range (engelSeq A a b)).Finite :=
      Set.finite_univ.subset (Set.subset_univ _)
    let s : Finset A := hfin.toFinset.filter (fun x => x ≠ 1)
    have hbs : b ∈ s := by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨0, engelSeq_zero A a b⟩, hb1⟩
    obtain ⟨x, hxs, hxmin⟩ :=
      Finset.exists_min_image s (fun x : A => mOf (x : E m ≃ₗᵢ[ℝ] E m)) ⟨b, hbs⟩
    have hxne : x ≠ 1 := (Finset.mem_filter.mp hxs).2
    have hδpos : 0 < mOf (x : E m ≃ₗᵢ[ℝ] E m) := by
      rcases eq_or_lt_of_le (mOf_nonneg (x : E m ≃ₗᵢ[ℝ] E m)) with h | h
      · have hx1 : (x : E m ≃ₗᵢ[ℝ] E m) = 1 := mOf_eq_zero_iff.mp h.symm
        exact absurd (Subtype.ext (by simpa using hx1)) hxne
      · exact h
    have hδle : ∀ i : ℕ, engelSeq A a b i ≠ 1 →
        mOf (x : E m ≃ₗᵢ[ℝ] E m) ≤ mOf (engelSeq A a b i : E m ≃ₗᵢ[ℝ] E m) := by
      intro i hi
      refine hxmin (engelSeq A a b i) ?_
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨i, rfl⟩, hi⟩
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδpos (by norm_num : (1 / 2 : ℝ) < 1)
    have hBN : engelSeq A a b N = 1 := by
      by_contra h
      have h1 := hδle N h
      have h2 := hshrink N
      have h3 : (1 / 2 : ℝ) ^ N * (1 / 4) < mOf (x : E m ≃ₗᵢ[ℝ] E m) := by
        have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ N := pow_pos (by norm_num) N
        nlinarith
      linarith
    have hex : ∃ n : ℕ, engelSeq A a b n = 1 := ⟨N, hBN⟩
    have hi₀ : engelSeq A a b (Nat.find hex) = 1 := Nat.find_spec hex
    have hmin0 : ∀ j : ℕ, j < Nat.find hex → engelSeq A a b j ≠ 1 :=
      fun j hj => Nat.find_min hex hj
    have hB1 : engelSeq A a b 1 = 1 := by
      have hpos : 0 < Nat.find hex := by
        rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
        · rw [h] at hi₀
          exact absurd (by simpa using hi₀) hb1
        · exact h
      have key : ∀ k : ℕ, k ≤ Nat.find hex - 1 → engelSeq A a b (Nat.find hex - k) = 1 := by
        intro k
        induction k with
        | zero => intro _; simpa using hi₀
        | succ k ih =>
          intro hk
          have h2 : Nat.find hex - (k + 1) = (Nat.find hex - (k + 2)) + 1 := by omega
          have h3 : Nat.find hex - k = (Nat.find hex - (k + 2)) + 2 := by omega
          rw [h2]
          have hthis : engelSeq A a b (Nat.find hex - k) = 1 := ih (by omega)
          rw [h3] at hthis
          exact osc.engelSeq_step A a b ha hbound (Nat.find hex - (k + 2)) hthis
      have h1 : Nat.find hex - (Nat.find hex - 1) = 1 := by omega
      have hk := key (Nat.find hex - 1) le_rfl
      simpa [h1] using hk
    have hcab : (a : E m ≃ₗᵢ[ℝ] E m) * (b : E m ≃ₗᵢ[ℝ] E m)
        * (a : E m ≃ₗᵢ[ℝ] E m)⁻¹ * (b : E m ≃ₗᵢ[ℝ] E m)⁻¹ = 1 := by
      have h2 : (a : E m ≃ₗᵢ[ℝ] E m) * (b : E m ≃ₗᵢ[ℝ] E m)
          * (a : E m ≃ₗᵢ[ℝ] E m)⁻¹ * (b : E m ≃ₗᵢ[ℝ] E m)⁻¹
          = (engelSeq A a b 1 : E m ≃ₗᵢ[ℝ] E m) := by
        simpa using (engelSeq_succ A a b 0).symm
      calc (a : E m ≃ₗᵢ[ℝ] E m) * (b : E m ≃ₗᵢ[ℝ] E m)
            * (a : E m ≃ₗᵢ[ℝ] E m)⁻¹ * (b : E m ≃ₗᵢ[ℝ] E m)⁻¹
          = (engelSeq A a b 1 : E m ≃ₗᵢ[ℝ] E m) := h2
        _ = 1 := by simp [hB1]
    calc (a : E m ≃ₗᵢ[ℝ] E m) * (b : E m ≃ₗᵢ[ℝ] E m)
        = ((a : E m ≃ₗᵢ[ℝ] E m) * (b : E m ≃ₗᵢ[ℝ] E m)
            * (a : E m ≃ₗᵢ[ℝ] E m)⁻¹ * (b : E m ≃ₗᵢ[ℝ] E m)⁻¹)
          * ((b : E m ≃ₗᵢ[ℝ] E m) * (a : E m ≃ₗᵢ[ℝ] E m)) := by group
      _ = 1 * ((b : E m ≃ₗᵢ[ℝ] E m) * (a : E m ≃ₗᵢ[ℝ] E m)) := by rw [hcab]
      _ = (b : E m ≃ₗᵢ[ℝ] E m) * (a : E m ≃ₗᵢ[ℝ] E m) := one_mul _

end

end Work.Mostow
