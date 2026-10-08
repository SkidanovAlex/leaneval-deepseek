import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Coherence

/-- An integer square is never `2`. -/
lemma int_sq_ne_two (n : ℤ) : n ^ 2 ≠ 2 := by
  intro hn
  have hh : n * n % 4 = 2 := by
    rw [← pow_two, hn]
    norm_num
  exact Int.sq_ne_two_mod_four n hh

/-- If a sum of integer squares over `s` equals `2`, then exactly two elements of `s`
contribute `±1` (i.e. their square is `1`) and every other element of `s` is mapped to `0`
by `c`. -/
theorem sum_sq_eq_two {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (h : ∑ z ∈ s, c z ^ 2 = 2) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ c x ^ 2 = 1 ∧ c y ^ 2 = 1 ∧
      ∀ z ∈ s, z ≠ x → z ≠ y → c z = 0 := by
  classical
  -- The set of elements of `s` on which `c` does not vanish.
  let T : Finset ι := s.filter (fun z => c z ≠ 0)
  have hTsub : T ⊆ s := Finset.filter_subset _ s
  -- The sum of squares is unchanged when restricted to `T`.
  have hsum : ∑ z ∈ T, c z ^ 2 = 2 := by
    have h1 : ∑ z ∈ T, c z ^ 2 = ∑ z ∈ s, (if c z ≠ 0 then c z ^ 2 else 0) := by
      show ∑ z ∈ s.filter (fun z => c z ≠ 0), c z ^ 2 = _
      rw [Finset.sum_filter]
    rw [h1]
    have hcongr : ∀ z ∈ s, (if c z ≠ 0 then c z ^ 2 else 0) = c z ^ 2 := by
      intro z _
      by_cases hc : c z = 0
      · simp [hc]
      · simp [hc]
    rw [Finset.sum_congr rfl hcongr, h]
  -- Each summand over `T` is at least `1`.
  have hge1 : ∀ z ∈ T, 1 ≤ c z ^ 2 := by
    intro z hz
    have hz' : c z ≠ 0 := (Finset.mem_filter.mp hz).2
    have hp := sq_pos_of_ne_zero hz'
    omega
  -- Hence `T` has at most two elements.
  have hcard : T.card ≤ 2 := by
    have hh := Finset.card_nsmul_le_sum T (fun z => c z ^ 2) (1 : ℤ) hge1
    rw [nsmul_eq_mul, mul_one] at hh
    have hZ : (T.card : ℤ) ≤ 2 := by
      calc (T.card : ℤ) ≤ ∑ z ∈ T, c z ^ 2 := hh
        _ = 2 := hsum
    omega
  -- And at least one, since the sum is `2 ≠ 0`.
  have hcardpos : 0 < T.card := by
    by_contra hc
    have hc0 : T.card = 0 := by omega
    have hT0 : T = ∅ := Finset.card_eq_zero.mp hc0
    rw [hT0] at hsum
    simp only [Finset.sum_empty] at hsum
    exact absurd hsum (by norm_num)
  have hcases : T.card = 1 ∨ T.card = 2 := by omega
  rcases hcases with h1 | h2
  · -- A single contributor would force its square to equal `2`, impossible.
    rcases Finset.card_eq_one.mp h1 with ⟨a, ha⟩
    rw [ha] at hsum
    simp only [Finset.sum_singleton] at hsum
    exact absurd hsum (int_sq_ne_two (c a))
  · -- Two contributors, each with square exactly `1`.
    rcases Finset.card_eq_two.mp h2 with ⟨x, y, hxy, hTxy⟩
    have hxT : x ∈ T := by rw [hTxy]; simp
    have hyT : y ∈ T := by rw [hTxy]; simp
    have hsum2 : c x ^ 2 + c y ^ 2 = 2 := by
      rw [hTxy, Finset.sum_insert (by simpa using hxy), Finset.sum_singleton] at hsum
      exact hsum
    have hcx : c x ^ 2 = 1 := by
      have h1 := hge1 x hxT
      have h2 := hge1 y hyT
      omega
    have hcy : c y ^ 2 = 1 := by
      have h1 := hge1 x hxT
      have h2 := hge1 y hyT
      omega
    refine ⟨x, hTsub hxT, y, hTsub hyT, hxy, hcx, hcy, ?_⟩
    intro z hz hzx hzy
    by_contra hc
    have hzT : z ∈ T := by
      show z ∈ s.filter (fun z => c z ≠ 0)
      exact Finset.mem_filter.mpr ⟨hz, hc⟩
    rw [hTxy] at hzT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzT
    rcases hzT with hh | hh
    · exact hzx hh
    · exact hzy hh

end Work.Coherence
