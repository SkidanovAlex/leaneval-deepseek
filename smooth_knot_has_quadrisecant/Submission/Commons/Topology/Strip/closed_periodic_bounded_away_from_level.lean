import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Topology.Strip

open Set

/-- If `K ⊆ ℝ × ℝ` is closed, periodic with period `p > 0` in the first coordinate,
contained in the horizontal strip `a ≤ y ≤ b`, and avoids the horizontal level `y = c`,
then the level `c` is bounded away from the second coordinates of all points of `K`
by a uniform positive amount. -/
theorem closed_periodic_bounded_away_from_level {p a b c : ℝ} (hp : 0 < p) (hab : a < b)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hsub : K ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hper : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K)
    (hc : ∀ q : ℝ × ℝ, q ∈ K → q.2 ≠ c) :
    ∃ δ > 0, ∀ q : ℝ × ℝ, q ∈ K → (q.2 ≤ c - δ ∨ c + δ ≤ q.2) := by
  -- Step 1: `K` is invariant under translation by any integer multiple of `p` in the
  -- first coordinate.
  have htrans : ∀ (n : ℤ) (q : ℝ × ℝ), q ∈ K → (q.1 + (n : ℝ) * p, q.2) ∈ K := by
    intro n
    refine Int.induction_on n ?_ ?_ ?_
    · intro q hq; simpa using hq
    · intro i ih q hq
      have h1 : (q.1 + ((i : ℤ) : ℝ) * p, q.2) ∈ K := ih q hq
      have h2 : ((q.1 + ((i : ℤ) : ℝ) * p) + p, q.2) ∈ K :=
        (hper (q.1 + ((i : ℤ) : ℝ) * p, q.2)).mp h1
      have key : ((q.1 + ((i : ℤ) : ℝ) * p) + p, q.2)
          = (q.1 + (((i : ℤ) + 1 : ℤ) : ℝ) * p, q.2) := by
        congr 1
        push_cast
        ring
      rwa [key] at h2
    · intro i ih q hq
      have h1 := ih q hq
      apply (hper (q.1 + ((-(i : ℤ) - 1 : ℤ) : ℝ) * p, q.2)).mpr
      have key : ((q.1 + ((-(i : ℤ) - 1 : ℤ) : ℝ) * p) + p, q.2)
          = (q.1 + ((-(i : ℤ)) : ℝ) * p, q.2) := by
        congr 1
        push_cast
        ring
      rw [key]
      simpa using h1
  -- Step 2: the compact fundamental domain `C` and the compact set `K ∩ C`.
  set C : Set (ℝ × ℝ) := Icc (0 : ℝ) p ×ˢ Icc a b with hCdef
  have hCcompact : IsCompact C := by
    rw [hCdef]; exact isCompact_Icc.prod isCompact_Icc
  have hCclosed : IsClosed C := by
    rw [hCdef]; exact isClosed_Icc.prod isClosed_Icc
  have hKCcompact : IsCompact (K ∩ C) :=
    hCcompact.of_isClosed_subset (hK.inter hCclosed) inter_subset_right
  have hYcompact : IsCompact (Prod.snd '' (K ∩ C)) :=
    hKCcompact.image continuous_snd
  -- Step 3: `c` is not a second coordinate of any point of `K ∩ C`.
  have hcancel : c ∉ Prod.snd '' (K ∩ C) := by
    rintro ⟨y, hy, hyc⟩
    exact hc y hy.1 hyc
  -- Step 4: extract the uniform gap from openness of the complement.
  obtain ⟨ε, hεpos, hεsub⟩ :=
    (Metric.isOpen_iff.mp hYcompact.isClosed.isOpen_compl) c hcancel
  refine ⟨ε, hεpos, ?_⟩
  intro q hq
  -- Translate `q` into the fundamental domain.
  have hshift : ∃ x : ℝ, 0 ≤ x ∧ x ≤ p ∧ (x, q.2) ∈ K := by
    let m : ℤ := ⌊q.1 / p⌋
    have hm1 : (m : ℝ) ≤ q.1 / p := Int.floor_le _
    have hm2 : q.1 / p < (m : ℝ) + 1 := Int.lt_floor_add_one _
    have hpne : p ≠ 0 := ne_of_gt hp
    have h0 : 0 ≤ q.1 - (m : ℝ) * p := by
      have hle : (m : ℝ) * p ≤ q.1 := by
        have h := mul_le_mul_of_nonneg_right hm1 (le_of_lt hp)
        rwa [div_mul_cancel₀ _ hpne] at h
      linarith
    have hltp : q.1 - (m : ℝ) * p < p := by
      have hlt : q.1 < ((m : ℝ) + 1) * p := by
        have h := mul_lt_mul_of_pos_right hm2 hp
        rwa [div_mul_cancel₀ _ hpne] at h
      nlinarith
    refine ⟨q.1 + ((-m : ℤ) : ℝ) * p, ?_, ?_, ?_⟩
    · have heq : q.1 + ((-m : ℤ) : ℝ) * p = q.1 - (m : ℝ) * p := by
        push_cast; ring
      rw [heq]; exact h0
    · have heq : q.1 + ((-m : ℤ) : ℝ) * p = q.1 - (m : ℝ) * p := by
        push_cast; ring
      rw [heq]; exact le_of_lt hltp
    · exact htrans (-m) q hq
  obtain ⟨x, hx0, hxp, hxK⟩ := hshift
  have hxKC : (x, q.2) ∈ K ∩ C := by
    refine ⟨hxK, ?_⟩
    rw [hCdef, mem_prod]
    exact ⟨⟨hx0, hxp⟩, ⟨(hsub hq).1, (hsub hq).2⟩⟩
  have hmem : q.2 ∈ Prod.snd '' (K ∩ C) := ⟨(x, q.2), hxKC, rfl⟩
  -- The gap holds for this value.
  have hdist : ε ≤ dist q.2 c := by
    by_contra hcon
    exact (hεsub (Metric.mem_ball.mpr (lt_of_not_ge hcon))) hmem
  rw [Real.dist_eq] at hdist
  rcases lt_or_ge (q.2 - c) 0 with h | h
  · left
    rw [abs_of_neg h] at hdist
    linarith
  · right
    rw [abs_of_nonneg h] at hdist
    linarith

end Commons.Topology.Strip