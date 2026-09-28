import Mathlib
import Submission.Work.HP.GradCount.ncard_spec_le

namespace Work.HP.BoundaryMain

/-- The set of integer points `c` subject to the two families of inequalities is finite: each
coordinate `c k` (`k ≠ j`) is confined to a bounded real interval because `u ≠ 0`, and then `c j`
is confined to a bounded real interval because `v ≠ 0`.  Concretely the set is contained in the
finite product of integer intervals `∏ k, Icc (-⌈P k⌉) ⌈P k⌉`. -/
theorem spec_box_finite (n : ℕ) (j : Fin (n + 1)) (u v C : ℝ) (hu : u ≠ 0) (hv : v ≠ 0)
    (w A : Fin (n + 1) → ℝ) :
    ({c : Fin (n + 1) → ℤ |
        (∀ k : Fin (n + 1), k ≠ j → |(c k : ℝ) * u + A k| ≤ C) ∧
        |(c j : ℝ) * v + ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) + A j| ≤ C} :
        Set (Fin (n + 1) → ℤ)).Finite := by
  classical
  -- The uniform bound on every coordinate.
  set P : Fin (n + 1) → ℝ := fun k =>
    if k = j then (C + |A j| + ∑ i ∈ Finset.univ.erase j, |w i| * ((C + |A i|) / |u|)) / |v|
    else (C + |A k|) / |u| with hP
  have hPj : P j = (C + |A j| + ∑ i ∈ Finset.univ.erase j, |w i| * ((C + |A i|) / |u|)) / |v| := by
    simp [hP]
  have hPk : ∀ k, k ≠ j → P k = (C + |A k|) / |u| := by
    intro k hk; simp [hP, hk]
  refine (Set.Finite.pi (fun k => Set.finite_Icc (-⌈P k⌉) ⌈P k⌉)).subset ?_
  intro c hc
  simp only [Set.mem_ofPred_eq] at hc
  -- Coordinates `k ≠ j` are bounded because `u ≠ 0`.
  have hbound_ne : ∀ k, k ≠ j → |(c k : ℝ)| ≤ (C + |A k|) / |u| := by
    intro k hk
    have hCk := hc.1 k hk
    have h1 : |(c k : ℝ)| * |u| ≤ C + |A k| := by
      have h := abs_add_le ((c k : ℝ) * u + A k) (-(A k))
      rw [abs_neg] at h
      have heq : (c k : ℝ) * u + A k + -(A k) = (c k : ℝ) * u := by ring
      rw [heq] at h
      rw [abs_mul] at h
      linarith
    rw [le_div_iff₀ (abs_pos.mpr hu)]
    exact h1
  -- Coordinate `j` is bounded because `v ≠ 0`, once the others are.
  have hbound_j : |(c j : ℝ)| ≤
      (C + |A j| + ∑ i ∈ Finset.univ.erase j, |w i| * ((C + |A i|) / |u|)) / |v| := by
    set T : ℝ := ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) with hT
    have hTsum : |T| ≤ ∑ i ∈ Finset.univ.erase j, |w i| * ((C + |A i|) / |u|) := by
      rw [hT]
      calc |∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ)|
          ≤ ∑ i ∈ Finset.univ.erase j, |w i * (c i : ℝ)| :=
            Finset.abs_sum_le_sum_abs (fun i => w i * (c i : ℝ)) (Finset.univ.erase j)
        _ = ∑ i ∈ Finset.univ.erase j, |w i| * |(c i : ℝ)| := by
            apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
        _ ≤ ∑ i ∈ Finset.univ.erase j, |w i| * ((C + |A i|) / |u|) := by
            apply Finset.sum_le_sum; intro i hi
            exact mul_le_mul_of_nonneg_left (hbound_ne i (Finset.mem_erase.mp hi).1) (abs_nonneg _)
    have hTb : |(c j : ℝ) * v + T + A j| ≤ C := hc.2
    have hT2 : |T + A j| ≤ |T| + |A j| := abs_add_le T (A j)
    have h := abs_add_le ((c j : ℝ) * v + T + A j) (-(T + A j))
    rw [abs_neg] at h
    have heq : (c j : ℝ) * v + T + A j + -(T + A j) = (c j : ℝ) * v := by ring
    rw [heq] at h
    have hcv : |(c j : ℝ) * v| ≤
        C + |A j| + ∑ i ∈ Finset.univ.erase j, |w i| * ((C + |A i|) / |u|) := by
      linarith
    rw [abs_mul] at hcv
    rw [le_div_iff₀ (abs_pos.mpr hv)]
    exact hcv
  rw [Set.mem_pi]
  intro k _
  rw [Set.mem_Icc]
  have hb : |(c k : ℝ)| ≤ P k := by
    by_cases hk : k = j
    · rw [hk, hPj]; exact hbound_j
    · rw [hPk k hk]; exact hbound_ne k hk
  obtain ⟨hl, hr⟩ := abs_le.mp hb
  constructor
  · have h1 : ((-(c k) : ℤ) : ℝ) ≤ (⌈P k⌉ : ℤ) := by
      push_cast
      linarith [hl, Int.le_ceil (P k)]
    have h2 : (-(c k) : ℤ) ≤ ⌈P k⌉ := by exact_mod_cast h1
    omega
  · have h4 : (c k : ℝ) ≤ (⌈P k⌉ : ℤ) := le_trans hr (Int.le_ceil (P k))
    exact_mod_cast h4

end Work.HP.BoundaryMain
