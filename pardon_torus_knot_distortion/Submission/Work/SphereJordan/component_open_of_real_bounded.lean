import Mathlib

namespace Work.SphereJordan

open Set

/-- Auxiliary: in an open subset of `ℝ`, every point has another point of the set strictly
below it and another strictly above it. -/
theorem exists_lt_mem_of_isOpen {K : Set ℝ} (hK : IsOpen K) {x : ℝ} (hx : x ∈ K) :
    ∃ y ∈ K, y < x := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hK.mem_nhds hx)
  refine ⟨x - ε / 2, hεsub ?_, by linarith⟩
  rw [Metric.mem_ball, Real.dist_eq]
  have h1 : x - ε / 2 - x = -(ε / 2) := by ring
  rw [h1, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
  linarith

/-- Auxiliary: in an open subset of `ℝ`, every point has another point of the set strictly
above it. -/
theorem exists_gt_mem_of_isOpen {K : Set ℝ} (hK : IsOpen K) {x : ℝ} (hx : x ∈ K) :
    ∃ y ∈ K, x < y := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hK.mem_nhds hx)
  refine ⟨x + ε / 2, hεsub ?_, by linarith⟩
  rw [Metric.mem_ball, Real.dist_eq]
  have h1 : x + ε / 2 - x = ε / 2 := by ring
  rw [h1, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
  linarith

theorem component_open_of_real_bounded {P : Set ℝ} (hP : IsOpen P) {t₀ : ℝ} (ht₀ : t₀ ∈ P)
    (hbdd : Bornology.IsBounded (connectedComponentIn P t₀)) :
    ∃ s₀ s₁ : ℝ, connectedComponentIn P t₀ = Set.Ioo s₀ s₁ ∧ s₀ < t₀ ∧ t₀ < s₁ ∧
      s₀ ∉ P ∧ s₁ ∉ P := by
  set K := connectedComponentIn P t₀ with hKdef
  have hKopen : IsOpen K := hP.connectedComponentIn
  have hKord : K.OrdConnected := (isPreconnected_connectedComponentIn (x := t₀) (F := P)).ordConnected
  have ht₀K : t₀ ∈ K := mem_connectedComponentIn ht₀
  have hKsub : K ⊆ P := connectedComponentIn_subset P t₀
  have hKne : K.Nonempty := ⟨t₀, ht₀K⟩
  -- boundedness of K gives upper and lower bounds
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hbdd
  have hbound : ∀ x ∈ K, |x| ≤ r := by
    intro x hx
    have h1 : dist x 0 ≤ r := hr hx
    rw [Real.dist_eq] at h1
    simpa using h1
  have hbddBelow : BddBelow K := ⟨-r, fun x hx => (abs_le.mp (hbound x hx)).1⟩
  have hbddAbove : BddAbove K := ⟨r, fun x hx => (abs_le.mp (hbound x hx)).2⟩
  -- strict bounds around t₀
  obtain ⟨y₀, hy₀K, hy₀⟩ := exists_lt_mem_of_isOpen hKopen ht₀K
  obtain ⟨y₁, hy₁K, hy₁⟩ := exists_gt_mem_of_isOpen hKopen ht₀K
  have hs₀_lt : sInf K < t₀ := lt_of_le_of_lt (csInf_le hbddBelow hy₀K) hy₀
  have ht₀_lt_s₁ : t₀ < sSup K := lt_of_lt_of_le hy₁ (le_csSup hbddAbove hy₁K)
  have hs₀_lt_s₁ : sInf K < sSup K := lt_trans hs₀_lt ht₀_lt_s₁
  -- K ⊆ Ioo (sInf K) (sSup K)
  have hsubset1 : K ⊆ Ioo (sInf K) (sSup K) := by
    intro x hx
    constructor
    · rcases lt_or_eq_of_le (csInf_le hbddBelow hx) with h | h
      · exact h
      · exfalso
        have hxK : sInf K ∈ K := by rw [h]; exact hx
        obtain ⟨y, hyK, hy⟩ := exists_lt_mem_of_isOpen hKopen hxK
        have := csInf_le hbddBelow hyK
        linarith
    · rcases lt_or_eq_of_le (le_csSup hbddAbove hx) with h | h
      · exact h
      · exfalso
        have hxK : sSup K ∈ K := by rw [← h]; exact hx
        obtain ⟨y, hyK, hy⟩ := exists_gt_mem_of_isOpen hKopen hxK
        have := le_csSup hbddAbove hyK
        linarith
  -- Ioo (sInf K) (sSup K) ⊆ K
  have hsubset2 : Ioo (sInf K) (sSup K) ⊆ K := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨a, haK, hau⟩ := exists_lt_of_csInf_lt hKne hu1
    obtain ⟨b, hbK, hub⟩ := exists_lt_of_lt_csSup hKne hu2
    exact hKord.out haK hbK ⟨le_of_lt hau, le_of_lt hub⟩
  have hKeq : K = Ioo (sInf K) (sSup K) := subset_antisymm hsubset1 hsubset2
  -- endpoints are not in P
  have hs₀_notP : sInf K ∉ P := by
    intro hs₀P
    have hIcoSub : Ico (sInf K) (sSup K) ⊆ P := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with h | h
      · rw [← h]; exact hs₀P
      · exact hKsub (by rw [hKeq]; exact ⟨h, hx.2⟩)
    have hmem : t₀ ∈ Ico (sInf K) (sSup K) := ⟨le_of_lt hs₀_lt, ht₀_lt_s₁⟩
    have hsub : Ico (sInf K) (sSup K) ⊆ K :=
      (isPreconnected_Ico (a := sInf K) (b := sSup K)).subset_connectedComponentIn hmem hIcoSub
    have hs₀K : sInf K ∈ K := hsub ⟨le_refl _, hs₀_lt_s₁⟩
    have : sInf K ∈ Ioo (sInf K) (sSup K) := by rw [← hKeq]; exact hs₀K
    exact lt_irrefl _ this.1
  have hs₁_notP : sSup K ∉ P := by
    intro hs₁P
    have hIocSub : Ioc (sInf K) (sSup K) ⊆ P := by
      intro x hx
      rcases eq_or_lt_of_le hx.2 with h | h
      · rw [h]; exact hs₁P
      · exact hKsub (by rw [hKeq]; exact ⟨hx.1, h⟩)
    have hmem : t₀ ∈ Ioc (sInf K) (sSup K) := ⟨hs₀_lt, le_of_lt ht₀_lt_s₁⟩
    have hsub : Ioc (sInf K) (sSup K) ⊆ K :=
      (isPreconnected_Ioc (a := sInf K) (b := sSup K)).subset_connectedComponentIn hmem hIocSub
    have hs₁K : sSup K ∈ K := hsub ⟨hs₀_lt_s₁, le_refl _⟩
    have : sSup K ∈ Ioo (sInf K) (sSup K) := by rw [← hKeq]; exact hs₁K
    exact lt_irrefl _ this.2
  exact ⟨sInf K, sSup K, hKeq, hs₀_lt, ht₀_lt_s₁, hs₀_notP, hs₁_notP⟩

end Work.SphereJordan
