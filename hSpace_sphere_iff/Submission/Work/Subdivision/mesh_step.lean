import Mathlib

namespace Work.Subdivision

/-- Auxiliary: any two points of `Set.range p` are within the diameter of that set. -/
private lemma range_dist_le_diam {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]
    (p : ι → E) (a b : ι) : ‖p a - p b‖ ≤ Metric.diam (Set.range p) := by
  have hb : Bornology.IsBounded (Set.range p) := (Set.finite_range p).isBounded
  have h := Metric.dist_le_diam_of_mem hb (Set.mem_range_self a) (Set.mem_range_self b)
  rwa [dist_eq_norm] at h

/-- The centroid of a nonempty finset is within the diameter of `Set.range p` of every `p i`. -/
private lemma centroid_dist_le_diam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (p : ι → E) (S : Finset ι) (hS : S.Nonempty) (i : ι) :
    ‖(S.card : ℝ)⁻¹ • (∑ j ∈ S, p j) - p i‖ ≤ Metric.diam (Set.range p) := by
  have hSc_pos : (0:ℝ) < S.card := by
    have : 0 < S.card := hS.card_pos
    exact_mod_cast this
  have hSc_ne : (S.card : ℝ) ≠ 0 := ne_of_gt hSc_pos
  have hsplit : ∑ j ∈ S, (p j - p i) = (∑ j ∈ S, p j) - (S.card : ℝ) • p i := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  have heq : (S.card : ℝ)⁻¹ • (∑ j ∈ S, p j) - p i
      = (S.card : ℝ)⁻¹ • (∑ j ∈ S, (p j - p i)) := by
    rw [hsplit, smul_sub, smul_smul, inv_mul_cancel₀ hSc_ne, one_smul]
  rw [heq]
  calc ‖(S.card : ℝ)⁻¹ • (∑ j ∈ S, (p j - p i))‖
      = (S.card : ℝ)⁻¹ * ‖∑ j ∈ S, (p j - p i)‖ := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg (le_of_lt hSc_pos)]
    _ ≤ (S.card : ℝ)⁻¹ * ∑ j ∈ S, ‖p j - p i‖ := by
        apply mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (le_of_lt hSc_pos))
    _ ≤ (S.card : ℝ)⁻¹ * ∑ j ∈ S, Metric.diam (Set.range p) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hSc_pos))
        exact Finset.sum_le_sum (fun j _ => range_dist_le_diam p j i)
    _ = Metric.diam (Set.range p) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hSc_ne, one_mul]

theorem mesh_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (p : ι → E) (S T : Finset ι) (hS : S.Nonempty) (hST : S ⊆ T) :
    ‖(S.card : ℝ)⁻¹ • (∑ i ∈ S, p i) - (T.card : ℝ)⁻¹ • (∑ i ∈ T, p i)‖
      ≤ ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι) * Metric.diam (Set.range p) := by
  classical
  set x := (S.card : ℝ)⁻¹ • (∑ i ∈ S, p i) with hx
  set y := (T.card : ℝ)⁻¹ • (∑ i ∈ T, p i) with hy
  set d := Metric.diam (Set.range p) with hd
  have hSpos : 0 < S.card := hS.card_pos
  have hSc_ne : (S.card : ℝ) ≠ 0 := by
    have : (0:ℝ) < S.card := by exact_mod_cast hSpos
    exact ne_of_gt this
  have hT : T.Nonempty := hS.mono hST
  have hTc_pos : (0:ℝ) < T.card := by
    have : 0 < T.card := hT.card_pos
    exact_mod_cast this
  have hTc_ne : (T.card : ℝ) ≠ 0 := ne_of_gt hTc_pos
  have hSleT : S.card ≤ T.card := Finset.card_le_card hST
  have hTleN : T.card ≤ Fintype.card ι := Finset.card_le_univ T
  have hd_nonneg : 0 ≤ d := by rw [hd]; exact Metric.diam_nonneg
  have hsum_S : (S.card : ℝ) • x = ∑ i ∈ S, p i := by
    rw [hx, smul_smul, mul_inv_cancel₀ hSc_ne, one_smul]
  have hx_bound : ∀ i : ι, ‖x - p i‖ ≤ d := by
    intro i
    rw [hd]
    have hsplit : ∑ j ∈ S, (p j - p i) = (∑ j ∈ S, p j) - (S.card : ℝ) • p i := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
    have heq : x - p i = (S.card : ℝ)⁻¹ • (∑ j ∈ S, (p j - p i)) := by
      rw [hx, hsplit, smul_sub, smul_smul, inv_mul_cancel₀ hSc_ne, one_smul]
    rw [heq]
    calc ‖(S.card : ℝ)⁻¹ • (∑ j ∈ S, (p j - p i))‖
        = (S.card : ℝ)⁻¹ * ‖∑ j ∈ S, (p j - p i)‖ := by
          rw [norm_smul, norm_inv, Real.norm_of_nonneg (le_of_lt (by
            have : (0:ℝ) < S.card := by exact_mod_cast hSpos
            exact this))]
      _ ≤ (S.card : ℝ)⁻¹ * ∑ j ∈ S, ‖p j - p i‖ := by
          apply mul_le_mul_of_nonneg_left (norm_sum_le _ _)
          have : (0:ℝ) < S.card := by exact_mod_cast hSpos
          exact inv_nonneg.mpr (le_of_lt this)
      _ ≤ (S.card : ℝ)⁻¹ * ∑ j ∈ S, Metric.diam (Set.range p) := by
          apply mul_le_mul_of_nonneg_left _
          have : (0:ℝ) < S.card := by exact_mod_cast hSpos
          exact inv_nonneg.mpr (le_of_lt this)
          exact Finset.sum_le_sum (fun j _ => range_dist_le_diam p j i)
      _ = Metric.diam (Set.range p) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hSc_ne, one_mul]
  have hsumT : ∑ i ∈ T, p i = (∑ i ∈ T\S, p i) + (S.card : ℝ) • x := by
    rw [← Finset.sum_sdiff hST, hsum_S]
  have hR : ∑ i ∈ T\S, (x - p i) = ((T\S).card : ℝ) • x - ∑ i ∈ T\S, p i := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  have hcard : ((T\S).card : ℝ) = (T.card : ℝ) - (S.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hST, Nat.cast_sub hSleT]
  have key : (T.card : ℝ) • x - ∑ i ∈ T, p i = ∑ i ∈ T\S, (x - p i) := by
    rw [hsumT, hR, hcard, sub_smul]
    abel
  have hxy : x - y = (T.card : ℝ)⁻¹ • ∑ i ∈ T\S, (x - p i) := by
    rw [← key, smul_sub, smul_smul, inv_mul_cancel₀ hTc_ne, one_smul, ← hy]
  have hZ : ‖∑ i ∈ T\S, (x - p i)‖ ≤ ((T\S).card : ℝ) * d := by
    calc ‖∑ i ∈ T\S, (x - p i)‖ ≤ ∑ i ∈ T\S, ‖x - p i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ T\S, d := Finset.sum_le_sum (fun i _ => hx_bound i)
      _ = ((T\S).card : ℝ) * d := by rw [Finset.sum_const, nsmul_eq_mul]
  have hTleN_real : (T.card:ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hTleN
  have hn_pos : (0:ℝ) < (Fintype.card ι : ℝ) := lt_of_lt_of_le hTc_pos hTleN_real
  have hcoe : ((T.card:ℝ) - (S.card:ℝ)) / (T.card:ℝ)
      ≤ ((Fintype.card ι:ℝ) - 1) / (Fintype.card ι) := by
    have hSge1 : (1:ℝ) ≤ (S.card:ℝ) := by
      have h1 : (1:ℕ) ≤ S.card := Finset.one_le_card.mpr hS
      exact_mod_cast h1
    have h1 : (T.card:ℝ) - (S.card:ℝ) ≤ (T.card:ℝ) - 1 := by linarith
    have h2 : ((T.card:ℝ) - (S.card:ℝ)) / (T.card:ℝ) ≤ ((T.card:ℝ) - 1) / (T.card:ℝ) :=
      div_le_div_of_nonneg_right h1 (le_of_lt hTc_pos)
    have h3 : ((T.card:ℝ) - 1) / (T.card:ℝ) ≤ ((Fintype.card ι:ℝ) - 1) / (Fintype.card ι) := by
      have hTeq : ((T.card:ℝ) - 1) / (T.card:ℝ) = 1 - 1/(T.card:ℝ) := by
        rw [sub_div, div_self hTc_ne]
      have hNeq : ((Fintype.card ι:ℝ) - 1) / (Fintype.card ι) = 1 - 1/(Fintype.card ι) := by
        rw [sub_div, div_self (ne_of_gt hn_pos)]
      rw [hTeq, hNeq]
      apply sub_le_sub_left
      exact one_div_le_one_div_of_le hTc_pos hTleN_real
    exact le_trans h2 h3
  calc ‖x - y‖ = ‖(T.card:ℝ)⁻¹ • ∑ i ∈ T\S, (x - p i)‖ := by rw [hxy]
    _ = (T.card:ℝ)⁻¹ * ‖∑ i ∈ T\S, (x - p i)‖ := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg (le_of_lt hTc_pos)]
    _ ≤ (T.card:ℝ)⁻¹ * (((T\S).card:ℝ) * d) :=
        mul_le_mul_of_nonneg_left hZ (inv_nonneg.mpr (le_of_lt hTc_pos))
    _ = (((T.card:ℝ) - (S.card:ℝ)) / (T.card:ℝ)) * d := by
        rw [hcard]; ring
    _ ≤ (((Fintype.card ι:ℝ) - 1) / (Fintype.card ι)) * d :=
        mul_le_mul_of_nonneg_right hcoe hd_nonneg

end Work.Subdivision
