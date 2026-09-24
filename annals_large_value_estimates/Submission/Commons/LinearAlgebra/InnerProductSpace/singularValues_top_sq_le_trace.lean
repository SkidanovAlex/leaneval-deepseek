import Submission.Commons.LinearAlgebra.InnerProductSpace.singularValues_top_le_trace_bound

namespace Commons.LinearAlgebra.InnerProductSpace

theorem singularValues_top_sq_le_trace
    {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F) {m : ℕ} (hm : Module.finrank 𝕜 F = m)
    (hm1 : 1 ≤ m) :
    T.singularValues 0 ^ 2 ≤
      8 * (∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i ^ 6
            - (∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i ^ 2) ^ 3 / (m : ℝ) ^ 2)
          ^ (1 / 3 : ℝ)
      + 8 * ((∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i ^ 2) / (m : ℝ)) := by
  subst hm
  have hvanish : ∀ i : ℕ, Module.finrank 𝕜 F ≤ i → T.singularValues i = 0 := by
    intro i hi
    have hrank : Module.finrank 𝕜 T.range ≤ Module.finrank 𝕜 F := Submodule.finrank_le T.range
    have hlt : ¬ i < Module.finrank 𝕜 T.range := by omega
    have h : ¬ 0 < T.singularValues i := by
      rw [T.singularValues_pos_iff_lt_finrank_range]; exact hlt
    exact le_antisymm (not_lt.mp h) (T.singularValues_nonneg i)
  have h2v : (∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i ^ 2)
      = ∑ i ∈ Finset.range (Module.finrank 𝕜 F), T.singularValues i ^ 2 :=
    sum_fin_eq_sum_range_of_vanish (fun i => T.singularValues i ^ 2)
      (fun i hi => by rw [T.singularValues_of_finrank_le hi]; ring)
      (fun i hi => by rw [hvanish i hi]; ring)
  have h6v : (∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i ^ 6)
      = ∑ i ∈ Finset.range (Module.finrank 𝕜 F), T.singularValues i ^ 6 :=
    sum_fin_eq_sum_range_of_vanish (fun i => T.singularValues i ^ 6)
      (fun i hi => by rw [T.singularValues_of_finrank_le hi]; ring)
      (fun i hi => by rw [hvanish i hi]; ring)
  have hmpos : (0:ℝ) < (Module.finrank 𝕜 F : ℝ) := by
    have : 0 < Module.finrank 𝕜 F := lt_of_lt_of_le Nat.zero_lt_one hm1
    exact_mod_cast this
  have hPQ : (∑ i ∈ Finset.range (Module.finrank 𝕜 F), T.singularValues i ^ 2) ^ 3
      ≤ (Module.finrank 𝕜 F : ℝ) ^ 2
        * ∑ i ∈ Finset.range (Module.finrank 𝕜 F), T.singularValues i ^ 6 := by
    have h1 := pow_sum_div_card_le_sum_pow (s := Finset.range (Module.finrank 𝕜 F))
        (f := fun i => T.singularValues i ^ 2) (fun i _ => by positivity) 2
    simp only [Finset.card_range] at h1
    rw [show (2:ℕ) + 1 = 3 from rfl] at h1
    have h2 : (∑ i ∈ Finset.range (Module.finrank 𝕜 F), (T.singularValues i ^ 2) ^ 3)
        = ∑ i ∈ Finset.range (Module.finrank 𝕜 F), T.singularValues i ^ 6 := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [h2] at h1
    rw [div_le_iff₀ (pow_pos hmpos 2)] at h1
    nlinarith [h1]
  set A : ℝ := (∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i ^ 6)
      - (∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i ^ 2) ^ 3
          / (Module.finrank 𝕜 F : ℝ) ^ 2 with hAdef
  set B : ℝ := (∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i ^ 2)
      / (Module.finrank 𝕜 F : ℝ) with hBdef
  have hA : 0 ≤ A := by
    rw [hAdef, h2v, h6v, sub_nonneg, div_le_iff₀ (pow_pos hmpos 2)]
    nlinarith [hPQ]
  have hB : 0 ≤ B := by
    rw [hBdef]
    apply div_nonneg
    · apply Finset.sum_nonneg; intro i _; exact pow_nonneg (T.singularValues_nonneg i) 2
    · exact hmpos.le
  have hbd : T.singularValues 0 ≤ 2 * A ^ (1/6:ℝ) + 2 * B ^ (1/2:ℝ) := by
    have h := singularValues_top_le_trace_bound T rfl hm1
    rw [← hAdef, ← hBdef] at h
    exact h
  have key1 : T.singularValues 0 ^ 2 ≤ (2 * A ^ (1/6:ℝ) + 2 * B ^ (1/2:ℝ)) ^ 2 :=
    pow_le_pow_left₀ (T.singularValues_nonneg 0) hbd 2
  have key2 : (2 * A ^ (1/6:ℝ) + 2 * B ^ (1/2:ℝ)) ^ (2:ℕ) ≤ 8 * A ^ (1/3:ℝ) + 8 * B := by
    have hA13 : (A ^ (1/6:ℝ)) ^ (2:ℕ) = A ^ (1/3:ℝ) := by
      rw [← Real.rpow_mul_natCast hA (1/6) 2, show (1/6:ℝ) * (2:ℕ) = 1/3 by norm_num]
    have hB12 : (B ^ (1/2:ℝ)) ^ (2:ℕ) = B := by
      rw [← Real.rpow_mul_natCast hB (1/2) 2, show (1/2:ℝ) * (2:ℕ) = 1 by norm_num,
        Real.rpow_one]
    have hmain : (2 * A ^ (1/6:ℝ) + 2 * B ^ (1/2:ℝ)) ^ (2:ℕ)
        ≤ 8 * (A ^ (1/6:ℝ)) ^ (2:ℕ) + 8 * (B ^ (1/2:ℝ)) ^ (2:ℕ) := by
      nlinarith [sq_nonneg (A ^ (1/6:ℝ) - B ^ (1/2:ℝ))]
    calc (2 * A ^ (1/6:ℝ) + 2 * B ^ (1/2:ℝ)) ^ (2:ℕ)
        ≤ 8 * (A ^ (1/6:ℝ)) ^ (2:ℕ) + 8 * (B ^ (1/2:ℝ)) ^ (2:ℕ) := hmain
      _ = 8 * A ^ (1/3:ℝ) + 8 * B := by rw [hA13, hB12]
  linarith [key1, key2]

end Commons.LinearAlgebra.InnerProductSpace
