import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.InnerProductSpace

lemma caseB_algebra {s R m : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R) (hm : 4 ≤ m)
    (h : 4 * (s ^ 2 + R) ≤ m * s ^ 2) :
    -(3 / 4) * s ^ 6 ≤ R ^ 3 / (m - 1) ^ 2 - (s ^ 2 + R) ^ 3 / m ^ 2 := by
  have hmpos : (0:ℝ) < m := by linarith
  have hP0 : (0:ℝ) ≤ s ^ 2 + R := by positivity
  have hPb : s ^ 2 + R ≤ m * s ^ 2 / 4 := by linarith
  have hP2 : (s ^ 2 + R) ^ 2 ≤ m ^ 2 * s ^ 4 / 16 := by
    nlinarith [hPb, hP0, sq_nonneg s]
  have key1 : -(3 * (s ^ 2 + R) ^ 2 * s ^ 2) ≤ R ^ 3 - (s ^ 2 + R) ^ 3 := by
    have hid : R ^ 3 - (s ^ 2 + R) ^ 3 + 3 * (s ^ 2 + R) ^ 2 * s ^ 2
        = s ^ 4 * (3 * (s ^ 2 + R) - s ^ 2) := by ring
    have hnn : 0 ≤ s ^ 4 * (3 * (s ^ 2 + R) - s ^ 2) := by
      apply mul_nonneg (pow_nonneg hs 4)
      nlinarith [hs, hR]
    linarith
  have hP2s : 3 * (s ^ 2 + R) ^ 2 * s ^ 2 ≤ (3 / 16) * m ^ 2 * s ^ 6 := by
    have h1 := mul_le_mul_of_nonneg_right hP2 (by positivity : (0:ℝ) ≤ 3 * s ^ 2)
    nlinarith [h1]
  have hms : (0:ℝ) ≤ m ^ 2 * s ^ 6 := by positivity
  have hcross : -(3 / 4) * m ^ 2 * s ^ 6 ≤ R ^ 3 - (s ^ 2 + R) ^ 3 := by
    linarith [key1, hP2s, hms]
  have hdiv : (-(3 / 4) * m ^ 2 * s ^ 6) / m ^ 2 ≤ (R ^ 3 - (s ^ 2 + R) ^ 3) / m ^ 2 :=
    div_le_div_of_nonneg_right hcross (by positivity)
  have hsimple : (-(3 / 4) * m ^ 2 * s ^ 6) / m ^ 2 = -(3 / 4) * s ^ 6 := by
    field_simp
  have hge : R ^ 3 / m ^ 2 ≤ R ^ 3 / (m - 1) ^ 2 := by
    apply div_le_div_of_nonneg_left (pow_nonneg hR 3)
    · nlinarith
    · nlinarith
  calc R ^ 3 / (m - 1) ^ 2 - (s ^ 2 + R) ^ 3 / m ^ 2
      ≥ R ^ 3 / m ^ 2 - (s ^ 2 + R) ^ 3 / m ^ 2 := by linarith [hge]
    _ = (R ^ 3 - (s ^ 2 + R) ^ 3) / m ^ 2 := by rw [sub_div]
    _ ≥ (-(3 / 4) * m ^ 2 * s ^ 6) / m ^ 2 := hdiv
    _ = -(3 / 4) * s ^ 6 := hsimple

lemma key_real {m : ℕ} (hm : 1 ≤ m) (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    x 0 ≤ 2 * ((∑ i ∈ Finset.range m, x i ^ 6)
                - (∑ i ∈ Finset.range m, x i ^ 2) ^ 3 / (m : ℝ) ^ 2) ^ (1 / 6 : ℝ)
         + 2 * ((∑ i ∈ Finset.range m, x i ^ 2) / (m : ℝ)) ^ (1 / 2 : ℝ) := by
  set P : ℝ := ∑ i ∈ Finset.range m, x i ^ 2 with hPdef
  set Q : ℝ := ∑ i ∈ Finset.range m, x i ^ 6 with hQdef
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hx0 : (0:ℝ) ≤ x 0 := hx 0
  have hP0 : 0 ≤ P := by
    rw [hPdef]; exact Finset.sum_nonneg fun i _ => by positivity
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]; exact Finset.sum_nonneg fun i _ => by positivity
  have hs2P : x 0 ^ 2 ≤ P := by
    rw [hPdef]
    exact Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => by positivity)
      (a := 0) (Finset.mem_range.mpr (lt_of_lt_of_le Nat.zero_lt_one hm))
  have hPQ : P ^ 3 ≤ (m:ℝ) ^ 2 * Q := by
    have h1 := pow_sum_div_card_le_sum_pow (s := Finset.range m)
        (f := fun i => x i ^ 2) (fun i _ => by positivity) 2
    simp only [Finset.card_range] at h1
    rw [show (2:ℕ) + 1 = 3 from rfl] at h1
    have h2 : (∑ i ∈ Finset.range m, (x i ^ 2) ^ 3) = ∑ i ∈ Finset.range m, x i ^ 6 := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [h2, ← hPdef, ← hQdef] at h1
    rw [div_le_iff₀ (pow_pos hmpos 2)] at h1
    nlinarith [h1]
  have hrad0 : 0 ≤ Q - P ^ 3 / (m:ℝ) ^ 2 := by
    rw [sub_nonneg, div_le_iff₀ (pow_pos hmpos 2)]
    nlinarith [hPQ]
  by_cases hA : (m:ℝ) * x 0 ^ 2 ≤ 4 * P
  · have hle : x 0 / 2 ≤ (P / (m:ℝ)) ^ (1/2:ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by positivity) (by positivity)]
      rw [div_pow, show (2:ℝ)^2 = 4 by norm_num]
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) hmpos]
      nlinarith [hA]
    have key : x 0 ≤ 2 * (Q - P ^ 3 / (m:ℝ) ^ 2) ^ (1/6:ℝ)
        + 2 * (P / (m:ℝ)) ^ (1/2:ℝ) := by
      have h1 : 0 ≤ 2 * (Q - P ^ 3 / (m:ℝ) ^ 2) ^ (1/6:ℝ) := by
        have := Real.rpow_nonneg hrad0 (1/6:ℝ); linarith
      linarith
    exact key
  · push Not at hA
    by_cases hs0 : x 0 = 0
    · have key : x 0 ≤ 2 * (Q - P ^ 3 / (m:ℝ) ^ 2) ^ (1/6:ℝ)
          + 2 * (P / (m:ℝ)) ^ (1/2:ℝ) := by
        rw [hs0]
        have h1 : 0 ≤ 2 * (Q - P ^ 3 / (m:ℝ) ^ 2) ^ (1/6:ℝ) := by
          have := Real.rpow_nonneg hrad0 (1/6:ℝ); linarith
        have h2 : 0 ≤ 2 * (P / (m:ℝ)) ^ (1/2:ℝ) := by
          have := Real.rpow_nonneg (show (0:ℝ) ≤ P/(m:ℝ) by positivity) (1/2:ℝ); linarith
        linarith
      exact key
    · have hs0pos : 0 < x 0 := lt_of_le_of_ne (hx 0) (Ne.symm hs0)
      have hm4 : (4:ℝ) ≤ (m:ℝ) := by
        have h1 : 4 * x 0 ^ 2 ≤ (m:ℝ) * x 0 ^ 2 := by nlinarith [hA, hs2P]
        have h2 : 0 < x 0 ^ 2 := pow_pos hs0pos 2
        exact le_of_mul_le_mul_right h1 h2
      have h0mem : 0 ∈ Finset.range m :=
        Finset.mem_range.mpr (lt_of_lt_of_le Nat.zero_lt_one hm)
      set R : ℝ := ∑ i ∈ (Finset.range m).erase 0, x i ^ 2 with hRdef
      set Qr : ℝ := ∑ i ∈ (Finset.range m).erase 0, x i ^ 6 with hQrdef
      have hR0 : 0 ≤ R := by rw [hRdef]; exact Finset.sum_nonneg fun i _ => by positivity
      have hPeq : P = x 0 ^ 2 + R := by
        have h := Finset.sum_erase_add (Finset.range m) (fun i => x i ^ 2) h0mem
        rw [hPdef, hRdef]; linarith
      have hQeq : Q = x 0 ^ 6 + Qr := by
        have h := Finset.sum_erase_add (Finset.range m) (fun i => x i ^ 6) h0mem
        rw [hQdef, hQrdef]; linarith
      have hm4nat : 4 ≤ m := by exact_mod_cast hm4
      have hmcrit : (0:ℝ) < (((m - 1 : ℕ) : ℝ)) := by
        have : 0 < m - 1 := by omega
        exact_mod_cast this
      have hmR : R ^ 3 ≤ (((m - 1 : ℕ) : ℝ)) ^ 2 * Qr := by
        have h1 := pow_sum_div_card_le_sum_pow (s := (Finset.range m).erase 0)
            (f := fun i => x i ^ 2) (fun i _ => by positivity) 2
        have hc : ((Finset.range m).erase 0).card = m - 1 := by
          rw [Finset.card_erase_of_mem h0mem, Finset.card_range]
        rw [hc, show (2:ℕ) + 1 = 3 from rfl] at h1
        have h2 : (∑ i ∈ (Finset.range m).erase 0, (x i ^ 2) ^ 3)
            = ∑ i ∈ (Finset.range m).erase 0, x i ^ 6 := by
          apply Finset.sum_congr rfl; intro i _; ring
        rw [h2, ← hRdef, ← hQrdef] at h1
        rw [div_le_iff₀ (pow_pos hmcrit 2)] at h1
        nlinarith [h1]
      have hcast : (((m - 1 : ℕ) : ℝ)) = (m:ℝ) - 1 := by
        rw [Nat.cast_sub hm]; norm_num
      have hRad : x 0 ^ 6 / 4 ≤ Q - P ^ 3 / (m:ℝ) ^ 2 := by
        have halg := caseB_algebra (s := x 0) (R := R) (m := (m:ℝ)) (hx 0) hR0 hm4 (by
          rw [← hPeq]; linarith)
        have hQrb : R ^ 3 / ((m:ℝ) - 1) ^ 2 ≤ Qr := by
          rw [div_le_iff₀ (pow_pos (by linarith : (0:ℝ) < (m:ℝ)-1) 2)]
          rw [hcast] at hmR
          linarith [hmR]
        rw [hQeq, hPeq]
        linarith [halg, hQrb]
      have hroot : x 0 / 2 ≤ (Q - P ^ 3 / (m:ℝ) ^ 2) ^ (1/6:ℝ) := by
        have ht : (0:ℝ) ≤ x 0 / 2 := by positivity
        have hroot2 : ((x 0 / 2) ^ 6 : ℝ) ^ (1/6:ℝ) = x 0 / 2 := by
          rw [← Real.rpow_natCast (x 0 / 2) 6, ← Real.rpow_mul ht,
            show ((6:ℕ):ℝ) * (1/6) = 1 by norm_num, Real.rpow_one]
        have h64 : (x 0 / 2) ^ 6 ≤ x 0 ^ 6 / 4 := by
          have h : (x 0 / 2) ^ 6 = x 0 ^ 6 / 64 := by ring
          have h6 : (0:ℝ) ≤ x 0 ^ 6 := by positivity
          rw [h]; linarith
        calc x 0 / 2 = ((x 0 / 2) ^ 6 : ℝ) ^ (1/6:ℝ) := hroot2.symm
          _ ≤ (x 0 ^ 6 / 4 : ℝ) ^ (1/6:ℝ) :=
              Real.rpow_le_rpow (by positivity) h64 (by norm_num)
          _ ≤ (Q - P ^ 3 / (m:ℝ) ^ 2) ^ (1/6:ℝ) :=
              Real.rpow_le_rpow (by positivity) hRad (by norm_num)
      have key : x 0 ≤ 2 * (Q - P ^ 3 / (m:ℝ) ^ 2) ^ (1/6:ℝ)
          + 2 * (P / (m:ℝ)) ^ (1/2:ℝ) := by
        have h2 : 0 ≤ 2 * (P / (m:ℝ)) ^ (1/2:ℝ) := by
          have := Real.rpow_nonneg (show (0:ℝ) ≤ P/(m:ℝ) by positivity) (1/2:ℝ); linarith
        linarith
      exact key

lemma sum_fin_eq_sum_range_of_vanish {n m : ℕ} (g : ℕ → ℝ)
    (hn : ∀ i, n ≤ i → g i = 0) (hM : ∀ i, m ≤ i → g i = 0) :
    (∑ i : Fin n, g i) = ∑ i ∈ Finset.range m, g i := by
  rw [Fin.sum_univ_eq_sum_range]
  have h1 : ∑ i ∈ Finset.range (min n m), g i = ∑ i ∈ Finset.range n, g i := by
    apply Finset.sum_subset (Finset.range_mono (Nat.min_le_left n m))
    intro i hi hni
    simp only [Finset.mem_range, not_lt] at hi hni
    exact hM i (by omega)
  have h2 : ∑ i ∈ Finset.range (min n m), g i = ∑ i ∈ Finset.range m, g i := by
    apply Finset.sum_subset (Finset.range_mono (Nat.min_le_right n m))
    intro i hi hni
    simp only [Finset.mem_range, not_lt] at hi hni
    exact hn i (by omega)
  rw [← h1, h2]

theorem singularValues_top_le_trace_bound
    {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F) {m : ℕ} (hm : Module.finrank 𝕜 F = m) (hm1 : 1 ≤ m) :
    T.singularValues 0 ≤
      2 * (∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i ^ 6
            - (∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i ^ 2) ^ 3 / (m : ℝ) ^ 2)
          ^ (1 / 6 : ℝ)
      + 2 * ((∑ i : Fin (Module.finrank 𝕜 E), T.singularValues i ^ 2) / (m : ℝ)) ^ (1 / 2 : ℝ) := by
  subst hm
  have hnonneg : ∀ i : ℕ, 0 ≤ T.singularValues i := fun i => T.singularValues_nonneg i
  have hvanish : ∀ i : ℕ, Module.finrank 𝕜 F ≤ i → T.singularValues i = 0 := by
    intro i hi
    have hrank : Module.finrank 𝕜 T.range ≤ Module.finrank 𝕜 F := Submodule.finrank_le T.range
    have hlt : ¬ i < Module.finrank 𝕜 T.range := by omega
    have h : ¬ 0 < T.singularValues i := by
      rw [T.singularValues_pos_iff_lt_finrank_range]; exact hlt
    exact le_antisymm (not_lt.mp h) (T.singularValues_nonneg i)
  have hkey := key_real hm1 (fun i => T.singularValues i) hnonneg
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
  rw [h2v, h6v]
  exact hkey

end Commons.LinearAlgebra.InnerProductSpace