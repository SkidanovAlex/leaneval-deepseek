import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.GeometryOfNumbers.SuccessiveMinima

theorem exists_gap_index {N R : ℕ} (lam : ℕ → ℝ) (hN : 1 ≤ N) (hR : R < N)
    (hmono : ∀ i j, i ≤ j → lam i ≤ lam j) (hpos : ∀ i, i ≤ N → 0 < lam i)
    (hRle : lam R ≤ 1) {ε : ℝ} (hε : 0 < ε) {Q : ℝ} (hQ : 1 < Q)
    (hgapN : Q ^ (ε / (2 * (N : ℝ))) ≤ lam N) :
    ∃ k, R ≤ k ∧ k < N ∧ lam k / lam (k + 1) ≤ Q ^ (-(ε / (2 * (N : ℝ) * ((N : ℝ) - R)))) := by
  by_contra hgoal
  push_neg at hgoal
  have hQpos : 0 < Q := lt_trans zero_lt_one hQ
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have hcast : ((N - R : ℕ) : ℝ) = (N:ℝ) - (R:ℝ) := Nat.cast_sub (le_of_lt hR)
  have hNRne0 : (N - R : ℕ) ≠ 0 := by omega
  have hNmR_ne : ((N - R : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hNRne0
  set e : ℝ := ε / (2 * (N:ℝ) * ((N:ℝ) - (R:ℝ))) with he_def
  set G : ℝ := Q ^ e with hG_def
  have hGpos : 0 < G := by rw [hG_def]; exact Real.rpow_pos_of_pos hQpos e
  have key : ∀ k, R ≤ k → k < N → lam (k+1) < G * lam k := by
    intro k hRk hkN
    have hkpos : 0 < lam (k+1) := hpos (k+1) (by omega)
    have h := hgoal k hRk hkN
    rw [lt_div_iff₀ hkpos] at h
    have hprod : Q ^ e * Q ^ (-e) = 1 := by
      rw [← Real.rpow_add hQpos, add_neg_cancel, Real.rpow_zero]
    have h2 : Q ^ e * (Q ^ (-e) * lam (k+1)) < Q ^ e * lam k :=
      mul_lt_mul_of_pos_left h (Real.rpow_pos_of_pos hQpos e)
    have h3 : Q ^ e * (Q ^ (-e) * lam (k+1)) = lam (k+1) := by
      rw [← mul_assoc, hprod, one_mul]
    rw [h3] at h2
    rw [hG_def]
    exact h2
  have main : ∀ j, j ≤ N - R → lam (R + j) ≤ lam R * G ^ j := by
    intro j
    induction j with
    | zero =>
        intro _
        simp
    | succ j ih =>
        intro hj
        have hjle : j ≤ N - R := by omega
        have hih := ih hjle
        have hRk : R ≤ R + j := by omega
        have hkN : R + j < N := by omega
        have hkey := key (R + j) hRk hkN
        calc lam (R + j + 1)
            _ ≤ G * lam (R + j) := le_of_lt hkey
            _ ≤ G * (lam R * G ^ j) := mul_le_mul_of_nonneg_left hih hGpos.le
            _ = lam R * G ^ (j+1) := by rw [pow_succ']; ring
  have strict_main : ∀ j, 1 ≤ j → j ≤ N - R → lam (R + j) < lam R * G ^ j := by
    intro j hj1 hjle
    have hle' : j - 1 ≤ N - R := by omega
    have hmain := main (j-1) hle'
    have hRk : R ≤ R + (j-1) := by omega
    have hkN : R + (j-1) < N := by omega
    have hkey := key (R + (j-1)) hRk hkN
    calc lam (R + j)
        = lam (R + (j-1) + 1) := by congr 1; omega
        _ < G * lam (R + (j-1)) := hkey
        _ ≤ G * (lam R * G ^ (j-1)) := mul_le_mul_of_nonneg_left hmain hGpos.le
        _ = lam R * G ^ j := by
              conv_rhs => rw [show j = j - 1 + 1 by omega, pow_succ']
              ring
  have hNRpos : 1 ≤ N - R := by omega
  have hstrict := strict_main (N-R) hNRpos (le_refl _)
  have hRadd : R + (N - R) = N := by omega
  rw [hRadd] at hstrict
  have he_mul : e * (((N - R : ℕ)) : ℝ) = ε / (2 * (N:ℝ)) := by
    rw [he_def, ← hcast]
    rw [div_mul_eq_mul_div]
    exact mul_div_mul_right (c := (((N - R : ℕ)) : ℝ)) ε (2 * (N:ℝ)) hNmR_ne
  have hpow : G ^ (N - R) = Q ^ (ε / (2 * (N:ℝ))) := by
    have h1 : G ^ (N - R) = G ^ (((N-R:ℕ)):ℝ) := (Real.rpow_natCast G (N-R)).symm
    rw [h1, hG_def]
    rw [← Real.rpow_mul hQpos.le e (((N-R:ℕ)):ℝ)]
    rw [he_mul]
  have hNlt : lam N < lam R * Q ^ (ε / (2 * (N:ℝ))) := by
    calc lam N < lam R * G ^ (N - R) := hstrict
      _ = lam R * Q ^ (ε / (2 * (N:ℝ))) := by rw [hpow]
  have hQpowpos : 0 ≤ Q ^ (ε / (2 * (N:ℝ))) := le_of_lt (Real.rpow_pos_of_pos hQpos _)
  have hbound : lam R * Q ^ (ε / (2 * (N:ℝ))) ≤ Q ^ (ε / (2 * (N:ℝ))) :=
    mul_le_of_le_one_left hQpowpos hRle
  exact (not_lt_of_ge hgapN) (lt_of_lt_of_le hNlt hbound)

end Commons.GeometryOfNumbers.SuccessiveMinima