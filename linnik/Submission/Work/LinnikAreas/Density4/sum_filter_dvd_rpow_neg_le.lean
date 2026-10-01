import Mathlib

set_option linter.unusedVariables false

namespace Work.LinnikAreas.Density4

/-- Sum bound for `e^{-σ}` over the multiples of `h` in `[1, B]`, for `0 ≤ σ ≤ 1`:
`Σ_{e ≤ B, h ∣ e} e^{-σ} ≤ B^{1-σ} (1 + log B) / h`.

Writing `e = h k` and using `e^{1-σ} ≤ B^{1-σ}` together with `1/(hk) = (1/h)(1/k)`
reduces the estimate to the harmonic bound `Σ_{k=1}^{B} 1/k ≤ 1 + log B`. -/
lemma sum_filter_dvd_rpow_neg_le {h B : ℕ} (hh : 1 ≤ h) (hB : 1 ≤ B) {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∑ e ∈ (Finset.Icc 1 B).filter (fun e => h ∣ e), (e : ℝ) ^ (-σ)
      ≤ (B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ)) / (h : ℝ) := by
  classical
  have hhpos : (0 : ℕ) < h := by omega
  have hhRpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    have : (0 : ℕ) < B := by omega
    exact_mod_cast this
  have hexp : (0 : ℝ) ≤ 1 - σ := by linarith [hσ0, hσ1]
  -- The index set of quotients: `k ≤ B` with `h * k ≤ B`.
  set T : Finset ℕ := (Finset.Icc 1 B).filter (fun k => h * k ≤ B) with hTdef
  have hTmem : ∀ k : ℕ, k ∈ T ↔ 1 ≤ k ∧ k ≤ B ∧ h * k ≤ B := by
    intro k
    simp only [hTdef, Finset.mem_filter, Finset.mem_Icc, and_assoc]
  -- The multiples of `h` in `[1, B]` are exactly `{h * k : k ∈ T}`.
  have himage : T.image (fun k => h * k) = (Finset.Icc 1 B).filter (fun e => h ∣ e) := by
    apply Finset.ext
    intro e
    rw [Finset.mem_image]
    constructor
    · rintro ⟨k, hk, hk_eq⟩
      obtain ⟨hk1, _hk2, hkB⟩ := (hTmem k).mp hk
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← hk_eq]
        exact one_le_mul hh hk1
      · rw [← hk_eq]; exact hkB
      · exact ⟨k, hk_eq.symm⟩
    · intro he
      rw [Finset.mem_filter, Finset.mem_Icc] at he
      obtain ⟨⟨_he1, he2⟩, hdvd⟩ := he
      have hmul : h * (e / h) = e := Nat.mul_div_cancel' hdvd
      refine ⟨e / h, ?_, hmul⟩
      rw [hTmem (e / h)]
      refine ⟨?_, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos (e / h) with h0 | hp
        · rw [h0, mul_zero] at hmul; omega
        · exact hp
      · calc e / h = 1 * (e / h) := (one_mul _).symm
          _ ≤ h * (e / h) := Nat.mul_le_mul_right _ hh
          _ = e := hmul
          _ ≤ B := he2
      · rw [hmul]; exact he2
  -- Reindex the sum over multiples of `h` as a sum over `k ∈ T`.
  have hsum_eq : ∑ e ∈ (Finset.Icc 1 B).filter (fun e => h ∣ e), (e : ℝ) ^ (-σ)
      = ∑ k ∈ T, ((h * k : ℕ) : ℝ) ^ (-σ) := by
    rw [← himage]
    refine Finset.sum_image (s := T) (f := fun e : ℕ => (e : ℝ) ^ (-σ)) (g := fun k : ℕ => h * k) ?_
    intro a _ b _ hab
    exact Nat.mul_left_cancel hhpos hab
  -- Per-term bound: `(hk)^{-σ} ≤ B^{1-σ} (hk)^{-1}`.
  have hterm : ∀ k ∈ T, ((h * k : ℕ) : ℝ) ^ (-σ)
      ≤ (B : ℝ) ^ (1 - σ) * ((h * k : ℕ) : ℝ) ^ (-1 : ℝ) := by
    intro k hk
    obtain ⟨hk1, _hk2, hkB⟩ := (hTmem k).mp hk
    have hrpos : (0 : ℝ) < ((h * k : ℕ) : ℝ) := by
      have : (0 : ℕ) < h * k := Nat.mul_pos (by omega) (by omega)
      exact_mod_cast this
    have hrle : ((h * k : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hkB
    have hsplit : ((h * k : ℕ) : ℝ) ^ (-σ)
        = ((h * k : ℕ) : ℝ) ^ (1 - σ) * ((h * k : ℕ) : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hrpos]
      congr 1
      ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hrpos.le hrle hexp)
      (Real.rpow_nonneg hrpos.le _)
  -- The harmonic bound.
  have hH : ∑ k ∈ Finset.Icc 1 B, (k : ℝ) ^ (-1 : ℝ) ≤ 1 + Real.log (B : ℝ) := by
    have hcast : (harmonic B : ℝ) = ∑ k ∈ Finset.Icc 1 B, (k : ℝ)⁻¹ := by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl
    simp_rw [Real.rpow_neg_one]
    rw [← hcast]
    exact harmonic_le_one_add_log B
  have hsum_le : ∑ k ∈ T, (k : ℝ) ^ (-1 : ℝ) ≤ 1 + Real.log (B : ℝ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hH
    · rw [hTdef]; exact Finset.filter_subset _ _
    · intro i _ _
      exact Real.rpow_nonneg (Nat.cast_nonneg i) _
  calc ∑ e ∈ (Finset.Icc 1 B).filter (fun e => h ∣ e), (e : ℝ) ^ (-σ)
      = ∑ k ∈ T, ((h * k : ℕ) : ℝ) ^ (-σ) := hsum_eq
    _ ≤ ∑ k ∈ T, (B : ℝ) ^ (1 - σ) * ((h * k : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (B : ℝ) ^ (1 - σ) * ∑ k ∈ T, ((h * k : ℕ) : ℝ) ^ (-1 : ℝ) := by
        rw [Finset.mul_sum]
    _ = (B : ℝ) ^ (1 - σ) * ((h : ℝ) ^ (-1 : ℝ) * ∑ k ∈ T, (k : ℝ) ^ (-1 : ℝ)) := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [Nat.cast_mul, Real.rpow_neg_one, mul_inv]
    _ ≤ (B : ℝ) ^ (1 - σ) * ((h : ℝ) ^ (-1 : ℝ) * (1 + Real.log (B : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsum_le (Real.rpow_nonneg hhRpos.le _))
          (Real.rpow_nonneg hBpos.le _)
    _ = (B : ℝ) ^ (1 - σ) * (1 + Real.log (B : ℝ)) / (h : ℝ) := by
        rw [Real.rpow_neg_one, div_eq_mul_inv]; ring

end Work.LinnikAreas.Density4
