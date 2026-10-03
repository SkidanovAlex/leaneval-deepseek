import Mathlib

namespace Work.FIArea4

open Finset

/-- Splitting the symmetric harmonic sum over `ℤ` into twice its positive part. -/
private lemma sum_erase_Icc_abs_inv (N : ℕ) :
    (∑ l ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, (1 : ℝ) / |(l : ℝ)|)
      = 2 * ∑ m ∈ Finset.Icc (1 : ℤ) (N : ℤ), (1 : ℝ) / |(m : ℝ)| := by
  have hpos : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0).filter (fun l => 0 < l)
      = Finset.Icc (1 : ℤ) (N : ℤ) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]
    omega
  have hneg : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0).filter (fun l => l < 0)
      = (Finset.Icc (1 : ℤ) (N : ℤ)).image (fun l => -l) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hne, h1, h2⟩, h3⟩
      exact ⟨-l, ⟨by omega, by omega⟩, by ring⟩
    · rintro ⟨m, ⟨hm1, hm2⟩, hm⟩
      omega
  have hdisj : Disjoint (((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0).filter (fun l => 0 < l))
      (((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0).filter (fun l => l < 0)) := by
    rw [Finset.disjoint_left]
    intro l hl1 hl2
    simp only [Finset.mem_filter] at hl1 hl2
    omega
  have hunion : (((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0).filter (fun l => 0 < l))
      ∪ (((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0).filter (fun l => l < 0))
      = (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0 := by
    ext l
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      have h0 : l ≠ 0 := (Finset.mem_erase.mp h).1
      rcases lt_or_gt_of_ne h0 with hlt | hgt
      · exact Or.inr ⟨h, hlt⟩
      · exact Or.inl ⟨h, hgt⟩
  have hsum_neg :
      (∑ l ∈ (Finset.Icc (1 : ℤ) (N : ℤ)).image (fun l => -l), (1 : ℝ) / |(l : ℝ)|)
        = ∑ m ∈ Finset.Icc (1 : ℤ) (N : ℤ), (1 : ℝ) / |(m : ℝ)| := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro m _
      simp
    · intro a _ b _ h
      exact neg_injective h
  calc ∑ l ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, (1 : ℝ) / |(l : ℝ)|
      = ∑ l ∈ (((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0).filter (fun l => 0 < l))
            ∪ (((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0).filter (fun l => l < 0)),
            (1 : ℝ) / |(l : ℝ)| := by
          rw [hunion]
      _ = ∑ l ∈ ((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0).filter (fun l => 0 < l),
              (1 : ℝ) / |(l : ℝ)|
            + ∑ l ∈ ((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0).filter (fun l => l < 0),
              (1 : ℝ) / |(l : ℝ)| :=
          Finset.sum_union hdisj
      _ = 2 * ∑ m ∈ Finset.Icc (1 : ℤ) (N : ℤ), (1 : ℝ) / |(m : ℝ)| := by
          rw [hpos, hneg, hsum_neg]
          ring

/-- The positive part of the symmetric harmonic sum is the harmonic number. -/
private lemma sum_Icc_int_inv_eq_harmonic (N : ℕ) :
    (∑ l ∈ Finset.Icc (1 : ℤ) (N : ℤ), (1 : ℝ) / |(l : ℝ)|) = (harmonic N : ℝ) := by
  have hbij : (∑ l ∈ Finset.Icc (1 : ℤ) (N : ℤ), (1 : ℝ) / |(l : ℝ)|)
      = ∑ i ∈ Finset.Icc 1 N, ((i : ℝ))⁻¹ := by
    refine Finset.sum_bij (s := Finset.Icc (1 : ℤ) (N : ℤ)) (t := Finset.Icc 1 N)
      (f := fun l : ℤ => (1 : ℝ) / |(l : ℝ)|) (g := fun i : ℕ => ((i : ℝ))⁻¹)
      (fun (l : ℤ) _ => l.toNat) ?_ ?_ ?_ ?_
    · intro l hl
      simp only [Finset.mem_Icc] at hl ⊢
      refine ⟨?_, ?_⟩
      · rw [Int.le_toNat (by omega)]; exact hl.1
      · rw [Int.toNat_le]; exact hl.2
    · intro l1 hl1 l2 hl2 h
      simp only [Finset.mem_Icc] at hl1 hl2
      have h1 : 0 ≤ l1 := by omega
      have h2 : 0 ≤ l2 := by omega
      have := congrArg (fun n : ℕ => (n : ℤ)) h
      simpa [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] using this
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨(b : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      exact Int.toNat_natCast b
    · intro l hl
      simp only [Finset.mem_Icc] at hl
      have h0 : 0 ≤ l := by omega
      have hcast : (l : ℝ) = (l.toNat : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
      rw [hcast]
      simp
  rw [hbij]
  have h2 : (harmonic N : ℝ) = ∑ i ∈ Finset.Icc 1 N, ((i : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [h2]

/-- The harmonic sum over `ℤ`: `Σ_{0<|ℓ|≤N} 1/|ℓ| ≤ C log N`. -/
theorem logSine_harmonic_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    (∑ l ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0, (1 : ℝ) / |(l : ℝ)|) ≤ C * Real.log N := by
  refine ⟨2 * (1 + (Real.log 2)⁻¹), ?_, fun N hN => ?_⟩
  · have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · rw [sum_erase_Icc_abs_inv N, sum_Icc_int_inv_eq_harmonic N]
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hL : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hN2
    have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hkey : 1 ≤ Real.log (N : ℝ) * (Real.log 2)⁻¹ := by
      have : 1 ≤ Real.log (N : ℝ) / Real.log 2 := by
        rw [one_le_div₀ hc]
        exact hL
      rwa [div_eq_mul_inv] at this
    have hLn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
    have hharm : (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
    nlinarith [hkey, hc, hharm, hLn]

end Work.FIArea4
