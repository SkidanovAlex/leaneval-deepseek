import Mathlib

namespace Work.LinnikAreas.BGTZ

theorem linnik_rhs_reindex (g : ℕ → ℝ)
    (hgmul : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b)
    (R k Q0 : ℕ) (hk1 : 1 ≤ k) (hkQ0 : Nat.Coprime k Q0) :
    (g k)⁻¹ * (∑ m ∈ (Finset.Icc 1 R).filter (fun m => k * m ≤ R ∧ m ∣ Q0), (g m)⁻¹)
      = ∑ n ∈ (Finset.Icc 1 R).filter (fun n => k ∣ n ∧ n / k ∣ Q0), (g n)⁻¹ := by
  set S : Finset ℕ := (Finset.Icc 1 R).filter (fun m => k * m ≤ R ∧ m ∣ Q0) with hS
  set T : Finset ℕ := (Finset.Icc 1 R).filter (fun n => k ∣ n ∧ n / k ∣ Q0) with hT
  have hkpos : 0 < k := hk1
  have hS_mem : ∀ m, m ∈ S ↔ (1 ≤ m ∧ m ≤ R ∧ k * m ≤ R ∧ m ∣ Q0) := by
    intro m
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
  have hT_mem : ∀ n, n ∈ T ↔ (1 ≤ n ∧ n ≤ R ∧ k ∣ n ∧ n / k ∣ Q0) := by
    intro n
    rw [hT, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
  have hTimg : T = S.image (fun m => k * m) := by
    ext n
    simp only [hT_mem n, hS_mem, Finset.mem_image]
    constructor
    · rintro ⟨hn1, hnR, hkdn, hndvd⟩
      refine ⟨n / k, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · exact (Nat.le_div_iff_mul_le hkpos).mpr (by
          have : k ≤ n := Nat.le_of_dvd (by omega) hkdn
          simpa using this)
      · exact le_trans (Nat.div_le_self n k) hnR
      · rw [Nat.mul_div_cancel' hkdn]; exact hnR
      · exact hndvd
      · exact Nat.mul_div_cancel' hkdn
    · rintro ⟨m, ⟨hm1, hmR, hkmR, hmdvd⟩, rfl⟩
      refine ⟨?_, hkmR, ⟨m, rfl⟩, ?_⟩
      · simpa using Nat.mul_le_mul hk1 hm1
      · rw [Nat.mul_div_right m hkpos]; exact hmdvd
  have hinj : Set.InjOn (fun m => k * m) ↑S := by
    intro a _ b _ hab
    exact Nat.mul_left_cancel hkpos hab
  have hsum1 : ∑ n ∈ T, (g n)⁻¹ = ∑ m ∈ S, (g (k * m))⁻¹ := by
    rw [hTimg]
    exact Finset.sum_image hinj
  have hsum2 : ∑ m ∈ S, (g (k * m))⁻¹ = (g k)⁻¹ * ∑ m ∈ S, (g m)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m hmS
    obtain ⟨hm1, hmR, hkmR, hmdvd⟩ := (hS_mem m).mp hmS
    have hcop : Nat.Coprime k m := hkQ0.coprime_dvd_right hmdvd
    rw [hgmul k m hcop, mul_inv]
  exact hsum2.symm.trans hsum1.symm

end Work.LinnikAreas.BGTZ
