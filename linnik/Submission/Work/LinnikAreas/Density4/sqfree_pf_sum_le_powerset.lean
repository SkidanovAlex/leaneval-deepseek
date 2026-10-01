import Mathlib

namespace Work.LinnikAreas.Density4

theorem sqfree_pf_sum_le_powerset (M : ℕ) (b : ℕ → ℝ) (hb : ∀ p, 0 ≤ b p) :
    (∑ u ∈ (Finset.Icc 1 M).filter Squarefree, ∏ p ∈ u.primeFactors, b p)
      ≤ ∑ T ∈ ((Finset.Icc 2 M).filter Nat.Prime).powerset, ∏ p ∈ T, b p := by
  set S : Finset ℕ := (Finset.Icc 1 M).filter Squarefree with hS
  set P : Finset ℕ := (Finset.Icc 2 M).filter Nat.Prime with hP
  have hmain : (∑ u ∈ S, ∏ p ∈ u.primeFactors, b p)
      ≤ ∑ T ∈ P.powerset, ∏ p ∈ T, b p := by
    have hg : ∀ T : Finset ℕ, 0 ≤ ∏ p ∈ T, b p :=
      fun T => Finset.prod_nonneg (fun p _ => hb p)
    have hinj : Set.InjOn (fun u : ℕ => u.primeFactors) (↑S : Set ℕ) := by
      intro u hu v hv huv
      have huS : u ∈ S := Finset.mem_coe.mp hu
      have hvS : v ∈ S := Finset.mem_coe.mp hv
      have hsu : Squarefree u := (Finset.mem_filter.mp huS).2
      have hsv : Squarefree v := (Finset.mem_filter.mp hvS).2
      have huv' : u.primeFactors = v.primeFactors := huv
      have hu' := Nat.prod_primeFactors_of_squarefree hsu
      have hv' := Nat.prod_primeFactors_of_squarefree hsv
      rw [← hu', ← hv', huv']
    have hsub : S.image (fun u : ℕ => u.primeFactors) ⊆ P.powerset := by
      intro T hT
      rw [Finset.mem_powerset]
      obtain ⟨u, huS, rfl⟩ := Finset.mem_image.mp hT
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc]
      have hu1 : u ∈ Finset.Icc 1 M := (Finset.mem_filter.mp huS).1
      obtain ⟨hu1a, hu1b⟩ := Finset.mem_Icc.mp hu1
      have hpP : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ u := (Nat.mem_primeFactors.mp hp).2.1
      exact ⟨⟨hpP.two_le, le_trans (Nat.le_of_dvd (by omega) hpdvd) hu1b⟩, hpP⟩
    calc (∑ u ∈ S, ∏ p ∈ u.primeFactors, b p)
        = ∑ T ∈ S.image (fun u : ℕ => u.primeFactors), ∏ p ∈ T, b p :=
          (Finset.sum_image (f := fun T : Finset ℕ => ∏ p ∈ T, b p) hinj).symm
      _ ≤ ∑ T ∈ P.powerset, ∏ p ∈ T, b p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ => hg T)
  rw [hS, hP] at hmain
  exact hmain

end Work.LinnikAreas.Density4
