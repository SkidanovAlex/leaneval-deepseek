import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Integral

open MeasureTheory intervalIntegral
open scoped BigOperators

theorem sum_intervalIntegral_Icc_swap (g : ℕ → ℝ → ℝ) (K : ℕ)
    (hg : ∀ k ∈ Finset.Icc 1 K, IntervalIntegrable (g k) MeasureTheory.volume (0:ℝ) (k:ℝ)) :
    (∑ k ∈ Finset.Icc 1 K, ∫ u in (0 : ℝ)..((k:ℝ)), g k u)
      = ∫ u in (0 : ℝ)..((K:ℝ)),
          ∑ k ∈ (Finset.Icc 1 K).filter (fun k : ℕ => u < (k : ℝ)), g k u := by
  set s : Finset ℕ := Finset.Icc 1 K with hs
  -- interval-integrability of the indicator functions on 0..K
  have hii : ∀ k ∈ s,
      IntervalIntegrable (fun u => Set.indicator {x : ℝ | x ≤ (k:ℝ)} (g k) u) volume (0:ℝ) (K:ℝ) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp (hs ▸ hk)).1
    have hkK : k ≤ K := (Finset.mem_Icc.mp (hs ▸ hk)).2
    rw [intervalIntegrable_iff]
    change IntegrableOn ((Set.Iic (k:ℝ)).indicator (g k)) (Set.uIoc (0:ℝ) (K:ℝ)) volume
    rw [integrableOn_indicator_iff measurableSet_Iic]
    have hset : Set.Iic (k:ℝ) ∩ Set.uIoc (0:ℝ) (K:ℝ) = Set.uIoc (0:ℝ) (k:ℝ) := by
      rw [Set.uIoc_of_le (Nat.cast_nonneg K), Set.uIoc_of_le (by positivity : (0:ℝ) ≤ (k:ℝ))]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨hxk, hx0, _⟩; exact ⟨hx0, hxk⟩
      · rintro ⟨hx0, hxk⟩; exact ⟨hxk, hx0, le_trans hxk (by exact_mod_cast hkK)⟩
    rw [hset]
    exact intervalIntegrable_iff.mp (hg k (hs ▸ hk))
  -- pointwise description of where the two integrands differ
  set A : Set ℝ := ((Finset.Icc 1 K).image (fun k : ℕ => (k:ℝ)) : Set ℝ) with hA
  have hFG : ∀ u : ℝ, u ∉ A →
      (∑ k ∈ s, Set.indicator {x : ℝ | x ≤ (k:ℝ)} (g k) u)
        = ∑ k ∈ s.filter (fun k : ℕ => u < (k:ℝ)), g k u := by
    intro u hu
    have hterm : ∀ k ∈ s,
        Set.indicator {x : ℝ | x ≤ (k:ℝ)} (g k) u = if u < (k:ℝ) then g k u else 0 := by
      intro k hk
      have hne : u ≠ (k:ℝ) := by
        intro h
        apply hu
        rw [hA]
        simp only [Finset.mem_coe, Finset.mem_image]
        exact ⟨k, hs ▸ hk, h.symm⟩
      rw [Set.indicator_apply]
      have hiff : (u ∈ {x : ℝ | x ≤ (k:ℝ)}) ↔ u < (k:ℝ) := by
        rw [Set.mem_ofPred_eq]
        exact ⟨fun h => lt_of_le_of_ne h hne, fun h => le_of_lt h⟩
      exact if_congr hiff rfl rfl
    rw [Finset.sum_congr rfl hterm,
      Finset.sum_filter (s := s) (p := fun k : ℕ => u < (k:ℝ)) (f := fun k => g k u)]
  -- the exceptional set has measure zero
  have hA_null : volume A = 0 := by
    rw [hA]
    exact Set.Finite.measure_zero (Finset.finite_toSet _) volume
  calc
    (∑ k ∈ Finset.Icc 1 K, ∫ u in (0 : ℝ)..((k:ℝ)), g k u)
        = ∑ k ∈ s, ∫ u in (0 : ℝ)..((K:ℝ)), Set.indicator {x : ℝ | x ≤ (k:ℝ)} (g k) u := by
          rw [hs]
          apply Finset.sum_congr rfl
          intro k hk
          have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
          exact (intervalIntegral.integral_indicator
            (show (k:ℝ) ∈ Set.Icc (0:ℝ) (K:ℝ) from
              ⟨by positivity, by exact_mod_cast hkK⟩)).symm
    _ = ∫ u in (0 : ℝ)..((K:ℝ)), ∑ k ∈ s, Set.indicator {x : ℝ | x ≤ (k:ℝ)} (g k) u :=
          (intervalIntegral.integral_finsetSum hii).symm
    _ = ∫ u in (0 : ℝ)..((K:ℝ)),
          ∑ k ∈ (Finset.Icc 1 K).filter (fun k : ℕ => u < (k : ℝ)), g k u := by
          apply intervalIntegral.integral_congr_ae
          rw [MeasureTheory.ae_iff]
          apply measure_mono_null _ hA_null
          intro x hx
          by_contra hxA
          exact hx (fun _ => hFG x hxA)

end Commons.Analysis.Integral