import Mathlib

open MeasureTheory Set

namespace Work.ZeroDensity.Ingham

/-- Reindexing identity used in the tail estimate: shifting the argument of `F` by one turns a
sum over `Ico a b` into a sum over `Ico (a+1) (b+1)`. -/
private lemma sum_Ico_shift_succ (F : ℕ → ℝ) (a b : ℕ) :
    ∑ n ∈ Finset.Ico a b, F (n + 1) = ∑ j ∈ Finset.Ico (a + 1) (b + 1), F j := by
  rw [show (∑ n ∈ Finset.Ico a b, F (n + 1)) = ∑ n ∈ Finset.Ico a b, F (1 + n) from
    Finset.sum_congr rfl (fun n _ => by rw [Nat.add_comm])]
  exact Finset.sum_Ico_add F a b 1

/-- Tail (decreasing) part of the unimodal sum/integral comparison: if `0 < x₀`, `f` is
nonnegative on `(0,∞)`, antitone on `[x₀,∞)` and integrable on `(0,∞)`, then for every `N` the sum
of `f` over the naturals `i ∈ Ico ⌈x₀⌉₊ N` is bounded by `∫_{(0,∞)} f + f x₀`. -/
theorem sum_Ico_ceil_le_integral_add {f : ℝ → ℝ} {x₀ : ℝ} (hx : 0 < x₀)
    (hanti : AntitoneOn f (Set.Ici x₀))
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi (0:ℝ)))
    (hnn : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ f x) (N : ℕ) :
    ∑ i ∈ Finset.Ico (⌈x₀⌉₊) N, f i ≤
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) f + f x₀ := by
  set K : ℕ := ⌈x₀⌉₊ with hK
  have hxK : x₀ ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil x₀
  have hKpos : (0:ℝ) < K := lt_of_lt_of_le hx hxK
  have hfnn' : ∀ n : ℕ, 0 < n → 0 ≤ f (n:ℝ) := fun n hn =>
    hnn (n:ℝ) (by rw [Set.mem_Ioi]; exact_mod_cast hn)
  have hIntNonneg : 0 ≤ MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) f :=
    integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioi hnn)
  by_cases hNK : N ≤ K
  · rw [Finset.Ico_eq_empty_iff.mpr (not_lt.mpr hNK), Finset.sum_empty]
    have h0 : 0 ≤ f x₀ := hnn x₀ (by simpa using hx)
    linarith
  · have hKN : K < N := not_le.mp hNK
    have hK1N : K + 1 ≤ N := Nat.succ_le_of_lt hKN
    have hsplit : ∑ i ∈ Finset.Ico K N, f (i:ℝ) =
        f (K:ℝ) + ∑ i ∈ Finset.Ico (K+1) N, f (i:ℝ) := by
      have h := Finset.sum_Ico_consecutive (fun i : ℕ => f (i:ℝ)) (Nat.le_succ K) hK1N
      have hone : ∑ i ∈ Finset.Ico K (K+1), f (i:ℝ) = f (K:ℝ) := by
        rw [Finset.sum_Ico_eq_sum_range (f := fun i : ℕ => f (i:ℝ)) K (K+1)]
        simp
      rw [← h, hone]
    have htail : ∑ i ∈ Finset.Ico (K+1) N, f (i:ℝ) ≤ ∫ x in Set.Ioi (K:ℝ), f x := by
      have hanti' : AntitoneOn f (Set.Icc (K:ℝ) (N:ℝ)) :=
        hanti.mono (fun x hx => le_trans hxK hx.1)
      have hintK : MeasureTheory.IntegrableOn f (Set.Ioi (K:ℝ)) :=
        hint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hKpos))
      have hnnK : ∀ t ∈ Set.Ioi (K:ℝ), 0 ≤ f t :=
        fun t ht => hnn t (Set.Ioi_subset_Ioi (le_of_lt hKpos) ht)
      have hmain := AntitoneOn.sum_Ico_le_integral (f := f) (a := K) (b := N) hanti' hintK hnnK
      have hreindex : ∑ n ∈ Finset.Ico K N, f (n+1 : ℕ) =
          ∑ i ∈ Finset.Ico (K+1) (N+1), f (i:ℝ) :=
        sum_Ico_shift_succ (fun k : ℕ => f (k:ℝ)) K N
      have hstep : ∑ i ∈ Finset.Ico (K+1) N, f (i:ℝ) ≤
          ∑ i ∈ Finset.Ico (K+1) (N+1), f (i:ℝ) := by
        rw [Finset.sum_Ico_succ_top (f := fun i : ℕ => f (i:ℝ)) hK1N]
        exact le_add_of_nonneg_right (hfnn' N (by omega))
      calc ∑ i ∈ Finset.Ico (K+1) N, f (i:ℝ)
          ≤ ∑ i ∈ Finset.Ico (K+1) (N+1), f (i:ℝ) := hstep
        _ = ∑ n ∈ Finset.Ico K N, f (n+1 : ℕ) := hreindex.symm
        _ ≤ ∫ x in Set.Ioi (K:ℝ), f x := hmain
    have hfm : f (K:ℝ) ≤ f x₀ := hanti (show x₀ ∈ Set.Ici x₀ from le_refl x₀)
      (show (K:ℝ) ∈ Set.Ici x₀ from hxK) hxK
    have hInt_le : ∫ x in Set.Ioi (K:ℝ), f x ≤ ∫ x in Set.Ioi (0:ℝ), f x := by
      apply setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Ioi hnn)
      exact (Set.Ioi_subset_Ioi (le_of_lt hKpos)).eventuallyLE
    calc ∑ i ∈ Finset.Ico K N, f (i:ℝ)
        = f (K:ℝ) + ∑ i ∈ Finset.Ico (K+1) N, f (i:ℝ) := hsplit
      _ ≤ f (K:ℝ) + ∫ x in Set.Ioi (K:ℝ), f x := add_le_add (le_refl _) htail
      _ ≤ f x₀ + ∫ x in Set.Ioi (0:ℝ), f x := add_le_add hfm hInt_le
      _ = MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) f + f x₀ := by
        rw [add_comm]

end Work.ZeroDensity.Ingham
