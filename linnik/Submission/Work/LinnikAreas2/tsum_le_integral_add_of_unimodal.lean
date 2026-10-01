/-
# `LinnikAreas2.tsum_le_integral_add_of_unimodal` — the sharp unimodal sum/integral comparison

For `f : ℝ → ℝ` which is nonnegative, monotone on `[0,x₀]`, antitone on `[x₀,∞)` and integrable on
`(0,∞)` (a unimodal function with peak at `x₀`),

`Σ'_n f(n) ≤ ∫_{(0,∞)} f + 2·f(x₀)`.

This sharpens `Work.ZeroDensity.Ingham.tsum_le_integral_of_unimodal`, which gives
`Σ'_n f(n) ≤ 2·∫_{(0,∞)} f + 4·f(x₀)`: that version compares *both* the head `n < ⌈x₀⌉₊` and the
tail `n ≥ ⌈x₀⌉₊` against the *whole* integral `∫_{(0,∞)} f`, losing a genuine factor `2` on the
leading term.  Comparing the head with `∫_{(0,x₀]}` and the tail with `∫_{(x₀,∞)}` (the two
halves of `(0,∞)`) removes that loss, which is what the sharp HB (11.17)
(`LinnikAreas2.theta_diag_sharp2`) needs.

Equivalently: for a unimodal `f` with finite `∫|f'|` one has `Σ'_n f(n) ≤ ∫_{(0,∞)} f + ∫|f'|`,
and `∫|f'| = 2f(x₀) − f(0⁺) − f(∞) ≤ 2f(x₀)`.
-/
import Mathlib
import Submission.Work.ZeroDensity.Ingham.sum_range_ceil_le_integral_add
import Submission.Work.ZeroDensity.Ingham.sum_Ico_ceil_le_integral_add

open MeasureTheory Set

namespace Work.LinnikAreas2

/-- Reindexing identity: shifting the argument of `F` by one turns a sum over `Ico a b` into a sum
over `Ico (a+1) (b+1)`. -/
private lemma sum_Ico_shift_succ' (F : ℕ → ℝ) (a b : ℕ) :
    ∑ n ∈ Finset.Ico a b, F (n + 1) = ∑ j ∈ Finset.Ico (a + 1) (b + 1), F j := by
  rw [show (∑ n ∈ Finset.Ico a b, F (n + 1)) = ∑ n ∈ Finset.Ico a b, F (1 + n) from
    Finset.sum_congr rfl (fun n _ => by rw [Nat.add_comm])]
  exact Finset.sum_Ico_add F a b 1

/-- **Head of the sharp comparison.**  For `0 < x₀`, `f` nonnegative on `(0,∞)`, monotone on
`[0,x₀]` and integrable on `(0,∞)`,

`Σ_{n < ⌈x₀⌉₊} f n ≤ ∫_{(0,x₀]} f + f x₀`. -/
private theorem sum_range_ceil_le_integral_Ioc_add {f : ℝ → ℝ} {x₀ : ℝ} (hx : 0 < x₀)
    (hmono : MonotoneOn f (Set.Icc 0 x₀))
    (hint : IntegrableOn f (Set.Ioi (0:ℝ)))
    (hnn : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ f x) :
    ∑ i ∈ Finset.range (⌈x₀⌉₊), f i ≤
      (∫ x in Set.Ioc (0:ℝ) x₀, f x) + f x₀ := by
  set N : ℕ := ⌈x₀⌉₊ with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.ceil_pos.mpr hx
  obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hm_lt : (m : ℝ) < x₀ := by
    have hlt : (N : ℝ) < x₀ + 1 := by rw [hN]; exact Nat.ceil_lt_add_one hx.le
    have : (m : ℝ) = (N : ℝ) - 1 := by rw [hm]; push_cast; ring
    linarith
  have hm_le : (m : ℝ) ≤ x₀ := le_of_lt hm_lt
  rw [hm, Finset.sum_range_succ]
  have hmono' : MonotoneOn f (Set.Icc ((0:ℕ):ℝ) (m:ℝ)) :=
    hmono.mono (fun x hx' => ⟨by simpa using hx'.1, le_trans hx'.2 hm_le⟩)
  have hsum : ∑ x ∈ Finset.range m, f x ≤ ∫ x in (0:ℝ)..(m:ℝ), f x := by
    have h := MonotoneOn.sum_le_integral_Ico (a := 0) (b := m) (f := f) (Nat.zero_le _) hmono'
    simpa [Nat.Ico_zero_eq_range] using h
  have hflast : f m ≤ f x₀ := hmono ⟨by positivity, hm_le⟩ ⟨le_of_lt hx, le_rfl⟩ hm_le
  have hintIoc : IntegrableOn f (Set.Ioc (0:ℝ) x₀) :=
    hint.mono_set (fun x hx' => hx'.1)
  have hintIocm : IntegrableOn f (Set.Ioc (0:ℝ) (m:ℝ)) :=
    hint.mono_set (fun x hx' => hx'.1)
  have hintInt : IntegrableOn f (Set.Ioc (0:ℝ) (m:ℝ)) := hintIocm
  have hle1 : ∫ x in (0:ℝ)..(m:ℝ), f x ≤ ∫ x in Set.Ioc (0:ℝ) x₀, f x := by
    rw [intervalIntegral.integral_of_le (show (0:ℝ) ≤ (m:ℝ) by positivity)]
    refine MeasureTheory.setIntegral_mono_set hintIoc ?_ ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
        (fun x hx' => hnn x hx'.1)
    · exact Filter.Eventually.of_forall
        (fun x (hx' : x ∈ Set.Ioc (0:ℝ) (m:ℝ)) => ⟨hx'.1, le_trans hx'.2 hm_le⟩)
  linarith

/-- **Tail of the sharp comparison.**  For `0 < x₀`, `f` nonnegative on `(0,∞)`, antitone on
`[x₀,∞)` and integrable on `(0,∞)`,

`Σ_{⌈x₀⌉₊ ≤ i < N} f i ≤ ∫_{(x₀,∞)} f + f x₀`. -/
private theorem sum_Ico_ceil_le_integral_Ioi_add {f : ℝ → ℝ} {x₀ : ℝ} (hx : 0 < x₀)
    (hanti : AntitoneOn f (Set.Ici x₀))
    (hint : IntegrableOn f (Set.Ioi (0:ℝ)))
    (hnn : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ f x) (N : ℕ) :
    ∑ i ∈ Finset.Ico (⌈x₀⌉₊) N, f i ≤ (∫ x in Set.Ioi x₀, f x) + f x₀ := by
  set K : ℕ := ⌈x₀⌉₊ with hK
  have hxK : x₀ ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil x₀
  have hKpos : (0:ℝ) < K := lt_of_lt_of_le hx hxK
  have hfnn' : ∀ n : ℕ, 0 < n → 0 ≤ f (n:ℝ) := fun n hn =>
    hnn (n:ℝ) (by rw [Set.mem_Ioi]; exact_mod_cast hn)
  have h0 : 0 ≤ f x₀ := hnn x₀ (by simpa using hx)
  have hIntIoi : 0 ≤ ∫ x in Set.Ioi x₀, f x :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx' => hnn x (lt_trans hx hx'))
  by_cases hNK : N ≤ K
  · rw [Finset.Ico_eq_empty_iff.mpr (not_lt.mpr hNK), Finset.sum_empty]
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
        hanti.mono (fun x hx' => le_trans hxK hx'.1)
      have hintK : IntegrableOn f (Set.Ioi (K:ℝ)) :=
        hint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hKpos))
      have hnnK : ∀ t ∈ Set.Ioi (K:ℝ), 0 ≤ f t :=
        fun t ht => hnn t (Set.Ioi_subset_Ioi (le_of_lt hKpos) ht)
      have hmain := AntitoneOn.sum_Ico_le_integral (f := f) (a := K) (b := N) hanti' hintK hnnK
      have hreindex : ∑ n ∈ Finset.Ico K N, f (n+1 : ℕ) =
          ∑ i ∈ Finset.Ico (K+1) (N+1), f (i:ℝ) :=
        sum_Ico_shift_succ' (fun k : ℕ => f (k:ℝ)) K N
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
    have hInt_le : ∫ x in Set.Ioi (K:ℝ), f x ≤ ∫ x in Set.Ioi x₀, f x := by
      refine setIntegral_mono_set (hint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hx))) ?_ ?_
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
          (fun x hx' => hnn x (lt_trans hx hx'))
      · exact (Set.Ioi_subset_Ioi hxK).eventuallyLE
    calc ∑ i ∈ Finset.Ico K N, f (i:ℝ)
        = f (K:ℝ) + ∑ i ∈ Finset.Ico (K+1) N, f (i:ℝ) := hsplit
      _ ≤ f (K:ℝ) + ∫ x in Set.Ioi (K:ℝ), f x := add_le_add (le_refl _) htail
      _ ≤ f x₀ + ∫ x in Set.Ioi x₀, f x := add_le_add hfm hInt_le
      _ = (∫ x in Set.Ioi x₀, f x) + f x₀ := by rw [add_comm]

/-- **The sharp unimodal sum/integral comparison.**  If `f` is nonnegative, monotone on `[0,x₀]`,
antitone on `[x₀,∞)` and integrable on `(0,∞)`, then `Σ'_n f(n) ≤ ∫_{(0,∞)} f + 2 f(x₀)`. -/
theorem tsum_le_integral_add_of_unimodal {f : ℝ → ℝ} {x₀ : ℝ} (hx : 0 < x₀)
    (hnn0 : ∀ n : ℕ, 0 ≤ f n) (hnn : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ f x)
    (hmono : MonotoneOn f (Set.Icc 0 x₀)) (hanti : AntitoneOn f (Set.Ici x₀))
    (hint : IntegrableOn f (Set.Ioi 0)) :
    tsum (fun n : ℕ => f n) ≤ (∫ x in Set.Ioi (0:ℝ), f x) + 2 * f x₀ := by
  set K : ℕ := ⌈x₀⌉₊ with hK
  have hxK : x₀ ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil x₀
  have h0 : 0 ≤ f x₀ := hnn x₀ (by simpa using hx)
  -- the two halves of `(0,∞)`
  have hpartition : ∫ x in Set.Ioi (0:ℝ), f x
      = (∫ x in Set.Ioc (0:ℝ) x₀, f x) + ∫ x in Set.Ioi x₀, f x := by
    have hunion : Set.Ioc (0:ℝ) x₀ ∪ Set.Ioi x₀ = Set.Ioi (0:ℝ) := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, _⟩ | h2)
        · exact h1
        · exact lt_trans hx h2
      · intro h
        by_cases hle : x ≤ x₀
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr (lt_of_not_ge hle)
    have hdisj : Disjoint (Set.Ioc (0:ℝ) x₀) (Set.Ioi x₀) :=
      Set.disjoint_left.mpr (fun a ha ha' => absurd ha.2 (not_le.mpr ha'))
    rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set (fun x hx' => hx'.1)) (hint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hx)))]
  -- affine combination of the two halves
  have htwo : (∫ x in Set.Ioc (0:ℝ) x₀, f x) + f x₀ + ((∫ x in Set.Ioi x₀, f x) + f x₀)
      ≤ (∫ x in Set.Ioi (0:ℝ), f x) + 2 * f x₀ := by
    have hnn1 : 0 ≤ ∫ x in Set.Ioc (0:ℝ) x₀, f x :=
      setIntegral_nonneg measurableSet_Ioc (fun x hx' => hnn x hx'.1)
    have hnn2 : 0 ≤ ∫ x in Set.Ioi x₀, f x :=
      setIntegral_nonneg measurableSet_Ioi (fun x hx' => hnn x (lt_trans hx hx'))
    rw [hpartition]; linarith
  -- every partial sum
  have hrange : ∀ N : ℕ, ∑ i ∈ Finset.range N, f i
      ≤ (∫ x in Set.Ioi (0:ℝ), f x) + 2 * f x₀ := by
    intro N
    have hhead := sum_range_ceil_le_integral_Ioc_add hx hmono hint hnn
    have htail := sum_Ico_ceil_le_integral_Ioi_add hx hanti hint hnn N
    by_cases hNK : N ≤ K
    · have hsub : Finset.range N ⊆ Finset.range K := Finset.range_subset_range.mpr hNK
      have h1 : ∑ i ∈ Finset.range N, f i ≤ ∑ i ∈ Finset.range K, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnn0 i)
      have h2 : ∑ i ∈ Finset.range K, f i ≤ (∫ x in Set.Ioi (0:ℝ), f x) + 2 * f x₀ := by
        have h3 : (∫ x in Set.Ioc (0:ℝ) x₀, f x) + f x₀ ≤
            (∫ x in Set.Ioi (0:ℝ), f x) + 2 * f x₀ := by
          have hnn1 : 0 ≤ ∫ x in Set.Ioc (0:ℝ) x₀, f x :=
            setIntegral_nonneg measurableSet_Ioc (fun x hx' => hnn x hx'.1)
          have hnn2 : 0 ≤ ∫ x in Set.Ioi x₀, f x :=
            setIntegral_nonneg measurableSet_Ioi (fun x hx' => hnn x (lt_trans hx hx'))
          rw [hpartition]; linarith
        exact le_trans hhead h3
      exact le_trans h1 h2
    · have hKN : K ≤ N := le_of_lt (not_le.mp hNK)
      have hsplit := Finset.sum_range_add_sum_Ico (fun i : ℕ => f i) hKN
      have hIco : ∑ i ∈ Finset.Ico K N, f i ≤ (∫ x in Set.Ioi x₀, f x) + f x₀ := by
        simpa [hK] using htail
      calc ∑ i ∈ Finset.range N, f i
          = ∑ i ∈ Finset.range K, f i + ∑ i ∈ Finset.Ico K N, f i := hsplit.symm
        _ ≤ ((∫ x in Set.Ioc (0:ℝ) x₀, f x) + f x₀) + ((∫ x in Set.Ioi x₀, f x) + f x₀) :=
            add_le_add hhead hIco
        _ ≤ (∫ x in Set.Ioi (0:ℝ), f x) + 2 * f x₀ := htwo
  exact Real.tsum_le_of_sum_le (f := fun n : ℕ => f n) (fun i => hnn0 i) fun u =>
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => by
      simp only [Finset.mem_range]
      have hle : i ≤ u.sup id := Finset.le_sup (f := id) hi
      omega) (fun i _ _ => hnn0 i)) (hrange (u.sup id + 1))

end Work.LinnikAreas2
