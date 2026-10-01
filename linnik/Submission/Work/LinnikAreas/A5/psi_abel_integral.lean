import Mathlib

namespace Work.LinnikAreas.A5

open MeasureTheory intervalIntegral Finset

private lemma vonMangoldt_zero : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  exact not_isPrimePow_zero

/-- The indicator of a measurable set preserves interval integrability. -/
private lemma intervalIntegrable_indicator {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (s : Set ℝ) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) volume a b :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

/-- Pointwise description of `ψ` on the range `[1, M]` as a finite sum of indicators. -/
private lemma psi_eq_sum_Icc_ite {M : ℕ} {t : ℝ} (ht1 : 1 ≤ t) (htM : t ≤ (M : ℝ)) :
    Chebyshev.psi t =
      ∑ n ∈ Icc 1 M, (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
  have hfloor : ⌊t⌋₊ ≤ M := by
    have h := Nat.floor_le_floor htM
    rwa [Nat.floor_natCast] at h
  have ht0 : (0 : ℝ) ≤ t := by linarith
  calc Chebyshev.psi t
      = ∑ n ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) := Chebyshev.psi_eq_sum_Icc t
    _ = ∑ n ∈ Icc 0 ⌊t⌋₊,
          (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
        refine sum_congr rfl fun n hn => ?_
        rw [if_pos]
        have hn' : (n : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast (mem_Icc.mp hn).2
        have h' : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
        linarith
    _ = ∑ n ∈ Icc 0 M,
          (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
        refine sum_subset ?_ ?_
        · intro x hx
          rw [mem_Icc] at hx ⊢
          exact ⟨hx.1, hx.2.trans hfloor⟩
        · intro x hx hxs
          rw [mem_Icc] at hx
          have hcon : ¬ ((x : ℝ) ≤ t) := by
            intro h
            exact hxs (by rw [mem_Icc]; exact ⟨hx.1, Nat.le_floor h⟩)
          rw [if_neg hcon]
    _ = ∑ n ∈ Icc 1 M,
          (if (n : ℝ) ≤ t then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
        refine (sum_subset (s₁ := Icc 1 M) (s₂ := Icc 0 M) ?_ ?_).symm
        · intro x hx
          rw [mem_Icc] at hx ⊢
          exact ⟨by omega, hx.2⟩
        · intro x hx hxs
          rw [mem_Icc] at hx
          have hx0 : x = 0 := by
            by_contra h
            exact hxs (by rw [mem_Icc]; exact ⟨by omega, hx.2⟩)
          subst hx0
          rw [Nat.cast_zero, if_pos ht0, vonMangoldt_zero]

/-- Integration against the indicator of `[c, ∞)`. -/
private lemma integral_indicator_Ici {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (f : ℝ → ℝ) :
    ∫ x in a..b, Set.indicator (Set.Ici c) f x = ∫ x in c..b, f x := by
  have hae : (Set.Ici c).indicator f =ᵐ[volume] (Set.Ioi c).indicator f :=
    indicator_ae_eq_of_ae_eq_set (Ioi_ae_eq_Ici (μ := volume)).symm
  have hset : Set.Ioc a b ∩ Set.Ioi c = Set.Ioc c b := by
    ext x
    simp only [Set.mem_inter, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩
      exact ⟨⟨lt_of_le_of_lt hac h3, h2⟩, h3⟩
  rw [integral_congr_ae_restrict (ae_mono Measure.restrict_le_self hae),
    integral_of_le (hac.trans hcb), setIntegral_indicator measurableSet_Ioi,
    integral_of_le hcb, hset]

theorem psi_abel_integral (M : ℕ) (G : ℝ → ℝ) (hM : 1 ≤ M)
    (hcont : ContinuousOn G (Set.Icc (1:ℝ) (M:ℝ)))
    (hdiff : ∀ t ∈ Set.Ioo (1:ℝ) (M:ℝ), DifferentiableAt ℝ G t)
    (hint : IntervalIntegrable (fun t : ℝ => Chebyshev.psi t * deriv G t) volume (1:ℝ) (M:ℝ))
    (hint2 : IntervalIntegrable (deriv G) volume (1:ℝ) (M:ℝ)) :
    (∑ n ∈ Finset.Icc 1 M, (ArithmeticFunction.vonMangoldt n : ℝ) * G (n:ℝ))
      = Chebyshev.psi (M:ℝ) * G (M:ℝ)
        - ∫ t in (1:ℝ)..(M:ℝ), Chebyshev.psi t * deriv G t := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  -- The main integral identity
  have hInt : ∫ t in (1:ℝ)..(M:ℝ), Chebyshev.psi t * deriv G t
      = ∑ n ∈ Finset.Icc 1 M,
          (ArithmeticFunction.vonMangoldt n : ℝ) * (G (M:ℝ) - G (n:ℝ)) := by
    have h1 : ∫ t in (1:ℝ)..(M:ℝ), Chebyshev.psi t * deriv G t
        = ∫ t in (1:ℝ)..(M:ℝ), ∑ n ∈ Finset.Icc 1 M,
            Set.indicator (Set.Ici (n:ℝ))
              (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℝ) * deriv G t) t := by
      refine integral_congr fun t ht => ?_
      have htI : t ∈ Set.Icc (1:ℝ) (M:ℝ) := by rwa [Set.uIcc_of_le hM1] at ht
      rw [psi_eq_sum_Icc_ite htI.1 htI.2, sum_mul]
      refine sum_congr rfl fun n _ => ?_
      by_cases h : (n : ℝ) ≤ t
      · rw [if_pos h, Set.indicator_of_mem (show t ∈ Set.Ici (n:ℝ) from h)]
      · rw [if_neg h, Set.indicator_of_notMem (show t ∉ Set.Ici (n:ℝ) from h), zero_mul]
    rw [h1, intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun n hn => ?_
      rw [mem_Icc] at hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn.2
      have hFTC : ∫ t in (n:ℝ)..(M:ℝ), deriv G t = G (M:ℝ) - G (n:ℝ) :=
        integral_eq_sub_of_hasDerivAt_of_le hnM
          (hcont.mono (Set.Icc_subset_Icc hn1 le_rfl))
          (fun x hx => (hdiff x (Set.Ioo_subset_Ioo_left hn1 hx)).hasDerivAt)
          (hint2.mono_set (by
            rw [Set.uIcc_of_le hnM, Set.uIcc_of_le hM1]
            exact Set.Icc_subset_Icc hn1 le_rfl))
      rw [integral_indicator_Ici hn1 hnM, intervalIntegral.integral_const_mul, hFTC]
    · intro n _
      exact intervalIntegrable_indicator (hint2.const_mul (ArithmeticFunction.vonMangoldt n))
        (Set.Ici (n:ℝ)) measurableSet_Ici
  -- ψ at M
  have hpsiM : Chebyshev.psi (M:ℝ)
      = ∑ n ∈ Finset.Icc 1 M, (ArithmeticFunction.vonMangoldt n : ℝ) := by
    rw [psi_eq_sum_Icc_ite (M := M) (t := (M:ℝ)) hM1 le_rfl]
    refine sum_congr rfl fun n hn => ?_
    rw [mem_Icc] at hn
    rw [if_pos (by exact_mod_cast hn.2)]
  rw [hInt, hpsiM, Finset.sum_mul]
  have hsub : (∑ n ∈ Finset.Icc 1 M,
        (ArithmeticFunction.vonMangoldt n : ℝ) * (G (M:ℝ) - G (n:ℝ)))
      = (∑ n ∈ Finset.Icc 1 M, (ArithmeticFunction.vonMangoldt n : ℝ) * G (M:ℝ))
        - ∑ n ∈ Finset.Icc 1 M, (ArithmeticFunction.vonMangoldt n : ℝ) * G (n:ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact sum_congr rfl fun n _ => mul_sub _ _ _
  rw [hsub]
  ring

end Work.LinnikAreas.A5
