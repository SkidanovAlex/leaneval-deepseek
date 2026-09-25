import Mathlib
import Submission.Commons.Analysis.Fourier.separated_exponentials_near_orthogonal

namespace Commons.Analysis.Fourier

open MeasureTheory Finset
open scoped BigOperators ENNReal

/-- Nonnegativity of a finite supremum of nonnegative reals, written with the
`⨆ a ∈ B, ·` notation (which for `ℝ` ranges over the whole type and assigns `sSup ∅ = 0`
to the points outside `B`). -/
private lemma iSup_finset_nonneg' {α : Type*} (B : Finset α) (u : α → ℝ)
    (h : ∀ a, 0 ≤ u a) : 0 ≤ (⨆ a ∈ B, u a) := by
  rcases B.eq_empty_or_nonempty with hB | hB
  · subst hB
    simp
  · obtain ⟨a₀, ha₀⟩ := hB
    have hbdd : BddAbove (Set.range (fun a => ⨆ (_ : a ∈ B), u a)) := by
      refine ⟨∑ a ∈ B, u a, ?_⟩
      rintro _ ⟨a, rfl⟩
      change (⨆ (_ : a ∈ B), u a) ≤ ∑ a ∈ B, u a
      by_cases ha : a ∈ B
      · rw [show (⨆ (_ : a ∈ B), u a) = u a from ciSup_pos (f := fun _ => u a) ha]
        exact Finset.single_le_sum (fun i _ => h i) ha
      · rw [show (⨆ (_ : a ∈ B), u a) = sSup (∅ : Set ℝ) from
            ciSup_neg (f := fun _ => u a) ha, Real.sSup_empty]
        exact Finset.sum_nonneg (fun _ _ => h _)
    have h1 : u a₀ ≤ ⨆ a, ⨆ (_ : a ∈ B), u a := by
      calc u a₀ = ⨆ (_ : a₀ ∈ B), u a₀ := (ciSup_pos (f := fun _ => u a₀) ha₀).symm
        _ ≤ ⨆ a, ⨆ (_ : a ∈ B), u a := le_ciSup hbdd a₀
    exact le_trans (h a₀) h1

/-- For a finite family of nonnegative reals the square of the supremum is at most the sum of
the squares (a consequence of `(sup u)² ≤ ∑ u²`, i.e. of the fact that a maximum of
nonnegative numbers is dominated in square by the sum of all squares). -/
private lemma iSup_finset_sq_le_sum' {α : Type*} (B : Finset α) (u : α → ℝ)
    (h : ∀ a, 0 ≤ u a) : (⨆ a ∈ B, u a) ^ 2 ≤ ∑ a ∈ B, (u a) ^ 2 := by
  have hnn : 0 ≤ (⨆ a ∈ B, u a) := iSup_finset_nonneg' B u h
  have h1 : (⨆ a ∈ B, u a) ≤ Real.sqrt (∑ a ∈ B, (u a) ^ 2) := by
    rcases isEmpty_or_nonempty α with hα | hα
    · have hB : B = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (fun hne => hne.elim fun a _ => isEmptyElim a)
      rw [show (⨆ a : α, ⨆ (_ : a ∈ B), u a) = (⨆ a : α, (0 : ℝ)) from by
            apply iSup_congr; intro a
            rw [show (⨆ (_ : a ∈ B), u a) = sSup (∅ : Set ℝ) from
              ciSup_neg (f := fun _ => u a) (by rw [hB]; simp)]
            exact Real.sSup_empty]
      rw [Real.iSup_of_isEmpty]
      simp [hB]
    · apply ciSup_le
      intro b
      by_cases hb : b ∈ B
      · rw [show (⨆ (_ : b ∈ B), u b) = u b from ciSup_pos (f := fun _ => u b) hb]
        rw [← Real.sqrt_sq (h b)]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun _ _ => sq_nonneg _) hb)
      · rw [show (⨆ (_ : b ∈ B), u b) = sSup (∅ : Set ℝ) from
            ciSup_neg (f := fun _ => u b) hb, Real.sSup_empty]
        exact Real.sqrt_nonneg _
  calc (⨆ a ∈ B, u a) ^ 2 ≤ (Real.sqrt (∑ a ∈ B, (u a) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hnn h1 2
    _ = ∑ a ∈ B, (u a) ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- **The maximal exponential sum over a finite class of coefficient vectors, mean-square bound.**
Let `lam : Fin K → ℝ` be `1`-separated, and let `B` be a finite set of coefficient vectors with
`∑ k, ‖b k‖ ^ 2 ≤ R ^ 2` for every `b ∈ B`.  Then the mean square over `y ∈ [0,1]` of the maximal
exponential sum `sup_{b ∈ B} ‖∑ k, b k * exp(I * lam k * y)‖` is at most `C * R ^ 2 * #B`.

This is the per-level estimate (4.24)–(4.25) in Bourgain's proof of his Lemma 4.13: the
near-orthogonality of `1`-separated exponentials
(`Commons.Analysis.Fourier.separated_exponentials_near_orthogonal`) controls the mean square of
each individual exponential sum, and the maximum over the *finite* set `B` is controlled by the
sum over `B` through the pointwise inequality `(sup_{b ∈ B} u b) ^ 2 ≤ ∑_{b ∈ B} (u b) ^ 2`.  The
integral is a Lebesgue integral over `[0,1]` in `ℝ≥0∞`, so no measurability of the pointwise
supremum is needed. -/
theorem max_finset_exponential_sum_l2 (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Finset (Fin K → ℂ)) (R : ℝ), 0 ≤ R →
      (∀ b ∈ B, ∑ k : Fin K, ‖b k‖ ^ 2 ≤ R ^ 2) →
      ∫⁻ y in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (⨆ b ∈ B, ‖∑ k : Fin K,
            b k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ 2
        ≤ ENNReal.ofReal (C * R ^ 2 * (B.card : ℝ)) := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ := separated_exponentials_near_orthogonal
  refine ⟨C₀, hC₀pos, ?_⟩
  intro B R hR hB
  set U : (Fin K → ℂ) → ℝ → ℝ :=
    fun b y => ‖∑ k : Fin K, b k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ with hU
  have hUcont : ∀ b, Continuous (U b) := by
    intro b
    have : Continuous fun y : ℝ => ∑ k : Fin K, b k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) :=
      continuous_finsetSum _ (fun k _ => by fun_prop)
    simpa only [hU] using this.norm
  have hUnn : ∀ b y, 0 ≤ U b y := fun b y => norm_nonneg _
  have hpt : ∀ y : ℝ,
      ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2 ≤ ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := by
    intro y
    have hsup := iSup_finset_sq_le_sum' B (fun b => U b y) (fun b => hUnn b y)
    have hnn : 0 ≤ (⨆ b ∈ B, U b y) := iSup_finset_nonneg' B (fun b => U b y) (fun b => hUnn b y)
    calc ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2
        = ENNReal.ofReal ((⨆ b ∈ B, U b y) ^ 2) := (ENNReal.ofReal_pow hnn 2).symm
      _ ≤ ENNReal.ofReal (∑ b ∈ B, (U b y) ^ 2) := ENNReal.ofReal_le_ofReal hsup
      _ = ∑ b ∈ B, ENNReal.ofReal ((U b y) ^ 2) :=
            ENNReal.ofReal_sum_of_nonneg (fun b _ => sq_nonneg _)
      _ = ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := by
            apply Finset.sum_congr rfl; intro b _
            rw [ENNReal.ofReal_pow (hUnn b y) 2]
  have hmeas : ∀ b ∈ B, Measurable (fun y : ℝ => ENNReal.ofReal (U b y) ^ 2) := by
    intro b _
    exact ((hUcont b).measurable.ennreal_ofReal.pow_const 2)
  have hint : ∀ b ∈ B, Integrable (fun y : ℝ => (U b y) ^ 2)
      (volume.restrict (Set.Ioc 0 1)) := by
    intro b _
    have hcont : Continuous (fun y : ℝ => (U b y) ^ 2) := (hUcont b).pow 2
    exact (hcont.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  calc ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2
      ≤ ∫⁻ y in Set.Ioc (0 : ℝ) 1, ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := lintegral_mono hpt
    _ = ∑ b ∈ B, ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (U b y) ^ 2 := by
          rw [lintegral_finsetSum]
          intro b hb; exact hmeas b hb
    _ = ∑ b ∈ B, ENNReal.ofReal (∫ y in (0 : ℝ)..1, (U b y) ^ 2) := by
          apply Finset.sum_congr rfl; intro b hb
          have h1 : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (U b y) ^ 2
              = ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((U b y) ^ 2) := by
            apply lintegral_congr; intro y
            rw [ENNReal.ofReal_pow (hUnn b y) 2]
          rw [h1]
          have h2 := ofReal_integral_eq_lintegral_ofReal (hint b hb)
            (ae_of_all _ (fun y => sq_nonneg (U b y)))
          rw [← h2]
          congr 1
          rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ ≤ ∑ b ∈ B, ENNReal.ofReal (C₀ * R ^ 2) := by
          apply Finset.sum_le_sum; intro b hb
          apply ENNReal.ofReal_le_ofReal
          have hc := hC₀ K lam hsep b
          calc ∫ y in (0 : ℝ)..1, (U b y) ^ 2
              ≤ C₀ * ∑ k : Fin K, ‖b k‖ ^ 2 := by
                rw [hU]; exact hc
            _ ≤ C₀ * R ^ 2 :=
                mul_le_mul_of_nonneg_left (hB b hb) (le_of_lt hC₀pos)
    _ = ENNReal.ofReal (C₀ * R ^ 2 * (B.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast (B.card),
              ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((B.card : ℕ) : ℝ) by positivity)]
          ring_nf

end Commons.Analysis.Fourier
