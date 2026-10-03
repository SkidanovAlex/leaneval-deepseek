import Mathlib
import Submission.Work.FIArea7.SumChiDefs
import Submission.Work.FIArea7.UniCharTerm6

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary norm bounds for the factors of `uniCoeff` -/

/-- `‖uniPow z k‖ ≤ 1` for every `z` (including `z = 0`). -/
lemma norm_uniPow_le_one_local (z : GaussianInt) (k : ℤ) : ‖uniPow z k‖ ≤ 1 := by
  rw [uniPow]
  by_cases hz : z.toComplex = 0
  · rw [hz, zero_div, norm_zpow, norm_zero, zero_zpow_eq]
    split <;> norm_num
  · have hnorm : ‖z.toComplex / ((‖z.toComplex‖ : ℝ) : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hz)]
    rw [norm_zpow, hnorm]
    simp

/-- `‖uniCoeff ε β k z‖ ≤ ‖β z‖` as soon as `‖ε z‖ ≤ 1`. -/
lemma uniCoeff_norm_le_local (β : GaussianInt → ℂ) (k : ℤ) (ε : GaussianInt → ℤ)
    (hε : ∀ z : GaussianInt, ‖((ε z : ℤ) : ℂ)‖ ≤ 1) (z : GaussianInt) :
    ‖uniCoeff ε β k z‖ ≤ ‖β z‖ := by
  rw [uniCoeff, norm_mul, norm_mul]
  calc ‖((ε z : ℤ) : ℂ)‖ * ‖betaPrime β z‖ * ‖uniPow z k‖
      ≤ 1 * ‖β z‖ * 1 := by
        gcongr
        · exact hε z
        · exact norm_betaPrime_le β z
        · exact norm_uniPow_le_one_local z k
    _ = ‖β z‖ := by ring

/-! ## Cauchy–Schwarz on a fibre -/

/-- **Cauchy–Schwarz for a finite complex sum**: `‖Σ_{z∈s} f z‖² ≤ |s|·Σ_{z∈s} ‖f z‖²`. -/
lemma norm_sum_sq_le_card_mul_sum_normSq (s : Finset GaussianInt) (f : GaussianInt → ℂ) :
    ‖∑ z ∈ s, f z‖ ^ 2 ≤ (s.card : ℝ) * ∑ z ∈ s, ‖f z‖ ^ 2 := by
  have h1 : ‖∑ z ∈ s, f z‖ ≤ ∑ z ∈ s, ‖f z‖ := norm_sum_le _ _
  have h2 : 0 ≤ ∑ z ∈ s, ‖f z‖ := Finset.sum_nonneg (fun z _ => norm_nonneg _)
  have h3 : 0 ≤ ‖∑ z ∈ s, f z‖ := norm_nonneg _
  have e1 : ‖∑ z ∈ s, f z‖ * ‖∑ z ∈ s, f z‖
      ≤ (∑ z ∈ s, ‖f z‖) * (∑ z ∈ s, ‖f z‖) := mul_self_le_mul_self h3 h1
  have e2 : (∑ z ∈ s, ‖f z‖) * (∑ z ∈ s, ‖f z‖) ≤ (s.card : ℝ) * ∑ z ∈ s, ‖f z‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := s) (f := fun z => ‖f z‖)
    rw [sq] at this
    exact this
  rw [sq]
  linarith [e1, e2]

/-! ## The `L²`-mass of the §17 class function -/

/-- **The `L²`-mass of the §17 class function.** If every class of `G = (ℤ[i]/Q)^*` is met by at
most `M²` points of the box, then the squared moduli of the class function `uniClassFn` (with the
coefficient `uniCoeff ε v k`) sum to at most `M²` times the mass of `v` on the box. -/
theorem sum_uniClassFn_normSq_le (Pa : Work.FITop.Params) (Q : ℕ) [NeZero Q]
    (ε : GaussianInt → ℤ) (v : GaussianInt → ℂ) (k : ℤ)
    (hε : ∀ z : GaussianInt, ‖((ε z : ℤ) : ℂ)‖ ≤ 1) (M : ℕ)
    (hM : ∀ a : Work.FIArea7.GaussUnit Q,
      ((Work.FIArea7.uniUnitBox Pa Q).filter (fun z => Work.FIArea7.unitClassD Q z = a)).card
        ≤ M * M) :
    ∑ a : Work.FIArea7.GaussUnit Q,
        ‖Work.FIArea7.uniClassFn Pa Q (Work.FIArea7.uniCoeff ε v k) a‖ ^ 2
      ≤ (M : ℝ) ^ 2 * ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖v z‖ ^ 2 := by
  classical
  set c : GaussianInt → ℂ := uniCoeff ε v k with hc
  -- the coefficient is dominated by `v` on the box
  have hcz : ∀ z : GaussianInt, ‖c z‖ ≤ ‖v z‖ := by
    intro z
    rw [hc]
    exact uniCoeff_norm_le_local v k ε hε z
  -- Cauchy–Schwarz on a single fibre
  have hCS : ∀ s : Finset GaussianInt,
      ‖∑ z ∈ s, star (c z)‖ ^ 2 ≤ (s.card : ℝ) * ∑ z ∈ s, ‖c z‖ ^ 2 := by
    intro s
    have h := norm_sum_sq_le_card_mul_sum_normSq s (fun z => star (c z))
    calc ‖∑ z ∈ s, star (c z)‖ ^ 2
        ≤ (s.card : ℝ) * ∑ z ∈ s, ‖star (c z)‖ ^ 2 := h
      _ = (s.card : ℝ) * ∑ z ∈ s, ‖c z‖ ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl (fun z _ => by rw [norm_star])
  -- the bound on each class
  have hmain : ∀ a : GaussUnit Q,
      ‖uniClassFn Pa Q c a‖ ^ 2
        ≤ (M : ℝ) ^ 2
            * ∑ z ∈ (uniUnitBox Pa Q).filter (fun z => unitClassD Q z = a), ‖c z‖ ^ 2 := by
    intro a
    have hCSa := hCS ((uniUnitBox Pa Q).filter (fun z => unitClassD Q z = a))
    have hcard : ((((uniUnitBox Pa Q).filter
        (fun z => unitClassD Q z = a)).card : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by
      have h2 : ((((uniUnitBox Pa Q).filter
          (fun z => unitClassD Q z = a)).card : ℕ) : ℝ) ≤ ((M * M : ℕ) : ℝ) := by
        exact_mod_cast hM a
      simpa [Nat.cast_mul, pow_two] using h2
    have hnn : 0 ≤ ∑ z ∈ (uniUnitBox Pa Q).filter (fun z => unitClassD Q z = a), ‖c z‖ ^ 2 :=
      Finset.sum_nonneg (fun z _ => by positivity)
    calc ‖uniClassFn Pa Q c a‖ ^ 2
        = ‖∑ z ∈ (uniUnitBox Pa Q).filter (fun z => unitClassD Q z = a), star (c z)‖ ^ 2 := by
          rw [uniClassFn]
      _ ≤ ((((uniUnitBox Pa Q).filter
              (fun z => unitClassD Q z = a)).card : ℕ) : ℝ)
            * ∑ z ∈ (uniUnitBox Pa Q).filter (fun z => unitClassD Q z = a), ‖c z‖ ^ 2 := hCSa
      _ ≤ (M : ℝ) ^ 2
            * ∑ z ∈ (uniUnitBox Pa Q).filter (fun z => unitClassD Q z = a), ‖c z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcard hnn
  -- the fibres partition the box `uniUnitBox`
  have hfib : (∑ a : GaussUnit Q,
        ∑ z ∈ (uniUnitBox Pa Q).filter (fun z => unitClassD Q z = a), ‖c z‖ ^ 2)
      = ∑ z ∈ uniUnitBox Pa Q, ‖c z‖ ^ 2 := by
    simpa using Finset.sum_fiberwise (uniUnitBox Pa Q) (unitClassD Q) (fun z => ‖c z‖ ^ 2)
  calc ∑ a : GaussUnit Q, ‖uniClassFn Pa Q c a‖ ^ 2
      ≤ ∑ a : GaussUnit Q, (M : ℝ) ^ 2
            * ∑ z ∈ (uniUnitBox Pa Q).filter (fun z => unitClassD Q z = a), ‖c z‖ ^ 2 :=
        Finset.sum_le_sum (fun a _ => hmain a)
    _ = (M : ℝ) ^ 2 * ∑ a : GaussUnit Q,
            ∑ z ∈ (uniUnitBox Pa Q).filter (fun z => unitClassD Q z = a), ‖c z‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (M : ℝ) ^ 2 * ∑ z ∈ uniUnitBox Pa Q, ‖c z‖ ^ 2 := by rw [hfib]
    _ ≤ (M : ℝ) ^ 2 * ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖v z‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ z ∈ uniUnitBox Pa Q, ‖c z‖ ^ 2
            ≤ ∑ z ∈ uniUnitBox Pa Q, ‖v z‖ ^ 2 :=
              Finset.sum_le_sum (fun z _ => by
                have h := hcz z
                have h0 : 0 ≤ ‖c z‖ := norm_nonneg _
                have h1 : 0 ≤ ‖v z‖ := norm_nonneg _
                nlinarith [h, h0, h1])
          _ ≤ ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖v z‖ ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun z _ _ => by positivity)

end

end Work.FIArea7
