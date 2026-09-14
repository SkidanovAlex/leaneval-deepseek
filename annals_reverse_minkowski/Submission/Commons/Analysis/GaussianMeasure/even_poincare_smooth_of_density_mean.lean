import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.even_poincare_smooth_of_range_dense
import Submission.Commons.Analysis.GaussianMeasure.integrable_mul_exp_neg_stronglyConvex

open MeasureTheory Real Filter
open scoped Real Topology

namespace Commons.Analysis.GaussianMeasure

noncomputable section

/-- **Even Poincaré inequality from the density of the range of the weighted Laplacian and the
creation energy bound.**  This is the assembly step: given the two analytic inputs (the range
density `hdens` and the energy bound `henergy`) it derives the sharp even Poincaré inequality
with constant `1/(4π)`. -/
theorem even_poincare_smooth_of_density_mean {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] (f h : E → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2))
    (heven : ∀ x : E, f (-x) = f x)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2)
    (hh : ContDiff ℝ 1 h) (hheven : ∀ x : E, h (-x) = h x)
    (hgh : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |h x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖)
    (hdens : ∀ g : E → ℝ, ContDiff ℝ 1 g → (∀ x, g (-x) = g x) →
      (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
        |g x| ≤ C * (1 + ‖x‖) ^ N ∧
        |fderiv ℝ g x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) →
      (∫ x, g x * Real.exp (-(f x))) = 0 →
      ∀ ε : ℝ, 0 < ε → ∃ u : E → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
        (∫ x, ((- Laplacian.laplacian u x
              + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                  ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) - g x) ^ 2
            * Real.exp (-(f x))) ≤ ε)
    (henergy : ∀ u : E → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) →
      (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
        |u x| ≤ C * (1 + ‖x‖) ^ N ∧
        |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
        |fderiv ℝ (fderiv ℝ u) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) →
      4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
        ≤ (∫ x, (- Laplacian.laplacian u x
              + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                  ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ^ 2
            * Real.exp (-(f x)))) :
    (∫ x, h x ^ 2 * Real.exp (-(f x)))
        - (∫ x, h x * Real.exp (-(f x))) ^ 2 / (∫ x, Real.exp (-(f x)))
      ≤ (1 / (4 * Real.pi)) * ∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)) := by
  obtain ⟨Ch, hCh, Nh, hghN⟩ := hgh
  have hh_cont : Continuous h := hh.continuous
  -- integrability of the weight, of `h * weight` and of `h² * weight`
  have hZint : Integrable (fun x : E => Real.exp (-(f x))) := by
    simpa using integrable_mul_exp_neg_stronglyConvex f (fun _ => (1:ℝ)) hf hconv
      continuous_const (1:ℝ) (by norm_num) 0 (fun x => by simp)
  have hBint : Integrable (fun x : E => h x * Real.exp (-(f x))) :=
    integrable_mul_exp_neg_stronglyConvex f h hf hconv hh_cont Ch hCh Nh
      (fun x => (hghN x 0).1)
  have h2int : Integrable (fun x : E => h x ^ 2 * Real.exp (-(f x))) :=
    integrable_mul_exp_neg_stronglyConvex f (fun x => h x ^ 2) hf hconv (hh_cont.pow 2)
      (Ch ^ 2) (sq_nonneg _) (Nh * 2) (fun x => by
        have habs : |h x| ≤ Ch * (1 + ‖x‖) ^ Nh := (hghN x 0).1
        have h2 : h x ^ 2 ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg (h x)) habs 2
          rwa [sq_abs] at this
        rw [abs_of_nonneg (sq_nonneg _)]
        calc h x ^ 2 ≤ (Ch * (1 + ‖x‖) ^ Nh) ^ 2 := h2
          _ = Ch ^ 2 * (1 + ‖x‖) ^ (Nh * 2) := by rw [mul_pow, pow_mul])
  -- positivity of the total mass
  have hZpos : 0 < ∫ x : E, Real.exp (-(f x)) := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall (fun x => (Real.exp_pos _).le)) hZint]
    have hsupp : Function.support (fun x : E => Real.exp (-(f x))) = Set.univ := by
      ext x; simp only [Function.mem_support, Set.mem_univ, iff_true, ne_eq]
      exact Real.exp_ne_zero _
    rw [hsupp]
    exact isOpen_univ.measure_pos (volume : Measure E) Set.univ_nonempty
  set Z : ℝ := ∫ x : E, Real.exp (-(f x)) with hZdef
  set B : ℝ := ∫ x : E, h x * Real.exp (-(f x)) with hBdef
  have hZne : Z ≠ 0 := by rw [hZdef]; exact ne_of_gt hZpos
  set c : ℝ := B / Z with hcdef
  set k : E → ℝ := fun x => h x - c with hkdef
  -- `k` is even, `C¹` and of polynomial growth
  have hkeven : ∀ x : E, k (-x) = k x := by
    intro x
    change h (-x) - c = h x - c
    rw [hheven x]
  have hkcont : ContDiff ℝ 1 k := by
    rw [hkdef]
    exact hh.sub contDiff_const
  have hkgrowth : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E,
      |k x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ k x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ := by
    refine ⟨Ch + |c|, add_nonneg hCh (abs_nonneg c), Nh, fun x v => ⟨?_, ?_⟩⟩
    · change |h x - c| ≤ (Ch + |c|) * (1 + ‖x‖) ^ Nh
      have hbase : (1:ℝ) ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
      have h3 : |c| ≤ |c| * (1 + ‖x‖) ^ Nh := by
        have hp : (1:ℝ) ≤ (1 + ‖x‖) ^ Nh := one_le_pow₀ hbase
        nlinarith [abs_nonneg c]
      calc |h x - c| ≤ |h x| + |c| := abs_sub _ _
        _ ≤ Ch * (1 + ‖x‖) ^ Nh + |c| * (1 + ‖x‖) ^ Nh := add_le_add (hghN x 0).1 h3
        _ = (Ch + |c|) * (1 + ‖x‖) ^ Nh := by ring
    · change |fderiv ℝ (fun x => h x - c) x v| ≤ (Ch + |c|) * (1 + ‖x‖) ^ Nh * ‖v‖
      rw [fderiv_sub_const c]
      have hle : Ch * (1 + ‖x‖) ^ Nh ≤ (Ch + |c|) * (1 + ‖x‖) ^ Nh :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg c)) (by positivity)
      calc |fderiv ℝ h x v| ≤ Ch * (1 + ‖x‖) ^ Nh * ‖v‖ := (hghN x v).2
        _ ≤ (Ch + |c|) * (1 + ‖x‖) ^ Nh * ‖v‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg v)
  -- the weighted mean of `k` vanishes
  have hkmean : ∫ x : E, k x * Real.exp (-(f x)) = 0 := by
    have hsplit : (fun x : E => k x * Real.exp (-(f x)))
        = fun x : E => h x * Real.exp (-(f x)) - c * Real.exp (-(f x)) := by
      funext x; change (h x - c) * Real.exp (-(f x)) = _; ring
    rw [hsplit, integral_sub hBint (hZint.const_mul c), integral_const_mul]
    rw [← hBdef, ← hZdef, hcdef]
    field_simp
    ring
  -- range density for `k`
  have hrange : ∀ ε : ℝ, 0 < ε → ∃ u : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      (∫ x, ((- Laplacian.laplacian u x
            + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) - k x) ^ 2
          * Real.exp (-(f x))) ≤ ε :=
    fun ε hε => hdens k hkcont hkeven hkgrowth hkmean ε hε
  have hRD := even_poincare_smooth_of_range_dense f k hf hH hconv heven hgf
    hkcont hkeven hkgrowth hrange henergy
  -- weighted second moment of `k`
  have hk2 : ∫ x : E, k x ^ 2 * Real.exp (-(f x))
      = (∫ x : E, h x ^ 2 * Real.exp (-(f x))) - B ^ 2 / Z := by
    have hA : Integrable (fun x : E => h x ^ 2 * Real.exp (-(f x))) := h2int
    have hBf : Integrable (fun x : E => 2 * c * (h x * Real.exp (-(f x)))) :=
      hBint.const_mul (2 * c)
    have hCf : Integrable (fun x : E => c ^ 2 * Real.exp (-(f x))) := hZint.const_mul (c ^ 2)
    have hAB : Integrable (fun x : E =>
        h x ^ 2 * Real.exp (-(f x)) - 2 * c * (h x * Real.exp (-(f x)))) := hA.sub hBf
    have step1 : (∫ x : E, k x ^ 2 * Real.exp (-(f x)))
        = ∫ x : E, (h x ^ 2 * Real.exp (-(f x)) - 2 * c * (h x * Real.exp (-(f x))))
            + c ^ 2 * Real.exp (-(f x)) :=
      integral_congr_ae (Eventually.of_forall (fun x => by
        change (h x - c) ^ 2 * Real.exp (-(f x)) = _; ring))
    have step2 : (∫ x : E, (h x ^ 2 * Real.exp (-(f x)) - 2 * c * (h x * Real.exp (-(f x))))
            + c ^ 2 * Real.exp (-(f x)))
        = (∫ x : E, h x ^ 2 * Real.exp (-(f x)) - 2 * c * (h x * Real.exp (-(f x))))
            + (∫ x : E, c ^ 2 * Real.exp (-(f x))) :=
      integral_add hAB hCf
    have step3 : (∫ x : E, h x ^ 2 * Real.exp (-(f x)) - 2 * c * (h x * Real.exp (-(f x))))
        = (∫ x : E, h x ^ 2 * Real.exp (-(f x)))
            - (∫ x : E, 2 * c * (h x * Real.exp (-(f x)))) :=
      integral_sub hA hBf
    rw [step1, step2, step3, integral_const_mul, integral_const_mul]
    rw [← hBdef, ← hZdef, hcdef]
    field_simp
    ring
  -- the weighted gradient energy agrees with that of `h`
  have hgrad : ∫ x : E, ‖fderiv ℝ k x‖ ^ 2 * Real.exp (-(f x))
      = ∫ x : E, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x)) := by
    apply integral_congr_ae
    refine Eventually.of_forall (fun x => ?_)
    change ‖fderiv ℝ k x‖ ^ 2 * Real.exp (-(f x)) = ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(f x))
    have hfk : fderiv ℝ k x = fderiv ℝ h x := by
      rw [hkdef]
      exact fderiv_sub_const c
    rw [hfk]
  -- convert the inequality for `k` into the desired variance inequality for `h`
  rw [hkmean] at hRD
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div, sub_zero] at hRD
  rw [hk2] at hRD
  rw [hgrad] at hRD
  exact hRD

end

end Commons.Analysis.GaussianMeasure
