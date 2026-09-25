import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

/-!
# Subadditivity of the `ℓ²`-valued dyadic maximal function

For a finite family `f : Fin n → ℝ → ℝ` we have defined

`ell2Max f x = Σ_t (dyMax (‖f t ·‖ₑ) x)²`

in `Submission/Work/BourgainPlan/Maximal/ell2Maximal.lean`. The present file proves that its square
root is *subadditive*:

`(ell2Max (f + g) x) ^ (1/2) ≤ (ell2Max f x) ^ (1/2) + (ell2Max g x) ^ (1/2)`.

This is the `ℓ²` triangle inequality for the vector-valued maximal function
`(M f_t)_t`, i.e. Fefferman--Stein's vector-valued maximal operator is *sublinear* pointwise. It is
what lets one run the standard "maximal operator is a norm"-style arguments (dominated convergence,
density of a nice class, comparison of two maximal operators) on `ell2Max`.

Two ingredients suffice, and both are proved here:

* **Subadditivity of the scalar dyadic maximal function**, `dyMax_add_le`:
  `dyMax (φ + ψ) x ≤ dyMax φ x + dyMax ψ x`. This is immediate from additivity of the Lebesgue
  integral and `sup (a_i + b_i) ≤ sup a_i + sup b_i`, and needs only measurability of one summand
  (the other is treated by the *unconditional* `lintegral_add_right`-style transfer through
  `lintegral_add_left`).
* **Minkowski's inequality in `ℝ≥0∞` for finite sums**, `ENNReal_sum_sq_rpow_half_add_le`:
  `(Σ (a_i + b_i)²) ^ (1/2) ≤ (Σ a_i²) ^ (1/2) + (Σ b_i²) ^ (1/2)`. Values `⊤` are handled by a
  case split; when the two right-hand sides are finite all the entries are finite and the
  inequality is `Real.Lp_add_le_of_nonneg` (Minkowski for finite sums of nonnegative reals) after
  passing through `ENNReal.toReal`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- **Subadditivity of the scalar dyadic maximal function.**
`dyMax (φ + ψ) ≤ dyMax φ + dyMax ψ` pointwise. Only measurability of `φ` is needed: when both are
measurable this is additivity of the integral, and otherwise one can always turn the integral of a
sum into a sum of integrals using *one* measurable summand. -/
lemma dyMax_add_le {φ ψ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (_hψ : Measurable ψ) (x : ℝ) :
    dyMax (φ + ψ) x ≤ dyMax φ x + dyMax ψ x := by
  unfold dyMax
  refine iSup_le fun n => iSup_le fun k => iSup_le fun hx => ?_
  have hInt : ∫⁻ y in dyCell n k, (φ + ψ) y
      = (∫⁻ y in dyCell n k, φ y) + ∫⁻ y in dyCell n k, ψ y := by
    simp only [Pi.add_apply]
    rw [lintegral_add_left hφ]
  rw [hInt, mul_add]
  exact add_le_add (le_iSup_of_le n (le_iSup_of_le k (le_iSup_of_le hx le_rfl)))
    (le_iSup_of_le n (le_iSup_of_le k (le_iSup_of_le hx le_rfl)))

/-- **Minkowski's inequality for finite sums in `ℝ≥0∞`** (exponent `2`, and square roots on both
sides): `(Σ_i (a_i + b_i)²)^{1/2} ≤ (Σ_i a_i²)^{1/2} + (Σ_i b_i²)^{1/2}`.

If either right-hand side is `⊤` there is nothing to prove; otherwise every `a_i` and `b_i` is
finite (it is bounded by the corresponding square root of a finite sum of squares), the two sides
are finite, and the statement is the classical finite-sum Minkowski inequality
`Real.Lp_add_le_of_nonneg` transported through `ENNReal.toReal`. -/
lemma ENNReal_sum_sq_rpow_half_add_le {ι : Type*} [Fintype ι] (a b : ι → ℝ≥0∞) :
    (∑ i, (a i + b i) ^ (2:ℝ)) ^ ((1:ℝ)/2)
      ≤ (∑ i, a i ^ (2:ℝ)) ^ ((1:ℝ)/2) + (∑ i, b i ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
  have h12 : (0:ℝ) < (1:ℝ)/2 := by norm_num
  by_cases hA : (∑ i, a i ^ (2:ℝ)) ^ ((1:ℝ)/2) = ⊤
  · rw [hA, top_add]; exact le_top
  by_cases hB : (∑ i, b i ^ (2:ℝ)) ^ ((1:ℝ)/2) = ⊤
  · rw [hB, add_top]; exact le_top
  have hAlt : (∑ i, a i ^ (2:ℝ)) < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos h12).mp (lt_top_iff_ne_top.mpr hA)
  have hBlt : (∑ i, b i ^ (2:ℝ)) < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos h12).mp (lt_top_iff_ne_top.mpr hB)
  have hai : ∀ i, a i < ⊤ := fun i => by
    have h : a i ^ (2:ℝ) < ⊤ := (ENNReal.sum_lt_top.mp hAlt) i (Finset.mem_univ i)
    by_contra hcon
    rw [top_le_iff.mp (not_lt.mp hcon)] at h
    rw [ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 2)] at h
    exact lt_irrefl _ h
  have hbi : ∀ i, b i < ⊤ := fun i => by
    have h : b i ^ (2:ℝ) < ⊤ := (ENNReal.sum_lt_top.mp hBlt) i (Finset.mem_univ i)
    by_contra hcon
    rw [top_le_iff.mp (not_lt.mp hcon)] at h
    rw [ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 2)] at h
    exact lt_irrefl _ h
  have hCtoReal : (∑ i, (a i + b i) ^ (2:ℝ)).toReal
      = ∑ i, ((a i).toReal + (b i).toReal) ^ (2:ℝ) := by
    rw [ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← ENNReal.toReal_rpow, ENNReal.toReal_add (ne_of_lt (hai i)) (ne_of_lt (hbi i))]
    · intro i _
      exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ne_of_lt (ENNReal.add_lt_top.mpr ⟨hai i, hbi i⟩)))
  have hAtoReal : (∑ i, a i ^ (2:ℝ)).toReal = ∑ i, (a i).toReal ^ (2:ℝ) := by
    rw [ENNReal.toReal_sum]
    · exact Finset.sum_congr rfl fun i _ => by rw [← ENNReal.toReal_rpow]
    · intro i _
      exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt (hai i)))
  have hBtoReal : (∑ i, b i ^ (2:ℝ)).toReal = ∑ i, (b i).toReal ^ (2:ℝ) := by
    rw [ENNReal.toReal_sum]
    · exact Finset.sum_congr rfl fun i _ => by rw [← ENNReal.toReal_rpow]
    · intro i _
      exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt (hbi i)))
  have hLHSlt : (∑ i, (a i + b i) ^ (2:ℝ)) ^ ((1:ℝ)/2) < ⊤ := by
    refine ENNReal.rpow_lt_top_of_nonneg h12.le ?_
    exact ne_of_lt (ENNReal.sum_lt_top.mpr fun i _ => ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ne_of_lt (ENNReal.add_lt_top.mpr ⟨hai i, hbi i⟩)))
  have hRHSlt : (∑ i, a i ^ (2:ℝ)) ^ ((1:ℝ)/2) + (∑ i, b i ^ (2:ℝ)) ^ ((1:ℝ)/2) < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hA, lt_top_iff_ne_top.mpr hB⟩
  refine (ENNReal.toReal_le_toReal (ne_of_lt hLHSlt) (ne_of_lt hRHSlt)).mp ?_
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_add hA hB, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow, hCtoReal, hAtoReal, hBtoReal]
  exact Real.Lp_add_le_of_nonneg Finset.univ (p := 2) (by norm_num)
    (fun i _ => ENNReal.toReal_nonneg) (fun i _ => ENNReal.toReal_nonneg)

/-- Subadditivity of the `ℓ²`-valued dyadic maximal function: the square root of `ell2Max` is
subadditive over finite families (the `ℓ²` triangle inequality in `ℝ≥0∞`, together with
subadditivity of the scalar dyadic maximal function `dyMax`). -/
theorem ell2Max_rpow_half_add_le {n : ℕ} (f g : Fin n → ℝ → ℝ)
    (hf : ∀ t, Measurable (f t)) (hg : ∀ t, Measurable (g t)) (x : ℝ) :
    (Work.BourgainPlan.Maximal.ell2Max (f + g) x) ^ ((1 : ℝ) / 2)
      ≤ (Work.BourgainPlan.Maximal.ell2Max f x) ^ ((1 : ℝ) / 2)
        + (Work.BourgainPlan.Maximal.ell2Max g x) ^ ((1 : ℝ) / 2) := by
  -- Pointwise (in the component `t`) subadditivity of `dyMax`, using `‖f t y + g t y‖ₑ ≤ ‖f t y‖ₑ
  -- + ‖g t y‖ₑ`.
  have hcomp : ∀ t : Fin n,
      dyMax (fun y => ‖(f + g) t y‖ₑ) x
        ≤ dyMax (fun y => ‖f t y‖ₑ) x + dyMax (fun y => ‖g t y‖ₑ) x := by
    intro t
    refine le_trans (dyMax_mono ?_ x) (dyMax_add_le ((hf t).enorm) ((hg t).enorm) x)
    intro y
    simp only [Pi.add_apply]
    exact enorm_add_le _ _
  -- Square both sides and sum over the components.
  have hstep : ell2Max (f + g) x
      ≤ ∑ t, (dyMax (fun y => ‖f t y‖ₑ) x + dyMax (fun y => ‖g t y‖ₑ) x) ^ (2:ℝ) := by
    unfold ell2Max
    exact Finset.sum_le_sum fun t _ => ENNReal.rpow_le_rpow (hcomp t) (by norm_num)
  -- Take square roots and apply Minkowski.
  refine le_trans (ENNReal.rpow_le_rpow hstep (by norm_num)) ?_
  simpa only [ell2Max] using
    ENNReal_sum_sq_rpow_half_add_le (fun t : Fin n => dyMax (fun y => ‖f t y‖ₑ) x)
      (fun t : Fin n => dyMax (fun y => ‖g t y‖ₑ) x)

end Work.BourgainPlan.Maximal
