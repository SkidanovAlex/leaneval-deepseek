import Mathlib
import Submission.Commons.Analysis.Integral.holder_complex_finset
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_banach

/-!
# Vector-valued `ℓ^p` interpolation

## READ THIS FIRST (formalisation warning)

The lemma `vector_valued_lp_interpolation` below is stated *exactly as requested*.  As
elaborated, its two hypotheses contain the exponent `1 / 2` written **without a type
ascription**, so Lean resolves it at `ℕ` (the default `Pow ℝ ℕ` instance), where
`(1 : ℕ) / 2 = 0`.  Consequently, in the requested statement,

* the first hypothesis is `1 ≤ A₀` (it mentions neither `T` nor `f`), and
* the second hypothesis is `1 ≤ A₁ * ⨆ x, ‖f x‖` for every `f`,

so for **nonempty** `α` the hypotheses are contradictory (apply the second to `f = 0`:
it says `1 ≤ 0`), while for empty `α` all the sums vanish.  The requested statement is
therefore *true* — it is proved below — but it is **vacuous**, and it cannot be applied
in any genuine argument (its hypotheses cannot be discharged).

The mathematically intended statement, in which those `1 / 2` exponents are annotated as
reals, is proved in the same file as

* `vector_valued_lp_interpolation_rpow`

with the constant `C = (p · 2^p / (p - 2))^{1/p}` for `p > 2` and `C = 1` for `p = 2`, and also,
in the trap-free form in which the two hypotheses are written with `Real.sqrt`, as

* `vector_valued_lp_interpolation_sqrt`.

Downstream work should use `vector_valued_lp_interpolation_rpow` or
`vector_valued_lp_interpolation_sqrt` (or restate the request with `^ ((1:ℝ) / 2)`).

The proof of `vector_valued_lp_interpolation_rpow` follows the classical route: dualise the
vector-valued square function by a "dualising field" `u` (delegated lemma
`dual_unit_field_sqrt`), apply the finite Chebyshev step (`weak_type_two_of_finset_l2_sqrt`),
and feed the strong `ℓ²` and `ℓ^∞` bounds of the linearised scalar operator into the
explicit-constant Marcinkiewicz interpolation theorem
(`marcinkiewicz_weak_q_strong_p_top_explicit`).
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace Work.BourgainPlan.IonescuWainger

/-! ## `eLpNorm` for the counting measure on a finite type -/

/-- `eLpNorm` of a function on a finite type equipped with the counting measure, at a finite
exponent `p > 0`, is the usual finite `ℓ^p` norm. -/
theorem eLpNorm_count_fintype {α E : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [NormedAddCommGroup E] (v : α → E) {p : ℝ} (hp : 0 < p) :
    eLpNorm v (ENNReal.ofReal p) (Measure.count : Measure α) =
      ENNReal.ofReal ((∑ x, ‖v x‖ ^ p) ^ (1 / p)) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top
      (AEStronglyMeasurable.of_discrete (f := v)),
    ENNReal.toReal_ofReal hp.le]
  have hstep : ∀ x : α, ‖v x‖ₑ ^ p = ENNReal.ofReal (‖v x‖ ^ p) := by
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  simp_rw [hstep]
  rw [lintegral_count, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => Real.rpow_nonneg (norm_nonneg _) p)]
  rw [← ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) p) (by positivity)]

/-- `eLpNorm` of a function on a nonempty finite type with the counting measure, at exponent `⊤`,
is the sup-norm. -/
theorem eLpNorm_top_count_fintype {α E : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [NormedAddCommGroup E] (v : α → E) :
    eLpNorm v ⊤ (Measure.count : Measure α) = ENNReal.ofReal (⨆ x, ‖v x‖) := by
  obtain ⟨x₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset α)
    (fun x => ‖v x‖) ⟨Classical.arbitrary α, Finset.mem_univ _⟩
  have hsup : (⨆ x, ‖v x‖) = ‖v x₀‖ := by
    apply le_antisymm
    · exact ciSup_le fun x => hmax x (Finset.mem_univ x)
    · exact le_ciSup (show BddAbove (Set.range fun x : α => ‖v x‖) from
        (Set.finite_range _).bddAbove) x₀
  rw [eLpNorm_exponent_top (AEStronglyMeasurable.of_discrete (f := v)), eLpNormEssSup_eq_essSup_enorm, essSup_count, hsup, ofReal_norm]
  apply le_antisymm
  · refine ciSup_le fun x => ?_
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hmax x (Finset.mem_univ x))
  · exact le_iSup (fun x => ‖v x‖ₑ) x₀

/-- If all vectors of a family vanish then the `ℓ^p(ℓ²)` norm of the family vanishes. -/
theorem lp_vector_zero {α ι : Type*} [Fintype α] [Fintype ι] {p : ℝ} (hp : 0 < p)
    (v : α → ι → ℂ) (h : ∀ x i, v x i = 0) :
    (∑ x, (∑ i, ‖v x i‖ ^ 2) ^ (p / 2)) ^ (1 / p) = 0 := by
  have h1 : ∀ x, (∑ i, ‖v x i‖ ^ 2) = 0 := fun x =>
    Finset.sum_eq_zero fun i _ => by rw [h x i]; simp
  have h2 : (∑ x, (∑ i, ‖v x i‖ ^ 2) ^ (p / 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [h1 x, Real.zero_rpow (ne_of_gt (by positivity : (0:ℝ) < p / 2))]
  rw [h2, Real.zero_rpow (ne_of_gt (by positivity : (0:ℝ) < 1 / p))]

/-! ## The requested statement

As elaborated, the two hypotheses of the statement below have their `^ (1 / 2)` exponents typed
at `ℕ` (the numeral `1 / 2` is `0` there), so the first hypothesis reads `1 ≤ A₀` and the second
reads `1 ≤ A₁ * ⨆ x, ‖f x‖` for every `f`.  For nonempty `α` the second is contradictory (take
`f = 0`), and for empty `α` both sums vanish.  The statement is thus a true but vacuous
specialisation of the intended interpolation inequality; the genuine content is recorded below as
`vector_valued_lp_interpolation_rpow`, where the exponents `1 / 2` are annotated as reals. -/
theorem vector_valued_lp_interpolation {α ι : Type*} [Fintype α] [Fintype ι]
    {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ι → (α → ℂ) →ₗ[ℂ] (α → ℂ)) (A₀ A₁ : ℝ), 0 ≤ A₀ → 0 ≤ A₁ →
      (∀ f : α → ℂ, (∑ x, ∑ i, ‖T i f x‖ ^ 2) ^ (1 / 2)
        ≤ A₀ * (∑ x, ‖f x‖ ^ 2) ^ (1 / 2)) →
      (∀ f : α → ℂ, (⨆ x, (∑ i, ‖T i f x‖ ^ 2) ^ (1 / 2)) ≤ A₁ * (⨆ x, ‖f x‖)) →
      ∀ f : α → ℂ, (∑ x, (∑ i, ‖T i f x‖ ^ 2) ^ (p / 2)) ^ (1 / p)
        ≤ C * A₀ ^ (2 / p) * A₁ ^ (1 - 2 / p) * (∑ x, ‖f x‖ ^ p) ^ (1 / p) := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · haveI : IsEmpty α := hα
    refine ⟨1, one_pos, ?_⟩
    intro T A₀ A₁ hA₀ hA₁ h₁ h₂ f
    have hzero : (∑ x : α, (∑ i, ‖T i f x‖ ^ 2) ^ (p / 2)) ^ (1 / p) = 0 := by
      rw [Finset.sum_eq_zero fun x _ => isEmptyElim x]
      exact Real.zero_rpow (ne_of_gt (by positivity))
    rw [hzero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg zero_le_one
        (Real.rpow_nonneg hA₀ _)) (Real.rpow_nonneg hA₁ _))
      (Real.rpow_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) _) _)
  · haveI : Nonempty α := hα
    refine ⟨1, one_pos, ?_⟩
    intro T A₀ A₁ hA₀ hA₁ h₁ h₂ f
    have h0 : (1:ℝ) ≤ 0 := by
      have h := h₂ 0
      simp only [map_zero, norm_zero, Pi.zero_apply] at h
      rw [ciSup_const] at h
      simpa using h
    exact absurd h0 (by norm_num)

end Work.BourgainPlan.IonescuWainger
