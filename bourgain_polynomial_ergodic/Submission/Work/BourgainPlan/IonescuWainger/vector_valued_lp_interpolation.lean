import Mathlib
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_q_strong_p_top
import Submission.Commons.Analysis.Integral.holder_complex_finset
import Submission.Work.BourgainPlan.IonescuWainger.marcinkiewicz_weak_q_strong_p_top_explicit
import Submission.Work.BourgainPlan.IonescuWainger.dual_unit_field_sqrt
import Submission.Work.BourgainPlan.IonescuWainger.weak_type_two_of_finset_l2_sqrt

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

/-- **Vector-valued `ℓ^p` interpolation** (the intended form of
`vector_valued_lp_interpolation`): a family of linear operators that is bounded on
`ℓ²(ℓ²_ι)` with constant `A₀` and pointwise bounded with constant `A₁` is bounded on `ℓ^p(ℓ²_ι)`
with constant `C p · A₀^{2/p} A₁^{1-2/p}`, for `2 ≤ p`. -/
theorem vector_valued_lp_interpolation_rpow {α ι : Type*} [Fintype α] [Fintype ι]
    {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ι → (α → ℂ) →ₗ[ℂ] (α → ℂ)) (A₀ A₁ : ℝ), 0 ≤ A₀ → 0 ≤ A₁ →
      (∀ f : α → ℂ, (∑ x, ∑ i, ‖T i f x‖ ^ 2) ^ ((1:ℝ) / 2)
        ≤ A₀ * (∑ x, ‖f x‖ ^ 2) ^ ((1:ℝ) / 2)) →
      (∀ f : α → ℂ, (⨆ x, (∑ i, ‖T i f x‖ ^ 2) ^ ((1:ℝ) / 2)) ≤ A₁ * (⨆ x, ‖f x‖)) →
      ∀ f : α → ℂ, (∑ x, (∑ i, ‖T i f x‖ ^ 2) ^ (p / 2)) ^ (1 / p)
        ≤ C * A₀ ^ (2 / p) * A₁ ^ (1 - 2 / p) * (∑ x, ‖f x‖ ^ p) ^ (1 / p) := by
  classical
  rcases lt_or_eq_of_le hp with hpgt | hpeq
  · refine ⟨(p * (2:ℝ) ^ p / (p - 2)) ^ (1 / p), ?_, ?_⟩
    · exact Real.rpow_pos_of_pos (by positivity) _
    · intro T A₀ A₁ hA₀ hA₁ h₁ h₂ f
      have hp0 : 0 < p := by linarith
      rcases isEmpty_or_nonempty α with hα | hα
      · haveI : IsEmpty α := hα
        have hzero : (∑ x : α, (∑ i, ‖T i f x‖ ^ 2) ^ (p / 2)) ^ (1 / p) = 0 := by
          rw [Finset.sum_eq_zero fun x _ => isEmptyElim x]
          exact Real.zero_rpow (ne_of_gt (by positivity))
        rw [hzero]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
            (Real.rpow_nonneg hA₀ _)) (Real.rpow_nonneg hA₁ _))
          (Real.rpow_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) _) _)
      · haveI : Nonempty α := hα
        -- degenerate cases for the two constants
        rcases eq_or_lt_of_le hA₀ with hA₀0 | hA₀pos
        · have hT : ∀ x i, T i f x = 0 := by
            intro x i
            have hle : (∑ x, ∑ i, ‖T i f x‖ ^ 2) ^ ((1:ℝ)/2) ≤ 0 := by
              have h := h₁ f
              rw [← hA₀0] at h
              simpa using h
            have hnn : 0 ≤ ∑ x, ∑ i, ‖T i f x‖ ^ 2 :=
              Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => sq_nonneg _
            have hsq : (∑ x, ∑ i, ‖T i f x‖ ^ 2) = 0 := by
              have h0 : ((∑ x, ∑ i, ‖T i f x‖ ^ 2) ^ ((1:ℝ)/2)) = 0 :=
                le_antisymm hle (Real.rpow_nonneg hnn _)
              have hsqrt : Real.sqrt (∑ x, ∑ i, ‖T i f x‖ ^ 2) = 0 := by
                rw [Real.sqrt_eq_rpow]; exact h0
              calc (∑ x, ∑ i, ‖T i f x‖ ^ 2)
                  = (Real.sqrt (∑ x, ∑ i, ‖T i f x‖ ^ 2)) ^ 2 := (Real.sq_sqrt hnn).symm
                _ = 0 := by rw [hsqrt]; ring
            have hx0 : (∑ i, ‖T i f x‖ ^ 2) = 0 :=
              (Finset.sum_eq_zero_iff_of_nonneg
                (fun x _ => Finset.sum_nonneg fun i _ => sq_nonneg _)).mp hsq x (Finset.mem_univ x)
            exact norm_eq_zero.mp (sq_eq_zero_iff.mp
              ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hx0 i (Finset.mem_univ i)))
          rw [lp_vector_zero hp0 (fun x i => T i f x) hT]
          exact mul_nonneg
            (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
              (Real.rpow_nonneg hA₀ _)) (Real.rpow_nonneg hA₁ _))
            (Real.rpow_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) _) _)
        rcases eq_or_lt_of_le hA₁ with hA₁0 | hA₁pos
        · have hT : ∀ x i, T i f x = 0 := by
            intro x i
            have hx : (∑ i, ‖T i f x‖ ^ 2) ^ ((1:ℝ)/2) ≤ 0 := by
              refine le_trans (le_ciSup (show BddAbove (Set.range fun x : α =>
                (∑ i, ‖T i f x‖ ^ 2) ^ ((1:ℝ)/2)) from (Set.finite_range _).bddAbove) x) ?_
              calc (⨆ x, (∑ i, ‖T i f x‖ ^ 2) ^ ((1:ℝ)/2)) ≤ A₁ * (⨆ x, ‖f x‖) := h₂ f
                _ = 0 := by simp [← hA₁0]
            have hnn : 0 ≤ ∑ i, ‖T i f x‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
            have hsq : (∑ i, ‖T i f x‖ ^ 2) = 0 := by
              have h0 : ((∑ i, ‖T i f x‖ ^ 2) ^ ((1:ℝ)/2)) = 0 :=
                le_antisymm hx (Real.rpow_nonneg hnn _)
              have hsqrt : Real.sqrt (∑ i, ‖T i f x‖ ^ 2) = 0 := by
                rw [Real.sqrt_eq_rpow]; exact h0
              calc (∑ i, ‖T i f x‖ ^ 2)
                  = (Real.sqrt (∑ i, ‖T i f x‖ ^ 2)) ^ 2 := (Real.sq_sqrt hnn).symm
                _ = 0 := by rw [hsqrt]; ring
            exact norm_eq_zero.mp (sq_eq_zero_iff.mp
              ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hsq i (Finset.mem_univ i)))
          rw [lp_vector_zero hp0 (fun x i => T i f x) hT]
          exact mul_nonneg
            (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
              (Real.rpow_nonneg hA₀ _)) (Real.rpow_nonneg hA₁ _))
            (Real.rpow_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) _) _)
        · -- main case
          letI : MeasurableSpace α := ⊤
          haveI : MeasurableSingletonClass α := inferInstance
          obtain ⟨u, hu1, hu2⟩ := dual_unit_field_sqrt (fun x (i : ι) => T i f x)
          have hcs : ∀ (g : α → ℂ) (x : α),
              ‖∑ i, u x i * T i g x‖ ≤ Real.sqrt (∑ i, ‖T i g x‖ ^ (2:ℝ)) := by
            intro g x
            have hh := Commons.Analysis.Integral.holder_complex_finset (Finset.univ : Finset ι)
              (fun i => u x i) (fun i => T i g x) (p := 2) (q := 2)
              (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
            rw [Real.sqrt_eq_rpow]
            calc ‖∑ i, u x i * T i g x‖
                = ‖∑ i ∈ (Finset.univ : Finset ι), u x i * T i g x‖ := by simp
              _ ≤ (∑ i ∈ (Finset.univ : Finset ι), ‖u x i‖ ^ (2:ℝ)) ^ ((1:ℝ)/2)
                    * (∑ i ∈ (Finset.univ : Finset ι), ‖T i g x‖ ^ (2:ℝ)) ^ ((1:ℝ)/2) := hh
              _ ≤ 1 * (∑ i, ‖T i g x‖ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
                  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg
                    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) _)
                  calc (∑ i, ‖u x i‖ ^ (2:ℝ)) ^ ((1:ℝ)/2)
                      ≤ 1 ^ ((1:ℝ)/2) := Real.rpow_le_rpow
                        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
                        (hu1 x) (by norm_num)
                    _ = 1 := Real.one_rpow _
              _ = (∑ i, ‖T i g x‖ ^ (2:ℝ)) ^ ((1:ℝ)/2) := one_mul _
          have hL2 : ∀ g : α → ℂ, Real.sqrt (∑ x, ‖∑ i, u x i * T i g x‖ ^ (2:ℝ))
              ≤ A₀ * Real.sqrt (∑ x, ‖g x‖ ^ (2:ℝ)) := by
            intro g
            rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
            have hpt : ∀ x, ‖∑ i, u x i * T i g x‖ ^ (2:ℝ) ≤ ∑ i, ‖T i g x‖ ^ (2:ℝ) := by
              intro x
              calc ‖∑ i, u x i * T i g x‖ ^ (2:ℝ)
                  ≤ (Real.sqrt (∑ i, ‖T i g x‖ ^ (2:ℝ))) ^ (2:ℝ) :=
                    Real.rpow_le_rpow (norm_nonneg _) (hcs g x) (by norm_num)
                _ = ∑ i, ‖T i g x‖ ^ (2:ℝ) := by
                    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul
                      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _),
                      show ((1:ℝ)/2) * 2 = 1 by norm_num, Real.rpow_one]
            have hsum : (∑ x, ‖∑ i, u x i * T i g x‖ ^ (2:ℝ))
                ≤ ∑ x, ∑ i, ‖T i g x‖ ^ (2:ℝ) := Finset.sum_le_sum fun x _ => hpt x
            have hb : (∑ x, ∑ i, ‖T i g x‖ ^ (2:ℝ)) = ∑ x, ∑ i, ‖T i g x‖ ^ 2 := by
              simp_rw [Real.rpow_two]
            have hb2 : (∑ x, ‖g x‖ ^ (2:ℝ)) = ∑ x, ‖g x‖ ^ 2 := by simp_rw [Real.rpow_two]
            have hsq : (∑ x, ∑ i, ‖T i g x‖ ^ 2) ≤ A₀ ^ 2 * ∑ x, ‖g x‖ ^ 2 := by
              have hg1 := h₁ g
              have hA : 0 ≤ ∑ x, ∑ i, ‖T i g x‖ ^ 2 :=
                Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => sq_nonneg _
              have hB : 0 ≤ ∑ x, ‖g x‖ ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
              have h2 := pow_le_pow_left₀ (Real.rpow_nonneg hA _) hg1 2
              rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hA, ← Real.sqrt_eq_rpow, mul_pow,
                Real.sq_sqrt hB] at h2
              exact h2
            calc (∑ x, ‖∑ i, u x i * T i g x‖ ^ (2:ℝ)) ^ ((1:ℝ)/2)
                ≤ (A₀ ^ 2 * (∑ x, ‖g x‖ ^ (2:ℝ))) ^ ((1:ℝ)/2) := by
                  refine Real.rpow_le_rpow
                    (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) _) ?_ (by norm_num)
                  calc (∑ x, ‖∑ i, u x i * T i g x‖ ^ (2:ℝ))
                      ≤ ∑ x, ∑ i, ‖T i g x‖ ^ (2:ℝ) := hsum
                    _ = ∑ x, ∑ i, ‖T i g x‖ ^ 2 := hb
                    _ ≤ A₀ ^ 2 * ∑ x, ‖g x‖ ^ 2 := hsq
                    _ = A₀ ^ 2 * (∑ x, ‖g x‖ ^ (2:ℝ)) := by rw [hb2]
              _ = A₀ * (∑ x, ‖g x‖ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
                  rw [Real.mul_rpow (sq_nonneg A₀)
                    (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) _),
                    ← Real.sqrt_eq_rpow, Real.sqrt_sq hA₀pos.le]
          have hLinf : ∀ g : α → ℂ, (⨆ x, ‖∑ i, u x i * T i g x‖) ≤ A₁ * (⨆ x, ‖g x‖) := by
            intro g
            refine ciSup_le fun x => ?_
            calc ‖∑ i, u x i * T i g x‖ ≤ Real.sqrt (∑ i, ‖T i g x‖ ^ (2:ℝ)) := hcs g x
              _ = (∑ i, ‖T i g x‖ ^ (2:ℝ)) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
              _ = (∑ i, ‖T i g x‖ ^ 2) ^ ((1:ℝ)/2) := by simp_rw [Real.rpow_two]
              _ ≤ A₁ * (⨆ x, ‖g x‖) :=
                  le_trans (le_ciSup (show BddAbove (Set.range fun x : α =>
                    (∑ i, ‖T i g x‖ ^ 2) ^ ((1:ℝ)/2)) from (Set.finite_range _).bddAbove) x) (h₂ g)
          have hweak := weak_type_two_of_finset_l2_sqrt hA₀pos.le
            (fun g x => ∑ i, u x i * T i g x) hL2
          have hstrong : ∀ g : α → ℂ,
              eLpNorm (fun x => ∑ i, u x i * T i g x) ⊤ (Measure.count : Measure α)
                ≤ ENNReal.ofReal A₁ * eLpNorm g ⊤ (Measure.count : Measure α) := by
            intro g
            rw [eLpNorm_top_count_fintype (fun x => ∑ i, u x i * T i g x),
              eLpNorm_top_count_fintype g]
            calc ENNReal.ofReal (⨆ x, ‖∑ i, u x i * T i g x‖)
                ≤ ENNReal.ofReal (A₁ * ⨆ x, ‖g x‖) := ENNReal.ofReal_le_ofReal (hLinf g)
              _ = ENNReal.ofReal A₁ * ENNReal.ofReal (⨆ x, ‖g x‖) :=
                  ENNReal.ofReal_mul hA₁pos.le
          have hadd : ∀ g₁ g₂ : α → ℂ, (fun x => ∑ i, u x i * T i (g₁ + g₂) x)
              = (fun x => ∑ i, u x i * T i g₁ x) + (fun x => ∑ i, u x i * T i g₂ x) := by
            intro g₁ g₂
            funext x
            simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
          have hM := marcinkiewicz_weak_q_strong_p_top_explicit
            (μ := (Measure.count : Measure α)) (ν := (Measure.count : Measure α))
            (fun g x => ∑ i, u x i * T i g x) hadd
            (fun g => (Measurable.of_discrete).aemeasurable)
            (q := 2) (A0 := A₀) (A1 := A₁) (by norm_num) hA₀pos hA₁pos hweak hstrong
            (p := p) hpgt
          have hreal := hM f Measurable.of_discrete
          rw [eLpNorm_count_fintype (fun x => ∑ i, u x i * T i f x) hp0,
            eLpNorm_count_fintype f hp0] at hreal
          have hmain : (∑ x, ‖∑ i, u x i * T i f x‖ ^ p) ^ (1 / p)
              ≤ (p * (2*A₀) ^ (2:ℝ) * (2*A₁) ^ (p - 2) / (p - 2)) ^ (1 / p)
                * (∑ x, ‖f x‖ ^ p) ^ (1 / p) := by
            have hKnn : 0 ≤ p * (2*A₀) ^ (2:ℝ) * (2*A₁) ^ (p - 2) / (p - 2) := by positivity
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hKnn _)] at hreal
            exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hreal
          have hLHSid : (∑ x, ‖∑ i, u x i * T i f x‖ ^ p) ^ (1 / p)
              = (∑ x, (∑ i, ‖T i f x‖ ^ 2) ^ (p / 2)) ^ (1 / p) := by
            congr 1
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hu2 x, Complex.norm_def, Complex.normSq_ofReal,
              Real.sqrt_mul_self (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
              ← Real.rpow_mul (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _),
              show ((1:ℝ)/2) * p = p / 2 by ring]
            simp_rw [← Real.rpow_two]
          -- the explicit constant
          set C : ℝ := (p * (2:ℝ) ^ p / (p - 2)) ^ (1 / p) with hC
          have hbase : 0 ≤ p * (2:ℝ) ^ p / (p - 2) := by positivity
          have hCpos : 0 < C := Real.rpow_pos_of_pos (by positivity) _
          have h1p : (1 / p) * p = 1 := by
            rw [div_eq_mul_inv, one_mul, inv_mul_cancel₀ (ne_of_gt hp0)]
          have hp1 : p * (1 / p) = 1 := by
            rw [mul_one_div, div_self (ne_of_gt hp0)]
          have hCp : C ^ p = p * (2:ℝ) ^ p / (p - 2) := by
            rw [hC, ← Real.rpow_mul hbase (1 / p) p, h1p, Real.rpow_one]
          have h4 : (2:ℝ) ^ (p - 2) = (2:ℝ) ^ p / 4 := by
            have h : (2:ℝ) ^ p = (2:ℝ) ^ (p - 2) * 4 := by
              conv_lhs => rw [show p = (p - 2) + 2 by ring]
              rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),
                show (2:ℝ) ^ (2:ℝ) = 4 by rw [Real.rpow_two]; norm_num]
            rw [h]; ring
          have hK : p * (2*A₀) ^ (2:ℝ) * (2*A₁) ^ (p - 2) / (p - 2)
              = C ^ p * A₀ ^ (2:ℝ) * A₁ ^ (p - 2) := by
            rw [hCp, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hA₀pos.le,
              Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hA₁pos.le, h4,
              show (2:ℝ) ^ (2:ℝ) = 4 by rw [Real.rpow_two]; norm_num]
            ring
          have hKroot : (p * (2*A₀) ^ (2:ℝ) * (2*A₁) ^ (p - 2) / (p - 2)) ^ (1 / p)
              = C * A₀ ^ (2 / p) * A₁ ^ (1 - 2 / p) := by
            rw [hK, Real.mul_rpow
                (mul_nonneg (Real.rpow_nonneg hCpos.le _) (Real.rpow_nonneg hA₀pos.le _))
                (Real.rpow_nonneg hA₁pos.le _),
              Real.mul_rpow (Real.rpow_nonneg hCpos.le _) (Real.rpow_nonneg hA₀pos.le _),
              ← Real.rpow_mul hCpos.le p (1 / p),
              ← Real.rpow_mul hA₀pos.le 2 (1 / p),
              ← Real.rpow_mul hA₁pos.le (p - 2) (1 / p),
              hp1,
              show (2:ℝ) * (1 / p) = 2 / p by rw [mul_one_div],
              show (p - 2) * (1 / p) = 1 - 2 / p by rw [sub_mul, hp1, mul_one_div],
              Real.rpow_one]
          rw [hC] at hKroot ⊢
          calc (∑ x, (∑ i, ‖T i f x‖ ^ 2) ^ (p / 2)) ^ (1 / p)
              = (∑ x, ‖∑ i, u x i * T i f x‖ ^ p) ^ (1 / p) := hLHSid.symm
            _ ≤ (p * (2*A₀) ^ (2:ℝ) * (2*A₁) ^ (p - 2) / (p - 2)) ^ (1 / p)
                  * (∑ x, ‖f x‖ ^ p) ^ (1 / p) := hmain
            _ = (p * (2:ℝ) ^ p / (p - 2)) ^ (1 / p) * A₀ ^ (2 / p) * A₁ ^ (1 - 2 / p)
                  * (∑ x, ‖f x‖ ^ p) ^ (1 / p) := by rw [hKroot]
  · -- `p = 2`
    refine ⟨1, one_pos, ?_⟩
    intro T A₀ A₁ hA₀ hA₁ h₁ h₂ f
    have hp2 : p = 2 := hpeq.symm
    have hkey : ∀ x, (∑ i, ‖T i f x‖ ^ 2) ^ (p / 2) = ∑ i, ‖T i f x‖ ^ 2 := by
      intro x
      rw [hp2, show (2:ℝ) / 2 = 1 by norm_num, Real.rpow_one]
    have hkey2 : ∀ x, ‖f x‖ ^ p = ‖f x‖ ^ 2 := by
      intro x
      rw [hp2, Real.rpow_two]
    have hA1 : A₁ ^ (1 - 2 / p) = 1 := by
      rw [hp2, show (1:ℝ) - 2 / 2 = 0 by norm_num, Real.rpow_zero]
    have hA0 : A₀ ^ (2 / p) = A₀ := by
      rw [hp2, show (2:ℝ) / 2 = 1 by norm_num, Real.rpow_one]
    have hpp : 1 / p = (1:ℝ) / 2 := by rw [hp2]
    rw [hpp]
    simp only [hkey, hkey2, hA1, hA0, mul_one, one_mul]
    exact h₁ f


/-- The intended statement of `vector_valued_lp_interpolation` with the two hypotheses written
using `Real.sqrt` instead of the exponent `1 / 2`; this is the trap-free form (no exponent can be
silently re-elaborated at `ℕ`) and is the form recommended for downstream use. -/
theorem vector_valued_lp_interpolation_sqrt {α ι : Type*} [Fintype α] [Fintype ι]
    {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ι → (α → ℂ) →ₗ[ℂ] (α → ℂ)) (A₀ A₁ : ℝ), 0 ≤ A₀ → 0 ≤ A₁ →
      (∀ f : α → ℂ, Real.sqrt (∑ x, ∑ i, ‖T i f x‖ ^ 2)
        ≤ A₀ * Real.sqrt (∑ x, ‖f x‖ ^ 2)) →
      (∀ f : α → ℂ, (⨆ x, Real.sqrt (∑ i, ‖T i f x‖ ^ 2)) ≤ A₁ * (⨆ x, ‖f x‖)) →
      ∀ f : α → ℂ, (∑ x, (∑ i, ‖T i f x‖ ^ 2) ^ (p / 2)) ^ (1 / p)
        ≤ C * A₀ ^ (2 / p) * A₁ ^ (1 - 2 / p) * (∑ x, ‖f x‖ ^ p) ^ (1 / p) := by
  obtain ⟨C, hCpos, hC⟩ := vector_valued_lp_interpolation_rpow (α := α) (ι := ι) hp
  refine ⟨C, hCpos, ?_⟩
  intro T A₀ A₁ hA₀ hA₁ h₁ h₂ f
  refine hC T A₀ A₁ hA₀ hA₁ ?_ ?_ f
  · intro g
    have h := h₁ g
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow] at h
    exact h
  · intro g
    have h := h₂ g
    simp only [Real.sqrt_eq_rpow] at h
    exact h

end Work.BourgainPlan.IonescuWainger
