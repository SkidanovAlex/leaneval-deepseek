import Submission.Work.BourgainPlan.Thm52.Thm52
import Submission.Work.BourgainPlan.IonescuWainger.mz_square_function_finsupp
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear

/-!
# KMSZ Theorem 5.2 for operator families defined on finitely supported sequences

The concrete Ionescu–Wainger families of the corpus are *not* defined on all of `ℤ → ℂ`: the arc
multiplier `opArc φ hφ E` is a multiplier of `ℓ²(ℤ)` and, in `OpArcLinear.lean`, an honest
`ℂ`-linear map on the finitely supported sequences, `opArcLM φ hφ E : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)`
(the torsion-arc multipliers are not even defined on all of `ℤ → ℂ`, their kernels not being
absolutely summable).

This file therefore restates the small-scale step (KMSZ (5.4)) and Theorem 5.2 with the family
defined on `ℤ → ₀ ℂ`, using `Work.BourgainPlan.IonescuWainger.mz_square_function_finsupp` (the
Marcinkiewicz–Zygmund theorem on that domain).  Every input of
`Work.BourgainPlan.Maximal.KMSZMajorArcStatement` is finitely supported, so this is the form in
which the §6.3 application consumes the theorem.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.Thm52

open Work.BourgainPlan.Maximal (varRho varRhoAll varRhoFrom)

noncomputable section

/-- The difference of two linear maps from a module to `ℤ → ℂ` (coefficientwise) is linear. -/
theorem isLinearMap_sub_of_module {M : Type*} [AddCommGroup M] [Module ℂ M] {R : Type*}
    {T : R → M → (ℤ → ℂ)} (a b : R) (h1 : IsLinearMap ℂ (T a)) (h2 : IsLinearMap ℂ (T b)) :
    IsLinearMap ℂ (fun g : M => fun y : ℤ => T a g y - T b g y) := by
  refine ⟨?_, ?_⟩
  · intro g g'
    ext y
    have e1 : T a (g + g') y = T a g y + T a g' y := by
      have h := congr_fun (h1.map_add g g') y
      simpa using h
    have e2 : T b (g + g') y = T b g y + T b g' y := by
      have h := congr_fun (h2.map_add g g') y
      simpa using h
    rw [e1, e2, Pi.add_apply]
    ring
  · intro c g
    ext y
    have e1 : T a (c • g) y = c * T a g y := by
      have h := congr_fun (h1.map_smul c g) y
      simpa using h
    have e2 : T b (c • g) y = c * T b g y := by
      have h := congr_fun (h2.map_smul c g) y
      simpa using h
    rw [e1, e2, Pi.smul_apply, smul_eq_mul]
    ring

/-- **The uniform-in-signs bound for the lacunary differences**, with the family defined on
finitely supported sequences (the shape of the Ionescu–Wainger input for the concrete families). -/
def SignedDiffBoundF (p : ℝ) (T : ℕ → (ℤ →₀ ℂ) → (ℤ → ℂ)) (n : ℕ) (A : ℝ) : Prop :=
  ∀ (l : ℕ), l ≤ n → ∀ (ω : Fin (2 ^ (n - l)) → Bool) (f : ℤ →₀ ℂ),
    (∫⁻ y : ℤ, ‖∑ m : Fin (2 ^ (n - l)), (if ω m then (1 : ℂ) else -1)
        * (T (((m : ℕ) + 1) * 2 ^ l) f y - T ((m : ℕ) * 2 ^ l) f y)‖ₑ ^ p ∂Measure.count)
      ≤ ENNReal.ofReal (A ^ p) * lpPow p (⇑f)

/-- **The large-scale (sampling-principle) bound**, finitely supported inputs. -/
def LargeScaleBoundF (p : ℝ) (T : ℕ → (ℤ →₀ ℂ) → (ℤ → ℂ)) (κ : ℕ) (B : ℝ) : Prop :=
  ∀ f : ℤ →₀ ℂ,
    eLpNorm (fun y : ℤ => varRhoFrom 2 κ (fun n => T n f y)) (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal B * lpNorm p (⇑f)

/-- **The level square function is controlled by the uniform-in-signs bound** (KMSZ §5 Step 1,
finitely supported domain): Marcinkiewicz–Zygmund (`mz_square_function_finsupp`). -/
theorem exists_levelSq_bound_finsupp (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n l M : ℕ) (hM : M = 2 ^ (n - l))
      (T : ℕ → (ℤ →₀ ℂ) → (ℤ → ℂ)) (hlin : ∀ i, IsLinearMap ℂ (T i))
      (A : ℝ) (hA : 0 ≤ A)
      (hT : ∀ (ω : Fin M → Bool) (g : ℤ →₀ ℂ),
        ∫⁻ y : ℤ, ‖∑ m : Fin M, (if ω m then (1 : ℂ) else -1)
            * (T (((m : ℕ) + 1) * 2 ^ l) g y - T ((m : ℕ) * 2 ^ l) g y)‖ₑ ^ p ∂Measure.count
          ≤ ENNReal.ofReal (A ^ p) * lpPow p (⇑g))
      (f : ℤ →₀ ℂ),
      (∫⁻ y : ℤ, (levelSq n l (fun i => T i f) y) ^ p ∂Measure.count)
        ≤ ENNReal.ofReal (C * A ^ p) * lpPow p (⇑f) := by
  obtain ⟨Cmz, hCmzpos, hCmz⟩ :=
    IonescuWainger.mz_square_function_finsupp (p := p) hp
  refine ⟨Cmz, hCmzpos, ?_⟩
  intro n l M hM T hlin A hA hT f
  subst hM
  set T' : Fin (2 ^ (n - l)) → (ℤ →₀ ℂ) → (ℤ → ℂ) := fun i g => fun y : ℤ =>
    T (((i : ℕ) + 1) * 2 ^ l) g y - T ((i : ℕ) * 2 ^ l) g y with hT'def
  have hlin' : ∀ i, IsLinearMap ℂ (T' i) := by
    intro i
    simp only [hT'def]
    exact isLinearMap_sub_of_module (((i : ℕ) + 1) * 2 ^ l) ((i : ℕ) * 2 ^ l)
      (hlin (((i : ℕ) + 1) * 2 ^ l)) (hlin ((i : ℕ) * 2 ^ l))
  have hT' : ∀ (ω : Fin (2 ^ (n - l)) → Bool) (g : ℤ →₀ ℂ),
      ∫⁻ y : ℤ, ‖∑ m : Fin (2 ^ (n - l)), (if ω m then (1 : ℂ) else -1) * T' m g y‖ₑ ^ p
        ∂Measure.count
        ≤ ENNReal.ofReal (A ^ p) * lpPow p (⇑g) := by
    intro ω g
    simpa only [hT'def] using hT ω g
  have key := hCmz T' hlin'
    (fun i g => (measurable_of_countable (T' i g)).aemeasurable) A hA hT'
    (fun _ : Unit => f)
  have h1 : ∀ (i : Fin (2 ^ (n - l))) (y : ℤ),
      (∑ _t : Unit, ‖T' i ((fun _ : Unit => f) _t) y‖ₑ ^ (2 : ℝ))
        = ‖T (((i : ℕ) + 1) * 2 ^ l) f y - T ((i : ℕ) * 2 ^ l) f y‖ₑ ^ (2 : ℝ) := by
    intro i y
    rw [Fintype.sum_unique]
  have hsum : ∀ y : ℤ,
      (∑ i : Fin (2 ^ (n - l)), ∑ _t : Unit,
          ‖T' i ((fun _ : Unit => f) _t) y‖ₑ ^ (2 : ℝ))
        = (∑ m ∈ Finset.range (2 ^ (n - l)),
            ‖T ((m + 1) * 2 ^ l) f y - T (m * 2 ^ l) f y‖ₑ ^ (2 : ℝ)) := by
    intro y
    exact (Finset.sum_congr rfl fun i _ => h1 i y).trans
      (Fin.sum_univ_eq_sum_range
        (fun m => ‖T ((m + 1) * 2 ^ l) f y - T (m * 2 ^ l) f y‖ₑ ^ (2 : ℝ)) (2 ^ (n - l)))
  have hL : (∫⁻ y : ℤ, (levelSq n l (fun i => T i f) y) ^ p ∂Measure.count)
      = ∫⁻ y : ℤ, (∑ i : Fin (2 ^ (n - l)), ∑ _t : Unit,
          ‖T' i ((fun _ : Unit => f) _t) y‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂Measure.count := by
    refine lintegral_congr fun y => ?_
    rw [levelSq, ← hsum y, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hR : lpPow p (⇑f)
      = ∫⁻ x : ℤ, (∑ _t : Unit, ‖(⇑((fun _ : Unit => f) _t) : ℤ → ℂ) x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
          ∂Measure.count := by
    rw [lpPow]
    refine lintegral_congr fun x => ?_
    rw [Fintype.sum_unique, ← ENNReal.rpow_mul, show (2 : ℝ) * (p / 2) = p by ring]
  rw [hL, hR]
  exact key

/-- **KMSZ (5.4)**, finitely supported domain. -/
theorem exists_small_scales_bound_finsupp (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (T : ℕ → (ℤ →₀ ℂ) → (ℤ → ℂ))
      (hlin : ∀ i, IsLinearMap ℂ (T i))
      (A : ℝ) (hA : 0 ≤ A) (hT : SignedDiffBoundF p T n A) (f : ℤ →₀ ℂ),
      eLpNorm (fun y : ℤ => varRho 2 0 (2 ^ n) (fun i => T i f y))
          (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal (C * ((n : ℝ) + 1) * A) * lpNorm p (⇑f) := by
  obtain ⟨Clev, hClevpos, hlev⟩ := exists_levelSq_bound_finsupp p hp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  refine ⟨2 * Clev ^ (1 / p), by positivity, ?_⟩
  intro n T hlin A hA hT f
  have hrm : eLpNorm (fun y : ℤ => varRho 2 0 (2 ^ n) (fun i => T i f y))
        (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal 2 * ∑ l ∈ Finset.range (n + 1),
          eLpNorm (fun y : ℤ => ENNReal.ofReal
            (Work.BourgainPlan.Maximal.rmLevel n l (fun i => T i f y)))
            (ENNReal.ofReal p) Measure.count :=
    Work.BourgainPlan.Maximal.varELpNormLeRho (le_refl 2) Measure.count n hp
      (fun i => T i f) (fun i => (measurable_of_countable (T i f)).aemeasurable)
  have hlinv : lpNorm p (⇑f) = (lpPow p (⇑f)) ^ (1 / p) := by
    rw [lpNorm, lpPow, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete]
    rw [ENNReal.toReal_ofReal hp0.le]
  have hlevel : ∀ l ∈ Finset.range (n + 1),
      eLpNorm (fun y : ℤ => ENNReal.ofReal
          (Work.BourgainPlan.Maximal.rmLevel n l (fun i => T i f y)))
          (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal (Clev ^ (1 / p) * A) * lpNorm p (⇑f) := by
    intro l hl
    have hln : l ≤ n := by
      have := Finset.mem_range.mp hl; omega
    have hpow : (∫⁻ y : ℤ, (levelSq n l (fun i => T i f) y) ^ p ∂Measure.count)
        ≤ ENNReal.ofReal (Clev * A ^ p) * lpPow p (⇑f) :=
      hlev n l (2 ^ (n - l)) rfl T hlin A hA
        (fun ω g => (hT l hln) ω g) f
    have hen : eLpNorm (fun y : ℤ => ENNReal.ofReal
          (Work.BourgainPlan.Maximal.rmLevel n l (fun i => T i f y)))
          (ENNReal.ofReal p) Measure.count
        = (∫⁻ y : ℤ, (levelSq n l (fun i => T i f) y) ^ p ∂Measure.count) ^ (1 / p) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete,
        ENNReal.toReal_ofReal hp0.le]
      congr 1
      refine lintegral_congr fun y => ?_
      rw [enorm_eq_self, levelSq_eq_rmLevel]
    rw [hen]
    have hstep : (∫⁻ y : ℤ, (levelSq n l (fun i => T i f) y) ^ p ∂Measure.count) ^ (1 / p)
        ≤ (ENNReal.ofReal (Clev * A ^ p) * lpPow p (⇑f)) ^ (1 / p) :=
      ENNReal.rpow_le_rpow hpow (by positivity)
    refine hstep.trans ?_
    rw [hlinv, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    have hfac : (ENNReal.ofReal (Clev * A ^ p)) ^ (1 / p)
        = ENNReal.ofReal (Clev ^ (1 / p) * A) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      congr 1
      calc (Clev * A ^ p) ^ (1 / p)
          = Clev ^ (1 / p) * (A ^ p) ^ (1 / p) :=
            Real.mul_rpow (by positivity) (by positivity)
        _ = Clev ^ (1 / p) * A ^ (p * (1 / p)) := by
            rw [Real.rpow_mul hA p (1 / p)]
        _ = Clev ^ (1 / p) * A := by
            rw [show p * (1 / p) = 1 by field_simp, Real.rpow_one]
    rw [hfac]
  calc eLpNorm (fun y : ℤ => varRho 2 0 (2 ^ n) (fun i => T i f y))
        (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal 2 * ∑ l ∈ Finset.range (n + 1),
          eLpNorm (fun y : ℤ => ENNReal.ofReal
            (Work.BourgainPlan.Maximal.rmLevel n l (fun i => T i f y)))
            (ENNReal.ofReal p) Measure.count := hrm
    _ ≤ ENNReal.ofReal 2 * ∑ l ∈ Finset.range (n + 1),
          (ENNReal.ofReal (Clev ^ (1 / p) * A) * lpNorm p (⇑f)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlevel) (by positivity)
    _ = ENNReal.ofReal (2 * Clev ^ (1 / p) * ((n : ℝ) + 1) * A) * lpNorm p (⇑f) := by
        have hnat : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) + 1) := by
          rw [← ENNReal.ofReal_natCast (n + 1), Nat.cast_add, Nat.cast_one]
        have harg : 2 * ((n : ℝ) + 1) * (Clev ^ (1 / p) * A)
            = 2 * Clev ^ (1 / p) * ((n : ℝ) + 1) * A := by ring
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hnat,
          ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * ((n:ℝ) + 1)),
          harg]

/-- **KMSZ Theorem 5.2**, finitely supported domain: the form in which the §6.3 application
consumes it (all inputs of `KMSZMajorArcStatement` are finitely supported). -/
theorem exists_thm52_finsupp (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : ℕ) (T : ℕ → (ℤ →₀ ℂ) → (ℤ → ℂ))
      (hlin : ∀ i, IsLinearMap ℂ (T i))
      (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
      (hsmall : SignedDiffBoundF p T κ A)
      (hlarge : LargeScaleBoundF p T (2 ^ κ) B) (f : ℤ →₀ ℂ),
      eLpNorm (fun y : ℤ => varRhoAll 2 (fun i => T i f y)) (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal (C * ((κ : ℝ) + 1) * A + B) * lpNorm p (⇑f) := by
  obtain ⟨C₁, hC₁pos, hsmall'⟩ := exists_small_scales_bound_finsupp p hp
  refine ⟨C₁, hC₁pos, ?_⟩
  intro κ T hlin A B hA hB hsmall hlarge f
  have hsplit : eLpNorm (fun y : ℤ => varRhoAll 2 (fun i => T i f y))
        (ENNReal.ofReal p) Measure.count
      ≤ eLpNorm (fun y : ℤ => varRho 2 0 (2 ^ κ) (fun i => T i f y))
          (ENNReal.ofReal p) Measure.count
        + eLpNorm (fun y : ℤ => varRhoFrom 2 (2 ^ κ) (fun i => T i f y))
          (ENNReal.ofReal p) Measure.count :=
    (eLpNorm_mono_enorm AEStronglyMeasurable.of_discrete fun y => varRhoAll_le (by norm_num : (1:ℝ) ≤ 2) (2 ^ κ)
        (fun i => T i f y)).trans
      (eLpNorm_add_le_count p hp _ _)
  calc eLpNorm (fun y : ℤ => varRhoAll 2 (fun i => T i f y)) (ENNReal.ofReal p) Measure.count
      ≤ _ + _ := hsplit
    _ ≤ ENNReal.ofReal (C₁ * ((κ : ℝ) + 1) * A) * lpNorm p (⇑f)
          + ENNReal.ofReal B * lpNorm p (⇑f) :=
        add_le_add (hsmall' κ T hlin A hA hsmall f) (hlarge f)
    _ = ENNReal.ofReal (C₁ * ((κ : ℝ) + 1) * A + B) * lpNorm p (⇑f) := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) hB]

end

end Work.BourgainPlan.Thm52
