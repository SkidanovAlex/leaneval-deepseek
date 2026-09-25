import Submission.Work.BourgainPlan.Thm52.Defs

/-!
# KMSZ (5.4): the small-scale (Rademacher–Menshov + Marcinkiewicz–Zygmund) step

This file proves the *small-scale* half of KMSZ Theorem 5.2 in the corpus's `ℓᵖ(ℤ)` language.

The two analytic inputs are both already in the corpus:

* the **Rademacher–Menshov inequality** for the `ρ`-variation (condition (2) of KMSZ
  Definition 5.1), landed as `Work.BourgainPlan.Maximal.varELpNormLeRho`: the `Lᵖ` norm of the
  `ρ`-variation over the dyadic window `[0, 2^n]` is dominated by the sum of the `Lᵖ` norms of the
  `n+1` dyadic block square functions `rmLevel`;
* the **Marcinkiewicz–Zygmund theorem** (`Work.BourgainPlan.IonescuWainger.mz_square_function`,
  whose proof is Khintchine's inequality): a *uniform-in-signs* `ℓᵖ` bound for a family of linear
  operators controls the `Lᵖ` norm of the square function of their outputs.

Feeding the uniform-in-signs bound `SignedDiffBound` (which is what the Ionescu–Wainger multiplier
theorem supplies) into MZ at each of the `n+1` levels and summing gives KMSZ (5.4): the `2`-variation
over `[0, 2^n]` is bounded by `O(n+1)·A·‖f‖_{ℓᵖ}`, the `log N` of Theorem 5.2 being exactly the
number `n+1` of levels (KMSZ: "κ_N + 1 ≃ log N").
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.Thm52

noncomputable section

/-- The `ℝ≥0∞`-valued level square function is `ofReal` of the corpus's `ℝ`-valued `rmLevel`. -/
theorem levelSq_eq_rmLevel (n l : ℕ) (a : ℕ → ℤ → ℂ) (y : ℤ) :
    levelSq n l a y = ENNReal.ofReal (Work.BourgainPlan.Maximal.rmLevel n l (fun i => a i y)) := by
  rw [levelSq, Work.BourgainPlan.Maximal.rmLevel, Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg (fun m _ => by positivity))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← ofReal_norm, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
    ← ENNReal.ofReal_pow (norm_nonneg (a ((m + 1) * 2 ^ l) y - a (m * 2 ^ l) y)) 2]

/-- The difference of two linear maps on `ℤ → ℂ` (coefficientwise) is linear. -/
theorem isLinearMap_sub {R : Type*} {T : R → (ℤ → ℂ) → (ℤ → ℂ)} (a b : R)
    (h1 : IsLinearMap ℂ (T a)) (h2 : IsLinearMap ℂ (T b)) :
    IsLinearMap ℂ (fun g : ℤ → ℂ => fun y : ℤ => T a g y - T b g y) := by
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

/-- **The level square function is controlled by the uniform-in-signs bound** (the
Marcinkiewicz–Zygmund step, at one dyadic level). -/
theorem exists_levelSq_bound (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n l M : ℕ) (hM : M = 2 ^ (n - l))
      (T : ℕ → (ℤ → ℂ) → (ℤ → ℂ)) (hlin : ∀ i, IsLinearMap ℂ (T i))
      (hmeas : ∀ i (g : ℤ → ℂ), AEMeasurable (T i g) Measure.count)
      (A : ℝ) (hA : 0 ≤ A)
      (hT : ∀ (ω : Fin M → Bool) (g : ℤ → ℂ),
        ∫⁻ y : ℤ, ‖∑ m : Fin M, (if ω m then (1 : ℂ) else -1)
            * (T (((m : ℕ) + 1) * 2 ^ l) g y - T ((m : ℕ) * 2 ^ l) g y)‖ₑ ^ p ∂Measure.count
          ≤ ENNReal.ofReal (A ^ p) * lpPow p g)
      (f : ℤ → ℂ),
      (∫⁻ y : ℤ, (levelSq n l (fun i => T i f) y) ^ p ∂Measure.count)
        ≤ ENNReal.ofReal (C * A ^ p) * lpPow p f := by
  obtain ⟨Cmz, hCmzpos, hCmz⟩ :=
    IonescuWainger.mz_square_function (X := ℤ) (Y := ℤ) Measure.count Measure.count
      (p := p) hp
  refine ⟨Cmz, hCmzpos, ?_⟩
  intro n l M hM T hlin hmeas A hA hT f
  subst hM
  set T' : Fin (2 ^ (n - l)) → (ℤ → ℂ) → (ℤ → ℂ) := fun i g => fun y : ℤ =>
    T (((i : ℕ) + 1) * 2 ^ l) g y - T ((i : ℕ) * 2 ^ l) g y with hT'def
  have hlin' : ∀ i, IsLinearMap ℂ (T' i) := by
    intro i
    simp only [hT'def]
    exact isLinearMap_sub (((i : ℕ) + 1) * 2 ^ l) ((i : ℕ) * 2 ^ l)
      (hlin _) (hlin _)
  have hmeas' : ∀ (i : Fin (2 ^ (n - l))) (g : ℤ → ℂ), AEMeasurable (T' i g) Measure.count := by
    intro i g
    simp only [hT'def]
    exact (hmeas (((i : ℕ) + 1) * 2 ^ l) g).sub (hmeas ((i : ℕ) * 2 ^ l) g)
  have hT' : ∀ (ω : Fin (2 ^ (n - l)) → Bool) (g : ℤ → ℂ),
      ∫⁻ y : ℤ, ‖∑ m : Fin (2 ^ (n - l)), (if ω m then (1 : ℂ) else -1) * T' m g y‖ₑ ^ p
        ∂Measure.count
        ≤ ENNReal.ofReal (A ^ p) * lpPow p g := by
    intro ω g
    simpa only [hT'def] using hT ω g
  have key := hCmz T' hlin' hmeas' A hA hT' (fun _ : Unit => f)
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
  have hR : lpPow p f
      = ∫⁻ x : ℤ, (∑ _t : Unit, ‖(fun _ : Unit => f) _t x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
          ∂Measure.count := by
    rw [lpPow]
    refine lintegral_congr fun x => ?_
    rw [Fintype.sum_unique, ← ENNReal.rpow_mul, show (2 : ℝ) * (p / 2) = p by ring]
  rw [hL, hR]
  exact key

/-- **KMSZ (5.4)**, the small-scale half of the Rademacher–Menshov form of the
Ionescu–Wainger theorem: for a family `T` of linear operators on `ℓᵖ(ℤ)` whose lacunary differences
satisfy the uniform-in-signs bound `SignedDiffBound p T n A`, the `2`-variation of the family over
the dyadic window `[0, 2^n]` is bounded by `O(n+1)·A‖f‖`.

The `log N` of KMSZ Theorem 5.2 is the factor `n+1` — the number of dyadic levels. -/
theorem exists_small_scales_bound (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (T : ℕ → (ℤ → ℂ) → (ℤ → ℂ))
      (hlin : ∀ i, IsLinearMap ℂ (T i))
      (hmeas : ∀ i (g : ℤ → ℂ), AEMeasurable (T i g) Measure.count)
      (A : ℝ) (hA : 0 ≤ A) (hT : SignedDiffBound p T n A) (f : ℤ → ℂ),
      eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRho 2 0 (2 ^ n)
          (fun i => T i f y)) (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal (C * ((n : ℝ) + 1) * A) * lpNorm p f := by
  obtain ⟨Clev, hClevpos, hlev⟩ := exists_levelSq_bound p hp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  refine ⟨2 * Clev ^ (1 / p), by positivity, ?_⟩
  intro n T hlin hmeas A hA hT f
  have hrm : eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRho 2 0 (2 ^ n)
        (fun i => T i f y)) (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal 2 * ∑ l ∈ Finset.range (n + 1),
          eLpNorm (fun y : ℤ => ENNReal.ofReal
            (Work.BourgainPlan.Maximal.rmLevel n l (fun i => T i f y)))
            (ENNReal.ofReal p) Measure.count :=
    Work.BourgainPlan.Maximal.varELpNormLeRho (le_refl 2) Measure.count n hp
      (fun i => T i f) (fun i => hmeas i f)
  have hlinv : lpNorm p f = (lpPow p f) ^ (1 / p) := by
    rw [lpNorm, lpPow, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete]
    rw [ENNReal.toReal_ofReal hp0.le]
  have hlevel : ∀ l ∈ Finset.range (n + 1),
      eLpNorm (fun y : ℤ => ENNReal.ofReal
          (Work.BourgainPlan.Maximal.rmLevel n l (fun i => T i f y)))
          (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal (Clev ^ (1 / p) * A) * lpNorm p f := by
    intro l hl
    have hln : l ≤ n := by
      have := Finset.mem_range.mp hl; omega
    have hpow : (∫⁻ y : ℤ, (levelSq n l (fun i => T i f) y) ^ p ∂Measure.count)
        ≤ ENNReal.ofReal (Clev * A ^ p) * lpPow p f :=
      hlev n l (2 ^ (n - l)) rfl T hlin hmeas A hA
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
        ≤ (ENNReal.ofReal (Clev * A ^ p) * lpPow p f) ^ (1 / p) :=
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
  calc eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRho 2 0 (2 ^ n)
        (fun i => T i f y)) (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal 2 * ∑ l ∈ Finset.range (n + 1),
          eLpNorm (fun y : ℤ => ENNReal.ofReal
            (Work.BourgainPlan.Maximal.rmLevel n l (fun i => T i f y)))
            (ENNReal.ofReal p) Measure.count := hrm
    _ ≤ ENNReal.ofReal 2 * ∑ l ∈ Finset.range (n + 1),
          (ENNReal.ofReal (Clev ^ (1 / p) * A) * lpNorm p f) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlevel) (by positivity)
    _ = ENNReal.ofReal (2 * Clev ^ (1 / p) * ((n : ℝ) + 1) * A) * lpNorm p f := by
        have hnat : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) + 1) := by
          rw [← ENNReal.ofReal_natCast (n + 1), Nat.cast_add, Nat.cast_one]
        have harg : 2 * ((n : ℝ) + 1) * (Clev ^ (1 / p) * A)
            = 2 * Clev ^ (1 / p) * ((n : ℝ) + 1) * A := by ring
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hnat,
          ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * ((n:ℝ) + 1)),
          harg]

end

end Work.BourgainPlan.Thm52
