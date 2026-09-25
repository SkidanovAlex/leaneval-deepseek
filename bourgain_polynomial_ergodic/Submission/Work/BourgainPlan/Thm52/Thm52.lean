import Submission.Work.BourgainPlan.Thm52.Small
import Submission.Work.BourgainPlan.Maximal.varRho_tail_glue

/-!
# KMSZ Theorem 5.2: the Rademacher–Menshov (seminorm) form of the Ionescu–Wainger theorem

This file assembles the small-scale half (`exists_small_scales_bound`, the Rademacher–Menshov +
Marcinkiewicz–Zygmund step, KMSZ (5.4)) with the splitting property (condition (1) of KMSZ
Definition 5.1, landed as `varRhoSplitting`) and the large-scale input (KMSZ Definition 5.1(3) plus
the factorisation (6.22), packaged as `LargeScaleBound`), obtaining KMSZ **Theorem 5.2**:

for a family `T` of linear operators on `ℓᵖ(ℤ)` whose **lacunary differences** satisfy the
uniform-in-signs bound `SignedDiffBound p T κ A` (this is where the Ionescu–Wainger multiplier
theorem, KMSZ Theorem 1.9, enters, with `A = A_{2r}` of (6.21)) and whose **tail** from the
threshold `2^κ` on satisfies the sampling bound `LargeScaleBound p T (2^κ) B` (this is where the
sampling principle and the factorisation (6.22) enter, with `B = B_p` of (6.21)), the `2`-variation
of the family over the whole index range is bounded on `ℓᵖ(ℤ)` by

  `C·(C₂·A·(κ+1) + B)`,

i.e. `C₁(C₂ A_{2r} log N + C₃ B_p)` of KMSZ Theorem 5.2 (with `κ + 1 ≍ log N`).
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.BourgainPlan.Thm52

open Work.BourgainPlan.Maximal (varRho varRhoAll varRhoFrom)

noncomputable section

/-- **Splitting `varRhoAll` at a threshold** (the variable-index form of KMSZ Definition 5.1(1)):
the `ρ`-variation over the whole index range is at most the variation over the initial window
`[0, K]` plus the variation over the tail `[K, ∞)`. -/
theorem varRhoAll_le {ρ : ℝ} (hρ : 1 ≤ ρ) (K : ℕ) (a : ℕ → ℂ) :
    varRhoAll ρ a ≤ varRho ρ 0 K a + varRhoFrom ρ K a := by
  rw [varRhoAll]
  refine iSup_le fun hi => ?_
  have h1 : varRho ρ 0 hi a ≤ varRho ρ 0 (max hi K) a :=
    Work.BourgainPlan.Maximal.varRho_le_varRho_of_le_hi ρ (le_max_left hi K) a
  have h2 : varRho ρ 0 (max hi K) a ≤ varRho ρ 0 K a + varRho ρ K (max hi K) a :=
    Work.BourgainPlan.Maximal.varRhoSplitting hρ (Nat.zero_le K) (le_max_right hi K) a
  have h3 : varRho ρ K (max hi K) a ≤ varRhoFrom ρ K a :=
    le_iSup (fun hh : ℕ => varRho ρ K hh a) (max hi K)
  calc varRho ρ 0 hi a ≤ varRho ρ 0 (max hi K) a := h1
    _ ≤ varRho ρ 0 K a + varRho ρ K (max hi K) a := h2
    _ ≤ varRho ρ 0 K a + varRhoFrom ρ K a := add_le_add le_rfl h3

/-- The `eLpNorm` of an `ℝ≥0∞`-valued function on `ℤ` is its `Lᵖ` "norm". -/
theorem eLpNorm_ennreal_eq (p : ℝ) (hp : 0 < p) (F : ℤ → ℝ≥0∞) :
    eLpNorm F (ENNReal.ofReal p) Measure.count
      = (∫⁻ y : ℤ, F y ^ p ∂Measure.count) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete,
    ENNReal.toReal_ofReal hp.le]
  exact congrArg (fun z => z ^ (1 / p)) (lintegral_congr fun y => by rw [enorm_eq_self])

/-- **Minkowski's inequality for `ℝ≥0∞`-valued functions on `ℤ`** (two terms). -/
theorem eLpNorm_add_le_count (p : ℝ) (hp : 1 ≤ p) (F G : ℤ → ℝ≥0∞) :
    eLpNorm (fun y : ℤ => F y + G y) (ENNReal.ofReal p) Measure.count
      ≤ eLpNorm F (ENNReal.ofReal p) Measure.count
        + eLpNorm G (ENNReal.ofReal p) Measure.count := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hle := ENNReal.lintegral_Lp_add_le (μ := Measure.count)
    (measurable_of_countable F).aemeasurable (measurable_of_countable G).aemeasurable hp
  rw [eLpNorm_ennreal_eq p hp0 F, eLpNorm_ennreal_eq p hp0 G,
    eLpNorm_ennreal_eq p hp0 (fun y : ℤ => F y + G y)]
  exact hle

/-- **KMSZ Theorem 5.2** (the Rademacher–Menshov form of the Ionescu–Wainger multiplier theorem),
in the corpus's `ℓᵖ(ℤ)` language.

Given a family `T` of linear operators on `ℓᵖ(ℤ)` whose lacunary differences
`T ((m+1)2^l) − T (m 2^l)` satisfy the uniform-in-signs bound `SignedDiffBound p T κ A` (the shape
in which the Ionescu–Wainger theorem supplies them, with `A = A_{2r}`), and whose tail from `2^κ` on
satisfies the sampling bound `LargeScaleBound p T (2^κ) B` (`B = B_p`), the `2`-variation of the
family is bounded on `ℓᵖ(ℤ)` by `C·(A·(κ+1) + B)` — KMSZ's `C₁(C₂A_{2r} log N + C₃B_p)`. -/
theorem exists_thm52 (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : ℕ) (T : ℕ → (ℤ → ℂ) → (ℤ → ℂ))
      (hlin : ∀ i, IsLinearMap ℂ (T i))
      (hmeas : ∀ i (g : ℤ → ℂ), AEMeasurable (T i g) Measure.count)
      (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
      (hsmall : SignedDiffBound p T κ A)
      (hlarge : LargeScaleBound p T (2 ^ κ) B) (f : ℤ → ℂ),
      eLpNorm (fun y : ℤ => varRhoAll 2 (fun i => T i f y)) (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal (C * ((κ : ℝ) + 1) * A + B) * lpNorm p f := by
  obtain ⟨C₁, hC₁pos, hsmall'⟩ := exists_small_scales_bound p hp
  refine ⟨C₁, hC₁pos, ?_⟩
  intro κ T hlin hmeas A B hA hB hsmall hlarge f
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
    _ ≤ ENNReal.ofReal (C₁ * ((κ : ℝ) + 1) * A) * lpNorm p f + ENNReal.ofReal B * lpNorm p f :=
        add_le_add (hsmall' κ T hlin hmeas A hA hsmall f) (hlarge f)
    _ = ENNReal.ofReal (C₁ * ((κ : ℝ) + 1) * A + B) * lpNorm p f := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) hB]

end

end Work.BourgainPlan.Thm52
