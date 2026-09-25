import Mathlib
import Submission.Work.BourgainPlan.Maximal.canonical_arcs
import Submission.Work.BourgainPlan.Maximal.absMaxSumLpContraction
import Submission.Work.BourgainPlan.Maximal.dressing

/-!
# KMSZ (6.12): the minor-arc `ℓᵖ` bound for the density averages

Source: Kosz–Mirek–Słomian–Zhang, arXiv:2606.12663, §6.2.  With the `ℤ`-average

`A_N f (m) = N⁻¹ Σ_{i<N} f (m + P (i))`

and the dyadic Ionescu–Wainger projection `Π = Π_{≤l,≤m}` (a multiplier with symbol
`Σ_{σ ∈ R_{≤2^l}} η_{≤m}(· - σ)`, i.e. `opArc φ hφ (canonicalFinset (2^l))` for a bump `φ` of scale
`2^{m-1}`), the decomposition `A_N f = A_N Π f + A_N (f - Π f)` gives

`‖A_N (f - Π_{≤l,≤m} f)‖_{ℓᵖ} ≲_p 2^{C_p γ l} ‖f‖_{ℓᵖ}`,

which for the parameters `l = l(N) = α Log N` (`α` small) is KMSZ **(6.12)**,
`‖A_N (f - Π_{≤l(N),≤-dL(N)} f)‖_{ℓ^{p₀}} ≲_γ N^γ ‖f‖_{ℓ^{p₀}}`.

Everything here is an *operator-norm* argument (no symbol product is needed): the `ℓᵖ` contraction
of the single average `A_N` (a convex combination of shifts, `‖A_N‖_{ℓᵖ → ℓᵖ} ≤ 1`), the `ℓᵖ` bound
for `Π` (the analytic input `IWProjectionBound` = KMSZ (6.11)), and the triangle inequality
`‖A_N (1 - Π)‖ ≤ 1 + ‖Π‖ ≤ 1 + 2^{C_p γ l}`.
-/

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- The **`ℤ`-average** `A_N f (m) = N⁻¹ Σ_{i<N} f (m + P (i))` with complex values (the
`ℂ`-valued companion of `discAvgZ`). -/
def discAvgZC (P : Polynomial ℤ) (N : ℕ) (g : ℤ → ℂ) (m : ℤ) : ℂ :=
  ((N : ℂ)⁻¹) * ∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))

/-- The `ℤ`-average is additive. -/
lemma discAvgZC_sub (P : Polynomial ℤ) (N : ℕ) (g h : ℤ → ℂ) :
    discAvgZC P N (g - h) = discAvgZC P N g - discAvgZC P N h := by
  funext m
  simp only [discAvgZC, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]

/-- **The `ℓ^q` contraction of the `ℤ`-average** `A_N`: a convex combination of shifts of `g`, hence
`‖A_N g‖_{ℓ^q} ≤ ‖g‖_{ℓ^q}` for every `q ≥ 1`. -/
theorem discAvgZC_contraction (P : Polynomial ℤ) (N : ℕ) {q : ℝ} (hq : 1 ≤ q)
    (g : ℤ → ℂ) :
    ∫⁻ m : ℤ, ‖discAvgZC P N g m‖ₑ ^ q ∂MeasureTheory.Measure.count
      ≤ ∫⁻ m : ℤ, ‖g m‖ₑ ^ q ∂MeasureTheory.Measure.count := by
  classical
  set w : ℝ≥0∞ := ENNReal.ofReal ((N : ℝ)⁻¹) with hw
  have hwsum : (∑ i ∈ Finset.range N, w) ≤ 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hw]
    rcases eq_or_ne N 0 with hN | hN
    · rw [hN]; simp
    · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (N:ℝ))]
      rw [mul_inv_cancel₀ (ne_of_gt hNpos)]
      simp
  -- the pointwise bound
  have hpt : ∀ m : ℤ, ‖discAvgZC P N g m‖ₑ
      ≤ ∑ i ∈ Finset.range N, w * ‖g (m + P.eval (i : ℤ))‖ₑ := by
    intro m
    have h1 : discAvgZC P N g m
        = ((N : ℂ)⁻¹) * ∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ)) := rfl
    rw [h1, enorm_mul]
    have h2 : ‖((N : ℂ)⁻¹)‖ₑ = w := by
      rw [hw, ← ofReal_norm, norm_inv, Complex.norm_natCast]
    rw [h2]
    calc w * ‖∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))‖ₑ
        ≤ w * ∑ i ∈ Finset.range N, ‖g (m + P.eval (i : ℤ))‖ₑ :=
          mul_le_mul_right (enorm_sum_le _ _) w
      _ = ∑ i ∈ Finset.range N, w * ‖g (m + P.eval (i : ℤ))‖ₑ := Finset.mul_sum ..
  calc ∫⁻ m : ℤ, ‖discAvgZC P N g m‖ₑ ^ q ∂MeasureTheory.Measure.count
      ≤ ∫⁻ m : ℤ, (∑ i ∈ Finset.range N, w * ‖g (m + P.eval (i : ℤ))‖ₑ) ^ q
          ∂MeasureTheory.Measure.count :=
        lintegral_mono fun m => ENNReal.rpow_le_rpow (hpt m) (by linarith)
    _ ≤ ∫⁻ m : ℤ, (∑ i ∈ Finset.range N,
            w * ‖g (m + P.eval (i : ℤ))‖ₑ ^ q) ∂MeasureTheory.Measure.count :=
        lintegral_mono fun m =>
          rpow_sum_mul_le_sum_mul_rpow _ _ _ hwsum hq
    _ = ∑ i ∈ Finset.range N,
          w * ∫⁻ m : ℤ, ‖g (m + P.eval (i : ℤ))‖ₑ ^ q ∂MeasureTheory.Measure.count := by
        rw [show (∫⁻ m : ℤ, (∑ i ∈ Finset.range N,
              w * ‖g (m + P.eval (i : ℤ))‖ₑ ^ q) ∂MeasureTheory.Measure.count)
            = ∑ i ∈ Finset.range N,
                ∫⁻ m : ℤ, w * ‖g (m + P.eval (i : ℤ))‖ₑ ^ q
                  ∂MeasureTheory.Measure.count
            from lintegral_finsetSum _ (fun i _ => by measurability)]
        exact Finset.sum_congr rfl fun i _ =>
          lintegral_const_mul w (f := fun m : ℤ => ‖g (m + P.eval (i : ℤ))‖ₑ ^ q)
            (by measurability)
    _ = ∑ i ∈ Finset.range N,
          w * ∫⁻ m : ℤ, ‖g m‖ₑ ^ q ∂MeasureTheory.Measure.count := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_count_add_right (fun m : ℤ => ‖g m‖ₑ ^ q) (P.eval (i : ℤ))]
    _ = (∑ i ∈ Finset.range N, w) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ q ∂MeasureTheory.Measure.count := by
        rw [Finset.sum_mul]
    _ ≤ 1 * ∫⁻ m : ℤ, ‖g m‖ₑ ^ q ∂MeasureTheory.Measure.count :=
        mul_le_mul_left hwsum _
    _ = ∫⁻ m : ℤ, ‖g m‖ₑ ^ q ∂MeasureTheory.Measure.count := one_mul _

/-! ## The minor-arc bound -/



end

end Work.BourgainPlan.Maximal
