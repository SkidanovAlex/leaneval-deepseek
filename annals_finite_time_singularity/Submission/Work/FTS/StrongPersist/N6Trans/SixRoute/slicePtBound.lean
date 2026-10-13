import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

set_option maxHeartbeats 1000000

/-! ## Elementary `rpow` and `sin` facts on `(0, π/2)` -/

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma spb_rpow_sq (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

/-- `sin (2x) ≥ 0` on `(0, π/2)`. -/
private lemma spb_sin_nonneg {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Real.sin (2 * x) := by
  refine Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) ?_
  linarith [hx.2, Real.pi_pos]

/-- `sin (2x) > 0` on a subinterval `(a,b) ⊆ (0, π/2)`. -/
private lemma spb_sin_pos {a b x : ℝ} (hx : x ∈ Set.Ioo a b) (ha : 0 < a)
    (hb : b < Real.pi / 2) : 0 < Real.sin (2 * x) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1, ha]) (by linarith [hx.2, hb, Real.pi_pos])

/-! ## The Cauchy–Schwarz step on a subinterval of `(0, π/2)` -/

/-- **Weighted Cauchy–Schwarz on a subinterval.**  For `a ≤ b` with `(a,b) ⊆ (0,π/2)`,
`(∫_a^b |f'|)² ≤ (∫_{(0,π/2)} (f')² sin(2θ)^{1-β}) · (∫_{(0,π/2)} sin(2θ)^{β-1})`,
as long as the two whole-interval integrals are finite.

Route: split `|f'| = (|f'| sin^{(1-β)/2}) · sin^{(β-1)/2}` and apply Cauchy–Schwarz
(`Work.Spaces.cs_integral`) on the subinterval `(a,b)`, then bound the two subinterval
integrals by the whole ones with `setIntegral_mono_set`. -/
private lemma cs_subinterval {β : ℝ} {f : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) (Set.Ioo 0 (Real.pi / 2)))
    (hintB : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (β - 1)) (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (_hab : a ≤ b) (ha : 0 < a) (hb : b < Real.pi / 2) :
    (∫ x in Set.Ioo a b, |deriv f x|) ^ 2 ≤
      (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β)) *
        (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (β - 1)) := by
  have hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩
  have hsub_ae : Set.Ioo a b ≤ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Filter.Eventually.of_forall fun x hx => hsub hx
  have hsinpos : ∀ x ∈ Set.Ioo a b, 0 < Real.sin (2 * x) :=
    fun x hx => spb_sin_pos hx ha hb
  have hsinfull : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ Real.sin (2 * x) :=
    fun x hx => spb_sin_nonneg hx
  have hIntF : MeasureTheory.IntegrableOn
      (fun x => (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β)) (Set.Ioo a b) :=
    hint.mono_set hsub
  have hIntS : MeasureTheory.IntegrableOn
      (fun x => (Real.sin (2 * x)) ^ (β - 1)) (Set.Ioo a b) := hintB.mono_set hsub
  have hmu : Measurable (fun x : ℝ => |deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2)) := by
    measurability
  have hmv : Measurable (fun x : ℝ => (Real.sin (2 * x)) ^ ((β - 1) / 2)) := by measurability
  have hu2 : MeasureTheory.IntegrableOn
      (fun x => (|deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2)) ^ 2) (Set.Ioo a b) := by
    refine hIntF.congr_fun ?_ measurableSet_Ioo
    intro x hx
    dsimp only
    rw [mul_pow, sq_abs, spb_rpow_sq _ _ (hsinpos x hx),
      show 2 * ((1 - β) / 2) = 1 - β by ring]
  have hv2 : MeasureTheory.IntegrableOn
      (fun x => ((Real.sin (2 * x)) ^ ((β - 1) / 2)) ^ 2) (Set.Ioo a b) := by
    refine hIntS.congr_fun ?_ measurableSet_Ioo
    intro x hx
    dsimp only
    rw [spb_rpow_sq _ _ (hsinpos x hx), show 2 * ((β - 1) / 2) = β - 1 by ring]
  have hu_mem : MeasureTheory.MemLp
      (fun x => |deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioo a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hmu.aestronglyMeasurable).2 hu2
  have hv_mem : MeasureTheory.MemLp
      (fun x => (Real.sin (2 * x)) ^ ((β - 1) / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioo a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hmv.aestronglyMeasurable).2 hv2
  have hcs := Work.Spaces.cs_integral hu_mem hv_mem
  have e1 : (∫ x in Set.Ioo a b,
        (|deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2))
          * ((Real.sin (2 * x)) ^ ((β - 1) / 2)))
      = ∫ x in Set.Ioo a b, |deriv f x| := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_assoc, ← Real.rpow_add (hsinpos x hx),
      show (1 - β) / 2 + (β - 1) / 2 = 0 by ring, Real.rpow_zero, mul_one]
  have e2 : (∫ x in Set.Ioo a b,
        (|deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2)) ^ 2)
      = ∫ x in Set.Ioo a b, (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_pow, sq_abs, spb_rpow_sq _ _ (hsinpos x hx),
      show 2 * ((1 - β) / 2) = 1 - β by ring]
  have e3 : (∫ x in Set.Ioo a b, ((Real.sin (2 * x)) ^ ((β - 1) / 2)) ^ 2)
      = ∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (β - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [spb_rpow_sq _ _ (hsinpos x hx), show 2 * ((β - 1) / 2) = β - 1 by ring]
  have key : (∫ x in Set.Ioo a b, |deriv f x|) ^ 2 ≤
      (∫ x in Set.Ioo a b, (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β))
        * (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (β - 1)) := by
    calc (∫ x in Set.Ioo a b, |deriv f x|) ^ 2
        = (∫ x in Set.Ioo a b,
            (|deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2))
              * ((Real.sin (2 * x)) ^ ((β - 1) / 2))) ^ 2 := by rw [e1]
      _ ≤ (∫ x in Set.Ioo a b, (|deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2)) ^ 2)
            * (∫ x in Set.Ioo a b, ((Real.sin (2 * x)) ^ ((β - 1) / 2)) ^ 2) := hcs
      _ = (∫ x in Set.Ioo a b, (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β))
            * (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (β - 1)) := by rw [e2, e3]
  have hFnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun x => (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β)) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinfull x hx) _))
  have hSnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun x => (Real.sin (2 * x)) ^ (β - 1)) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall fun x hx => Real.rpow_nonneg (hsinfull x hx) _)
  have hA : (∫ x in Set.Ioo a b, (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β))
      ≤ ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β) :=
    MeasureTheory.setIntegral_mono_set hint hFnn hsub_ae
  have hB : (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (β - 1))
      ≤ ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (β - 1) :=
    MeasureTheory.setIntegral_mono_set hintB hSnn hsub_ae
  have hA0 : 0 ≤ ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinfull x hx) _))
  have hB0 : 0 ≤ ∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (β - 1) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => Real.rpow_nonneg (le_of_lt (hsinpos x hx)) _)
  exact key.trans (mul_le_mul hA hB hB0 hA0)

/-! ## The fundamental theorem step -/

/-- **The fundamental theorem of calculus on a subinterval.**  For `a ≤ b` in `(0, π/2)` and `f`
of class `C¹` on `(0, π/2)`, `|f a - f b| ≤ ∫_a^b |f'|`. -/
private lemma ftc_bound {f : ℝ → ℝ} (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b < Real.pi / 2) :
    |f a - f b| ≤ ∫ x in Set.Ioo a b, |deriv f x| := by
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hFTC : ∫ x in a..b, deriv f x = f b - f a :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc (hsm.mono hsub) hab
  calc |f a - f b| = |f b - f a| := abs_sub_comm _ _
    _ = |∫ x in a..b, deriv f x| := by rw [hFTC]
    _ ≤ ∫ x in a..b, |deriv f x| := intervalIntegral.abs_integral_le_integral_abs hab
    _ = ∫ x in Set.Ioo a b, |deriv f x| := by
        rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **The pointwise difference bound for a `C¹` function on `(0,π/2)`, with the critical
`sin(2θ)^{β-1}` weight.**  For `0 < β ≤ 1` and `f` of class `C¹` on the open interval whose
`sin(2·)^{1-β}`-weighted squared derivative and whose weight `sin(2·)^{β-1}` are both integrable
on `(0,π/2)`:

`f(θ)² ≤ 2 f(π/4)² + 2 · (∫_0^{π/2} f'(t)² sin(2t)^{1-β} dt) · (∫_0^{π/2} sin(2t)^{β-1} dt)`
for every `θ ∈ (0,π/2)`.

Route: the fundamental theorem `f(π/4) - f(θ) = ∫_θ^{π/4} f'` (the interval `[θ,π/4]` lies inside
the open interval where `f` is `C¹`), then `|f(θ)| ≤ |f(π/4)| + ∫_θ^{π/4}|f'|`, then
Cauchy–Schwarz (`Work.Spaces.cs_integral`) applied to `u = sin(2·)^{(1-β)/2} f'` and
`v = sin(2·)^{(β-1)/2}` (whose product is `|f'|`) on the interval `(θ,π/4)`, where the two
subinterval integrals are bounded by the corresponding integrals over the whole `(0,π/2)`
(monotonicity of the integral of a nonnegative integrable function).
The two integrability hypotheses are the exact certificates this needs; `hintB` is not implied by
`hint` (both hold for every `β ∈ (0,1]`, but proving that is a separate `rpow`-integral
computation). -/
theorem slicePtBound {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) (Set.Ioo 0 (Real.pi / 2)))
    (hintB : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (β - 1)) (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (f θ) ^ 2 ≤ 2 * (f (Real.pi / 4)) ^ 2
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin (2 * θ)) ^ (β - 1)) := by
  have _ := hβ
  have _ := hβ1
  intro θ hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hπ4pos : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  set A : ℝ := ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β) with hA
  set B : ℝ := ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (β - 1) with hB
  rcases le_total θ (Real.pi / 4) with hle | hle
  · -- `θ ≤ π/4`: integrate over `(θ, π/4)`
    have hbnd := ftc_bound hsm hle hθ0 hπ4lt
    have haux : |f θ| ≤ |f (Real.pi / 4)| + ∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x| := by
      have h1 : |f θ| ≤ |f (Real.pi / 4)| + |f θ - f (Real.pi / 4)| := by
        calc |f θ| = |f (Real.pi / 4) + (f θ - f (Real.pi / 4))| := by
              rw [show f (Real.pi / 4) + (f θ - f (Real.pi / 4)) = f θ by ring]
          _ ≤ _ := abs_add_le _ _
      linarith [hbnd]
    have hI2 : (∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x|) ^ 2 ≤ A * B := by
      rw [hA, hB]
      exact cs_subinterval hint hintB hle hθ0 hπ4lt
    calc f θ ^ 2 = (|f θ|) ^ 2 := (sq_abs _).symm
      _ ≤ (|f (Real.pi / 4)| + ∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) haux 2
      _ ≤ 2 * (|f (Real.pi / 4)|) ^ 2
            + 2 * (∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x|) ^ 2 := by
            nlinarith [sq_nonneg (|f (Real.pi / 4)| - ∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x|)]
      _ = 2 * (f (Real.pi / 4)) ^ 2
            + 2 * (∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x|) ^ 2 := by rw [sq_abs]
      _ ≤ 2 * (f (Real.pi / 4)) ^ 2 + 2 * (A * B) := by linarith [hI2]
      _ = 2 * (f (Real.pi / 4)) ^ 2
            + 2 * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
                    (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β))
                * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
                    (Real.sin (2 * x)) ^ (β - 1)) := by rw [hA, hB]; ring
  · -- `π/4 ≤ θ`: integrate over `(π/4, θ)`
    have hbnd := ftc_bound hsm hle hπ4pos hθ1
    rw [abs_sub_comm] at hbnd
    have haux : |f θ| ≤ |f (Real.pi / 4)| + ∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x| := by
      have h1 : |f θ| ≤ |f (Real.pi / 4)| + |f θ - f (Real.pi / 4)| := by
        calc |f θ| = |f (Real.pi / 4) + (f θ - f (Real.pi / 4))| := by
              rw [show f (Real.pi / 4) + (f θ - f (Real.pi / 4)) = f θ by ring]
          _ ≤ _ := abs_add_le _ _
      linarith [hbnd]
    have hI2 : (∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x|) ^ 2 ≤ A * B := by
      rw [hA, hB]
      exact cs_subinterval hint hintB hle hπ4pos hθ1
    calc f θ ^ 2 = (|f θ|) ^ 2 := (sq_abs _).symm
      _ ≤ (|f (Real.pi / 4)| + ∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) haux 2
      _ ≤ 2 * (|f (Real.pi / 4)|) ^ 2
            + 2 * (∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x|) ^ 2 := by
            nlinarith [sq_nonneg (|f (Real.pi / 4)| - ∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x|)]
      _ = 2 * (f (Real.pi / 4)) ^ 2
            + 2 * (∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x|) ^ 2 := by rw [sq_abs]
      _ ≤ 2 * (f (Real.pi / 4)) ^ 2 + 2 * (A * B) := by linarith [hI2]
      _ = 2 * (f (Real.pi / 4)) ^ 2
            + 2 * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
                    (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β))
                * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
                    (Real.sin (2 * x)) ^ (β - 1)) := by rw [hA, hB]; ring

end Work.FTS.StrongPersist.N6Trans.SixRoute
