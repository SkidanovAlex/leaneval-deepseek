/-
Copyright: work module for the Elgindi finite-time singularity project.

# A sup bound from the two weighted `L²` integrals

`Work.FTS.H2.ModalSolR.supBoundOfIntegrals`: for `0 < c < d < π/2` there is `K > 0`
such that every `v : ℝ → ℝ` of class `C¹` on `[0, π/2]`, whose weighted `L²` norms
`∫_{Iθ} v² cos θ` and `∫_{Iθ} (v')² cos θ` are finite, satisfies

`|v θ| ≤ K · √(∫_{Iθ} v² cos θ + ∫_{Iθ} (v')² cos θ)`  for every `θ ∈ [c, d]`.

The proof is the one-dimensional Sobolev bound `abs_le_of_l2_Icc` (sup on `[c,d]` bounded by
the `L²`-norm of `v` and of `deriv v` on `[c,d]`) combined with the comparison of the two
`[c,d]`-integrals with the `cos`-weighted integrals over `Iθ`: on `[c,d] ⊆ Iθ` the weight
`cos` is bounded below by `cos d > 0`, so `∫_{[c,d]} F ≤ (1/cos d) · ∫_{Iθ} F cos` for any
nonnegative `F`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.EllipticEst.ModalSolution.abs_le_of_l2_Icc
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.H2.ModalSolR

/-- **Comparison of an integral over `[c,d] ⊆ Iθ` with the `cos`-weighted integral over
`Iθ`.**  If `0 < c < d < π/2`, `F ≥ 0` and `∫_{Iθ} F cos` converges, then
`∫_c^d F ≤ (1/cos d) · ∫_{Iθ} F cos`: the only loss is the factor `1/cos d`, since
`cos t ≥ cos d > 0` for `t ∈ [c,d]` and `[c,d] ⊆ Iθ` with a nonnegative integrand. -/
private lemma intervalIntegral_le_inv_cos_Itheta_aux {c d : ℝ} (hcd : c < d) (hc : 0 < c)
    (hd : d < Real.pi / 2) (F : ℝ → ℝ) (hF0 : ∀ t, 0 ≤ F t)
    (hFi : IntegrableOn (fun t => F t * Real.cos t) Work.Spaces.Iθ) :
    (∫ t in c..d, F t) ≤ (1 / Real.cos d) * ∫ t in Work.Spaces.Iθ, F t * Real.cos t := by
  have hcosd : 0 < Real.cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hc], hd⟩
  have hsub : Set.Ioc c d ⊆ Work.Spaces.Iθ := fun t ht =>
    ⟨(lt_trans hc ht.1).le, (lt_of_le_of_lt ht.2 hd).le⟩
  have hcos_t : ∀ t ∈ Work.Spaces.Iθ, 0 ≤ Real.cos t := by
    intro t ht
    rw [Work.Spaces.Iθ] at ht
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht.1],
      by linarith [Real.pi_pos, ht.2]⟩
  have hcos_ge : ∀ t ∈ Set.Ioc c d, Real.cos d ≤ Real.cos t := fun t ht =>
    Real.cos_le_cos_of_nonneg_of_le_pi (lt_trans hc ht.1).le (by linarith [Real.pi_pos, hd])
      ht.2
  have hIntFc : IntegrableOn (fun t => F t * Real.cos t) (Set.Ioc c d) := hFi.mono_set hsub
  -- the pointwise comparison with the weighted integrand, on `(c,d]`
  have hstep1 : (∫ t in Set.Ioc c d, F t)
      ≤ ∫ t in Set.Ioc c d, (1 / Real.cos d) * (F t * Real.cos t) := by
    have hpt : ∀ t ∈ Set.Ioc c d, F t ≤ (1 / Real.cos d) * (F t * Real.cos t) := by
      intro t ht
      have h1 : 1 ≤ Real.cos t / Real.cos d := (one_le_div hcosd).mpr (hcos_ge t ht)
      calc F t = F t * 1 := by ring
        _ ≤ F t * (Real.cos t / Real.cos d) := mul_le_mul_of_nonneg_left h1 (hF0 t)
        _ = (1 / Real.cos d) * (F t * Real.cos t) := by ring
    exact MeasureTheory.setIntegral_mono_of_nonneg (fun t _ => hF0 t) hpt
      (hIntFc.const_mul _)
  -- enlarging the domain from `(c,d]` to `Iθ`
  have hstep2 : (∫ t in Set.Ioc c d, F t * Real.cos t)
      ≤ ∫ t in Work.Spaces.Iθ, F t * Real.cos t := by
    have hnn : 0 ≤ᵐ[volume.restrict (Work.Spaces.Iθ)] (fun t => F t * Real.cos t) := by
      show ∀ᵐ t ∂(volume.restrict (Work.Spaces.Iθ)), 0 ≤ F t * Real.cos t
      rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun t ht => mul_nonneg (hF0 t) (hcos_t t ht))
    exact MeasureTheory.setIntegral_mono_set hFi hnn
      (Filter.Eventually.of_forall (fun t ht => hsub ht))
  rw [intervalIntegral.integral_of_le hcd.le]
  calc (∫ t in Set.Ioc c d, F t)
      ≤ ∫ t in Set.Ioc c d, (1 / Real.cos d) * (F t * Real.cos t) := hstep1
    _ = (1 / Real.cos d) * ∫ t in Set.Ioc c d, F t * Real.cos t := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (1 / Real.cos d) * ∫ t in Work.Spaces.Iθ, F t * Real.cos t :=
        mul_le_mul_of_nonneg_left hstep2 (div_nonneg zero_le_one hcosd.le)

theorem supBoundOfIntegrals {c d : ℝ} (hcd : c < d) (hc : 0 < c) (hd : d < Real.pi / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (v : ℝ → ℝ),
      ContDiffOn ℝ 1 v (Set.Icc 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => v θ ^ 2 * Real.cos θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv v θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ →
      ∀ θ ∈ Set.Icc c d,
        |v θ| ≤ K * Real.sqrt ((∫ θ in Work.Spaces.Iθ, v θ ^ 2 * Real.cos θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ)) := by
  have hcosd : 0 < Real.cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hc], hd⟩
  have hLpos : 0 < d - c := sub_pos.mpr hcd
  have hcosd1 : 0 < 1 / Real.cos d := div_pos one_pos hcosd
  have hcos_t : ∀ t ∈ Work.Spaces.Iθ, 0 ≤ Real.cos t := by
    intro t ht
    rw [Work.Spaces.Iθ] at ht
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht.1],
      by linarith [Real.pi_pos, ht.2]⟩
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hKpos : 0 < Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)
      + Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d) := by
    have ha : 0 < Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c) :=
      div_pos (Real.sqrt_pos_of_pos hcosd1) (Real.sqrt_pos_of_pos hLpos)
    have hb : 0 ≤ Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  refine ⟨Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)
      + Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d), hKpos, ?_⟩
  intro v hv h1 h2 θ hθ
  -- the two weighted integrals over `Iθ`
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, v θ ^ 2 * Real.cos θ with hAdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ with hBdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact MeasureTheory.setIntegral_nonneg hIθmeas (fun t ht => mul_nonneg (sq_nonneg _)
      (hcos_t t ht))
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact MeasureTheory.setIntegral_nonneg hIθmeas (fun t ht => mul_nonneg (sq_nonneg _)
      (hcos_t t ht))
  -- comparison of the `[c,d]`-integrals with `A` and `B`
  have hX : (∫ x in c..d, v x ^ 2) ≤ (1 / Real.cos d) * A := by
    rw [hAdef]
    exact intervalIntegral_le_inv_cos_Itheta_aux hcd hc hd (fun t => v t ^ 2)
      (fun t => sq_nonneg _) h1
  have hY : (∫ x in c..d, (deriv v x) ^ 2) ≤ (1 / Real.cos d) * B := by
    rw [hBdef]
    exact intervalIntegral_le_inv_cos_Itheta_aux hcd hc hd (fun t => (deriv v t) ^ 2)
      (fun t => sq_nonneg _) h2
  -- the two square-root bounds
  have hsX : Real.sqrt (∫ x in c..d, v x ^ 2)
      ≤ Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B) := by
    calc Real.sqrt (∫ x in c..d, v x ^ 2)
        ≤ Real.sqrt ((1 / Real.cos d) * A) := Real.sqrt_le_sqrt hX
      _ ≤ Real.sqrt ((1 / Real.cos d) * (A + B)) := by
          refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ hcosd1.le)
          linarith
      _ = Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B) := Real.sqrt_mul hcosd1.le (A + B)
  have hsY : Real.sqrt (∫ x in c..d, (deriv v x) ^ 2)
      ≤ Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B) := by
    calc Real.sqrt (∫ x in c..d, (deriv v x) ^ 2)
        ≤ Real.sqrt ((1 / Real.cos d) * B) := Real.sqrt_le_sqrt hY
      _ ≤ Real.sqrt ((1 / Real.cos d) * (A + B)) := by
          refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ hcosd1.le)
          linarith
      _ = Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B) := Real.sqrt_mul hcosd1.le (A + B)
  -- the one-dimensional Sobolev bound on `[c,d]`
  have hvcd : ContDiffOn ℝ 1 v (Set.Icc c d) :=
    hv.mono fun x hx => ⟨le_trans hc.le hx.1, le_trans hx.2 hd.le⟩
  have habs := _root_.Work.EllipticEst.ModalSolution.abs_le_of_l2_Icc v hcd hθ hvcd
  calc |v θ|
      ≤ Real.sqrt (∫ x in c..d, v x ^ 2) / Real.sqrt (d - c)
          + Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) := habs
    _ ≤ (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)) * Real.sqrt (A + B)
          + (Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d)) * Real.sqrt (A + B) := by
        refine add_le_add ?_ ?_
        · calc Real.sqrt (∫ x in c..d, v x ^ 2) / Real.sqrt (d - c)
              ≤ (Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B)) / Real.sqrt (d - c) :=
                div_le_div_of_nonneg_right hsX (Real.sqrt_nonneg _)
            _ = (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)) * Real.sqrt (A + B) := by
                ring
        · calc Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2)
              ≤ Real.sqrt (d - c) * (Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B)) :=
                mul_le_mul_of_nonneg_left hsY (Real.sqrt_nonneg _)
            _ = (Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d)) * Real.sqrt (A + B) := by
                ring
    _ = (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)
          + Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d)) * Real.sqrt (A + B) := by ring

end Work.FTS.H2.ModalSolR
