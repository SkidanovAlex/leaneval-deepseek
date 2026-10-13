import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-!
# Weighted Hardy inequality for the primitive, with the angular weight `sEta`

We prove that the primitive `F θ = ∫ t in 0..θ, g t` of a function `g` that is integrable
on `Iθ = [0, π/2]` with `g² sin(2θ)^{-η}` integrable satisfies

  `∫_{Iθ} F(θ)² · sin(2θ)^{-η} dθ ≤ K · ∫_{Iθ} g(θ)² · sin(2θ)^{-η} dθ`

with a universal constant `K`.

The argument is elementary but rather blunt.  Since `sin(2θ) ∈ [0,1]` on `Iθ` the weight
`σ θ = sin(2θ)^{-η}` is `≥ 1` on the interior of `Iθ`, hence `∫_{Iθ} σ θ dθ` is finite
(`Work.FTS.LocData.integral_sin_two_rpow_neg`) and dominates both `∫ g²` and `∫ g²σ`.  For
`θ ∈ Iθ` Cauchy–Schwarz on `[0,θ]` (with the constant test function `1`) gives

  `F(θ)² ≤ (π/2) · ∫_{Iθ} g²`,

so with `M² = (π/2)∫_{Iθ} g²` we get `∫ F²σ ≤ M² ∫ σ`; combining the two bounds produces the
constant `10⁶`.  No sharpness is intended: any constant would do for the applications.
-/

/-- `sEta` is nonnegative on `Iθ`. -/
private lemma sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _

/-- `sEta θ ≥ 1` at interior points of `Iθ`, because `sin(2θ) ∈ (0,1]` there. -/
private lemma one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsinle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_nonpos hsinpos hsinle
    (show -(Work.Spaces.eta) ≤ 0 by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h

/-- Almost every point of `Iθ` is an interior point (the two endpoints form a null set). -/
private lemma ae_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hmeq : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  rw [← hmeq]
  exact ae_restrict_mem measurableSet_Ioo

/-- `sEta` is integrable on `Iθ` (the singularity has exponent `η < 1`). -/
private lemma sEta_integrableOn :
    IntegrableOn Work.FTS.EllipticEst.sEta Work.Spaces.Iθ :=
  (Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])).1

/-- A crude numerical bound for the integral of the weight. -/
private lemma integral_sEta_le :
    ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ ≤ 10000 := by
  refine le_trans (Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])).2 ?_
  norm_num [Work.Spaces.eta]

/-- `sEta` is Borel measurable: it is continuous on the conull interior of `Iθ`. -/
private lemma sEta_aestronglyMeasurable :
    AEStronglyMeasurable Work.FTS.EllipticEst.sEta (volume.restrict Work.Spaces.Iθ) := by
  have hsin_cont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ)).continuousOn
  have hne : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))
  have hcont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin_cont.rpow_const (fun θ hθ => Or.inl (hne θ hθ))
  have h1 : AEStronglyMeasurable (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hmeq : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  rw [← hmeq]
  exact h1

/-- **Cauchy–Schwarz for the primitive.**  If `g` and `g²` are integrable on `Iθ` then the
primitive of `g` satisfies `(∫ t in 0..θ, g t)² ≤ (π/2) · ∫_{Iθ} g²` for every `θ ∈ Iθ`. -/
private theorem prim_sq_le {g : ℝ → ℝ} (hg : IntegrableOn g Work.Spaces.Iθ)
    (hg2 : IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (∫ t in (0 : ℝ)..θ, g t) ^ 2 ≤ (Real.pi / 2) * ∫ x in Work.Spaces.Iθ, g x ^ 2 := by
  have hθ0 : (0 : ℝ) ≤ θ := hθ.1
  have hsub : Set.Icc (0 : ℝ) θ ⊆ Work.Spaces.Iθ := Set.Icc_subset_Icc_right hθ.2
  have hgI : IntegrableOn g (Set.Icc (0 : ℝ) θ) := hg.mono_set hsub
  have hg2I : IntegrableOn (fun t => g t ^ 2) (Set.Icc (0 : ℝ) θ) := hg2.mono_set hsub
  have hu : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) θ)) :=
    (memLp_two_iff_integrable_sq hgI.aestronglyMeasurable).2 hg2I
  have hv : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Icc (0 : ℝ) θ)) :=
    memLp_const 1
  have hcs := Work.Spaces.cs_integral hu hv
  simp only [mul_one, one_pow] at hcs
  have hlen : (∫ x in Set.Icc (0 : ℝ) θ, (1 : ℝ)) = θ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hθ0,
      intervalIntegral.integral_const]
    simp
  rw [hlen] at hcs
  have hgval : (∫ t in (0 : ℝ)..θ, g t) = ∫ t in Set.Icc (0 : ℝ) θ, g t := by
    rw [intervalIntegral.integral_of_le hθ0, ← integral_Icc_eq_integral_Ioc]
  rw [hgval]
  have hmono : (∫ x in Set.Icc (0 : ℝ) θ, g x ^ 2) ≤ ∫ x in Work.Spaces.Iθ, g x ^ 2 :=
    setIntegral_mono_set hg2 (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall fun x hx => hsub hx)
  have hgnn : 0 ≤ ∫ x in Work.Spaces.Iθ, g x ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  calc (∫ x in Set.Icc (0 : ℝ) θ, g x) ^ 2
      ≤ (∫ x in Set.Icc (0 : ℝ) θ, g x ^ 2) * θ := hcs
    _ ≤ (∫ x in Work.Spaces.Iθ, g x ^ 2) * (Real.pi / 2) := mul_le_mul hmono hθ.2 hθ0 hgnn
    _ = (Real.pi / 2) * ∫ x in Work.Spaces.Iθ, g x ^ 2 := by ring

theorem HardyPrimEta :
    ∃ K : ℝ, 0 < K ∧ ∀ g : ℝ → ℝ,
      MeasureTheory.IntegrableOn g Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContinuousAt g θ) →
      MeasureTheory.IntegrableOn
          (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ,
            (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ K * ∫ θ in Work.Spaces.Iθ,
              (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  refine ⟨(10 : ℝ) ^ 6, by norm_num, fun g hg hgs _hcont => ?_⟩
  clear _hcont
  -- `sEta ≥ 1` almost everywhere on `Iθ`.
  have hone : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [ae_mem_Ioo] with θ hθ
    exact one_le_sEta_of_mem_Ioo hθ
  have haeI : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
    ae_restrict_mem measurableSet_Icc
  -- Step 1: `g²` is integrable on `Iθ`, because `g² ≤ g² · sEta` a.e.
  have hg2 : IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ := by
    refine hgs.mono' ?_ ?_
    · exact (hg.aestronglyMeasurable.mul hg.aestronglyMeasurable).congr
        (Eventually.of_forall fun θ => by simp [Pi.mul_apply, sq])
    · filter_upwards [hone] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc g θ ^ 2 = g θ ^ 2 * 1 := by ring
        _ ≤ g θ ^ 2 * Work.FTS.EllipticEst.sEta θ :=
            mul_le_mul_of_nonneg_left hθ (sq_nonneg _)
  -- Step 2: the Cauchy–Schwarz bound for the primitive.
  set M2 : ℝ := (Real.pi / 2) * ∫ x in Work.Spaces.Iθ, g x ^ 2 with hM2def
  have hM2nn : 0 ≤ M2 := by
    rw [hM2def]
    exact mul_nonneg (by positivity) (integral_nonneg fun x => sq_nonneg _)
  have hpoint : ∀ θ ∈ Work.Spaces.Iθ, (∫ t in (0 : ℝ)..θ, g t) ^ 2 ≤ M2 := by
    intro θ hθ
    rw [hM2def]
    exact prim_sq_le hg hg2 θ hθ
  -- Step 3: measurability of the integrand.
  have hFcont : ContinuousOn (fun x : ℝ => ∫ t in (0 : ℝ)..x, g t) Work.Spaces.Iθ := by
    have h2 : IntegrableOn g (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])]
      exact hg
    have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ))
      (b := Real.pi / 2) h2
    rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at h
  have hFsq : AEStronglyMeasurable (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    ((hFcont.aestronglyMeasurable measurableSet_Icc).mul
      (hFcont.aestronglyMeasurable measurableSet_Icc)).congr
      (Eventually.of_forall fun θ => by simp [Pi.mul_apply, sq])
  have hprod_aesm : AEStronglyMeasurable
      (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    (hFsq.mul sEta_aestronglyMeasurable).congr
      (Eventually.of_forall fun θ => by simp [Pi.mul_apply])
  -- Step 4: the two a.e. pointwise statements used for the integrals.
  have hbd : (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ᵐ[volume.restrict Work.Spaces.Iθ] fun θ => M2 * Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [haeI] with θ hθ
    exact mul_le_mul_of_nonneg_right (hpoint θ hθ) (sEta_nonneg hθ)
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [haeI] with θ hθ
    exact mul_nonneg (sq_nonneg _) (sEta_nonneg hθ)
  -- Step 5: integrability of the LHS integrand.
  have hM2σ : Integrable (fun θ => M2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := sEta_integrableOn.const_mul M2
  have hintF : Integrable
      (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
    refine hM2σ.mono' hprod_aesm ?_
    filter_upwards [haeI] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))]
    exact mul_le_mul_of_nonneg_right (hpoint θ hθ) (sEta_nonneg hθ)
  refine ⟨hintF, ?_⟩
  -- Step 6: the numerical estimates.
  have hgnnle : (∫ x in Work.Spaces.Iθ, g x ^ 2)
      ≤ ∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x := by
    refine integral_mono_ae hg2 hgs ?_
    filter_upwards [hone] with θ hθ
    calc g θ ^ 2 = g θ ^ 2 * 1 := by ring
      _ ≤ g θ ^ 2 * Work.FTS.EllipticEst.sEta θ := mul_le_mul_of_nonneg_left hθ (sq_nonneg _)
  have hA0 : 0 ≤ ∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x :=
    integral_nonneg_of_ae (by
      filter_upwards [haeI] with θ hθ
      exact mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  have hσ0 : 0 ≤ ∫ x in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta x :=
    integral_nonneg_of_ae (by
      filter_upwards [haeI] with θ hθ
      exact sEta_nonneg hθ)
  have hstep : (∫ θ in Work.Spaces.Iθ,
        (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ M2 * ∫ x in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta x := by
    have h := integral_mono_of_nonneg hnonneg hM2σ hbd
    rwa [integral_const_mul] at h
  calc (∫ θ in Work.Spaces.Iθ,
        (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ M2 * ∫ x in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta x := hstep
    _ = ((Real.pi / 2) * (∫ x in Work.Spaces.Iθ, g x ^ 2))
          * (∫ x in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta x) := by rw [hM2def]
    _ ≤ ((Real.pi / 2) * (∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x))
          * 10000 := by
        refine mul_le_mul ?_ integral_sEta_le hσ0 ?_
        · exact mul_le_mul_of_nonneg_left hgnnle (by positivity)
        · exact mul_nonneg (by positivity) hA0
    _ ≤ (10 : ℝ) ^ 6
          * (∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x) := by
        rw [show (Real.pi / 2)
              * (∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x) * 10000
            = ((Real.pi / 2) * 10000)
              * (∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x) from by ring]
        refine mul_le_mul_of_nonneg_right ?_ hA0
        nlinarith [Real.pi_lt_four]

end

end Work.FTS.EllipticEst.H2W
