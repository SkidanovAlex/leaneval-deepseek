/-
# The bound `(C0 f)² ≤ 100 Ef f`
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.C0Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Coercivity.SmoothNbhd_pth_slice
import Submission.Work.Coercivity.sq_integral_mul_le
import Submission.Work.Coercivity.C0Ih_le
import Submission.Work.Coercivity.C0D_le
import Submission.Work.Coercivity.C0thetaIBP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

private lemma continuous_C0g : Continuous C0g := by
  unfold C0g
  fun_prop

private lemma continuousOn_w_Ioi : ContinuousOn Spaces.w (Set.Ioi (0 : ℝ)) := by
  unfold Spaces.w
  exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
    (continuous_id.pow 2).continuousOn (fun x hx => pow_ne_zero 2 (ne_of_gt hx))

private lemma integrableOn_inv_w_sq :
    IntegrableOn (fun s : ℝ => (1 / (s * (1 + s) * Spaces.w s)) ^ 2) Spaces.Iz := by
  have hbase : IntegrableOn (fun s : ℝ => (1 / (1 + s)) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun s : ℝ => (s + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    refine h1.congr_fun (fun s hs => ?_) measurableSet_Ioi
    have hs0 : (0 : ℝ) < s := hs
    change (s + 1) ^ (-2 : ℝ) = (1 / (1 + s)) ^ 2
    rw [Real.rpow_neg (le_of_lt (by linarith : (0:ℝ) < s + 1)), Real.rpow_two]
    simp only [one_div, inv_pow]
    ring
  have hcont : ContinuousOn (fun s : ℝ => (1 / (s * (1 + s) * Spaces.w s)) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine ContinuousOn.pow (ContinuousOn.div continuousOn_const ?_ ?_) 2
    · exact ((continuous_id.mul (continuous_const.add continuous_id)).continuousOn).mul
        continuousOn_w_Ioi
    · intro s hs
      have hs0 : 0 < s := hs
      have hw : Spaces.w s ≠ 0 := by unfold Spaces.w; positivity
      exact mul_ne_zero (mul_ne_zero (ne_of_gt hs0) (by positivity)) hw
  have hIoi : IntegrableOn (fun s : ℝ => (1 / (s * (1 + s) * Spaces.w s)) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' hbase (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    have hs1 : (0 : ℝ) < 1 + s := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hval : (1 / (s * (1 + s) * Spaces.w s)) ^ 2 = (s / (1 + s) ^ 3) ^ 2 := by
      unfold Spaces.w
      field_simp
    rw [hval]
    have hkey : s ≤ (1 + s) ^ 2 := by nlinarith [hs0, sq_nonneg s]
    have hgoal : (s / (1 + s) ^ 3) ^ 2 ≤ (1 / (1 + s)) ^ 2 := by
      rw [div_pow, div_pow]
      rw [div_le_iff₀ (pow_pos (by positivity : (0:ℝ) < (1 + s) ^ 3) 2),
        div_mul_eq_mul_div, le_div_iff₀ (pow_pos hs1 2)]
      nlinarith [hkey, hs0, hs1, sq_nonneg (s ^ 2 - (1 + s) ^ 4)]
    exact hgoal
  rw [IntegrableOn] at hIoi ⊢
  rw [Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))] at hIoi
  exact hIoi

theorem C0_sq_le_Ef (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (hs : Spaces.SmoothNbhd f)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (C0 f) ^ 2 ≤ 100 * Ef f := by
  -- ## The measure on the quadrant and the three test functions.
  set μ : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hμdef
  set J : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Spaces.Iθ with hJdef
  set A : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Spaces.w p.1 with hAdef
  set B : ℝ × ℝ → ℝ := fun p => C0g p.2 * (1 / (p.1 * (1 + p.1) * Spaces.w p.1)) with hBdef
  set H : ℝ × ℝ → ℝ := fun p => C0g p.2 * f p.1 p.2 / (p.1 * (1 + p.1)) with hHdef
  have hJmeas : MeasurableSet J := by
    rw [hJdef]; exact measurableSet_Ioi.prod measurableSet_Icc
  have hμJ : μ = (volume.prod volume).restrict J := by
    rw [hμdef, hJdef]
    have h1 : volume.restrict Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) :=
      (Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [h1, Measure.prod_restrict]
  have hmemJ : ∀ᵐ p ∂μ, p ∈ J := by
    rw [hμJ]; exact ae_restrict_mem hJmeas
  -- ## Continuity of `A`, `B`, `H` on `J`.
  have hsub : Set.Ioi (0 : ℝ) ×ˢ Spaces.Iθ ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) :=
    Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num))
      (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
  have hfcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Spaces.Iθ) :=
    hs.continuousOn.mono hsub
  have hwcont : ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1) (Set.Ioi (0 : ℝ) ×ˢ Spaces.Iθ) :=
    continuousOn_w_Ioi.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hAcont : ContinuousOn A J := by rw [hAdef, hJdef]; exact hfcont.mul hwcont
  have hBcont : ContinuousOn B J := by
    rw [hBdef, hJdef]
    refine ContinuousOn.mul (continuous_C0g.comp_continuousOn continuous_snd.continuousOn) ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact ((continuous_fst.mul (continuous_const.add continuous_fst)).continuousOn).mul hwcont
    · intro p hp
      have hp1 : 0 < p.1 := hp.1
      have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
      have hw : Spaces.w p.1 ≠ 0 := by unfold Spaces.w; positivity
      exact mul_ne_zero (mul_ne_zero (ne_of_gt hp1) (ne_of_gt h1p1)) hw
  have hHcont : ContinuousOn H J := by
    rw [hHdef, hJdef]
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_C0g.comp_continuousOn continuous_snd.continuousOn).mul hfcont
    · exact (continuous_fst.mul (continuous_const.add continuous_fst)).continuousOn
    · intro p hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
      exact mul_ne_zero (ne_of_gt hp1) (ne_of_gt h1p1)
  have hA_aesm : AEStronglyMeasurable A μ := by
    rw [hμJ]; exact hAcont.aestronglyMeasurable hJmeas
  have hB_aesm : AEStronglyMeasurable B μ := by
    rw [hμJ]; exact hBcont.aestronglyMeasurable hJmeas
  have hH_aesm : AEStronglyMeasurable H μ := by
    rw [hμJ]; exact hHcont.aestronglyMeasurable hJmeas
  -- ## Integrability.
  have hA2int : Integrable (fun p : ℝ × ℝ => A p ^ 2) μ := by
    rw [hAdef]
    have h := hfw
    rw [IntegrableOn, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at h
    rw [hμdef]
    exact h
  have hC0g2_int : IntegrableOn (fun θ : ℝ => (C0g θ) ^ 2) Spaces.Iθ :=
    (continuous_C0g.pow 2).continuousOn.integrableOn_Icc
  have hB2int : Integrable (fun p : ℝ × ℝ => B p ^ 2) μ := by
    rw [hBdef]
    have h1 : (fun p : ℝ × ℝ => (C0g p.2 * (1 / (p.1 * (1 + p.1) * Spaces.w p.1))) ^ 2)
        = fun p : ℝ × ℝ => (1 / (p.1 * (1 + p.1) * Spaces.w p.1)) ^ 2 * (C0g p.2) ^ 2 := by
      funext p; rw [mul_pow]; ring
    rw [h1, hμdef]
    exact integrableOn_inv_w_sq.mul_prod hC0g2_int
  have hHdom : Integrable (fun p : ℝ × ℝ => (1 / 2) * (A p ^ 2 + B p ^ 2)) μ :=
    (hA2int.add hB2int).const_mul (1 / 2)
  have hHint : Integrable H μ := by
    refine Integrable.mono' hHdom hH_aesm ?_
    filter_upwards [hmemJ] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hwpos : 0 < Spaces.w p.1 := by unfold Spaces.w; positivity
    have hden : 0 < p.1 * (1 + p.1) := by positivity
    have hAeq : A p ^ 2 = (|f p.1 p.2| * Spaces.w p.1) ^ 2 := by
      rw [hAdef, mul_pow, mul_pow, sq_abs]
    have hBeq : B p ^ 2 = (|C0g p.2| * (1 / (p.1 * (1 + p.1) * Spaces.w p.1))) ^ 2 := by
      rw [hBdef, mul_pow, mul_pow, sq_abs]
    have hHeq : ‖H p‖ = (|f p.1 p.2| * Spaces.w p.1) *
        (|C0g p.2| * (1 / (p.1 * (1 + p.1) * Spaces.w p.1))) := by
      simp only [hHdef]
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hden]
      have hp1ne : p.1 ≠ 0 := ne_of_gt hp1
      have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
      have h1p1ne : (1 : ℝ) + p.1 ≠ 0 := ne_of_gt h1p1
      have hwne : Spaces.w p.1 ≠ 0 := ne_of_gt hwpos
      field_simp
    rw [hHeq, hAeq, hBeq]
    nlinarith [two_mul_le_add_sq (|f p.1 p.2| * Spaces.w p.1)
      (|C0g p.2| * (1 / (p.1 * (1 + p.1) * Spaces.w p.1)))]
  -- ## Fubini and the identification with the double integral.
  have hH_fub : (∫ s in Spaces.Iz, ∫ θ in Spaces.Iθ, H (s, θ)) = ∫ p, H p ∂μ := by
    have hint := hHint
    rw [hμdef] at hint ⊢
    exact (integral_prod H hint).symm
  have hX : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Spaces.Iθ, C0g θ * f s θ / (s * (1 + s)))
      = ∫ p, A p * B p ∂μ := by
    have hfill : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Spaces.Iθ, C0g θ * f s θ / (s * (1 + s)))
        = ∫ s in Spaces.Iz, ∫ θ in Spaces.Iθ, H (s, θ) := by
      rw [hHdef]
      exact setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))
    rw [hfill, hH_fub]
    refine integral_congr_ae ?_
    filter_upwards [hmemJ] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hwne : Spaces.w p.1 ≠ 0 := by unfold Spaces.w; positivity
    have hp1ne : p.1 ≠ 0 := ne_of_gt hp1
    have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
    have h1p1ne : (1 : ℝ) + p.1 ≠ 0 := ne_of_gt h1p1
    rw [hHdef, hAdef, hBdef]
    field_simp
  -- ## Cauchy–Schwarz and the two integrals.
  have hcs : (∫ p, A p * B p ∂μ) ^ 2 ≤ (∫ p, A p ^ 2 ∂μ) * (∫ p, B p ^ 2 ∂μ) :=
    sq_integral_mul_le μ A B hA_aesm hB_aesm hA2int hB2int
  have hA2eq : ∫ p, A p ^ 2 ∂μ = Ef f := by
    have hint := hA2int
    rw [hAdef] at hint ⊢
    rw [hμdef] at hint ⊢
    rw [integral_prod (fun p : ℝ × ℝ => (f p.1 p.2 * Spaces.w p.1) ^ 2) hint]
    rfl
  have hB2eq : ∫ p, B p ^ 2 ∂μ = C0Ih * C0D := by
    have h1 : (fun p : ℝ × ℝ => B p ^ 2)
        = fun p : ℝ × ℝ => (1 / (p.1 * (1 + p.1) * Spaces.w p.1)) ^ 2 * (C0g p.2) ^ 2 := by
      funext p; rw [hBdef, mul_pow]; ring
    rw [h1, hμdef]
    rw [integral_prod_mul (f := fun s : ℝ => (1 / (s * (1 + s) * Spaces.w s)) ^ 2)
      (g := fun θ : ℝ => (C0g θ) ^ 2)]
    have hC0D' : (∫ s in Spaces.Iz, (1 / (s * (1 + s) * Spaces.w s)) ^ 2) = C0D :=
      (setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [show C0Ih = ∫ θ in Spaces.Iθ, (C0g θ) ^ 2 from rfl, hC0D']
    ring
  -- ## The numeric bounds.
  have hnum : C0Ih * C0D ≤ 100 := by
    have h1 : C0Ih ≤ 729 := C0Ih_le
    have h2 : C0D ≤ 1 / 16 := C0D_le
    have h3 : 0 ≤ C0Ih := by rw [C0Ih]; exact integral_nonneg (fun θ => sq_nonneg _)
    have h4 : 0 ≤ C0D := by rw [C0D]; exact integral_nonneg (fun s => sq_nonneg _)
    nlinarith [h1, h2, h3, h4]
  have hEf : 0 ≤ Ef f := by
    rw [Ef, Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  -- ## The angular integration by parts giving `C0 f` as an explicit double integral.
  have hC0 : C0 f = -∫ s in Set.Ioi (0 : ℝ), ∫ θ in Spaces.Iθ, C0g θ * f s θ / (s * (1 + s)) := by
    have step1 : C0 f = ∫ s in Set.Ioi (0 : ℝ), FM.L12dens Spaces.K (Transport f) s := by
      rw [C0, L12f, FM.L12]
    rw [step1]
    have step2 : (∫ s in Set.Ioi (0 : ℝ), FM.L12dens Spaces.K (Transport f) s)
        = ∫ s in Set.Ioi (0 : ℝ),
            (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ, C0h θ * Spaces.pth f s θ := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
      have hs0 : s ≠ 0 := ne_of_gt hs'
      have hs1 : (1 : ℝ) + s ≠ 0 := by
        have hs0' : (0 : ℝ) < s := hs'
        have : (0 : ℝ) < 1 + s := by linarith
        exact ne_of_gt this
      rw [FM.L12dens]
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall (fun θ => ?_))
      simp only [Transport, Spaces.Dth, C0h, Spaces.K]
      field_simp
    rw [step2]
    have step3 : (∫ s in Set.Ioi (0 : ℝ),
          (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ, C0h θ * Spaces.pth f s θ)
        = -∫ s in Set.Ioi (0 : ℝ),
            (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ, C0g θ * f s θ := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
      obtain ⟨hgd, hgi⟩ := SmoothNbhd_pth_slice f hs s (le_of_lt hs')
      rw [C0thetaIBP (fun θ => f s θ) (Spaces.pth f s) hgd hgi]
      ring
    rw [step3]
    have step4 : (∫ s in Set.Ioi (0 : ℝ),
          (1 / (s * (1 + s))) * ∫ θ in Spaces.Iθ, C0g θ * f s θ)
        = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Spaces.Iθ, C0g θ * f s θ / (s * (1 + s)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
      rw [integral_div]
      ring
    rw [step4]
  calc (C0 f) ^ 2
      = (∫ p, A p * B p ∂μ) ^ 2 := by rw [hC0, hX]; ring
    _ ≤ (∫ p, A p ^ 2 ∂μ) * (∫ p, B p ^ 2 ∂μ) := hcs
    _ = Ef f * (C0Ih * C0D) := by rw [hA2eq, hB2eq]
    _ ≤ Ef f * 100 := by nlinarith [hnum, hEf]
    _ = 100 * Ef f := by ring

end Work.Coercivity
