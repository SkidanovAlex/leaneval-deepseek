import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.Decomp.bsMean_eq_zero_of_far
import Submission.Work.BSKinetic.Decomp.exists_radius_eq_zero_of_hasCompactSupport
import Submission.Work.BSKinetic.Decomp.norm_ge_of_bsWin_ne_zero
import Submission.Work.BSKinetic.abs_bsMean_le
import Submission.Work.BSKinetic.bsOneBodyUnproj_eq_iterKernel
import Submission.Work.BSKinetic.integrable_bsFamUnprojJoint
import Submission.Work.BSKinetic.integrable_bsFamUnprojSlice
import Submission.Work.OneBodyKin.bsPair_const_eq
import Submission.Work.OneBodyKin.bsPair_eq_cos
import Submission.Work.OneBodyKin.integrable_bsKern
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## Measurability of the box mean -/

private lemma aestronglyMeasurable_bsMean {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    AEStronglyMeasurable (fun u : ℝ³ => Work.BSKinetic.bsMean ℓ u ψ) := by
  have hjoint : AEStronglyMeasurable
      (((Set.univ : Set ℝ³) ×ˢ acube ℓ).indicator (fun w : ℝ³ × ℝ³ => ψ (ℓ • w.1 + w.2)))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    ((hψ.comp (by fun_prop)).aestronglyMeasurable).indicator
      (MeasurableSet.univ.prod (acube_measurable ℓ))
  have h2 : AEStronglyMeasurable (fun u : ℝ³ => ∫ z : ℝ³,
      (((Set.univ : Set ℝ³) ×ˢ acube ℓ).indicator (fun w : ℝ³ × ℝ³ => ψ (ℓ • w.1 + w.2))) (u, z))
      (volume : Measure ℝ³) :=
    hjoint.integral_prod_right'
  have h3 : AEStronglyMeasurable (fun u : ℝ³ => ∫ z in acube ℓ, ψ (ℓ • u + z))
      (volume : Measure ℝ³) := by
    have hinner : (fun u : ℝ³ => ∫ z : ℝ³,
        (((Set.univ : Set ℝ³) ×ˢ acube ℓ).indicator (fun w : ℝ³ × ℝ³ => ψ (ℓ • w.1 + w.2))) (u, z))
        = fun u : ℝ³ => ∫ z in acube ℓ, ψ (ℓ • u + z) := by
      funext u
      rw [← integral_indicator (acube_measurable ℓ)]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show ((Set.univ : Set ℝ³) ×ˢ acube ℓ).indicator
            (fun w : ℝ³ × ℝ³ => ψ (ℓ • w.1 + w.2)) (u, z)
          = (acube ℓ).indicator (fun z : ℝ³ => ψ (ℓ • u + z)) z
      by_cases hz : z ∈ acube ℓ
      · have hmem : (u, z) ∈ (Set.univ : Set ℝ³) ×ˢ acube ℓ :=
          Set.mem_prod.mpr ⟨Set.mem_univ u, hz⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hz]
      · have hmem : (u, z) ∉ (Set.univ : Set ℝ³) ×ˢ acube ℓ := fun h =>
          hz (Set.mem_prod.mp h).2
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hz]
    rw [← hinner]
    exact h2
  exact h3.const_mul ((ℓ ^ 3)⁻¹)

/-! ## Measurability of the cross form -/

private lemma aestronglyMeasurable_bsPair {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : ℝ³ => F ‖p‖)) {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    AEStronglyMeasurable (fun u : ℝ³ => Work.OneBodyKin.bsPair ℓ F u ψ) := by
  have hWcont : Continuous (fun w : (ℝ³ × ℝ³) × ℝ³ => Work.BSKinetic.bsWin ℓ w.1.1 w.2) := by
    rw [show (fun w : (ℝ³ × ℝ³) × ℝ³ => Work.BSKinetic.bsWin ℓ w.1.1 w.2)
        = fun w : (ℝ³ × ℝ³) × ℝ³ => Submission.BoseGases.chiScale ℓ (w.2 - ℓ • w.1.1) from rfl]
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.comp (by fun_prop)
  have hcont : Continuous (fun w : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ w.1.2 w.2 : ℂ))) *
        (((Work.BSKinetic.bsWin ℓ w.1.1 w.2 : ℝ)) : ℂ) * (ψ w.2 : ℂ)) := by
    refine Continuous.mul (Continuous.mul ?_ ?_) ?_
    · exact Complex.continuous_exp.comp (by fun_prop)
    · exact Complex.continuous_ofReal.comp hWcont
    · exact Complex.continuous_ofReal.comp (hψ.comp continuous_snd)
  have hcont' : Continuous (fun w : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ w.1.2 w.2 : ℂ))) *
        ((((Work.BSKinetic.bsWin ℓ w.1.1 w.2 : ℝ)) : ℂ) * (ψ w.2 : ℂ))) :=
    (Complex.continuous_exp.comp (by fun_prop)).mul
      ((Complex.continuous_ofReal.comp hWcont).mul (Complex.continuous_ofReal.comp (hψ.comp continuous_snd)))
  have hK2 : AEStronglyMeasurable (fun x : ℝ³ × ℝ³ =>
      Submission.BoseGases.kinFT (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ x.1 z : ℝ)) : ℂ) * (ψ z : ℂ)) x.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    hcont'.aestronglyMeasurable.integral_prod_right'
      (μ := (volume : Measure ℝ³).prod (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
  have hK1 : AEStronglyMeasurable (fun x : ℝ³ × ℝ³ =>
      Submission.BoseGases.kinFT (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ x.1 z : ℝ)) : ℂ)) x.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    have hfun : (fun x : ℝ³ × ℝ³ =>
        Submission.BoseGases.kinFT (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ x.1 z : ℝ)) : ℂ)) x.2)
        = fun x : ℝ³ × ℝ³ => Complex.exp (-(Complex.I * (inner ℝ (ℓ • x.2) x.1 : ℂ))) *
            ((ℓ : ℂ) ^ 3 * (Work.OneBodyKin.profHat (ℓ • x.2) : ℂ)) :=
      funext (fun x => Work.OneBodyKin.kinFT_bsWin hℓ x.1 x.2)
    rw [hfun]
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · have hs : StronglyMeasurable
          (fun x : ℝ³ × ℝ³ => (Work.OneBodyKin.profHat (ℓ • x.2) : ℂ)) :=
        Complex.continuous_ofReal.comp_stronglyMeasurable
          (Work.OneBodyKin.stronglyMeasurable_profHat.comp_measurable (by fun_prop))
      exact (aestronglyMeasurable_const (b := (ℓ : ℂ) ^ 3)).mul hs.aestronglyMeasurable
  have hAESM : AEStronglyMeasurable (fun x : ℝ³ × ℝ³ =>
      F ‖x.2‖ * (Submission.BoseGases.kinFT
          (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ x.1 z : ℝ)) : ℂ)) x.2 *
        star (Submission.BoseGases.kinFT
          (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ x.1 z : ℝ)) : ℂ) * (ψ z : ℂ)) x.2)).re)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    have hF' : AEStronglyMeasurable (fun x : ℝ³ × ℝ³ => F ‖x.2‖)
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
      hFi.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³)))
    have hprod : AEStronglyMeasurable (fun x : ℝ³ × ℝ³ =>
        Submission.BoseGases.kinFT (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ x.1 z : ℝ)) : ℂ)) x.2 *
          star (Submission.BoseGases.kinFT
            (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ x.1 z : ℝ)) : ℂ) * (ψ z : ℂ)) x.2))
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := hK1.mul hK2.star
    exact hF'.mul (Complex.continuous_re.comp_aestronglyMeasurable hprod)
  have hOut : AEStronglyMeasurable (fun u : ℝ³ => ∫ p : ℝ³, F ‖p‖ *
      (Submission.BoseGases.kinFT (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ)) p *
        star (Submission.BoseGases.kinFT
          (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ)) p)).re)
      (volume : Measure ℝ³) :=
    hAESM.integral_prod_right'
      (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
  exact hOut.const_mul ((2 * Real.pi) ^ 3)⁻¹

/-! ## A uniform bound on the cross form -/

private lemma abs_bsPair_le {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : ℝ³ => F ‖p‖)) {ψ : ℝ³ → ℝ}
    (hψ : Continuous ψ) (hcs : HasCompactSupport ψ) :
    ∃ C : ℝ, ∀ u : ℝ³, |Work.OneBodyKin.bsPair ℓ F u ψ| ≤ C := by
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hψ
  have hMb : ∀ z : ℝ³, |ψ z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
  have hψint : Integrable (fun z : ℝ³ => ‖ψ z‖) := hψ.norm.integrable_of_hasCompactSupport hcs.norm
  set Mχ : ℝ := ∫ z : ℝ³, |Submission.BoseGases.chi z| with hMχ
  set A : ℝ := ∫ z : ℝ³, ‖ψ z‖ with hA
  set CF : ℝ := ∫ p : ℝ³, ‖F ‖p‖‖ with hCF
  have hMχ0 : 0 ≤ Mχ := by rw [hMχ]; exact integral_nonneg (fun z => abs_nonneg _)
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun z => norm_nonneg _)
  have hCF0 : 0 ≤ CF := by rw [hCF]; exact integral_nonneg (fun p => norm_nonneg _)
  refine ⟨((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 3 * Mχ) * (Submission.BoseGases.chiSup * A) * CF, fun u => ?_⟩
  have hkin1 : ∀ p : ℝ³, ‖Submission.BoseGases.kinFT
      (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ)) p‖ ≤ ℓ ^ 3 * Mχ := by
    intro p
    have hexp : ‖Complex.exp (-(Complex.I * (inner ℝ (ℓ • p) u : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have hpf : ‖(Work.OneBodyKin.profHat (ℓ • p) : ℂ)‖ ≤ Mχ := by
      rw [hMχ]
      calc ‖(Work.OneBodyKin.profHat (ℓ • p) : ℂ)‖
          = |Work.OneBodyKin.profHat (ℓ • p)| := by simp
        _ ≤ ∫ z : ℝ³, |Submission.BoseGases.chi z| := Work.OneBodyKin.abs_profHat_le (ℓ • p)
    have hpow : ‖(ℓ : ℂ) ^ 3‖ = ℓ ^ 3 := by
      rw [norm_pow]
      congr 1
      simp [abs_of_pos hℓ]
    rw [Work.OneBodyKin.kinFT_bsWin hℓ u p, norm_mul, hexp, one_mul, norm_mul, hpow]
    exact mul_le_mul_of_nonneg_left hpf (by positivity)
  have hkin2 : ∀ p : ℝ³, ‖Submission.BoseGases.kinFT
      (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ)) p‖
      ≤ Submission.BoseGases.chiSup * A := by
    intro p
    refine le_trans (norm_integral_le_integral_norm (fun z : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        ((((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ)))) ?_
    have hpt : ∀ z : ℝ³, ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        ((((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ))‖ ≤ Submission.BoseGases.chiSup * ‖ψ z‖ := by
      intro z
      have hexp : ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      have hb1 : ‖((((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ))‖
          = |Work.BSKinetic.bsWin ℓ u z| := by simp
      have hb2 : ‖(((ψ z : ℝ)) : ℂ)‖ = |ψ z| := by simp
      rw [norm_mul, hexp, one_mul, norm_mul, hb1, hb2, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (Work.BSKinetic.abs_bsWin_le ℓ u z) (abs_nonneg _)
    have hInt : Integrable (fun z : ℝ³ => Submission.BoseGases.chiSup * ‖ψ z‖) := hψint.const_mul _
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => norm_nonneg _)) hInt
      (Filter.Eventually.of_forall hpt)) ?_
    rw [integral_const_mul, ← hA]
  have hpt : ∀ p : ℝ³, ‖F ‖p‖ * (Submission.BoseGases.kinFT
        (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ)) p *
        star (Submission.BoseGases.kinFT
          (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ)) p)).re‖
      ≤ ‖F ‖p‖‖ * ((ℓ ^ 3 * Mχ) * (Submission.BoseGases.chiSup * A)) := by
    intro p
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (F ‖p‖))
    calc ‖(Submission.BoseGases.kinFT
            (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ)) p *
          star (Submission.BoseGases.kinFT
            (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ)) p)).re‖
        ≤ ‖Submission.BoseGases.kinFT
            (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ)) p *
          star (Submission.BoseGases.kinFT
            (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ)) p)‖ :=
          Complex.abs_re_le_norm _
      _ = ‖Submission.BoseGases.kinFT
            (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ)) p‖ *
          ‖Submission.BoseGases.kinFT
            (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ)) p‖ := by
          rw [norm_mul, norm_star]
      _ ≤ (ℓ ^ 3 * Mχ) * (Submission.BoseGases.chiSup * A) :=
          mul_le_mul (hkin1 p) (hkin2 p) (norm_nonneg _)
            (mul_nonneg (by positivity) hMχ0)
  have hIint : Integrable (fun p : ℝ³ => ‖F ‖p‖‖ * ((ℓ ^ 3 * Mχ) * (Submission.BoseGases.chiSup * A))) :=
    hFi.norm.mul_const _
  have hmain : ‖∫ p : ℝ³, F ‖p‖ * (Submission.BoseGases.kinFT
        (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ)) p *
        star (Submission.BoseGases.kinFT
          (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ)) p)).re‖
      ≤ ((ℓ ^ 3 * Mχ) * (Submission.BoseGases.chiSup * A)) * CF := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => norm_nonneg _)) hIint
      (Filter.Eventually.of_forall hpt)) ?_
    rw [integral_mul_const ((ℓ ^ 3 * Mχ) * (Submission.BoseGases.chiSup * A)) (fun p : ℝ³ => ‖F ‖p‖‖),
      ← hCF]
    exact le_of_eq (mul_comm _ _)
  rw [Work.OneBodyKin.bsPair, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹)]
  calc ((2 * Real.pi) ^ 3)⁻¹ * |∫ p : ℝ³, F ‖p‖ * (Submission.BoseGases.kinFT
        (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ)) p *
        star (Submission.BoseGases.kinFT
          (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ)) p)).re|
      = ((2 * Real.pi) ^ 3)⁻¹ * ‖∫ p : ℝ³, F ‖p‖ * (Submission.BoseGases.kinFT
        (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ)) p *
        star (Submission.BoseGases.kinFT
          (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ)) p)).re‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (((ℓ ^ 3 * Mχ) * (Submission.BoseGases.chiSup * A)) * CF) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 3 * Mχ) * (Submission.BoseGases.chiSup * A) * CF := by ring

/-! ## Vanishing of the cross form when the windowed state vanishes -/

private lemma bsPair_eq_zero_of_vanishing {ℓ : ℝ} {F : ℝ → ℝ} {u : ℝ³} {ψ : ℝ³ → ℝ}
    (h : ∀ z : ℝ³, Work.BSKinetic.bsWin ℓ u z * ψ z = 0) :
    Work.OneBodyKin.bsPair ℓ F u ψ = 0 := by
  have hfun : (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ))
      = fun _ => 0 := by
    funext z
    rw [← Complex.ofReal_mul, h z]
    simp
  have hk : ∀ p : ℝ³, Submission.BoseGases.kinFT
      (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z : ℝ)) : ℂ) * (ψ z : ℂ)) p = 0 := by
    intro p
    rw [hfun]
    simp [Submission.BoseGases.kinFT]
  rw [Work.OneBodyKin.bsPair]
  simp [hk]

/-! ## The three `u`-integrability statements -/

theorem integrable_u_pieces {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (hFnn : ∀ r : ℝ, 0 ≤ F r) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.bsOneBodyUnproj ℓ F u ψ) ∧
      MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.bsMean ℓ u ψ * Work.OneBodyKin.bsPair ℓ F u ψ) ∧
      MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 * Work.OneBodyKin.bsPair ℓ F u (fun _ => 1)) := by
  classical
  -- ## the far-field region: outside the ball of radius `Rfar` everything vanishes
  obtain ⟨R, hR0, hR⟩ := Work.BSKinetic.Decomp.exists_radius_eq_zero_of_hasCompactSupport hcs
  set Rfar : ℝ := (R + ℓ) / ℓ with hRfar
  have hfar_le : ∀ u : ℝ³, Rfar < ‖u‖ → R + ℓ ≤ ℓ * ‖u‖ := by
    intro u hu
    have h1 : ℓ * Rfar = R + ℓ := by rw [hRfar]; field_simp
    have h2 : ℓ * Rfar < ℓ * ‖u‖ := mul_lt_mul_of_pos_left hu hℓ
    linarith
  have hmean_far : ∀ u : ℝ³, Rfar < ‖u‖ → Work.BSKinetic.bsMean ℓ u ψ = 0 := fun u hu =>
    Work.BSKinetic.Decomp.bsMean_eq_zero_of_far hℓ hR (hfar_le u hu)
  have hvan : ∀ u : ℝ³, Rfar < ‖u‖ → ∀ z : ℝ³, Work.BSKinetic.bsWin ℓ u z * ψ z = 0 := by
    intro u hu z
    by_cases hz : Work.BSKinetic.bsWin ℓ u z = 0
    · rw [hz, zero_mul]
    · rw [hR z (Work.BSKinetic.Decomp.norm_ge_of_bsWin_ne_zero hℓ (hfar_le u hu) hz), mul_zero]
  -- ## a uniform bound `M` and the distance `Rfar` are all we need for the mean
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hψ.continuous
  have hMb : ∀ z : ℝ³, |ψ z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
  have haesmMean : AEStronglyMeasurable (fun u : ℝ³ => Work.BSKinetic.bsMean ℓ u ψ)
      (volume : Measure ℝ³) := aestronglyMeasurable_bsMean hψ.continuous
  -- ## piece 1: Fubini/Tonelli on the jointly integrable kernel pairing
  have hpiece1 : MeasureTheory.Integrable (fun u : ℝ³ => Work.BSKinetic.bsOneBodyUnproj ℓ F u ψ) := by
    set P : ℝ³ × (ℝ³ × ℝ³) → ℝ := fun w =>
      Work.BSKinetic.bsWin ℓ w.1 w.2.1 * ψ w.2.1 *
        (Submission.BoseGases.kinKernel F (w.2.1 - w.2.2) *
          (Work.BSKinetic.bsWin ℓ w.1 w.2.2 * ψ w.2.2)) with hP
    have hPint : MeasureTheory.Integrable P
        ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod (volume : Measure ℝ³))) := by
      rw [hP]
      exact Work.BSKinetic.integrable_bsFamUnprojJoint hℓ hFi ψ hψ hcs
    have hTon : MeasureTheory.Integrable
        (fun u : ℝ³ => ∫ w : ℝ³ × ℝ³, P (u, w) ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
        (volume : Measure ℝ³) := hPint.integral_prod_left
    refine hTon.congr (Filter.Eventually.of_forall (fun u => ?_))
    show (∫ w : ℝ³ × ℝ³, P (u, w) ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
        = Work.BSKinetic.bsOneBodyUnproj ℓ F u ψ
    have hsl : MeasureTheory.Integrable (fun w : ℝ³ × ℝ³ => P (u, w))
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
      rw [hP]
      exact Work.BSKinetic.integrable_bsFamUnprojSlice hℓ hFi ψ hψ hcs u
    rw [MeasureTheory.integral_prod (fun w : ℝ³ × ℝ³ => P (u, w)) hsl,
      Work.BSKinetic.bsOneBodyUnproj_eq_iterKernel hℓ hFi ψ hψ hcs u]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show (∫ y : ℝ³, P (u, (x, y))) =
      Work.BSKinetic.bsWin ℓ u x * ψ x *
        ∫ y : ℝ³, Submission.BoseGases.kinKernel F (x - y) * (Work.BSKinetic.bsWin ℓ u y * ψ y)
    simp only [hP]
    rw [MeasureTheory.integral_const_mul]
  -- ## piece 2: the mean times the cross form (cross form integrable + mean bounded)
  have hpiece2 : MeasureTheory.Integrable
      (fun u : ℝ³ => Work.BSKinetic.bsMean ℓ u ψ * Work.OneBodyKin.bsPair ℓ F u ψ) := by
    have haesmPair : AEStronglyMeasurable (fun u : ℝ³ => Work.OneBodyKin.bsPair ℓ F u ψ)
        (volume : Measure ℝ³) := aestronglyMeasurable_bsPair hℓ hFi hψ.continuous
    obtain ⟨Cp, hCp⟩ := abs_bsPair_le hℓ hFi hψ.continuous hcs
    have hsuppPair : ∃ K : Set ℝ³, IsCompact K ∧
        ∀ u : ℝ³, Work.OneBodyKin.bsPair ℓ F u ψ ≠ 0 → u ∈ K :=
      ⟨Metric.closedBall 0 Rfar, isCompact_closedBall _ _, fun u hu => by
        rw [Metric.mem_closedBall, dist_zero_right]
        by_contra hc
        push Not at hc
        exact hu (bsPair_eq_zero_of_vanishing (hvan u hc))⟩
    have hIntPair : MeasureTheory.Integrable (fun u : ℝ³ => Work.OneBodyKin.bsPair ℓ F u ψ) :=
      Work.BSKinetic.integrable_of_compact_support hsuppPair haesmPair ⟨Cp, hCp⟩
    refine (hIntPair.mul_bdd (c := M) haesmMean (Filter.Eventually.of_forall (fun u => ?_))).congr
      (Filter.Eventually.of_forall (fun u => mul_comm _ _))
    rw [Real.norm_eq_abs]
    exact Work.BSKinetic.abs_bsMean_le hℓ hMb u
  -- ## piece 3: the square of the mean times the constant `bsPair ℓ F u 1`
  have hpiece3 : MeasureTheory.Integrable
      (fun u : ℝ³ => (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 *
        Work.OneBodyKin.bsPair ℓ F u (fun _ => 1)) := by
    have hSq : MeasureTheory.Integrable (fun u : ℝ³ => (Work.BSKinetic.bsMean ℓ u ψ) ^ 2) := by
      refine Work.BSKinetic.integrable_of_compact_support ?_ (haesmMean.pow 2) ?_
      · refine ⟨Metric.closedBall 0 Rfar, isCompact_closedBall _ _, fun u hu => ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        by_contra hc
        push Not at hc
        exact hu (by rw [hmean_far u hc]; ring)
      · refine ⟨M ^ 2, fun u => ?_⟩
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs (Work.BSKinetic.bsMean ℓ u ψ)]
        exact pow_le_pow_left₀ (abs_nonneg _) (Work.BSKinetic.abs_bsMean_le hℓ hMb u) 2
    have hconst : (fun u : ℝ³ => (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 *
          Work.OneBodyKin.bsPair ℓ F u (fun _ => 1))
        = fun u : ℝ³ => (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 *
            (Work.OneBodyKin.symA ℓ F 0 * ℓ ^ 3) :=
      funext (fun u => by rw [Work.OneBodyKin.bsPair_const_eq hℓ hFi u])
    rw [hconst]
    exact hSq.mul_const _
  exact ⟨hpiece1, hpiece2, hpiece3⟩

end Work.OneBodyKin
