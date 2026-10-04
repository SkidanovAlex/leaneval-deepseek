import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_mul_pd_eq_neg
import Submission.Work.Diff.STE.fourierCoeff_iterate_pd
import Submission.Work.Diff.STE.Lead.GalTame.tendstoIntegralRpowAddSq
import Submission.Work.Diff.STE.Lead.GalTame.regularisedFieldSmooth
import Submission.Work.Diff.STE.Lead.GalTame.regularisedFieldPdBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp periodic integration by parts with a real power (clean assembly)

`ibpComplexSharp` is the integration-by-parts input of Nirenberg's proof of the sharp
Gagliardo–Nirenberg inequality on the torus:

  `∫_{cube} ‖∂ᵢ g‖^p ≤ (p-1) ∫_{cube} ‖g‖ · ‖∂ᵢ g‖^{p-2} · ‖∂ᵢ∂ᵢ g‖`  for `p ≥ 2`.

The proof is the `ε`-regularisation argument: the field `F_ε = (‖∂ᵢg‖²+ε²)^((p-2)/2) • conj(∂ᵢg)`
is smooth and periodic (`regularisedFieldSmooth`), the periodic integration by parts
`integral_mul_pd_eq_neg` gives `∫ F_ε ∂ᵢg = -∫ (∂ᵢF_ε) g`, the pointwise bound
`regularisedFieldPdBound` bounds `‖∂ᵢF_ε‖`, and the limit `ε → 0⁺` is
`tendstoIntegralRpowAddSq`.
-/

noncomputable section

namespace Work.Diff.STE.Lead.GalTame.ResidGn

open MeasureTheory BigOperators
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A continuous real function is integrable on the (bounded) unit cube. -/
private lemma integrableOn_unitCube_of_continuous_real {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : Work.Diff.STE.unitCube (ι := ι)
      ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hF.continuousOn).mono_set hsub

/-- `(a^2)^((p-2)/2) * a^2 = a^p` for `a ≥ 0` and `p ≥ 2`. -/
private lemma sq_rpow_mul_sq {a p : ℝ} (ha : 0 ≤ a) (hp : 2 ≤ p) :
    (a ^ 2) ^ ((p - 2) / 2) * a ^ 2 = a ^ p := by
  rw [← Real.rpow_natCast a 2, Nat.cast_ofNat, ← Real.rpow_mul ha 2 ((p - 2) / 2),
    ← Real.rpow_add' ha (by linarith : 2 * ((p - 2) / 2) + 2 ≠ 0)]
  congr 1
  ring

theorem ibpComplexSharpR (i : ι) (p : ℝ) (hp : 2 ≤ p) (g : (ι → ℝ) → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Work.Diff.STE.Periodic1 g) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i g x‖ ^ p
      ≤ (p - 1) * ∫ x in Work.Diff.STE.unitCube (ι := ι),
          ‖g x‖ * ‖Work.Diff.STE.pd i g x‖ ^ (p - 2)
            * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖ := by
  have hs : (0 : ℝ) ≤ (p - 2) / 2 := by linarith
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hgper : Work.Diff.STE.PeriodicIn i g := fun x => hper i x
  have hw : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i g) :=
    Work.Diff.STE.contDiff_pd_of_contDiff_top hg
  have hwper : Work.Diff.STE.PeriodicIn i (Work.Diff.STE.pd i g) :=
    Work.Diff.STE.periodicIn_pd hgper
  have hW : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i (Work.Diff.STE.pd i g)) :=
    Work.Diff.STE.contDiff_pd_of_contDiff_top hw
  -- ## the `ε`-regularised inequality
  have key : ∀ ε : ℝ, 0 < ε →
      (∫ x in Work.Diff.STE.unitCube,
          ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
            * ‖Work.Diff.STE.pd i g x‖ ^ 2)
        ≤ (p - 1) * ∫ x in Work.Diff.STE.unitCube,
            ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * (‖g x‖ * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖) := by
    intro ε hε
    have hFsm : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ι → ℝ => ((‖Work.Diff.STE.pd i g y‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
          • (starRingEnd ℂ) (Work.Diff.STE.pd i g y)) :=
      (regularisedFieldSmooth (ι := ι) i ((p - 2) / 2) ε hε
        (Work.Diff.STE.pd i g) hw hwper).1
    have hFper : Work.Diff.STE.PeriodicIn i
        (fun y : ι → ℝ => ((‖Work.Diff.STE.pd i g y‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
          • (starRingEnd ℂ) (Work.Diff.STE.pd i g y)) :=
      (regularisedFieldSmooth (ι := ι) i ((p - 2) / 2) ε hε
        (Work.Diff.STE.pd i g) hw hwper).2
    set F : (ι → ℝ) → ℂ :=
      (fun y : ι → ℝ => ((‖Work.Diff.STE.pd i g y‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
        • (starRingEnd ℂ) (Work.Diff.STE.pd i g y)) with hFdef
    have hF1 : ContDiff ℝ 1 F := by rw [hFdef]; exact hFsm.of_le (by norm_num)
    have hFper' : Work.Diff.STE.PeriodicIn i F := by rw [hFdef]; exact hFper
    have hIBP : (∫ x in Work.Diff.STE.unitCube, F x * Work.Diff.STE.pd i g x)
        = - ∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pd i F x * g x :=
      Work.Diff.STE.integral_mul_pd_eq_neg i F g hF1 hg1 hFper' hgper
    have hpt : ∀ x : ι → ℝ, F x * Work.Diff.STE.pd i g x
        = ↑((((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
            * ‖Work.Diff.STE.pd i g x‖ ^ 2 : ℝ)) := by
      intro x
      have hFx : F x = ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
          • (starRingEnd ℂ) (Work.Diff.STE.pd i g x) := by rw [hFdef]
      rw [hFx, Complex.real_smul, mul_assoc, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
    have hInt : (∫ x in Work.Diff.STE.unitCube, F x * Work.Diff.STE.pd i g x)
        = ↑(∫ x in Work.Diff.STE.unitCube,
            ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * ‖Work.Diff.STE.pd i g x‖ ^ 2) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact integral_ofReal
    have hZeq : (↑(∫ x in Work.Diff.STE.unitCube,
            ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * ‖Work.Diff.STE.pd i g x‖ ^ 2) : ℂ)
        = - ∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pd i F x * g x := by
      rw [← hInt, hIBP]
    have hre : (∫ x in Work.Diff.STE.unitCube,
            ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * ‖Work.Diff.STE.pd i g x‖ ^ 2)
        = -(∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pd i F x * g x).re := by
      have h := congrArg Complex.re hZeq
      simpa using h
    -- ## Step 1 : move the derivative onto `g`
    have hstep1 : (∫ x in Work.Diff.STE.unitCube,
            ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * ‖Work.Diff.STE.pd i g x‖ ^ 2)
        ≤ ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x‖ * ‖g x‖ := by
      have hnorm : ‖∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pd i F x * g x‖
          ≤ ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x * g x‖ :=
        MeasureTheory.norm_integral_le_integral_norm
          (fun x : ι → ℝ => Work.Diff.STE.pd i F x * g x)
      have hcongr : (∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x * g x‖)
          = ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x‖ * ‖g x‖ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => norm_mul _ _))
      calc (∫ x in Work.Diff.STE.unitCube,
              ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
                * ‖Work.Diff.STE.pd i g x‖ ^ 2)
          = -(∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pd i F x * g x).re := hre
        _ ≤ ‖∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pd i F x * g x‖ := by
            have h2 := Complex.re_le_norm (-(∫ x in Work.Diff.STE.unitCube,
              Work.Diff.STE.pd i F x * g x))
            simpa using h2
        _ ≤ ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x * g x‖ := hnorm
        _ = ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x‖ * ‖g x‖ := hcongr
    -- ## Step 2 : the pointwise bound
    have hstep2 : (∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x‖ * ‖g x‖)
        ≤ (p - 1) * ∫ x in Work.Diff.STE.unitCube,
            ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * (‖g x‖ * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖) := by
      have hpt2 : ∀ x : ι → ℝ, ‖Work.Diff.STE.pd i F x‖ * ‖g x‖
          ≤ (p - 1) * (((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * (‖g x‖ * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖)) := by
        intro x
        have hB : ‖Work.Diff.STE.pd i F x‖
            ≤ (p - 1) * ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖ := by
          rw [hFdef]
          exact Work.Diff.STE.Lead.GalTame.regularisedFieldPdBound (ι := ι) i p hp ε hε (Work.Diff.STE.pd i g) hw x
        calc ‖Work.Diff.STE.pd i F x‖ * ‖g x‖
            ≤ ((p - 1) * ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
                * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖) * ‖g x‖ :=
              mul_le_mul_of_nonneg_right hB (norm_nonneg _)
          _ = (p - 1) * (((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
                * (‖g x‖ * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖)) := by ring
      have hθc : Continuous (fun x : ι → ℝ =>
          (‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2)) :=
        (Real.continuous_rpow_const hs).comp
          (((hw.continuous.norm).pow 2).add continuous_const)
      have hint1 : Integrable (fun x : ι → ℝ => ‖Work.Diff.STE.pd i F x‖ * ‖g x‖)
          (volume.restrict Work.Diff.STE.unitCube) :=
        integrableOn_unitCube_of_continuous_real
          (((Work.Diff.STE.continuous_pd hF1 i).norm).mul hg.continuous.norm)
      have hint2 : Integrable (fun x : ι → ℝ =>
            (p - 1) * (((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * (‖g x‖ * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖)))
          (volume.restrict Work.Diff.STE.unitCube) :=
        integrableOn_unitCube_of_continuous_real
          (continuous_const.mul (hθc.mul (hg.continuous.norm.mul hW.continuous.norm)))
      have hmono := MeasureTheory.integral_mono_ae hint1 hint2
        (Filter.Eventually.of_forall hpt2)
      have hconst : (∫ x in Work.Diff.STE.unitCube,
            (p - 1) * (((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * (‖g x‖ * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖)))
          = (p - 1) * ∫ x in Work.Diff.STE.unitCube,
              ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
                * (‖g x‖ * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖) :=
        MeasureTheory.integral_const_mul (p - 1) _
      rw [hconst] at hmono
      exact hmono
    calc (∫ x in Work.Diff.STE.unitCube,
            ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * ‖Work.Diff.STE.pd i g x‖ ^ 2)
        ≤ ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x‖ * ‖g x‖ := hstep1
      _ ≤ (p - 1) * ∫ x in Work.Diff.STE.unitCube,
            ((‖Work.Diff.STE.pd i g x‖ ^ 2 + ε ^ 2) ^ ((p - 2) / 2))
              * (‖g x‖ * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖) := hstep2
  -- ## the limits `ε → 0⁺`
  have hlimA : Filter.Tendsto
      (fun n : ℕ => ∫ x in Work.Diff.STE.unitCube,
        ((‖Work.Diff.STE.pd i g x‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) ^ ((p - 2) / 2))
          * ‖Work.Diff.STE.pd i g x‖ ^ 2)
      Filter.atTop
      (nhds (∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i g x‖ ^ p)) := by
    have h := tendstoIntegralRpowAddSq (ι := ι) ((p - 2) / 2) hs
      (fun x : ι → ℝ => ‖Work.Diff.STE.pd i g x‖ ^ 2)
      (fun x : ι → ℝ => ‖Work.Diff.STE.pd i g x‖ ^ 2)
      ((hw.continuous.norm).pow 2) ((hw.continuous.norm).pow 2)
      (fun x => sq_nonneg _) (fun x => sq_nonneg _)
    have h2 : (∫ x in Work.Diff.STE.unitCube,
          (‖Work.Diff.STE.pd i g x‖ ^ 2) ^ ((p - 2) / 2) * ‖Work.Diff.STE.pd i g x‖ ^ 2)
        = ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i g x‖ ^ p := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      exact sq_rpow_mul_sq (norm_nonneg _) hp
    rw [h2] at h
    exact h
  have hlimB : Filter.Tendsto
      (fun n : ℕ => (p - 1) * ∫ x in Work.Diff.STE.unitCube,
        ((‖Work.Diff.STE.pd i g x‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) ^ ((p - 2) / 2))
          * (‖g x‖ * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖))
      Filter.atTop
      (nhds ((p - 1) * ∫ x in Work.Diff.STE.unitCube,
        ‖g x‖ * ‖Work.Diff.STE.pd i g x‖ ^ (p - 2)
          * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖)) := by
    have h := tendstoIntegralRpowAddSq (ι := ι) ((p - 2) / 2) hs
      (fun x : ι → ℝ => ‖Work.Diff.STE.pd i g x‖ ^ 2)
      (fun x : ι → ℝ => ‖g x‖ * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖)
      ((hw.continuous.norm).pow 2) (hg.continuous.norm.mul hW.continuous.norm)
      (fun x => sq_nonneg _) (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have h2 : (∫ x in Work.Diff.STE.unitCube,
          (‖Work.Diff.STE.pd i g x‖ ^ 2) ^ ((p - 2) / 2)
            * (‖g x‖ * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖))
        = ∫ x in Work.Diff.STE.unitCube,
            ‖g x‖ * ‖Work.Diff.STE.pd i g x‖ ^ (p - 2)
              * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      have h3 : (‖Work.Diff.STE.pd i g x‖ ^ 2) ^ ((p - 2) / 2)
          = ‖Work.Diff.STE.pd i g x‖ ^ (p - 2) := by
        rw [← Real.rpow_natCast (‖Work.Diff.STE.pd i g x‖) 2, Nat.cast_ofNat,
          ← Real.rpow_mul (norm_nonneg _) 2 ((p - 2) / 2)]
        congr 1
        ring
      rw [h3]
      ring
    rw [h2] at h
    have hc := h.const_mul (p - 1)
    exact hc
  refine le_of_tendsto_of_tendsto' hlimA hlimB (fun n => ?_)
  exact key (1 / ((n : ℝ) + 1)) (by positivity)

end Work.Diff.STE.Lead.GalTame.ResidGn
