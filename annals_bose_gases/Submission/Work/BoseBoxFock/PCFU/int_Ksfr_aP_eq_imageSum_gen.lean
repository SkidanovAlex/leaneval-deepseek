import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseBoxFock.PCFU.int_Ksfr_aP_eq_imageSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.int_Ksfr_aP_eq_imageSum_gen`

**The `P_i`/`Q_j` slot split of the `s`-frame integral, at an arbitrary shift `b`.**

This is the sibling of `Work.BoseBoxFock.PCFU.int_Ksfr_aP_eq_imageSum`, in which the shift of the
frame is the *arbitrary* vector `b` rather than the slot value `x j`.  The proof is the same
argument: the pointwise `lowKer` form of the frame (`Ksfr_eq_lowKer`)

    ℓ³·Σ'_d Κ(u − b + ℓ•latVec d) = Ksfr(u − b) + 1

splits the slot mean `P_iΘ` off the fibre deviation `Q_j(P_iΘ)`; the two normalisation identities
`∫ Ksfr(· − b) = 0` (`integral_Ksfr_acube_eq_zero`, valid for *every* shift `b`) and
`ℓ³·P_j(P_iΘ) x = ∫_{acube ℓ} P_iΘ(x[j↦·])` (the definitional unfolding of `aP`) make the
constants cancel:

    ∫ Ksfr(·−b)·P_iΘ(x[j↦·]) = ℓ³∫ (Σ'_d Κ(·−b+ℓ•latVec d))·Q_j(P_iΘ)(x[j↦·]) .

Neither the *shift* `b` nor the *configuration* `x` enters the cancellation: `b` occurs only inside
the frame `u ↦ Ksfr(u − b)` and inside the lattice sum, and both normalisation identities are
shift-independent.  This is why the identical `core_identity` proof applies verbatim.

Everything here is `sorry`-free.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `P_iΞ` is measurable when `Ξ` is: the box mean is a parametric integral of the measurable
function `(x,y) ↦ Ξ(x[i↦y])`, hence strongly measurable in `x`. -/
private lemma measurable_aP_aux {N : ℕ} (ℓ : ℝ) (i : Fin N) {Ξ : Submission.BoseGases.X N → ℝ}
    (hΞm : Measurable Ξ) : Measurable (Submission.BoseGases.aP ℓ i Ξ) := by
  unfold Submission.BoseGases.aP
  refine Measurable.const_mul ?_ _
  have huncurry : StronglyMeasurable
      (fun p : Submission.BoseGases.X N × E3 => Ξ (Function.update p.1 i p.2)) :=
    (hΞm.comp (by fun_prop : Measurable
      (fun p : Submission.BoseGases.X N × E3 => Function.update p.1 i p.2))).stronglyMeasurable
  haveI : SFinite ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := inferInstance
  simpa using (huncurry.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).measurable

/-- **Global sup bound of the box mean**: if `|Ξ| ≤ B` *everywhere* then `|P_iΞ| ≤ B`
everywhere (no hypothesis on the box of the configuration is needed, since the mean of a function
bounded by `B` over the cube of volume `ℓ³` is again bounded by `B`). -/
private lemma aP_abs_le_global_aux {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Ξ : Submission.BoseGases.X N → ℝ} {B : ℝ} (hB : 0 ≤ B) (hΞ : ∀ x, |Ξ x| ≤ B) :
    ∀ x, |Submission.BoseGases.aP ℓ i Ξ x| ≤ B := by
  intro x
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
  have h1 : ‖∫ y, Ξ (Function.update x i y)
        ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))‖ ≤ B * ℓ ^ 3 := by
    have hb : ∀ᵐ y ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)),
        ‖Ξ (Function.update x i y)‖ ≤ B :=
      Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hΞ _
    have h := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (f := fun y => Ξ (Function.update x i y)) (C := B) hb
    rwa [Measure.real, Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)] at h
  unfold Submission.BoseGases.aP
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ℓ ^ 3)]
  calc (1 / ℓ ^ 3) * |∫ y, Ξ (Function.update x i y)
        ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))|
      ≤ (1 / ℓ ^ 3) * (B * ℓ ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.norm_eq_abs]; exact h1
    _ = B := by field_simp

/-- **Slot invariance of the box mean**: `P_iΞ` does not depend on the `i`-th coordinate, since
`update (update x i z) i y = update x i y`. -/
private lemma aP_update_eq_self {N : ℕ} (ℓ : ℝ) (i : Fin N)
    (Ξ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) (z : E3) :
    Submission.BoseGases.aP ℓ i Ξ (Function.update x i z) = Submission.BoseGases.aP ℓ i Ξ x := by
  simp only [Submission.BoseGases.aP]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [Function.update_idem]

/-- **The abstract cancellation.**  Let `Kc`, `Su`, `Pu` be functions on `ℝ³`, `c` a constant, and
`Qu := Pu − c`, related to `Kc` by `ℓ³·Su = Kc + 1` pointwise.  If the bounded slot functions are
integrable on a finite-measure set `s` and `∫_s Kc = 0`, `∫_s 1 = ℓ³`, `∫_s Pu = ℓ³c`, then

    ℓ³·∫_s Su·Qu = ∫_s Kc·Pu .

This is the *whole* arithmetic content of the `P_i`/`Q_j` slot split: the `+1` in `ℓ³Su` and the
`−c` in `Qu` cancel against the two normalisation identities `∫Kc = 0` and `∫Pu = ℓ³c`. -/
private lemma core_identity {ℓ : ℝ} {s : Set E3} {Kc Su Pu Qu : E3 → ℂ} {c : ℂ}
    (hs : MeasurableSet s)
    (hS : ∀ u, (ℓ : ℂ) ^ 3 * Su u = Kc u + 1)
    (hQ : ∀ u, Qu u = Pu u - c)
    (hKint : IntegrableOn Kc s volume)
    (hPint : IntegrableOn Pu s volume)
    (h1int : IntegrableOn (fun _ : E3 => (1 : ℂ)) s volume)
    (hKPint : IntegrableOn (fun u => Kc u * Pu u) s volume)
    (hK1Pint : IntegrableOn (fun u => (Kc u + 1) * Pu u) s volume)
    (hK1cint : IntegrableOn (fun u => (Kc u + 1) * c) s volume)
    (hK0 : ∫ u in s, Kc u = 0)
    (hone : ∫ u in s, (1 : ℂ) = (ℓ : ℂ) ^ 3)
    (hPval : ∫ u in s, Pu u = (ℓ : ℂ) ^ 3 * c) :
    (ℓ : ℂ) ^ 3 * ∫ u in s, Su u * Qu u = ∫ u in s, Kc u * Pu u := by
  have hstep1 : (ℓ : ℂ) ^ 3 * (∫ u in s, Su u * Qu u)
      = ∫ u in s, (ℓ : ℂ) ^ 3 * (Su u * Qu u) :=
    (MeasureTheory.integral_const_mul ((ℓ : ℂ) ^ 3) (fun u => Su u * Qu u)).symm
  have hstep2 : (∫ u in s, (ℓ : ℂ) ^ 3 * (Su u * Qu u))
      = ∫ u in s, (Kc u + 1) * Qu u := by
    refine MeasureTheory.setIntegral_congr_fun hs (fun u _ => ?_)
    rw [← mul_assoc, hS u]
  have hstep3 : (∫ u in s, (Kc u + 1) * Qu u)
      = ∫ u in s, (Kc u + 1) * (Pu u - c) := by
    refine MeasureTheory.setIntegral_congr_fun hs (fun u _ => ?_)
    rw [hQ u]
  have hstep4 : (∫ u in s, (Kc u + 1) * (Pu u - c))
      = ∫ u in s, ((Kc u + 1) * Pu u - (Kc u + 1) * c) := by
    refine MeasureTheory.setIntegral_congr_fun hs (fun u _ => ?_)
    ring
  have hstep5 : (∫ u in s, ((Kc u + 1) * Pu u - (Kc u + 1) * c))
      = (∫ u in s, (Kc u + 1) * Pu u) - ∫ u in s, (Kc u + 1) * c :=
    MeasureTheory.integral_sub hK1Pint hK1cint
  have hstep6a : (∫ u in s, (Kc u + 1) * Pu u)
      = (∫ u in s, Kc u * Pu u) + ∫ u in s, Pu u := by
    rw [show (∫ u in s, (Kc u + 1) * Pu u) = ∫ u in s, (Kc u * Pu u + Pu u) from
      MeasureTheory.setIntegral_congr_fun hs (fun u _ => by ring)]
    exact MeasureTheory.integral_add hKPint hPint
  have hstep6b : (∫ u in s, (Kc u + 1) * c) = (∫ u in s, (Kc u + 1)) * c :=
    MeasureTheory.integral_mul_const c (fun u => Kc u + 1)
  have hstep6c : (∫ u in s, (Kc u + 1)) = (∫ u in s, Kc u) + ∫ u in s, (1 : ℂ) :=
    MeasureTheory.integral_add hKint h1int
  rw [hstep1, hstep2, hstep3, hstep4, hstep5, hstep6a, hstep6b, hstep6c, hK0, hone, hPval]
  ring

theorem int_Ksfr_aP_eq_imageSum_gen {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ))
    {n : ℕ} (i j : Fin n) (b : EuclideanSpace ℝ (Fin 3))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (x : Submission.BoseGases.X n) :
    ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
        Work.BoseBoxFock.Ksfr v fc μ N (u - b)
          * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
              (Function.update x j u) : ℝ) : ℂ)
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
              (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                    (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                    (u - b + Work.BoseBoxFock.ellH v μ
                      • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                    (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                    (Function.update x j u) : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := hΘb
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (Θ 0)) (hC 0)
  have hψm : Measurable (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ) :=
    measurable_aP_aux (Work.BoseBoxFock.ellH v μ) i hΘm
  have hψb : ∀ y, |Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ y| ≤ C :=
    aP_abs_le_global_aux hℓ i hC0 (fun y => by simpa [Real.norm_eq_abs] using hC y)
  -- the vertical normalisation `∫_{acube ℓ} 1 = ℓ³`
  have hone : (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ), (1 : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3 := by
    rw [MeasureTheory.integral_const,
      Submission.BoseGases.real_volume_acube (Work.BoseBoxFock.ellH v μ) hℓ.le]
    simp
  have hKc_aesm : AEStronglyMeasurable
      (fun u : E3 => Work.BoseBoxFock.Ksfr v fc μ N (u - b))
      (volume.restrict (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))) :=
    ((continuous_Ksfr (v := v) (fc := fc) (μ := μ) (N := N)).comp
      (by fun_prop : Continuous (fun u : E3 => u - b))).aestronglyMeasurable
  have hBK0 : 0 ≤ (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        |Work.BoseBoxFock.fLh v fc μ N s|) := Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hInt_Kc : IntegrableOn (fun u : E3 => Work.BoseBoxFock.Ksfr v fc μ N (u - b))
      (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top _ hℓ.le) hKc_aesm
      (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        |Work.BoseBoxFock.fLh v fc μ N s|)
      (Filter.Eventually.of_forall (fun u => norm_Ksfr_le (u - b)))
  have hPu_aesm : AEStronglyMeasurable
      (fun u : E3 => ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
        (Function.update x j u) : ℝ) : ℂ))
      (volume.restrict (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))) :=
    (Complex.continuous_ofReal.measurable.comp
        (hψm.comp (by fun_prop : Measurable
          (fun u : E3 => Function.update x j u)))).aestronglyMeasurable
  have hInt_Pu : IntegrableOn (fun u : E3 => ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
        (Function.update x j u) : ℝ) : ℂ))
      (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top _ hℓ.le) hPu_aesm C
      (Filter.Eventually.of_forall (fun u => by simpa using hψb (Function.update x j u)))
  have hInt_one : IntegrableOn (fun _ : E3 => (1 : ℂ))
      (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top _ hℓ.le) aestronglyMeasurable_const 1
      (Filter.Eventually.of_forall (fun _ => by simp))
  have hInt_KcPu : IntegrableOn (fun u : E3 => Work.BoseBoxFock.Ksfr v fc μ N (u - b)
        * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
            (Function.update x j u) : ℝ) : ℂ))
      (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top _ hℓ.le) (hKc_aesm.mul hPu_aesm)
      ((∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        |Work.BoseBoxFock.fLh v fc μ N s|) * C)
      (Filter.Eventually.of_forall (fun u => by
        rw [norm_mul]
        exact mul_le_mul (norm_Ksfr_le (u - b))
          (by simpa using hψb (Function.update x j u)) (norm_nonneg _) hBK0))
  have hInt_Kc1 : IntegrableOn (fun u : E3 => Work.BoseBoxFock.Ksfr v fc μ N (u - b) + 1)
      (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top _ hℓ.le)
      (hKc_aesm.add aestronglyMeasurable_const)
      ((∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        |Work.BoseBoxFock.fLh v fc μ N s|) + 1)
      (Filter.Eventually.of_forall (fun u =>
        le_trans (norm_add_le _ _) (add_le_add (norm_Ksfr_le (u - b)) (by simp))))
  have hInt_Kc1Pu : IntegrableOn (fun u : E3 => (Work.BoseBoxFock.Ksfr v fc μ N (u - b) + 1)
        * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
            (Function.update x j u) : ℝ) : ℂ))
      (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top _ hℓ.le)
      ((hKc_aesm.add aestronglyMeasurable_const).mul hPu_aesm)
      (((∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        |Work.BoseBoxFock.fLh v fc μ N s|) + 1) * C)
      (Filter.Eventually.of_forall (fun u => by
        rw [norm_mul]
        refine mul_le_mul ?_ (by simpa using hψb (Function.update x j u)) (norm_nonneg _) ?_
        · exact le_trans (norm_add_le _ _) (add_le_add (norm_Ksfr_le (u - b)) (by simp))
        · positivity))
  have hInt_Kc1c : IntegrableOn (fun u : E3 => (Work.BoseBoxFock.Ksfr v fc μ N (u - b) + 1)
        * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) j
            (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ) x : ℝ) : ℂ))
      (Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ)) volume :=
    hInt_Kc1.mul_const _
  -- the pointwise `lowKer` form of the frame (`Ksfr_eq_lowKer`)
  have hS_eq : ∀ u : E3, (Work.BoseBoxFock.ellH v μ : ℂ) ^ 3
        * (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
              (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
              (u - b + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = Work.BoseBoxFock.Ksfr v fc μ N (u - b) + 1 := by
    intro u
    rw [Ksfr_eq_lowKer (v := v) (fc := fc) (μ := μ) (N := N) hℓ hκ hN (u - b)]
    ring
  -- the fibre deviation in the slot `j` splits off the (slot-`j`-invariant) mean
  have hQ_eq : ∀ u : E3, ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
          (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
          (Function.update x j u) : ℝ) : ℂ)
        = ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
              (Function.update x j u) : ℝ) : ℂ)
          - ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) j
              (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ) x : ℝ) : ℂ) := by
    intro u
    simp only [Submission.BoseGases.aQ, Complex.ofReal_sub, aP_update_eq_self]
  have hK0 : (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
      Work.BoseBoxFock.Ksfr v fc μ N (u - b)) = 0 :=
    integral_Ksfr_acube_eq_zero (v := v) (fc := fc) (μ := μ) (N := N) b
  -- the definitional unfolding of the slot mean `aP`
  have hPval : (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
        ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
          (Function.update x j u) : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
        * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) j
            (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ) x : ℝ) : ℂ) :=
    (ofReal_pow_mul_aP_eq_integral hℓ j
      (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ) x).symm
  exact (core_identity (ℓ := Work.BoseBoxFock.ellH v μ)
    (s := Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ))
    (Kc := fun u : E3 => Work.BoseBoxFock.Ksfr v fc μ N (u - b))
    (Su := fun u : E3 => ∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
        (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
        (u - b + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
    (Pu := fun u : E3 => ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
        (Function.update x j u) : ℝ) : ℂ))
    (Qu := fun u : E3 => ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
        (Function.update x j u) : ℝ) : ℂ))
    (c := ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) j
        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ) x : ℝ) : ℂ))
    (Submission.BoseGases.acube_measurable _) hS_eq hQ_eq hInt_Kc hInt_Pu hInt_one hInt_KcPu
    hInt_Kc1Pu hInt_Kc1c hK0 hone hPval).symm

end Work.BoseBoxFock.PCFU
