import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.abs_wSmallPair_le
import Submission.Work.BoseFixB1.aesm_wSmallPair_pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.integrableOn_wSmallPair_cube_fixed`

Companion to `Submission/Work/BoseFixB1/integrableOn_wSmallPair_cube.lean`.

The statement **as requested** for `Work.BoseFixB1.integrableOn_wSmallPair_cube` used `R0` in the
hypothesis `hfsupp` *before* the binder group `{ℓ d R0 : ℝ}`.  With the workspace's
`autoImplicit = false` (lakefile `[leanOptions]`) that is a hard error (`Unknown identifier R0`),
so the requested declaration cannot be elaborated at all; with `autoImplicit = true` (the way the
request was accepted) it silently elaborates to a *different* statement in which `hfsupp`'s `R0`
is a second, implicit variable, decoupled from the radius constrained by `hR`/`hRχ` — i.e. the
dilute-regime content is lost (the pointwise bound `abs_wSmallPair_le`, which is the only available
control of the kernel, needs the support hypothesis with the *same* radius as `hR`).

This module carries the **intended** statement (a single radius `R0`, pulled out as an implicit
binder immediately before `hfsupp`, so the explicit hypothesis order is exactly the requested one)
and its complete proof, under the name
`Work.BoseFixB1.integrableOn_wSmallPair_cube_fixed`.

The content is the same as in the companion file: `|wSmallPair| ≤ C·|f(x−y)|` with a constant `C`
(`abs_wSmallPair_le_const_fixed`), `|f(x−y)|` is integrable over the product of two finite
Lebesgue restrictions (`integrable_comp_sub_prod_fixed`), and `Integrable.mono'` finishes, using
`aesm_wSmallPair_prod_full` for a.e. strong measurability.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Product integrability of the difference profile**, `_fixed` copy (see the module header). -/
theorem integrable_comp_sub_prod_fixed {f : ℝ³ → ℝ} (hf : MeasureTheory.Integrable f)
    {s t : Set ℝ³}
    (hs : (MeasureTheory.volume : MeasureTheory.Measure ℝ³) s < ⊤)
    (ht : (MeasureTheory.volume : MeasureTheory.Measure ℝ³) t < ⊤) :
    MeasureTheory.Integrable (fun p : ℝ³ × ℝ³ => f (p.1 - p.2))
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict s).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict t)) := by
  haveI hfin_t : IsFiniteMeasure ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict t) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact ht⟩
  haveI hfin_s : IsFiniteMeasure ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hs⟩
  have hqmp : Measure.QuasiMeasurePreserving (fun p : ℝ³ × ℝ³ => p.1 - p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ³))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ³) :=
    quasiMeasurePreserving_sub_of_right_invariant _ _
  have hmeasFull : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => f (p.1 - p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ³)) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  have hle : ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict s).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict t)
      ≤ (MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ³) :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hmeas : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => f (p.1 - p.2))
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict s).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict t)) :=
    hmeasFull.mono_measure hle
  refine (integrable_prod_iff (f := fun p : ℝ³ × ℝ³ => f (p.1 - p.2)) hmeas).2 ⟨?_, ?_⟩
  · refine ae_of_all _ (fun x => ?_)
    have h1 : MeasureTheory.Integrable (fun y : ℝ³ => f (x - y))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ³) :=
      ((Submission.BoseGases.measurePreserving_sub_left x).integrable_comp
        (g := f) hf.aestronglyMeasurable).2 hf
    exact h1.mono_measure Measure.restrict_le_self
  · have hsm : AEStronglyMeasurable
        (fun x : ℝ³ => ∫ y, ‖f (x - y)‖
          ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict t))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict s) :=
      hmeas.norm.integral_prod_right'
    have hbound : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict s),
        ‖∫ y, ‖f (x - y)‖ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict t)‖
          ≤ ∫ z : ℝ³, |f z| := by
      refine ae_of_all _ (fun x => ?_)
      have h1vol : MeasureTheory.Integrable (fun y : ℝ³ => |f (x - y)|)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ³) :=
        (((Submission.BoseGases.measurePreserving_sub_left x).integrable_comp
          (g := f) hf.aestronglyMeasurable).2 hf).abs
      have hstep1 : (∫ y : ℝ³, |f (x - y)|
            ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict t))
          ≤ ∫ y : ℝ³, |f (x - y)| :=
        setIntegral_le_integral h1vol (ae_of_all _ (fun y => abs_nonneg _))
      have hstep2 : (∫ y : ℝ³, |f (x - y)|) = ∫ z : ℝ³, |f z| :=
        Submission.BoseGases.integral_comp_sub_left (fun z : ℝ³ => |f z|) x
      have hnonneg : 0 ≤ ∫ y, ‖f (x - y)‖
          ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict t) :=
        integral_nonneg (fun y => norm_nonneg _)
      rw [Real.norm_of_nonneg hnonneg]
      calc (∫ y, ‖f (x - y)‖ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict t))
          = (∫ y, |f (x - y)|
              ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict t)) := by
            simp only [Real.norm_eq_abs]
        _ ≤ ∫ y, |f (x - y)| := hstep1
        _ = ∫ z, |f z| := hstep2
    exact Integrable.of_bound hsm _ hbound

/-- **Constant pointwise bound**, `_fixed` copy (see the module header). -/
lemma abs_wSmallPair_le_const_fixed {M : ℕ} (hM : 1 ≤ M) {ℓ d R0 : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {f : ℝ³ → ℝ}
    (hfsupp : ∀ z : ℝ³, R0 ≤ ‖z‖ → f z = 0)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u x y : ℝ³) :
    |Submission.BoseGases.wSmallPair M ℓ d u f x y| ≤
      ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) *
        ((2 / Work.SmallBoxSliding.smallConvLower M) *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M))) * |f (x - y)| := by
  have hdecay : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
      ≤ Submission.BoseGases.chiSmallDecay M := by
    have hb := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • x - u)
    rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb
  have hsup : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  have hdecay0 : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmallDecay_nonneg M
  have hsc : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hBnn : 0 ≤ (2 / Work.SmallBoxSliding.smallConvLower M) *
      (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :=
    mul_nonneg (div_nonneg (by norm_num) hsc.le) (mul_nonneg hsup hdecay0)
  have hstep := abs_wSmallPair_le (M := M) hM hℓ hd hfsupp hR hRχ u x y
  refine le_trans hstep ?_
  have h2 : (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
      * ((2 / Work.SmallBoxSliding.smallConvLower M)
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * |f (x - y)|)
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * ((2 / Work.SmallBoxSliding.smallConvLower M)
            * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * |f (x - y)|) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay hsup)
      (mul_nonneg hBnn (abs_nonneg _))
  refine le_trans h2 (le_of_eq ?_)
  ring

/-- **The intended statement** (single radius `R0`): the localised two-body kernel is integrable
on the product of two centred cubes in the dilute small-box regime. -/
theorem integrableOn_wSmallPair_cube_fixed {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfint : MeasureTheory.Integrable f)
    {R0 : ℝ}
    (hfsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → f z = 0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u f p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) := by
  have hAfin : (MeasureTheory.volume : MeasureTheory.Measure ℝ³)
      (Submission.BoseGases.acube ℓ) < ⊤ :=
    Submission.BoseGases.acube_lt_top ℓ (le_of_lt hℓ)
  have hdom : MeasureTheory.Integrable (fun p : ℝ³ × ℝ³ =>
      ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) *
        ((2 / Work.SmallBoxSliding.smallConvLower M) *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)))
        * |f (p.1 - p.2)|)
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
          (Submission.BoseGases.acube ℓ))) :=
    (integrable_comp_sub_prod_fixed hfint.abs hAfin hAfin).const_mul _
  have haesm : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.wSmallPair M ℓ d u f p.1 p.2)
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
          (Submission.BoseGases.acube ℓ))) :=
    (aesm_wSmallPair_prod_full (M := M) (ℓ := ℓ) (d := d) u hfint.aemeasurable).mono_measure
      (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.wSmallPair M ℓ d u f p.1 p.2)
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
          (Submission.BoseGases.acube ℓ))) := by
    refine hdom.mono' haesm (ae_of_all _ (fun p => ?_))
    rw [Real.norm_eq_abs]
    exact abs_wSmallPair_le_const_fixed (M := M) hM hℓ hd hfsupp hR hRχ u p.1 p.2
  rw [MeasureTheory.IntegrableOn]
  rw [Measure.volume_eq_prod ℝ³ ℝ³, ← Measure.prod_restrict]
  exact hInt

end Work.BoseFixB1
