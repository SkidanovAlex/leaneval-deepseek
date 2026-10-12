import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.chiChiCoulAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.psiM_pairing` — the `χχ`-pairing as a single `ψ_m`-integral

The lemma of the `L¹`-weight-tail chapter (design `sources/boseDCF/bose_L1tails.md`, the `T7`
route) which rewrites the localised two-body pairing

  `∫_w∈B ∫_y∈B χ_ℓ(w) χ_ℓ(y) W(w − y + ℓ•m) G w y`

into the pairing of `W` against the **`y`-fold** `ψ_m`

  `∫_z W(z) ψ_m(z)`,   `ψ_m(z) = ∫_{‖y‖≤ℓ/2} χ_ℓ(y) χ_ℓ(z + y − ℓ•m) G(z + y − ℓ•m) y dy`.

## Proof

Everything is the change of variables `z = w − y + ℓ•m` plus Fubini.  Concretely, with
`a = ℓ•latVec m`, `χ = chiScale ℓ` the two sides are both equal to the **product integral**

  `∫ p : E³ × E³, χ p.1 · χ p.2 · W(p.1 − p.2 + a) · G p.1 p.2`  (`pairF`),

because

* the `(w,y)`-domain `boxL ℓ × boxL ℓ` may be replaced by all of `E³ × E³` — the integrand
  vanishes whenever `χ w = 0` or `χ y = 0`, i.e. off `halfBall ℓ ⊆ boxL ℓ` (`pairing_left`);
* the substitution `(z,y) ↦ (z + y − a, y)` is the measure preserving shear `pairShear a`
  of `E³ × E³` (`measurePreserving_add_prod` composed with a translation), so
  `∫∫ W(z) χ(y) χ(z+y−a) G(z+y−a,y) = ∫∫ χ(w) χ(y) W(w−y+a) G w y` (`pairing_right`).

Both Fubini steps need the integrability of the two integrands; the `H`-shaped one
(`pairH`, with the weight on the *first* variable) is dominated by
`(chiSupAbs · sup‖G‖)·(‖W p.1‖ · χ p.2)`, a product of two integrable functions
(`Integrable.mul_prod`), and `pairF` is its shear pull-back
(`MeasurePreserving.integrable_comp_of_integrable`).

Nothing in the proof needs the hypotheses `hm : m ≠ 0` and `hWs` (the support of `W`); only
`hℓ : 0 < ℓ` is used — through `χ_ℓ(x) = 0` for `‖x‖ > ℓ/2` and `halfBall ℓ ⊆ boxL ℓ`, which both
fail at `ℓ ≤ 0`.  The smoothness of `G` is used only through its continuity (boundedness on the
compact `halfBall ℓ × halfBall ℓ`).
-/

noncomputable section

open MeasureTheory
open scoped Real Topology

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1. The window `chiScale ℓ` -/

/-- The scaled bump is nonnegative. -/
private lemma chiScale_nonneg (ℓ : ℝ) (x : E3) : 0 ≤ Submission.BoseGases.chiScale ℓ x :=
  Submission.BoseGases.chi_nonneg _

/-- The scaled bump vanishes outside the closed ball of radius `ℓ/2`. -/
private lemma chiScale_eq_zero_of_norm_gt {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : ℓ / 2 < ‖x‖) :
    Submission.BoseGases.chiScale ℓ x = 0 := by
  rw [Submission.BoseGases.chiScale]
  apply Submission.BoseGases.chi_eq_zero_of_norm_gt
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ℓ⁻¹), inv_mul_eq_div,
    lt_div_iff₀ (by linarith : (0:ℝ) < ℓ)]
  linarith

/-- Contrapositive form: a nonvanishing value of the window forces the point into `halfBall ℓ`. -/
private lemma chiScale_ne_zero_norm_le {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : Submission.BoseGases.chiScale ℓ x ≠ 0) : ‖x‖ ≤ ℓ / 2 := by
  by_contra h
  exact hx (chiScale_eq_zero_of_norm_gt hℓ (lt_of_not_ge h))

/-- Membership in `halfBall ℓ` is the norm bound `‖x‖ ≤ ℓ/2`. -/
private lemma halfBall_mem_iff {ℓ : ℝ} {x : E3} : x ∈ halfBall ℓ ↔ ‖x‖ ≤ ℓ / 2 := by
  rw [halfBall, Metric.mem_closedBall, dist_eq_norm, sub_zero]

/-- The norm of a real number coerced into `ℂ`. -/
private lemma norm_ofReal_c (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- `boxL ℓ` is closed. -/
private lemma isClosed_boxL {ℓ : ℝ} (hℓ : ℓ ≠ 0) : IsClosed (Work.BoseK15.corpusBox.boxL ℓ) := by
  have h : Work.BoseK15.corpusBox.boxL ℓ
      = (fun x : E3 => ℓ⁻¹ • x) ⁻¹' Work.BoseB4.unitCell := by
    ext x
    simp only [Work.BoseB4.BoxData.boxL, Set.mem_smul_set, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [inv_smul_smul₀ hℓ]
      exact hy
    · intro hx
      exact ⟨ℓ⁻¹ • x, hx, by rw [smul_inv_smul₀ hℓ]⟩
  rw [h]
  exact Work.BoseB4.isClosed_unitCell.preimage (continuous_const_smul ℓ⁻¹)

/-- `boxL ℓ` is measurable. -/
private lemma measurableSet_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
  (isClosed_boxL (ne_of_gt hℓ)).measurableSet

/-- `halfBall ℓ` is measurable. -/
private lemma measurableSet_halfBall (ℓ : ℝ) : MeasurableSet (halfBall ℓ) := by
  rw [halfBall]
  exact Metric.isClosed_closedBall.measurableSet

/-- `boxL ℓ` as the cube `{x | ∀ i, |x i| ≤ ℓ/2}`. -/
private lemma boxL_eq_setOf {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.BoseK15.corpusBox.boxL ℓ = {x : E3 | ∀ i, |x i| ≤ ℓ / 2} := by
  ext x
  rw [Work.BoseBoxFock.mem_corpusBox_boxL hℓ]
  exact ⟨fun h i => h i, fun h i => h i⟩

/-- The window vanishes off `boxL ℓ` (which contains `halfBall ℓ`). -/
private lemma chiScale_eq_zero_of_not_mem_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : x ∉ Work.BoseK15.corpusBox.boxL ℓ) : Submission.BoseGases.chiScale ℓ x = 0 := by
  apply chiScale_eq_zero_of_norm_gt hℓ
  have hx' : ¬ (∀ i, |x i| ≤ ℓ / 2) := by
    intro h
    exact hx (by rw [boxL_eq_setOf hℓ]; exact h)
  push Not at hx'
  obtain ⟨i, hi⟩ := hx'
  have h1 : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
  linarith

/-- A set integral of a function vanishing off the set is the full integral. -/
private lemma setIntegral_eq_integral_of_eq_zero_off {s : Set E3} (hs : MeasurableSet s)
    {f : E3 → ℂ} (h : ∀ x, x ∉ s → f x = 0) : ∫ x in s, f x = ∫ x, f x := by
  rw [← MeasureTheory.integral_indicator hs]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, h x hx])

/-! ## §2. The two integrands on `E³ × E³` and the shear -/

/-- The `H`-shaped integrand: the weight acts on the **first** variable (the form in which the
integrability is easy). -/
private noncomputable def pairH (ℓ : ℝ) (a : E3) (W : E3 → ℝ) (G : E3 → E3 → ℂ)
    (p : E3 × E3) : ℂ :=
  ((W p.1 : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ p.2 : ℝ) : ℂ)
    * ((Submission.BoseGases.chiScale ℓ (p.1 + p.2 - a) : ℝ) : ℂ) * G (p.1 + p.2 - a) p.2

/-- The `F`-shaped integrand: the common value of both sides of the target, before the shear. -/
private noncomputable def pairF (ℓ : ℝ) (a : E3) (W : E3 → ℝ) (G : E3 → E3 → ℂ)
    (p : E3 × E3) : ℂ :=
  ((Submission.BoseGases.chiScale ℓ p.1 : ℝ) : ℂ)
    * ((Submission.BoseGases.chiScale ℓ p.2 : ℝ) : ℂ)
    * ((W (p.1 - p.2 + a) : ℝ) : ℂ) * G p.1 p.2

/-- The shear `(z,y) ↦ (z + y − a, y)` of `E³ × E³`. -/
private noncomputable def pairShear (a : E3) : (E3 × E3) ≃ᵐ (E3 × E3) where
  toFun p := (p.1 + p.2 - a, p.2)
  invFun p := (p.1 - p.2 + a, p.2)
  left_inv p := Prod.ext (by simp only [sub_eq_add_neg]; abel) rfl
  right_inv p := Prod.ext (by simp only [sub_eq_add_neg]; abel) rfl
  measurable_toFun :=
    (measurable_fst.add measurable_snd).sub measurable_const |>.prodMk measurable_snd
  measurable_invFun :=
    (measurable_fst.sub measurable_snd).add measurable_const |>.prodMk measurable_snd

@[simp] private lemma pairShear_apply (a : E3) (p : E3 × E3) :
    pairShear a p = (p.1 + p.2 - a, p.2) := rfl

@[simp] private lemma pairShear_symm_apply (a : E3) (p : E3 × E3) :
    (pairShear a).symm p = (p.1 - p.2 + a, p.2) := rfl

/-- The shear preserves the product Lebesgue measure: it is the measure preserving shear
`(z,y) ↦ (z+y, y)` (`measurePreserving_add_prod`) followed by the translation `z ↦ z − a`. -/
private lemma pairShear_measurePreserving (a : E3) :
    MeasurePreserving (pairShear a) (volume : Measure (E3 × E3)) (volume : Measure (E3 × E3)) := by
  have h1 : MeasurePreserving (fun p : E3 × E3 => (p.1 + p.2, p.2))
      (volume : Measure (E3 × E3)) (volume : Measure (E3 × E3)) :=
    MeasureTheory.measurePreserving_add_prod (volume : Measure E3) (volume : Measure E3)
  have h2 : MeasurePreserving (fun p : E3 × E3 => (p.1 - a, p.2))
      (volume : Measure (E3 × E3)) (volume : Measure (E3 × E3)) :=
    MeasurePreserving.prod (MeasureTheory.measurePreserving_add_right (volume : Measure E3) (-a))
      (MeasurePreserving.id (volume : Measure E3))
  have h3 : MeasurePreserving (fun p : E3 × E3 => (p.1 + p.2 - a, p.2))
      (volume : Measure (E3 × E3)) (volume : Measure (E3 × E3)) := h2.comp h1
  exact h3

/-! ## §3. Integrability -/

/-- Pointwise domination of `pairH` by a product of an `L¹` function of `p.1` and the window in
`p.2`: off the region `halfBall ℓ × halfBall ℓ` the integrand vanishes, and on it `G` is bounded
and `chiScale ℓ ≤ chiSupAbs`. -/
private lemma norm_pairH_le {ℓ : ℝ} (hℓ : 0 < ℓ) {a : E3} {W : E3 → ℝ} {G : E3 → E3 → ℂ}
    {M : ℝ} (hM : ∀ p ∈ halfBall ℓ ×ˢ halfBall ℓ, ‖Function.uncurry G p‖ ≤ M) (p : E3 × E3) :
    ‖pairH ℓ a W G p‖ ≤ (Submission.BoseGases.chiSupAbs * max M 0)
      * (‖W p.1‖ * Submission.BoseGases.chiScale ℓ p.2) := by
  have hc2 : 0 ≤ Submission.BoseGases.chiScale ℓ p.2 := chiScale_nonneg _ _
  have hcd : 0 ≤ Submission.BoseGases.chiScale ℓ (p.1 + p.2 - a) := chiScale_nonneg _ _
  have hcdS : Submission.BoseGases.chiScale ℓ (p.1 + p.2 - a)
      ≤ Submission.BoseGases.chiSupAbs := by
    have h := Submission.BoseGases.chiScale_abs_le_sup ℓ (p.1 + p.2 - a)
    rwa [abs_of_nonneg hcd] at h
  have hSnn : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  have hMnn : 0 ≤ max M 0 := le_max_right _ _
  have hwn : 0 ≤ ‖W p.1‖ := norm_nonneg _
  have hnorm : ‖pairH ℓ a W G p‖ = ‖W p.1‖ * Submission.BoseGases.chiScale ℓ p.2
      * Submission.BoseGases.chiScale ℓ (p.1 + p.2 - a) * ‖G (p.1 + p.2 - a) p.2‖ := by
    simp only [pairH, norm_mul, norm_ofReal_c, Real.norm_eq_abs, abs_of_nonneg hc2,
      abs_of_nonneg hcd]
  rw [hnorm]
  have key : Submission.BoseGases.chiScale ℓ (p.1 + p.2 - a) * ‖G (p.1 + p.2 - a) p.2‖
      ≤ Submission.BoseGases.chiSupAbs * max M 0 ∨
      ‖W p.1‖ * Submission.BoseGases.chiScale ℓ p.2 = 0 := by
    by_cases hz : Submission.BoseGases.chiScale ℓ p.2 = 0
    · exact Or.inr (by rw [hz, mul_zero])
    · left
      have hp2 : p.2 ∈ halfBall ℓ := by
        rw [halfBall_mem_iff]; exact chiScale_ne_zero_norm_le hℓ hz
      by_cases hz2 : Submission.BoseGases.chiScale ℓ (p.1 + p.2 - a) = 0
      · rw [hz2]; simp only [zero_mul]; exact mul_nonneg hSnn hMnn
      · have hp1 : p.1 + p.2 - a ∈ halfBall ℓ := by
          rw [halfBall_mem_iff]; exact chiScale_ne_zero_norm_le hℓ hz2
        have hgn : ‖G (p.1 + p.2 - a) p.2‖ ≤ max M 0 :=
          le_trans (hM (p.1 + p.2 - a, p.2) (by
            rw [Set.mem_prod]; exact ⟨hp1, hp2⟩)) (le_max_left _ _)
        exact mul_le_mul hcdS hgn (norm_nonneg _) hSnn
  rcases key with hkey | hkey
  · calc ‖W p.1‖ * Submission.BoseGases.chiScale ℓ p.2
          * Submission.BoseGases.chiScale ℓ (p.1 + p.2 - a) * ‖G (p.1 + p.2 - a) p.2‖
        = (‖W p.1‖ * Submission.BoseGases.chiScale ℓ p.2)
            * (Submission.BoseGases.chiScale ℓ (p.1 + p.2 - a)
              * ‖G (p.1 + p.2 - a) p.2‖) := by ring
      _ ≤ (‖W p.1‖ * Submission.BoseGases.chiScale ℓ p.2)
            * (Submission.BoseGases.chiSupAbs * max M 0) :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg hwn hc2)
      _ = (Submission.BoseGases.chiSupAbs * max M 0)
            * (‖W p.1‖ * Submission.BoseGases.chiScale ℓ p.2) := by ring
  · simp only [hkey, mul_zero, zero_mul]
    exact le_refl 0

/-- `pairH` is integrable on the product space. -/
private lemma integrable_pairH {ℓ : ℝ} (hℓ : 0 < ℓ) {a : E3} {W : E3 → ℝ} (hWi : Integrable W)
    {G : E3 → E3 → ℂ} (hGc : Continuous (Function.uncurry G)) :
    Integrable (pairH ℓ a W G) (volume : Measure (E3 × E3)) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0:E3) (ℓ/2)).prod (isCompact_closedBall (0:E3) (ℓ/2))
    |>.exists_bound_of_continuousOn (hGc.continuousOn.mono (Set.subset_univ _))
  have hχcont : Continuous (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chi_continuous.comp (continuous_const_smul ℓ⁻¹)
  have hχint : Integrable (Submission.BoseGases.chiScale ℓ) (volume : Measure E3) :=
    hχcont.integrable_of_hasCompactSupport
      (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ))
  have hmaj : Integrable (fun p : E3 × E3 => (Submission.BoseGases.chiSupAbs * max M 0)
      * (‖W p.1‖ * Submission.BoseGases.chiScale ℓ p.2)) (volume : Measure (E3 × E3)) :=
    (hWi.norm.mul_prod hχint).const_mul _
  have hWasm : AEStronglyMeasurable (fun p : E3 × E3 => ((W p.1 : ℝ) : ℂ))
      (volume : Measure (E3 × E3)) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable
        hWi.aestronglyMeasurable).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure E3)) (ν := (volume : Measure E3)))
  have hc1 : Continuous (fun p : E3 × E3 => ((Submission.BoseGases.chiScale ℓ p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hχcont.comp continuous_snd)
  have hc2 : Continuous (fun p : E3 × E3 =>
      ((Submission.BoseGases.chiScale ℓ (p.1 + p.2 - a) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (hχcont.comp ((continuous_fst.add continuous_snd).sub continuous_const))
  have hc3 : Continuous (fun p : E3 × E3 => G (p.1 + p.2 - a) p.2) :=
    hGc.comp (((continuous_fst.add continuous_snd).sub continuous_const).prodMk continuous_snd)
  have hmeas : AEStronglyMeasurable (pairH ℓ a W G) (volume : Measure (E3 × E3)) := by
    have h1 : AEStronglyMeasurable (fun p : E3 × E3 => ((W p.1 : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ p.2 : ℝ) : ℂ)) (volume : Measure (E3 × E3)) :=
      hWasm.mul hc1.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : E3 × E3 => ((W p.1 : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ p.2 : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ (p.1 + p.2 - a) : ℝ) : ℂ))
        (volume : Measure (E3 × E3)) :=
      h1.mul hc2.aestronglyMeasurable
    exact h2.mul hc3.aestronglyMeasurable
  exact Integrable.mono' hmaj hmeas (Filter.Eventually.of_forall fun p => norm_pairH_le hℓ hM p)

/-- `pairF` is integrable on the product space (it is the shear pull-back of `pairH`). -/
private lemma integrable_pairF {ℓ : ℝ} (hℓ : 0 < ℓ) {a : E3} {W : E3 → ℝ} (hWi : Integrable W)
    {G : E3 → E3 → ℂ} (hGc : Continuous (Function.uncurry G)) :
    Integrable (pairF ℓ a W G) (volume : Measure (E3 × E3)) := by
  have hH := integrable_pairH (a := a) hℓ hWi hGc
  have hsymm := MeasurePreserving.symm (pairShear a) (pairShear_measurePreserving a)
  refine (hsymm.integrable_comp_of_integrable hH).congr ?_
  filter_upwards with p
  have harg : p.1 - p.2 + a + p.2 - a = p.1 := by simp only [sub_eq_add_neg]; abel
  simp only [Function.comp_apply, pairShear_symm_apply, pairH, pairF, harg]
  ring

/-! ## §4. The two halves of the identity -/

/-- **Left half**: the box-restricted pairing equals the product integral.  Both domains may be
enlarged to `E³`, since the integrand vanishes whenever one of the two windows does. -/
private lemma pairing_left {ℓ : ℝ} (hℓ : 0 < ℓ) {a : E3} {W : E3 → ℝ} (hWi : Integrable W)
    {G : E3 → E3 → ℂ} (hGc : Continuous (Function.uncurry G)) :
    (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
          * ((W (w - y + a) : ℝ) : ℂ) * G w y)
      = ∫ p : E3 × E3, pairF ℓ a W G p := by
  change (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        pairF ℓ a W G (w, y)) = ∫ p : E3 × E3, pairF ℓ a W G p
  have hprod : (∫ p : E3 × E3, pairF ℓ a W G p)
      = ∫ w, ∫ y, pairF ℓ a W G (w, y) :=
    MeasureTheory.integral_prod (pairF ℓ a W G) (integrable_pairF (a := a) hℓ hWi hGc)
  rw [hprod]
  rw [show (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        pairF ℓ a W G (w, y))
      = ∫ w, ∫ y in Work.BoseK15.corpusBox.boxL ℓ, pairF ℓ a W G (w, y) from
    setIntegral_eq_integral_of_eq_zero_off (measurableSet_boxL hℓ) (fun w hw => by
      have hz : (fun y => pairF ℓ a W G (w, y)) = fun y => 0 := funext fun y => by
        simp [pairF, chiScale_eq_zero_of_not_mem_boxL hℓ hw]
      rw [hz]; simp)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  exact setIntegral_eq_integral_of_eq_zero_off (measurableSet_boxL hℓ) (fun y hy => by
    simp [pairF, chiScale_eq_zero_of_not_mem_boxL hℓ hy])

/-- **Pointwise core of the right half**: pulling the weight inside the `ψ`-integral and extending
the `y`-domain from `halfBall ℓ` to `E³` produces `∫ y, pairH (z,y)`. -/
private lemma wmul_psiM {ℓ : ℝ} (hℓ : 0 < ℓ) {a : E3} {W : E3 → ℝ} {G : E3 → E3 → ℂ} (z : E3) :
    ((W z : ℝ) : ℂ) * ∫ y in halfBall ℓ, ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ (z + y - a) : ℝ) : ℂ) * G (z + y - a) y
      = ∫ y, pairH ℓ a W G (z, y) := by
  rw [← MeasureTheory.integral_const_mul]
  rw [setIntegral_eq_integral_of_eq_zero_off (measurableSet_halfBall ℓ) (fun y hy => by
    have h0 : Submission.BoseGases.chiScale ℓ y = 0 := by
      apply chiScale_eq_zero_of_norm_gt hℓ
      rw [halfBall_mem_iff] at hy
      exact lt_of_not_ge hy
    simp [h0])]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [pairH]
  ring

/-- **Right half**: the pairing of `W` against `ψ_m` equals the product integral — the `z`-integral
is interchanged with the `y`-integral (Fubini) and the `z`-variable substituted by the
measure-preserving shear `(z,y) ↦ (z+y−a, y)`. -/
private lemma pairing_right {ℓ : ℝ} (hℓ : 0 < ℓ) {a : E3} {W : E3 → ℝ} (hWi : Integrable W)
    {G : E3 → E3 → ℂ} (hGc : Continuous (Function.uncurry G)) :
    (∫ z, ((W z : ℝ) : ℂ) * ∫ y in halfBall ℓ,
        ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ (z + y - a) : ℝ) : ℂ) * G (z + y - a) y)
      = ∫ p : E3 × E3, pairF ℓ a W G p := by
  have hH := integrable_pairH (a := a) hℓ hWi hGc
  have hprod : (∫ p : E3 × E3, pairH ℓ a W G p)
      = ∫ z, ∫ y, pairH ℓ a W G (z, y) :=
    MeasureTheory.integral_prod (pairH ℓ a W G) hH
  rw [show (∫ z, ((W z : ℝ) : ℂ) * ∫ y in halfBall ℓ,
        ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ (z + y - a) : ℝ) : ℂ) * G (z + y - a) y)
      = ∫ z, ∫ y, pairH ℓ a W G (z, y) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => wmul_psiM hℓ z)]
  rw [← hprod]
  have hcomp : (pairH ℓ a W G) = fun p => pairF ℓ a W G (pairShear a p) := by
    funext p
    have harg : p.1 + p.2 - a - p.2 + a = p.1 := by simp only [sub_eq_add_neg]; abel
    simp only [pairH, pairF, pairShear_apply, harg]
    ring
  rw [hcomp, MeasureTheory.MeasurePreserving.integral_comp' (pairShear_measurePreserving a)
    (pairF ℓ a W G)]

/-! ## §5. The target -/

theorem psiM_pairing {ℓ R : ℝ} (hℓ : 0 < ℓ) {m : Fin 3 → ℤ} (hm : m ≠ 0)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hWs : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → W x = 0)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
          * ((W (w - y + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) * G w y)
      = ∫ z, ((W z : ℝ) : ℂ) * Work.BoseBoxFock.L1Tails.psiM ℓ m G z := by
  have hGc : Continuous (Function.uncurry G) := hG.continuous
  have hL := pairing_left (ℓ := ℓ) (a := ℓ • Work.BoseBoxFock.latVec m) hℓ hWi hGc
  have hR := pairing_right (ℓ := ℓ) (a := ℓ • Work.BoseBoxFock.latVec m) hℓ hWi hGc
  rw [hL]
  rw [show (∫ z, ((W z : ℝ) : ℂ) * psiM ℓ m G z)
      = (∫ z, ((W z : ℝ) : ℂ) * ∫ y in halfBall ℓ,
          ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale ℓ
                (z + y - ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)
            * G (z + y - ℓ • Work.BoseBoxFock.latVec m) y) from by
    simp only [psiM, chiC]]
  exact hR.symm

end Work.BoseBoxFock.L1Tails
