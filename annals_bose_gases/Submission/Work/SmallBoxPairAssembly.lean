import Mathlib
import Submission.Commons.Algebra.BigOperators.sum_pairSet_eq_succAbove
import Submission.Work.SmallBoxPairFourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# SESSION-278 — D1 item (c2): the per-pair assembly

`SmallBoxPairIdent.core_identity` + `tau_pair_side` give the τ-side of the `(c2)`
identification and `SmallBoxPairFourier.fourier_pairFibreDens` + `pairMean_eq`
give the Fourier side.  This module performs the remaining Fubini bookkeeping,
closing the per-pair identity

    boxInv ℓ ^ 2 * ∫_{abox p ℓ} pairSlot·pairMean
      = 𝓕 (pairFibreDens) (−u) .
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators Convolution FourierTransform

namespace Submission

open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Fubini lemmas -/

/-- **Triple Fubini over the box and the centred cube².**  For a continuous kernel
`F : X p → (ℝ³ × ℝ³) → ℂ`, the iterated integral over `abox p ℓ` of the iterated
integral over `acube ℓ × acube ℓ` may be swapped. -/
lemma abox_cube2_swap {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (F : X p → (ℝ³ × ℝ³) → ℂ)
    (hFc : Continuous (Function.uncurry F)) :
    (∫ r2 in abox p ℓ, ∫ q in acube ℓ ×ˢ acube ℓ, F r2 q)
      = ∫ q in acube ℓ ×ˢ acube ℓ, ∫ r2 in abox p ℓ, F r2 q := by
  set μ : Measure (X p) := (volume : Measure (X p)).restrict (abox p ℓ) with hμ
  set ν : Measure (ℝ³ × ℝ³) := (volume : Measure (ℝ³ × ℝ³)).restrict (acube ℓ ×ˢ acube ℓ)
    with hν
  have hint : Integrable (Function.uncurry F) (μ.prod ν) := by
    have hvol : μ.prod ν
        = (volume : Measure (X p × (ℝ³ × ℝ³))).restrict
            (abox p ℓ ×ˢ (acube ℓ ×ˢ acube ℓ)) := by
      rw [hμ, hν, Measure.prod_restrict]
      rfl
    rw [hvol]
    exact ContinuousOn.integrableOn_compact
      ((abox_compact p hℓ).prod ((acube_compact hℓ).prod (acube_compact hℓ)))
      hFc.continuousOn
  have hswap := integral_integral_swap (μ := μ) (ν := ν) (f := F) hint
  have hgoal : (∫ r2 in abox p ℓ, ∫ q in acube ℓ ×ˢ acube ℓ, F r2 q)
      = ∫ r2, ∫ q, F r2 q ∂ν ∂μ := by rw [← hμ, ← hν]
  rw [hgoal]
  exact hswap

/-- Iterated cube integral as a product-measure integral. -/
lemma acube_iter_eq_prod {ℓ : ℝ} (hℓ : 0 < ℓ) (g : ℝ³ → ℝ³ → ℂ)
    (hg : Continuous (fun q : ℝ³ × ℝ³ => g q.1 q.2)) :
    (∫ y in acube ℓ, ∫ z in acube ℓ, g y z) = ∫ q in acube ℓ ×ˢ acube ℓ, g q.1 q.2 := by
  set ν : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ) with hν
  have hν2 : ν.prod ν = (volume : Measure (ℝ³ × ℝ³)).restrict (acube ℓ ×ˢ acube ℓ) := by
    rw [hν, Measure.prod_restrict]
    rfl
  have hint : Integrable (fun q : ℝ³ × ℝ³ => g q.1 q.2) (ν.prod ν) := by
    rw [hν2]
    exact ContinuousOn.integrableOn_compact ((acube_compact hℓ).prod (acube_compact hℓ))
      hg.continuousOn
  have h := MeasureTheory.integral_prod (μ := ν) (ν := ν)
    (f := fun q : ℝ³ × ℝ³ => g q.1 q.2) hint
  rw [← h, hν2]

/-- **Triple Fubini over the box and the two cubes.** -/
lemma abox_cube_cube_swap {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (F : X p → ℝ³ → ℝ³ → ℂ)
    (hFc : Continuous (fun t : X p × (ℝ³ × ℝ³) => F t.1 t.2.1 t.2.2)) :
    (∫ r2 in abox p ℓ, ∫ y in acube ℓ, ∫ z in acube ℓ, F r2 y z)
      = ∫ y in acube ℓ, ∫ z in acube ℓ, ∫ r2 in abox p ℓ, F r2 y z := by
  set G : X p → (ℝ³ × ℝ³) → ℂ := fun r2 q => F r2 q.1 q.2 with hG
  have hGc : Continuous (Function.uncurry G) := hFc
  have h1 : (∫ r2 in abox p ℓ, ∫ y in acube ℓ, ∫ z in acube ℓ, F r2 y z)
      = ∫ r2 in abox p ℓ, ∫ q in acube ℓ ×ˢ acube ℓ, G r2 q := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
    exact acube_iter_eq_prod hℓ (fun y z => F r2 y z)
      (hFc.comp (continuous_const.prodMk continuous_id))
  have h2 : (∫ r2 in abox p ℓ, ∫ q in acube ℓ ×ˢ acube ℓ, G r2 q)
      = ∫ q in acube ℓ ×ˢ acube ℓ, ∫ r2 in abox p ℓ, G r2 q := abox_cube2_swap hℓ G hGc
  have h3 : (∫ q in acube ℓ ×ˢ acube ℓ, ∫ r2 in abox p ℓ, G r2 q)
      = ∫ y in acube ℓ, ∫ z in acube ℓ, ∫ r2 in abox p ℓ, F r2 y z := by
    set μ : Measure (X p) := (volume : Measure (X p)).restrict (abox p ℓ) with hμ
    set ν : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ) with hν
    have hν2 : ν.prod ν = (volume : Measure (ℝ³ × ℝ³)).restrict (acube ℓ ×ˢ acube ℓ) := by
      rw [hν, Measure.prod_restrict]
      rfl
    have hint : Integrable (Function.uncurry G) (μ.prod (ν.prod ν)) := by
      have hvol : μ.prod (ν.prod ν)
          = (volume : Measure (X p × (ℝ³ × ℝ³))).restrict
              (abox p ℓ ×ˢ (acube ℓ ×ˢ acube ℓ)) := by
        rw [hμ, hν2, Measure.prod_restrict]
        rfl
      rw [hvol]
      exact ContinuousOn.integrableOn_compact
        ((abox_compact p hℓ).prod ((acube_compact hℓ).prod (acube_compact hℓ)))
        hFc.continuousOn
    have hright := Integrable.integral_prod_right (μ := μ) (ν := ν.prod ν)
      (f := Function.uncurry G) hint
    have hh : (∫ q, ∫ r2, G r2 q ∂μ ∂(ν.prod ν))
        = ∫ y, ∫ z, (∫ r2, G r2 (y, z) ∂μ) ∂ν ∂ν :=
      MeasureTheory.integral_prod (μ := ν) (ν := ν)
        (f := fun q : ℝ³ × ℝ³ => ∫ r2, G r2 q ∂μ) hright
    have hgoal : (∫ q in acube ℓ ×ˢ acube ℓ, ∫ r2 in abox p ℓ, G r2 q)
        = ∫ q, ∫ r2, G r2 q ∂μ ∂(ν.prod ν) := by rw [← hν2]
    rw [hgoal, hh]
  rw [h1, h2, h3]

/-! ## 2. The anti-diagonal kernel -/

/-- The anti-diagonal mode kernel `χ(y)χ(z)e^{i⟨P,y−z⟩}` (the symbol of the pair kernel at
momentum `P`). -/
noncomputable def pairKern (ℓ : ℝ) (P y z : ℝ³) : ℂ :=
  (chiScale ℓ y : ℂ) * (chiScale ℓ z : ℂ)
    * Complex.exp (Complex.I * ((inner ℝ P (y - z) : ℝ) : ℂ))

/-- **The peeled pair fibre in iterated form.**  With `j := i.succAbove j'` the
`pairFibreFun` integral over the remaining coordinates is the `r2`-integral of the
two-slot product. -/
lemma pairFibreFun_eq_iter {p : ℕ} {ℓ : ℝ} (_hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    (_hΦc : Continuous Φ)
    (i : Fin (p + 2)) (j' : Fin (p + 1)) (y z : ℝ³) :
    pairFibreFun ℓ Φ i (i.succAbove j') y z
      = ∫ r2 in abox p ℓ,
          (aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2)
            * (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) := by
  have hs : sucAboveInv i (i.succAbove j') (Fin.ne_succAbove i j') = j' :=
    Fin.succAbove_right_injective
      (succAbove_sucAboveInv i (i.succAbove j') (Fin.ne_succAbove i j'))
  rw [pairFibreFun, dif_pos (Fin.ne_succAbove i j'), hs]

/-- Continuity of the anti-diagonal kernel on `ℝ³ × ℝ³`. -/
lemma pairKern_continuous (ℓ : ℝ) (P : ℝ³) :
    Continuous (Function.uncurry (pairKern ℓ P)) := by
  rw [show Function.uncurry (pairKern ℓ P) = fun q : ℝ³ × ℝ³ =>
      (chiScale ℓ q.1 : ℂ) * (chiScale ℓ q.2 : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ P (q.1 - q.2) : ℝ) : ℂ)) from rfl]
  refine ((Complex.continuous_ofReal.comp
      ((chiScale_continuous ℓ).comp continuous_fst)).mul
    (Complex.continuous_ofReal.comp
      ((chiScale_continuous ℓ).comp continuous_snd))).mul ?_
  refine Complex.continuous_exp.comp (continuous_const.mul ?_)
  exact Complex.continuous_ofReal.comp
    (continuous_inner.comp (continuous_const.prodMk (continuous_fst.sub continuous_snd)))

/-! ## 3. The per-pair assembly -/

theorem c2_pair {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (i : Fin (p + 2)) (j' : Fin (p + 1)) (u : ℝ³) :
    boxInv ℓ ^ 2 * (∫ r2 in abox p ℓ,
        pairSlot ℓ Φ (qMode ℓ (-((2 * π : ℝ) • u))) (qMode ℓ ((2 * π : ℝ) • u)) i j' r2
          * pairMean ℓ Φ i j' r2)
      = 𝓕 (fun v => ((pairFibreDens ℓ Φ i (i.succAbove j') v : ℝ) : ℂ)) (-u) := by
  have hΦcc : Continuous Φ := hΦc.continuous
  have hAQc : Continuous (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) :=
    aQ_continuous hℓ (i.succAbove j') (aQ_continuous hℓ i hΦcc)
  have hAPc : Continuous (aP ℓ i (aP ℓ (i.succAbove j') Φ)) :=
    aP_continuous hℓ i (aP_continuous hℓ (i.succAbove j') hΦcc)
  have hcancelreal : (((ℓ ^ 3 : ℝ))⁻¹) ^ 2 * (ℓ ^ 6 : ℝ) = 1 := by
    have h0 : ℓ ≠ 0 := ne_of_gt hℓ
    field_simp
  have hcancel : boxInv ℓ ^ 2 * ((ℓ ^ 6 : ℝ) : ℂ) = 1 := by
    rw [boxInv, ← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Complex.ofReal_mul, hcancelreal,
      Complex.ofReal_one]
  -- the τ-side reduction
  have hI : (∫ r2 in abox p ℓ,
        pairSlot ℓ Φ (qMode ℓ (-((2 * π : ℝ) • u))) (qMode ℓ ((2 * π : ℝ) • u)) i j' r2
          * pairMean ℓ Φ i j' r2)
      = ∫ r2 in abox p ℓ, ((ℓ ^ 6 : ℝ) : ℂ)
          * ((∫ y in acube ℓ, ∫ z in acube ℓ,
                pairKern ℓ ((2 * π : ℝ) • u) y z
                  * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ))
              * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
    simp only []
    rw [core_identity hℓ hΦcc i j' r2 ((2 * π : ℝ) • u), pairMean_eq hℓ hΦcc i j' r2]
    simp only [pairKern]
    ring
  rw [hI]
  rw [MeasureTheory.integral_const_mul, ← mul_assoc, hcancel, one_mul]
  -- Step 2: pull the (y,z)-constant `↑(aP…)` inside the double integral
  have hstep_C : (∫ r2 in abox p ℓ,
          (∫ y in acube ℓ, ∫ z in acube ℓ,
              pairKern ℓ ((2 * π : ℝ) • u) y z
                * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ))
            * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ))
      = ∫ r2 in abox p ℓ, ∫ y in acube ℓ, ∫ z in acube ℓ,
          pairKern ℓ ((2 * π : ℝ) • u) y z
            * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)
            * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
    simp only []
    have h1 : (∫ y in acube ℓ, ∫ z in acube ℓ,
          pairKern ℓ ((2 * π : ℝ) • u) y z
            * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ))
        * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ)
        = ∫ y in acube ℓ, (∫ z in acube ℓ,
              pairKern ℓ ((2 * π : ℝ) • u) y z
                * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ))
            * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ) :=
      (MeasureTheory.integral_mul_const (μ := (volume : Measure ℝ³).restrict (acube ℓ))
        (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ) _).symm
    rw [h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact (MeasureTheory.integral_mul_const (μ := (volume : Measure ℝ³).restrict (acube ℓ))
      (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ) _).symm
  rw [hstep_C]
  -- Step 3: Fubini (r2 innermost)
  have hstep_D : (∫ r2 in abox p ℓ, ∫ y in acube ℓ, ∫ z in acube ℓ,
          pairKern ℓ ((2 * π : ℝ) • u) y z
            * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)
            * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ))
      = ∫ y in acube ℓ, ∫ z in acube ℓ, ∫ r2 in abox p ℓ,
          pairKern ℓ ((2 * π : ℝ) • u) y z
            * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)
            * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ) := by
    have hcont : Continuous (fun t : X p × (ℝ³ × ℝ³) =>
        pairKern ℓ ((2 * π : ℝ) • u) t.2.1 t.2.2
          * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' t.2.1 t.2.2 t.1) : ℝ) : ℂ)
          * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' t.1) : ℝ) : ℂ)) := by
      refine ((pairKern_continuous ℓ ((2 * π : ℝ) • u)).comp
        (continuous_snd.fst.prodMk continuous_snd.snd)).mul ?_ |>.mul ?_
      · exact Complex.continuous_ofReal.comp
          (hAQc.comp ((contDiff_ins2 i j').continuous.comp continuous_swap))
      · exact Complex.continuous_ofReal.comp
          (hAPc.comp ((contDiff_rest2 i j').continuous.comp continuous_fst))
    exact abox_cube_cube_swap hℓ (fun r2 y z =>
        pairKern ℓ ((2 * π : ℝ) • u) y z
          * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)
          * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ)) hcont
  rw [hstep_D]
  -- Step 4: the per-`(y,z)` `r2`-integral (complexification)
  have hstep_E : (∫ y in acube ℓ, ∫ z in acube ℓ, ∫ r2 in abox p ℓ,
          pairKern ℓ ((2 * π : ℝ) • u) y z
            * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)
            * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ))
      = ∫ y in acube ℓ, ∫ z in acube ℓ, pairKern ℓ ((2 * π : ℝ) • u) y z
          * (((∫ r2 in abox p ℓ, (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2)
                * (aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ)) : ℂ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only []
    have hcont : Continuous (fun r : X p =>
        (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r)
          * (aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r)) :=
      (hAQc.comp ((contDiff_ins2 i j').continuous.comp
        ((continuous_const : Continuous (fun _ : X p => ((y, z) : ℝ³ × ℝ³))).prodMk
          continuous_id))).mul
        (hAPc.comp (contDiff_rest2 i j').continuous)
    rw [show (∫ r2 in abox p ℓ,
          pairKern ℓ ((2 * π : ℝ) • u) y z
            * (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)
            * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ))
        = ∫ r2 in abox p ℓ, pairKern ℓ ((2 * π : ℝ) • u) y z
            * ((((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)
              * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall fun r2 => by ring)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hcong : (∫ r2 in abox p ℓ,
          (((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ) : ℂ)
            * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ))
        = ∫ r2 in abox p ℓ, ((((aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2) : ℝ)
            * ((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℝ) : ℂ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun r2 => by
        simp only []
        rw [← Complex.ofReal_mul])
    rw [hcong]
    exact Complex.ofRealCLM.integral_comp_comm (φ := fun r2 : X p =>
      (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2)
        * (aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2))
      (ContinuousOn.integrableOn_compact (abox_compact p hℓ) hcont.continuousOn)
  rw [hstep_E]
  -- the Fourier side
  have hR : 𝓕 (fun v => ((pairFibreDens ℓ Φ i (i.succAbove j') v : ℝ) : ℂ)) (-u)
      = ∫ y in acube ℓ, ∫ z in acube ℓ, pairKern ℓ ((2 * π : ℝ) • u) y z
          * (((∫ r2 in abox p ℓ, (aQ ℓ (i.succAbove j') (aQ ℓ i Φ)) (ins2 i j' y z r2)
                * (aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ)) : ℂ) := by
    rw [fourier_pairFibreDens hℓ hΦc (i := i) (j := i.succAbove j') (Fin.ne_succAbove i j') u]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only []
    rw [pairKern]
    congr 1
    rw [pairFibreFun_eq_iter hℓ hΦcc i j' y z]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
    ring
  exact hR.symm

/-! ## 4. The summed `(c2)` identity -/

/-- **D1 item (c2), summed form.**  The anti-diagonal τ-pairing quadratic form is the sum over
the ordered pairs of distinct slots of the Fourier transform of the pair density. -/
theorem c2_sum {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (u : ℝ³) :
    (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * bDag ℓ (qMode ℓ (-((2 * π : ℝ) • u)))
        (bDag ℓ (qMode ℓ ((2 * π : ℝ) • u)) (fun y => (Φ y : ℂ))) x)
      = ∑ q ∈ pairSet (p + 2), 𝓕 (fun v => ((pairFibreDens ℓ Φ q.1 q.2 v : ℝ) : ℂ)) (-u) := by
  rw [tau_pair_side hℓ hΦc.continuous (qMode ℓ (-((2 * π : ℝ) • u)))
    (qMode ℓ ((2 * π : ℝ) • u)) (continuous_qMode _) (continuous_qMode _)
    (integral_qMode_eq_zero hℓ _)]
  have hre : (∑ q ∈ pairSet (p + 2), 𝓕 (fun v => ((pairFibreDens ℓ Φ q.1 q.2 v : ℝ) : ℂ)) (-u))
      = ∑ i : Fin (p + 2), ∑ j' : Fin (p + 1),
          𝓕 (fun v => ((pairFibreDens ℓ Φ i (i.succAbove j') v : ℝ) : ℂ)) (-u) := by
    rw [pairSet]
    exact Commons.Algebra.BigOperators.sum_pairSet_eq_succAbove (n := p + 1)
      (F := fun a b : Fin (p + 2) =>
        𝓕 (fun v => ((pairFibreDens ℓ Φ a b v : ℝ) : ℂ)) (-u))
  rw [hre, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  exact c2_pair hℓ hΦc i j' u

end BoseGases
end Submission
