/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `C^{1,α}`-estimate for composition with a `C^{1,α}` map

If `Φ : X → X` is `C¹` on `Ω'` with `‖fderiv Φ‖ ≤ L` and `‖fderiv Φ x - fderiv Φ y‖ ≤ L ‖x-y‖^α`,
if `Φ` is globally `L`-Lipschitz on `Ω'` and maps `Ω'` into the open set `Ω`, and if
`W : X → ℂ` is `C¹` on `Ω`, then

  `‖W ∘ Φ‖_{C^{1,α}(Ω')} ≤ (1 + 2L + L^{1+α}) ‖W‖_{C^{1,α}(Ω)}`.

This is the transport estimate needed whenever an estimate is pulled back along a map which is
`C^{1,α}`-close to the identity (the gauge/deformation method for the perturbed `∂̄`-equation):
`L = 1 + O(ε)` gives a constant `4 + O(ε)`.

The pointwise bound on `fderiv Φ` does not give a global Lipschitz bound on a possibly
disconnected `Ω'`, so the global Lipschitz hypothesis `hlip` is carried explicitly.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Elementary real inequalities -/

/-- Elementary real inequality behind the order-`0` composition estimate: if `0 < p ≤ M * q`,
`M ≥ 0`, `α > 0` and `r ≥ 0`, then `r / q ^ α ≤ M ^ α * (r / p ^ α)`. -/
private lemma div_rpow_le_mul_div_rpow {r M p q α : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hα : 0 < α) (hp : 0 < p) (hpq : p ≤ M * q) :
    r / q ^ α ≤ M ^ α * (r / p ^ α) := by
  have hq : 0 < q := by
    by_contra h
    have hq0 : q ≤ 0 := le_of_not_gt h
    have : M * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM hq0
    linarith
  have hpq' : p ^ α ≤ M ^ α * q ^ α := by
    calc p ^ α ≤ (M * q) ^ α := Real.rpow_le_rpow hp.le hpq hα.le
      _ = M ^ α * q ^ α := Real.mul_rpow hM hq.le
  have hpα : 0 < p ^ α := Real.rpow_pos_of_pos hp α
  have hqα : 0 < q ^ α := Real.rpow_pos_of_pos hq α
  rw [← mul_div_assoc, le_div_iff₀ hpα, div_mul_eq_mul_div, div_le_iff₀ hqα]
  calc r * p ^ α ≤ r * (M ^ α * q ^ α) := mul_le_mul_of_nonneg_left hpq' hr
    _ = M ^ α * r * q ^ α := by ring

/-- `L ^ (1+α) = L ^ α * L` for `L ≥ 0` and `α > 0`. -/
private lemma rpow_one_add_eq {L α : ℝ} (hL : 0 ≤ L) (hα : 0 < α) :
    L ^ (1 + α) = L ^ α * L := by
  rw [Real.rpow_add' hL (by linarith : (1 : ℝ) + α ≠ 0), Real.rpow_one, mul_comm]

/-- The first term of the first-order Hölder estimate: `r * L ≤ (r / p^α) L^{1+α} q^α`
whenever `0 ≤ p ≤ L q`, `r ≥ 0`, `q ≥ 0`, and `p = 0` forces `r = 0`. -/
private lemma mul_le_div_mul_rpow_add {α L p q r : ℝ} (hα : 0 < α) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p ≤ L * q) (hr0 : p = 0 → r = 0) :
    r * L ≤ (r / p ^ α) * L ^ (1 + α) * q ^ α := by
  have hL1 := rpow_one_add_eq hL hα
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · have hp0' : p = 0 := hp0.symm
    have hz : r = 0 := hr0 hp0'
    rw [hz, hp0', Real.zero_rpow (ne_of_gt hα), zero_div]
    simp
  · have hd : p ^ α ≤ L ^ α * q ^ α := by
      calc p ^ α ≤ (L * q) ^ α := Real.rpow_le_rpow (le_of_lt hp0) hpq (le_of_lt hα)
        _ = L ^ α * q ^ α := Real.mul_rpow hL hq
    have hpα : 0 < p ^ α := Real.rpow_pos_of_pos hp0 α
    have hrp : 0 ≤ r / p ^ α := div_nonneg hr hpα.le
    calc r * L = (r / p ^ α) * p ^ α * L := by
          rw [div_mul_cancel₀ r (ne_of_gt hpα)]
      _ ≤ (r / p ^ α) * (L ^ α * q ^ α) * L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hrp) hL
      _ = (r / p ^ α) * L ^ (1 + α) * q ^ α := by rw [hL1]; ring

/-! ## Norms of within-derivatives on open sets -/

/-- On an open set the first iterated derivative within the set is the derivative. -/
lemma comp_norm_iteratedFDerivWithin_one_eq {f : X → ℂ} {Ω : Set X} (hΩ : IsOpen Ω) {x : X}
    (hx : x ∈ Ω) : ‖iteratedFDerivWithin ℝ 1 f Ω x‖ = ‖fderiv ℝ f x‖ := by
  rw [norm_iteratedFDerivWithin_one f (hΩ.uniqueDiffOn.uniqueDiffWithinAt hx),
    fderivWithin_of_isOpen hΩ hx]

/-- On an open set, the distance between two first iterated derivatives within the set is the
distance between the two derivatives. -/
lemma comp_norm_iteratedFDerivWithin_one_sub_eq {f : X → ℂ} {Ω : Set X} (hΩ : IsOpen Ω)
    {x y : X} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ‖iteratedFDerivWithin ℝ 1 f Ω x - iteratedFDerivWithin ℝ 1 f Ω y‖
      = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
  have h1 := dist_iteratedFDerivWithin_one (𝕜 := ℝ) f f
    (hΩ.uniqueDiffOn.uniqueDiffWithinAt hx) (hΩ.uniqueDiffOn.uniqueDiffWithinAt hy)
  simp only [dist_eq_norm] at h1
  rw [h1, fderivWithin_of_isOpen hΩ hx, fderivWithin_of_isOpen hΩ hy]

/-- The order-`0` iterated derivative within a set does not change norms of differences. -/
lemma comp_norm_iteratedFDerivWithin_zero_sub (f : X → ℂ) (Ω : Set X) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ := by
  simp only [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]

/-- Chain rule for the composition, in the situation at hand. -/
lemma comp_fderiv_eq {W : X → ℂ} {Φ : X → X} {Ω Ω' : Set X} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (hW : ContDiffOn ℝ 1 W Ω) (hΦ : ContDiffOn ℝ 1 Φ Ω') (hmaps : ∀ x ∈ Ω', Φ x ∈ Ω) {x : X}
    (hx : x ∈ Ω') :
    fderiv ℝ (fun z => W (Φ z)) x = (fderiv ℝ W (Φ x)).comp (fderiv ℝ Φ x) := by
  have hΦd : DifferentiableAt ℝ Φ x :=
    ((hΦ.contDiffWithinAt hx).differentiableWithinAt (by norm_num)).differentiableAt
      (hΩ'.mem_nhds hx)
  have hWd : DifferentiableAt ℝ W (Φ x) :=
    ((hW.contDiffWithinAt (hmaps x hx)).differentiableWithinAt (by norm_num)).differentiableAt
      (hΩ.mem_nhds (hmaps x hx))
  have h := fderiv_comp (𝕜 := ℝ) x hWd hΦd
  simpa only [Function.comp_def] using h

/-! ## The four components of the estimate -/

/-- Order-`0` sup norm: immediate from `Φ (Ω') ⊆ Ω`. -/
lemma comp_iterDerivNorm_zero_le {Ω Ω' : Set X} {W : X → ℂ} {Φ : X → X}
    (hmaps : ∀ x ∈ Ω', Φ x ∈ Ω) :
    Work.CR.Flat.iterDerivNorm 0 (fun x => W (Φ x)) Ω'
      ≤ Work.CR.Flat.iterDerivNorm 0 W Ω := by
  rw [Work.CR.Flat.iterDerivNorm_zero, Work.CR.Flat.iterDerivNorm_zero]
  exact iSup₂_le fun x hx => le_iSup₂_of_le (Φ x) (hmaps x hx) le_rfl

/-- Order-`1` sup norm: the chain rule and `‖fderiv Φ‖ ≤ L`. -/
lemma comp_iterDerivNorm_one_le {L : ℝ} (_hL : 0 ≤ L) {Ω Ω' : Set X} (hΩ : IsOpen Ω)
    (hΩ' : IsOpen Ω') {W : X → ℂ} {Φ : X → X} (hW : ContDiffOn ℝ 1 W Ω)
    (hΦ : ContDiffOn ℝ 1 Φ Ω') (hmaps : ∀ x ∈ Ω', Φ x ∈ Ω)
    (hdΦ : ∀ x ∈ Ω', ‖fderiv ℝ Φ x‖ ≤ L) :
    Work.CR.Flat.iterDerivNorm 1 (fun x => W (Φ x)) Ω'
      ≤ ENNReal.ofReal L * Work.CR.Flat.iterDerivNorm 1 W Ω := by
  refine iSup₂_le fun x hx => ?_
  rw [comp_norm_iteratedFDerivWithin_one_eq hΩ' hx,
    comp_fderiv_eq hΩ hΩ' hW hΦ hmaps hx]
  calc ENNReal.ofReal ‖(fderiv ℝ W (Φ x)).comp (fderiv ℝ Φ x)‖
      ≤ ENNReal.ofReal (‖fderiv ℝ W (Φ x)‖ * ‖fderiv ℝ Φ x‖) :=
        ENNReal.ofReal_le_ofReal (ContinuousLinearMap.opNorm_comp_le _ _)
    _ = ENNReal.ofReal ‖fderiv ℝ W (Φ x)‖ * ENNReal.ofReal ‖fderiv ℝ Φ x‖ :=
        ENNReal.ofReal_mul (norm_nonneg _)
    _ ≤ ENNReal.ofReal ‖fderiv ℝ W (Φ x)‖ * ENNReal.ofReal L :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal (hdΦ x hx)) _
    _ ≤ Work.CR.Flat.iterDerivNorm 1 W Ω * ENNReal.ofReal L := by
        refine mul_le_mul_left ?_ _
        rw [← comp_norm_iteratedFDerivWithin_one_eq hΩ (hmaps x hx)]
        exact Work.CR.Flat.le_iterDerivNorm 1 W Ω (hmaps x hx)
    _ = ENNReal.ofReal L * Work.CR.Flat.iterDerivNorm 1 W Ω := mul_comm _ _

/-- Order-`0` Hölder seminorm: the Lipschitz bound on `Φ` gives the factor `L ^ α`. -/
lemma comp_holderSeminorm_zero_le {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L) {Ω Ω' : Set X}
    {W : X → ℂ} {Φ : X → X} (hmaps : ∀ x ∈ Ω', Φ x ∈ Ω)
    (hlip : ∀ x ∈ Ω', ∀ y ∈ Ω', ‖Φ x - Φ y‖ ≤ L * ‖x - y‖) :
    Work.CR.Flat.holderSeminorm 0 α (fun x => W (Φ x)) Ω'
      ≤ ENNReal.ofReal (L ^ α) * Work.CR.Flat.holderSeminorm 0 α W Ω := by
  have hLα : (0 : ℝ) ≤ L ^ α := Real.rpow_nonneg hL α
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [comp_norm_iteratedFDerivWithin_zero_sub]
  by_cases h : Φ x = Φ y
  · rw [h, sub_self, norm_zero, zero_div, ENNReal.ofReal_zero]
    exact bot_le
  · have h1 := Work.CR.Flat.le_holderSeminorm 0 α W Ω (hmaps x hx) (hmaps y hy) h
    rw [comp_norm_iteratedFDerivWithin_zero_sub] at h1
    refine le_trans ?_ (mul_le_mul_right h1 (ENNReal.ofReal (L ^ α)))
    rw [← ENNReal.ofReal_mul hLα]
    refine ENNReal.ofReal_le_ofReal ?_
    exact div_rpow_le_mul_div_rpow (norm_nonneg _) hL hα
      (norm_pos_iff.mpr (sub_ne_zero.mpr h)) (hlip x hx y hy)

/-- Order-`1` Hölder seminorm: split the derivative of the composition and use the Hölder
bound on `fderiv W`, `‖fderiv Φ‖ ≤ L` and the Hölder bound on `fderiv Φ`. -/
lemma comp_holderSeminorm_one_le {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L) {Ω Ω' : Set X}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') {W : X → ℂ} {Φ : X → X} (hW : ContDiffOn ℝ 1 W Ω)
    (hΦ : ContDiffOn ℝ 1 Φ Ω') (hmaps : ∀ x ∈ Ω', Φ x ∈ Ω)
    (hlip : ∀ x ∈ Ω', ∀ y ∈ Ω', ‖Φ x - Φ y‖ ≤ L * ‖x - y‖)
    (hdΦ : ∀ x ∈ Ω', ‖fderiv ℝ Φ x‖ ≤ L)
    (hdΦα : ∀ x ∈ Ω', ∀ y ∈ Ω', ‖fderiv ℝ Φ x - fderiv ℝ Φ y‖ ≤ L * ‖x - y‖ ^ α) :
    Work.CR.Flat.holderSeminorm 1 α (fun x => W (Φ x)) Ω'
      ≤ ENNReal.ofReal (L ^ (1 + α)) * Work.CR.Flat.holderSeminorm 1 α W Ω
        + ENNReal.ofReal L * Work.CR.Flat.iterDerivNorm 1 W Ω := by
  have hLα : (0 : ℝ) ≤ L ^ α := Real.rpow_nonneg hL α
  have hL1a : (0 : ℝ) ≤ L ^ (1 + α) := Real.rpow_nonneg hL _
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hxypos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hdpos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hxypos α
  -- real-valued abbreviations
  set P : ℝ := ‖fderiv ℝ W (Φ x) - fderiv ℝ W (Φ y)‖ with hP
  set M : ℝ := ‖fderiv ℝ W (Φ y)‖ with hM
  have hP0 : 0 ≤ P := norm_nonneg _
  have hM0 : 0 ≤ M := norm_nonneg _
  -- the norm bound for the difference of the two derivatives of the composition
  have hop : ‖iteratedFDerivWithin ℝ 1 (fun z => W (Φ z)) Ω' x
        - iteratedFDerivWithin ℝ 1 (fun z => W (Φ z)) Ω' y‖
      ≤ P * L + M * (L * ‖x - y‖ ^ α) := by
    have hgoal : ‖iteratedFDerivWithin ℝ 1 (fun z => W (Φ z)) Ω' x
          - iteratedFDerivWithin ℝ 1 (fun z => W (Φ z)) Ω' y‖
        = ‖(fderiv ℝ W (Φ x)).comp (fderiv ℝ Φ x)
            - (fderiv ℝ W (Φ y)).comp (fderiv ℝ Φ y)‖ := by
      rw [comp_norm_iteratedFDerivWithin_one_sub_eq hΩ' hx hy,
        comp_fderiv_eq hΩ hΩ' hW hΦ hmaps hx,
        comp_fderiv_eq hΩ hΩ' hW hΦ hmaps hy]
    rw [hgoal, hP, hM]
    have hdecomp : (fderiv ℝ W (Φ x)).comp (fderiv ℝ Φ x)
        - (fderiv ℝ W (Φ y)).comp (fderiv ℝ Φ y)
        = (fderiv ℝ W (Φ x) - fderiv ℝ W (Φ y)).comp (fderiv ℝ Φ x)
          + (fderiv ℝ W (Φ y)).comp (fderiv ℝ Φ x - fderiv ℝ Φ y) := by
      ext v
      simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [hdecomp]
    calc ‖(fderiv ℝ W (Φ x) - fderiv ℝ W (Φ y)).comp (fderiv ℝ Φ x)
          + (fderiv ℝ W (Φ y)).comp (fderiv ℝ Φ x - fderiv ℝ Φ y)‖
        ≤ ‖(fderiv ℝ W (Φ x) - fderiv ℝ W (Φ y)).comp (fderiv ℝ Φ x)‖
            + ‖(fderiv ℝ W (Φ y)).comp (fderiv ℝ Φ x - fderiv ℝ Φ y)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ W (Φ x) - fderiv ℝ W (Φ y)‖ * ‖fderiv ℝ Φ x‖
            + ‖fderiv ℝ W (Φ y)‖ * ‖fderiv ℝ Φ x - fderiv ℝ Φ y‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ ‖fderiv ℝ W (Φ x) - fderiv ℝ W (Φ y)‖ * L
            + ‖fderiv ℝ W (Φ y)‖ * (L * ‖x - y‖ ^ α) :=
          add_le_add (mul_le_mul_of_nonneg_left (hdΦ x hx) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hdΦα x hx y hy) (norm_nonneg _))
  -- the real bound on the quotient
  have hreal : ‖iteratedFDerivWithin ℝ 1 (fun z => W (Φ z)) Ω' x
        - iteratedFDerivWithin ℝ 1 (fun z => W (Φ z)) Ω' y‖ / ‖x - y‖ ^ α
      ≤ (P / ‖Φ x - Φ y‖ ^ α) * L ^ (1 + α) + M * L := by
    rw [div_le_iff₀ hdpos]
    calc ‖iteratedFDerivWithin ℝ 1 (fun z => W (Φ z)) Ω' x
          - iteratedFDerivWithin ℝ 1 (fun z => W (Φ z)) Ω' y‖
        ≤ P * L + M * (L * ‖x - y‖ ^ α) := hop
      _ ≤ (P / ‖Φ x - Φ y‖ ^ α) * L ^ (1 + α) * ‖x - y‖ ^ α + (M * L) * ‖x - y‖ ^ α := by
          refine add_le_add ?_ ?_
          · exact mul_le_div_mul_rpow_add hα hL hP0 (norm_nonneg _) (norm_nonneg _)
              (hlip x hx y hy) (fun hp0 => by
                rw [hP, sub_eq_zero.mp (norm_eq_zero.mp hp0), sub_self, norm_zero])
          · exact le_of_eq (by ring)
      _ = ((P / ‖Φ x - Φ y‖ ^ α) * L ^ (1 + α) + M * L) * ‖x - y‖ ^ α := by ring
  -- the two ENNReal bounds on the two coefficients
  have hSle : ENNReal.ofReal (P / ‖Φ x - Φ y‖ ^ α)
      ≤ Work.CR.Flat.holderSeminorm 1 α W Ω := by
    by_cases h : Φ x = Φ y
    · have hPzero : P = 0 := by rw [hP, h, sub_self, norm_zero]
      have : P / ‖Φ x - Φ y‖ ^ α = 0 := by
        rw [hPzero, h, sub_self, norm_zero, Real.zero_rpow (ne_of_gt hα), zero_div]
      rw [this, ENNReal.ofReal_zero]
      exact bot_le
    · have h1 := Work.CR.Flat.le_holderSeminorm 1 α W Ω (hmaps x hx) (hmaps y hy) h
      rw [comp_norm_iteratedFDerivWithin_one_sub_eq hΩ (hmaps x hx) (hmaps y hy)] at h1
      rw [← hP] at h1
      exact h1
  have hMle : ENNReal.ofReal M ≤ Work.CR.Flat.iterDerivNorm 1 W Ω := by
    rw [hM, ← comp_norm_iteratedFDerivWithin_one_eq hΩ (hmaps y hy)]
    exact Work.CR.Flat.le_iterDerivNorm 1 W Ω (hmaps y hy)
  -- assemble
  have h1 : (0 : ℝ) ≤ P / ‖Φ x - Φ y‖ ^ α :=
    div_nonneg hP0 (Real.rpow_nonneg (norm_nonneg _) α)
  calc ENNReal.ofReal (‖iteratedFDerivWithin ℝ 1 (fun z => W (Φ z)) Ω' x
        - iteratedFDerivWithin ℝ 1 (fun z => W (Φ z)) Ω' y‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal ((P / ‖Φ x - Φ y‖ ^ α) * L ^ (1 + α) + M * L) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (P / ‖Φ x - Φ y‖ ^ α) * ENNReal.ofReal (L ^ (1 + α))
          + ENNReal.ofReal M * ENNReal.ofReal L := by
        rw [ENNReal.ofReal_add (mul_nonneg h1 hL1a) (mul_nonneg hM0 hL),
          ENNReal.ofReal_mul h1, ENNReal.ofReal_mul hM0]
    _ ≤ Work.CR.Flat.holderSeminorm 1 α W Ω * ENNReal.ofReal (L ^ (1 + α))
          + Work.CR.Flat.iterDerivNorm 1 W Ω * ENNReal.ofReal L :=
        add_le_add (mul_le_mul_left hSle _) (mul_le_mul_left hMle _)
    _ = ENNReal.ofReal (L ^ (1 + α)) * Work.CR.Flat.holderSeminorm 1 α W Ω
          + ENNReal.ofReal L * Work.CR.Flat.iterDerivNorm 1 W Ω := by ring

/-- **Composition estimate for the `C^{1,α}`-norm.**  (The pointwise bound on `fderiv Φ` does not
give a global Lipschitz bound on a possibly disconnected `Ω'`, so the global Lipschitz hypothesis
`hlip` is carried explicitly.) -/
theorem holderNorm_one_comp_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α L : ℝ} (hα0 : 0 < α) (hL : 0 ≤ L)
    {Ω Ω' : Set X} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    {W : X → ℂ} {Φ : X → X} (hW : ContDiffOn ℝ 1 W Ω) (hΦ : ContDiffOn ℝ 1 Φ Ω')
    (hmaps : ∀ x ∈ Ω', Φ x ∈ Ω)
    (hlip : ∀ x ∈ Ω', ∀ y ∈ Ω', ‖Φ x - Φ y‖ ≤ L * ‖x - y‖)
    (hdΦ : ∀ x ∈ Ω', ‖fderiv ℝ Φ x‖ ≤ L)
    (hdΦα : ∀ x ∈ Ω', ∀ y ∈ Ω', ‖fderiv ℝ Φ x - fderiv ℝ Φ y‖ ≤ L * ‖x - y‖ ^ α) :
    Work.CR.Flat.holderNorm 1 α (fun x => W (Φ x)) Ω'
      ≤ ENNReal.ofReal (1 + 2 * L + L ^ (1 + α)) * Work.CR.Flat.holderNorm 1 α W Ω := by
  have h0 : Work.CR.Flat.iterDerivNorm 0 (fun x => W (Φ x)) Ω'
      ≤ Work.CR.Flat.iterDerivNorm 0 W Ω := comp_iterDerivNorm_zero_le hmaps
  have hS0 : Work.CR.Flat.holderSeminorm 0 α (fun x => W (Φ x)) Ω'
      ≤ ENNReal.ofReal (L ^ α) * Work.CR.Flat.holderSeminorm 0 α W Ω :=
    comp_holderSeminorm_zero_le hα0 hL hmaps hlip
  have h1 : Work.CR.Flat.iterDerivNorm 1 (fun x => W (Φ x)) Ω'
      ≤ ENNReal.ofReal L * Work.CR.Flat.iterDerivNorm 1 W Ω :=
    comp_iterDerivNorm_one_le hL hΩ hΩ' hW hΦ hmaps hdΦ
  have hS1 : Work.CR.Flat.holderSeminorm 1 α (fun x => W (Φ x)) Ω'
      ≤ ENNReal.ofReal (L ^ (1 + α)) * Work.CR.Flat.holderSeminorm 1 α W Ω
        + ENNReal.ofReal L * Work.CR.Flat.iterDerivNorm 1 W Ω :=
    comp_holderSeminorm_one_le hα0 hL hΩ hΩ' hW hΦ hmaps hlip hdΦ hdΦα
  have hLHS : Work.CR.Flat.holderNorm 1 α (fun x => W (Φ x)) Ω'
      = (Work.CR.Flat.iterDerivNorm 0 (fun x => W (Φ x)) Ω'
          + Work.CR.Flat.holderSeminorm 0 α (fun x => W (Φ x)) Ω')
        + (Work.CR.Flat.iterDerivNorm 1 (fun x => W (Φ x)) Ω'
          + Work.CR.Flat.holderSeminorm 1 α (fun x => W (Φ x)) Ω') := by
    simp [Work.CR.Flat.holderNorm, Finset.sum_range_succ]
  have hRHS : Work.CR.Flat.holderNorm 1 α W Ω
      = (Work.CR.Flat.iterDerivNorm 0 W Ω + Work.CR.Flat.holderSeminorm 0 α W Ω)
        + (Work.CR.Flat.iterDerivNorm 1 W Ω + Work.CR.Flat.holderSeminorm 1 α W Ω) := by
    simp [Work.CR.Flat.holderNorm, Finset.sum_range_succ]
  rw [hLHS, hRHS]
  -- abbreviations
  set c : ℝ≥0∞ := ENNReal.ofReal (1 + 2 * L + L ^ (1 + α)) with hc
  set k1 : ℝ≥0∞ := ENNReal.ofReal (L ^ α) with hk1
  set kL : ℝ≥0∞ := ENNReal.ofReal L with hkL
  set k2 : ℝ≥0∞ := ENNReal.ofReal (2 * L) with hk2
  set k3 : ℝ≥0∞ := ENNReal.ofReal (L ^ (1 + α)) with hk3
  set H0 : ℝ≥0∞ := Work.CR.Flat.iterDerivNorm 0 W Ω with hsH0
  set S0 : ℝ≥0∞ := Work.CR.Flat.holderSeminorm 0 α W Ω with hsS0
  set H1 : ℝ≥0∞ := Work.CR.Flat.iterDerivNorm 1 W Ω with hsH1
  set S1 : ℝ≥0∞ := Work.CR.Flat.holderSeminorm 1 α W Ω with hsS1
  set H0' : ℝ≥0∞ := Work.CR.Flat.iterDerivNorm 0 (fun x => W (Φ x)) Ω' with hsH0'
  set S0' : ℝ≥0∞ := Work.CR.Flat.holderSeminorm 0 α (fun x => W (Φ x)) Ω' with hsS0'
  set H1' : ℝ≥0∞ := Work.CR.Flat.iterDerivNorm 1 (fun x => W (Φ x)) Ω' with hsH1'
  set S1' : ℝ≥0∞ := Work.CR.Flat.holderSeminorm 1 α (fun x => W (Φ x)) Ω' with hsS1'
  have h0c : H0' ≤ H0 := by rw [hsH0', hsH0]; exact h0
  have hS0c : S0' ≤ k1 * S0 := by rw [hsS0', hk1, hsS0]; exact hS0
  have h1c : H1' ≤ kL * H1 := by rw [hsH1', hkL, hsH1]; exact h1
  have hS1c : S1' ≤ k3 * S1 + kL * H1 := by rw [hsS1', hk3, hsS1, hkL, hsH1]; exact hS1
  -- the constants
  have hrpowα : (0 : ℝ) ≤ L ^ α := Real.rpow_nonneg hL α
  have hrpow1a : (0 : ℝ) ≤ L ^ (1 + α) := Real.rpow_nonneg hL _
  have h2L0 : (0 : ℝ) ≤ 2 * L := by linarith
  have hc0 : (0 : ℝ) ≤ 1 + 2 * L + L ^ (1 + α) := by linarith
  have hc1 : (1 : ℝ) ≤ 1 + 2 * L + L ^ (1 + α) := by linarith
  have hle_la : L ^ α ≤ 1 + 2 * L + L ^ (1 + α) := by
    rcases lt_or_ge L 1 with hL1 | hL1
    · have h := Real.rpow_le_rpow hL (le_of_lt hL1) (le_of_lt hα0)
      rw [Real.one_rpow] at h
      linarith
    · have h := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : α ≤ 1 + α)
      linarith
  have hle_2L : 2 * L ≤ 1 + 2 * L + L ^ (1 + α) := by linarith
  have hle_1a : L ^ (1 + α) ≤ 1 + 2 * L + L ^ (1 + α) := by linarith
  have e1 : (1 : ℝ≥0∞) ≤ c := by
    rw [hc, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hc1
  have e2 : k1 ≤ c := by rw [hk1, hc]; exact ENNReal.ofReal_le_ofReal hle_la
  have e3 : k2 ≤ c := by rw [hk2, hc]; exact ENNReal.ofReal_le_ofReal hle_2L
  have e4 : k3 ≤ c := by rw [hk3, hc]; exact ENNReal.ofReal_le_ofReal hle_1a
  have e5 : k2 = 2 * kL := by
    rw [hk2, hkL, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hA : 1 * H0 ≤ c * H0 := by rw [one_mul]; exact le_mul_of_one_le_left' e1
  have hB : k1 * S0 ≤ c * S0 := mul_le_mul_left e2 S0
  have hC : k2 * H1 ≤ c * H1 := mul_le_mul_left e3 H1
  have hD : k3 * S1 ≤ c * S1 := mul_le_mul_left e4 S1
  calc (H0' + S0') + (H1' + S1')
      ≤ (H0 + k1 * S0) + (kL * H1 + (k3 * S1 + kL * H1)) :=
        add_le_add (add_le_add h0c hS0c) (add_le_add h1c hS1c)
    _ = 1 * H0 + k1 * S0 + k2 * H1 + k3 * S1 := by rw [e5]; ring
    _ ≤ c * H0 + c * S0 + c * H1 + c * S1 :=
        add_le_add (add_le_add (add_le_add hA hB) hC) hD
    _ = c * ((H0 + S0) + (H1 + S1)) := by ring

end Work.NN.Final
