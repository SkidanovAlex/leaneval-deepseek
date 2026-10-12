import Mathlib
import Submission.Work.BoseBoxFock.acubePVFacts
import Submission.Work.BoseBoxFock.slotProj1_memLp_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotProj1_oneSub_contract_box`

The single-slot projection `slotProj1 e i` projects the slot `i` of a state onto the span of the
modes `e l`, with the projection kernel `PV e x y = Σ_l e l x * star (e l y)` and orthonormal
modes `e`.  The target is the **contraction of the one-subtraction**:

    ∫_{abox} ‖f − slotProj1 e i f‖² ≤ ∫_{abox} ‖f‖²

for a state `f` that vanishes outside the box `abox n ℓ`.

## Route

Everything reduces to the box Parseval identity of the one-particle projection.  Writing
`Pg = slotProj1 e i g` (`g` an everywhere bounded measurable representative of `f`), and peeling
the box `abox (n+1) ℓ` along the slot `i` (`kcInsN`), the pointwise identity

    Pg (kcInsN i (y,r)) = Σ_l e_l(y) · c_l(r),   c_l(r) = ∫_{acube ℓ} star (e_l) · g (kcInsN i (·,r))

(`slotProj1_kcInsN_eq`) converts both the mixed integral `∫ star g · Pg` and the square integral
`∫ ‖Pg‖²` into `∫_r Σ_l ‖c_l(r)‖²`:

* `inner_star_mul_eq` uses only conjugate-linearity of the Bochner integral
  (`∫ star F · e_l = star c_l`);
* `inner_normSq_eq` uses the cube orthonormality `∫_{acube} star (e_l) e_{l'} = δ_{ll'}`
  (`acube_orthonormal_modes`).

Hence `∫_{abox} (star g * Pg).re = ∫_{abox} ‖Pg‖²`, and the pointwise
`‖g − Pg‖² = ‖g‖² − 2 (star g * Pg).re + ‖Pg‖²` gives
`∫_{abox} ‖g − Pg‖² = ∫_{abox} ‖g‖² − ∫_{abox} ‖Pg‖² ≤ ∫_{abox} ‖g‖²`.
-/

noncomputable section

namespace Work.BoseBoxFock.XwSlot

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary measure-theoretic helpers -/

private lemma finiteMeasure_restrict_acube (ℓ : ℝ) (hℓ : 0 < ℓ) :
    IsFiniteMeasure ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩

private lemma finiteMeasure_restrict_abox (n : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top n ℓ hℓ.le⟩

/-- A mode, restricted to the cube, is in `L^∞`. -/
private lemma memLp_top_acube_mode {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (l : Fin m) :
    MemLp (e l) ⊤ ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) :=
  (hbdd l).mono_measure Measure.restrict_le_self

/-- A finite combination `Σ_l e_l(y) c_l` is in `L^∞` on the cube. -/
private lemma memLp_top_sum_mode_mul {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (c : Fin m → ℂ) :
    MemLp (fun y : Ω => ∑ l : Fin m, e l y * c l) ⊤
      ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) :=
  memLp_finsetSum (s := Finset.univ) (p := ⊤)
    (fun l _ => (memLp_top_acube_mode hbdd hsupp l).mul_const (c l))

/-! ## 2. The orthonormality of the modes over the cube -/

/-- The modes are orthonormal **over the cube**: since they are supported in
`boxL ℓ = acube ℓ`, the full-space orthonormality restricts to the cube. -/
theorem acube_orthonormal_modes {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Ω → ℂ}
    (he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (l l' : Fin m) :
    (∫ y in Submission.BoseGases.acube ℓ, star (e l y) * e l' y) = if l = l' then 1 else 0 := by
  have hpt : (fun y : Ω => star (e l y) * e l' y)
      = (Submission.BoseGases.acube ℓ).indicator (fun y : Ω => star (e l y) * e l' y) := by
    funext y
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hz : e l y = 0 := by
        by_contra hne
        exact hy (by rw [← boxL_eq_acube hℓ]; exact hsupp l (Function.mem_support.mpr hne))
      rw [hz, star_zero, zero_mul]
  have h1 : (∫ y in Submission.BoseGases.acube ℓ, star (e l y) * e l' y)
      = ∫ y, star (e l y) * e l' y := by
    rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun y => (congrFun hpt y).symm))
  rw [h1]
  simpa only [Complex.star_def] using he l l'

/-! ## 3. The `L²` bridge `∫ ‖W‖² = (∫ star W · W).re` -/

private lemma re_mul_conj_comm (z w : ℂ) :
    (z * (starRingEnd ℂ) w).re = ((starRingEnd ℂ) z * w).re := by
  rw [Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.conj_re,
    Complex.conj_im]
  ring

private lemma norm_sub_sq_complex' (z w : ℂ) :
    ‖z - w‖ ^ 2 = ‖z‖ ^ 2 - 2 * ((starRingEnd ℂ) z * w).re + ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, re_mul_conj_comm]
  ring

/-- The pointwise norm-subtraction identity in `ℂ`. -/
private lemma norm_sub_sq_complex (z w : ℂ) :
    ‖z - w‖ ^ 2 = ‖z‖ ^ 2 - 2 * (star z * w).re + ‖w‖ ^ 2 :=
  norm_sub_sq_complex' z w

private lemma star_mul_self_eq (z : ℂ) : star z * z = ↑(Complex.normSq z) := by
  rw [mul_comm, show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj]

private lemma star_mul_self_re (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [star_mul_self_eq, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

private lemma mul_star_self_eq (z : ℂ) : z * star z = ↑(Complex.normSq z) := by
  rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj]

private lemma integral_normSq_eq_re {α : Type*} [MeasurableSpace α] (μ : Measure α) {W : α → ℂ}
    (hW : Integrable (fun y => star (W y) * W y) μ) :
    (∫ y, ‖W y‖ ^ 2 ∂μ) = (∫ y, star (W y) * W y ∂μ).re := by
  have h1 : (∫ y, ‖W y‖ ^ 2 ∂μ) = ∫ y, (star (W y) * W y).re ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by
      show ‖W y‖ ^ 2 = (star (W y) * W y).re
      exact (star_mul_self_re (W y)).symm))
  have h2 := ContinuousLinearMap.integral_comp_comm Complex.reCLM hW
  simp only [Complex.reCLM_apply] at h2
  rw [h1]
  exact h2

/-! ## 4. The coefficient Parseval identities over the cube -/

/-- **Conjugate symmetry of the coefficient.**  The conjugate of the `l`-th coefficient of `F` is
the integral of `star F · e_l`. -/
private lemma star_cubeCoeff {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ} {F : Ω → ℂ} (l : Fin m) :
    star (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)
      = ∫ w in Submission.BoseGases.acube ℓ, star (F w) * e l w := by
  have h := slotStar_integral ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ))
    (fun w : Ω => star (e l w) * F w)
  rw [h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  show star (star (e l w) * F w) = star (F w) * e l w
  rw [star_mul, star_star]

/-- **The coefficient Parseval identity, star form.**  Integrating `star F` against the expansion
`Σ_l e_l c_l` of `F` in the modes returns `Σ_l ‖c_l‖²`. -/
theorem integral_star_mul_cubeCoeff {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Ω → ℂ}
    (he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {F : Ω → ℂ} (hFm : Measurable F) (hFb : ∃ C, ∀ y, ‖F y‖ ≤ C) :
    (∫ y in Submission.BoseGases.acube ℓ,
        star (F y) * (∑ l : Fin m, e l y *
          (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)))
      = ((∑ l : Fin m,
          ‖(∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)‖ ^ 2 : ℝ) : ℂ) := by
  haveI := finiteMeasure_restrict_acube ℓ hℓ
  obtain ⟨C, hC⟩ := hFb
  have hint : ∀ l : Fin m, Integrable
      (fun y : Ω => star (F y) * (e l y * (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)))
      ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) := by
    intro l
    refine MeasureTheory.MemLp.integrable le_top ?_
    refine MeasureTheory.MemLp.mul
      (MeasureTheory.memLp_top_of_bound (continuous_star.measurable.comp hFm).aestronglyMeasurable C
        (Filter.Eventually.of_forall (fun y => by simpa using hC y)))
      ((memLp_top_acube_mode hbdd hsupp l).mul_const _)
  have hpt : (fun y : Ω => star (F y) * (∑ l : Fin m, e l y *
        (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)))
      = (fun y : Ω => ∑ l : Fin m, star (F y) *
          (e l y * (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w))) := by
    funext y
    rw [Finset.mul_sum]
  rw [hpt, MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun l : Fin m => fun y : Ω => star (F y) *
        (e l y * (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)))
      (fun l _ => hint l)]
  have hstep : (fun l : Fin m => ∫ y in Submission.BoseGases.acube ℓ, star (F y) *
        (e l y * (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)))
      = (fun l : Fin m => (∫ y in Submission.BoseGases.acube ℓ, star (F y) * e l y) *
          (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)) := by
    funext l
    rw [show (fun y : Ω => star (F y) * (e l y * (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)))
        = (fun y : Ω => (star (F y) * e l y) * (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w))
        from funext fun y => by ring]
    rw [MeasureTheory.integral_mul_const]
  rw [hstep]
  have hstep2 : (fun l : Fin m => (∫ y in Submission.BoseGases.acube ℓ, star (F y) * e l y) *
        (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w))
      = (fun l : Fin m => star (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w) *
          (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)) := by
    funext l
    rw [star_cubeCoeff]
  rw [hstep2, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [star_mul_self_eq, Complex.normSq_eq_norm_sq]

/-- **The coefficient Parseval identity, norm-square form.** -/
theorem integral_mul_star_cubeCoeff {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Ω → ℂ}
    (he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (c : Fin m → ℂ) :
    (∫ y in Submission.BoseGases.acube ℓ,
        star (∑ l : Fin m, e l y * c l) * (∑ l : Fin m, e l y * c l))
      = ((∑ l : Fin m, ‖c l‖ ^ 2 : ℝ) : ℂ) := by
  haveI := finiteMeasure_restrict_acube ℓ hℓ
  have hprod : ∀ l l' : Fin m, MemLp (fun y : Ω => star (e l y) * e l' y) ⊤
      ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) := fun l l' =>
    MeasureTheory.MemLp.mul ((memLp_top_acube_mode hbdd hsupp l).star)
      (memLp_top_acube_mode hbdd hsupp l')
  have hint : ∀ l l' : Fin m, Integrable
      (fun y : Ω => (star (c l) * (star (e l y) * e l' y)) * c l')
      ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) := fun l l' =>
    MeasureTheory.MemLp.integrable le_top (((hprod l l').const_mul (star (c l))).mul_const (c l'))
  have hpt : (fun y : Ω => star (∑ l : Fin m, e l y * c l) * (∑ l : Fin m, e l y * c l))
      = (fun y : Ω => ∑ l : Fin m, ∑ l' : Fin m,
          (star (c l) * (star (e l y) * e l' y)) * c l') := by
    funext y
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    show star (e l y * c l) * (∑ l' : Fin m, e l' y * c l')
        = ∑ l' : Fin m, (star (c l) * (star (e l y) * e l' y)) * c l'
    rw [star_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l' _ => ?_)
    ring
  calc (∫ y in Submission.BoseGases.acube ℓ,
          star (∑ l : Fin m, e l y * c l) * (∑ l : Fin m, e l y * c l))
      = ∫ y in Submission.BoseGases.acube ℓ, ∑ l : Fin m, ∑ l' : Fin m,
          (star (c l) * (star (e l y) * e l' y)) * c l' := by
        rw [hpt]
    _ = ∑ l : Fin m, ∑ l' : Fin m,
          (star (c l) * (if l = l' then (1 : ℂ) else 0)) * c l' := by
        rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
            (f := fun l : Fin m => fun y : Ω => ∑ l' : Fin m,
              (star (c l) * (star (e l y) * e l' y)) * c l')
            (fun l _ => integrable_finsetSum _ (fun l' _ => hint l l'))]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
            (f := fun l' : Fin m => fun y : Ω => (star (c l) * (star (e l y) * e l' y)) * c l')
            (fun l' _ => hint l l')]
        refine Finset.sum_congr rfl (fun l' _ => ?_)
        rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul,
          acube_orthonormal_modes hℓ he hbdd hsupp l l']
    _ = ((∑ l : Fin m, ‖c l‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.sum_eq_single l]
        · rw [if_pos rfl, mul_one, star_mul_self_eq, Complex.normSq_eq_norm_sq]
        · intro l' _ hl'
          rw [if_neg (Ne.symm hl'), mul_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ l) h

/-! ## 5. The peeled pointwise form of the projection -/

/-- **The single-slot projection at a peeled configuration.**  Peeling the slot `i` off
`x = kcInsN n i (y,r)` turns the projection into the expansion of the fibre in the modes, with the
coefficients the cube-integrals of `star (e l) · g`. -/
theorem slotProj1_kcInsN_eq {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Ω → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {g : Submission.BoseGases.X (n+1) → ℂ} (hgm : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C)
    (i : Fin (n+1)) (y : Ω) (r : Submission.BoseGases.X n) :
    slotProj1 e i g (Submission.BoseGases.kcInsN n i (y, r))
      = ∑ l : Fin m, e l y *
          (∫ w in Submission.BoseGases.acube ℓ, star (e l w)
              * g (Submission.BoseGases.kcInsN n i (w, r))) := by
  haveI := finiteMeasure_restrict_acube ℓ hℓ
  obtain ⟨C, hC⟩ := hgb
  have hins : Measurable (fun w : Ω => Submission.BoseGases.kcInsN n i (w, r)) :=
    (Submission.BoseGases.kcInsN n i).measurable.comp
      (measurable_id.prodMk measurable_const)
  have hint : ∀ l : Fin m, Integrable
      (fun w : Ω => star (e l w) * g (Submission.BoseGases.kcInsN n i (w, r)))
      ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) := by
    intro l
    refine MeasureTheory.MemLp.integrable le_top ?_
    exact MeasureTheory.MemLp.mul
      ((memLp_top_acube_mode hbdd hsupp l).star)
      (MeasureTheory.memLp_top_of_bound (hgm.comp hins).aestronglyMeasurable C
        (Filter.Eventually.of_forall (fun w => hC _)))
  have h1 : slotProj1 e i g (Submission.BoseGases.kcInsN n i (y, r))
      = ∫ w : Ω, (∑ l : Fin m, e l y * star (e l w))
          * g (Submission.BoseGases.kcInsN n i (w, r)) := by
    rw [slotProj1]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    simp only [PV]
    rw [Submission.BoseGases.kc_insN_apply_same n i y r,
      Submission.BoseGases.update_kcInsN i y w r]
  have h2 : (∫ w : Ω, (∑ l : Fin m, e l y * star (e l w))
        * g (Submission.BoseGases.kcInsN n i (w, r)))
      = ∫ w in Submission.BoseGases.acube ℓ, (∑ l : Fin m, e l y * star (e l w))
        * g (Submission.BoseGases.kcInsN n i (w, r)) := by
    rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    by_cases hw : w ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw]
      have hz : (∑ l : Fin m, e l y * star (e l w)) = 0 := by
        refine Finset.sum_eq_zero (fun l _ => ?_)
        have h0 : e l w = 0 := by
          by_contra hne
          exact hw (by rw [← boxL_eq_acube hℓ]; exact hsupp l (Function.mem_support.mpr hne))
        rw [h0, star_zero, mul_zero]
      simp only [hz, zero_mul]
  rw [h1, h2]
  have h3 : (fun w : Ω => (∑ l : Fin m, e l y * star (e l w))
        * g (Submission.BoseGases.kcInsN n i (w, r)))
      = (fun w : Ω => ∑ l : Fin m, e l y *
          (star (e l w) * g (Submission.BoseGases.kcInsN n i (w, r)))) := by
    funext w
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [h3, MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun l : Fin m => fun w : Ω => e l y *
        (star (e l w) * g (Submission.BoseGases.kcInsN n i (w, r))))
      (fun l _ => (hint l).const_mul _)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [MeasureTheory.integral_const_mul]

/-! ## 6. The two per-fibre evaluations -/

/-- **The star form of the fibre expansion.** -/
theorem inner_star_mul_eq {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Ω → ℂ}
    (he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {F : Ω → ℂ} (hFm : Measurable F) (hFb : ∃ C, ∀ y, ‖F y‖ ≤ C) :
    (∫ y in Submission.BoseGases.acube ℓ,
        (star (F y) * (∑ l : Fin m, e l y *
          (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w))).re)
      = ∑ l : Fin m, ‖(∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)‖ ^ 2 := by
  haveI := finiteMeasure_restrict_acube ℓ hℓ
  have hFb' : ∃ C, ∀ y, ‖F y‖ ≤ C := hFb
  obtain ⟨C, hC⟩ := hFb
  have hInt : Integrable
      (fun y : Ω => star (F y) * (∑ l : Fin m, e l y *
        (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)))
      ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) := by
    refine MeasureTheory.MemLp.integrable le_top ?_
    exact MeasureTheory.MemLp.mul
      (MeasureTheory.memLp_top_of_bound (continuous_star.measurable.comp hFm).aestronglyMeasurable C
        (Filter.Eventually.of_forall (fun y => by simpa using hC y)))
      (memLp_top_sum_mode_mul hbdd hsupp
        (fun l => ∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w))
  have hre := ContinuousLinearMap.integral_comp_comm Complex.reCLM hInt
  simp only [Complex.reCLM_apply] at hre
  rw [hre, integral_star_mul_cubeCoeff hℓ he hbdd hsupp (F := F) hFm hFb', Complex.ofReal_re]

/-- **The norm-square form of the fibre expansion.** -/
theorem inner_normSq_eq {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Ω → ℂ}
    (he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {F : Ω → ℂ} (hFm : Measurable F) (hFb : ∃ C, ∀ y, ‖F y‖ ≤ C) :
    (∫ y in Submission.BoseGases.acube ℓ,
        ‖∑ l : Fin m, e l y * (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)‖ ^ 2)
      = ∑ l : Fin m, ‖(∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)‖ ^ 2 := by
  haveI := finiteMeasure_restrict_acube ℓ hℓ
  have hW : MemLp (fun y : Ω => ∑ l : Fin m, e l y *
      (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)) ⊤
      ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) :=
    memLp_top_sum_mode_mul hbdd hsupp
      (fun l => ∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)
  have hInt : Integrable (fun y : Ω => star (∑ l : Fin m, e l y *
      (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)) * (∑ l : Fin m, e l y *
      (∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w)))
      ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) :=
    MeasureTheory.MemLp.integrable le_top (MeasureTheory.MemLp.mul hW.star hW)
  rw [integral_normSq_eq_re _ hInt,
    integral_mul_star_cubeCoeff hℓ he hbdd hsupp
      (fun l : Fin m => ∫ w in Submission.BoseGases.acube ℓ, star (e l w) * F w),
    Complex.ofReal_re]

/-! ## 7. (moved to §3) -/

/-! ## 8. The contraction for an everywhere bounded measurable state -/

theorem oneSub_contract_bdd {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Ω → ℂ}
    (he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {g : Submission.BoseGases.X n → ℂ}
    (hgm : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    (∫ x in Submission.BoseGases.abox n ℓ, ‖g x - slotProj1 e i g x‖ ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖g x‖ ^ 2 := by
  classical
  cases n with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n' =>
    have hgb' : ∃ C, ∀ x, ‖g x‖ ≤ C := hgb
    obtain ⟨C, hC⟩ := hgb
    have hC0 : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0)
    have hgmem : MemLp g ⊤ :=
      memLp_top_of_bound hgm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
    obtain ⟨CPg, hCPg⟩ := slotProj1_ae_bounded hbdd hsupp i hgmem
    have hPg_aesm : AEStronglyMeasurable (slotProj1 e i g)
        (volume : Measure (Submission.BoseGases.X (n'+1))) :=
      slotProj1_aesm (fun l => (hbdd l).aestronglyMeasurable) i hgm.aestronglyMeasurable
    -- integrability of the three pieces over the box
    have hIC : Integrable (fun x : Submission.BoseGases.X (n'+1) => ‖slotProj1 e i g x‖ ^ 2)
        ((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
          (Submission.BoseGases.abox (n'+1) ℓ)) := by
      haveI := finiteMeasure_restrict_abox (n'+1) ℓ hℓ
      refine MeasureTheory.Integrable.of_bound
        ((hPg_aesm.mono_measure Measure.restrict_le_self).norm.pow 2) (CPg ^ 2) ?_
      filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hCPg] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hIB : Integrable
        (fun x : Submission.BoseGases.X (n'+1) => (star (g x) * slotProj1 e i g x).re)
        ((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
          (Submission.BoseGases.abox (n'+1) ℓ)) := by
      haveI := finiteMeasure_restrict_abox (n'+1) ℓ hℓ
      refine MeasureTheory.Integrable.of_bound
        (((hgm.aestronglyMeasurable.star).mul hPg_aesm).re.mono_measure
          Measure.restrict_le_self) (C * CPg) ?_
      filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hCPg] with x hx
      calc ‖(star (g x) * slotProj1 e i g x).re‖
          = |(star (g x) * slotProj1 e i g x).re| := Real.norm_eq_abs _
        _ ≤ ‖star (g x) * slotProj1 e i g x‖ := Complex.abs_re_le_norm _
        _ = ‖g x‖ * ‖slotProj1 e i g x‖ := by rw [norm_mul, norm_star]
        _ ≤ C * CPg := mul_le_mul (hC x) hx (norm_nonneg _) hC0
    have hIA : Integrable (fun x : Submission.BoseGases.X (n'+1) => ‖g x‖ ^ 2)
        ((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
          (Submission.BoseGases.abox (n'+1) ℓ)) := by
      haveI := finiteMeasure_restrict_abox (n'+1) ℓ hℓ
      refine MeasureTheory.Integrable.of_bound
        ((hgm.aestronglyMeasurable.norm.pow 2).mono_measure Measure.restrict_le_self) (C ^ 2) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
    -- the peel of the box along the slot `i`
    have hpeel2 := Submission.BoseGases.abox_integral_peel (n := n') (ℓ := ℓ) i
      (fun x : Submission.BoseGases.X (n'+1) => ‖slotProj1 e i g x‖ ^ 2) hIC
    have hpeel1 := Submission.BoseGases.abox_integral_peel (n := n') (ℓ := ℓ) i
      (fun x : Submission.BoseGases.X (n'+1) => (star (g x) * slotProj1 e i g x).re) hIB
    -- the per-fibre evaluations
    have hInner2 : ∀ r : Submission.BoseGases.X n',
        (∫ y in Submission.BoseGases.acube ℓ,
            ‖slotProj1 e i g (Submission.BoseGases.kcInsN n' i (y, r))‖ ^ 2)
          = ∑ l : Fin m, ‖(∫ w in Submission.BoseGases.acube ℓ, star (e l w)
              * g (Submission.BoseGases.kcInsN n' i (w, r)))‖ ^ 2 := by
      intro r
      have hins : Measurable (fun w : Ω => Submission.BoseGases.kcInsN n' i (w, r)) :=
        (Submission.BoseGases.kcInsN n' i).measurable.comp
          (measurable_id.prodMk measurable_const)
      have hpt : ∀ y : Ω,
          ‖slotProj1 e i g (Submission.BoseGases.kcInsN n' i (y, r))‖ ^ 2
            = ‖∑ l : Fin m, e l y * (∫ w in Submission.BoseGases.acube ℓ, star (e l w)
                * g (Submission.BoseGases.kcInsN n' i (w, r)))‖ ^ 2 := by
        intro y
        rw [slotProj1_kcInsN_eq hℓ hbdd hsupp hgm hgb' i y r]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact inner_normSq_eq hℓ he hbdd hsupp
        (F := fun w => g (Submission.BoseGases.kcInsN n' i (w, r)))
        (hgm.comp hins) ⟨C, fun w => hC _⟩
    have hInner1 : ∀ r : Submission.BoseGases.X n',
        (∫ y in Submission.BoseGases.acube ℓ,
            (star (g (Submission.BoseGases.kcInsN n' i (y, r)))
              * slotProj1 e i g (Submission.BoseGases.kcInsN n' i (y, r))).re)
          = ∑ l : Fin m, ‖(∫ w in Submission.BoseGases.acube ℓ, star (e l w)
              * g (Submission.BoseGases.kcInsN n' i (w, r)))‖ ^ 2 := by
      intro r
      have hins : Measurable (fun w : Ω => Submission.BoseGases.kcInsN n' i (w, r)) :=
        (Submission.BoseGases.kcInsN n' i).measurable.comp
          (measurable_id.prodMk measurable_const)
      have hpt : ∀ y : Ω,
          (star (g (Submission.BoseGases.kcInsN n' i (y, r)))
              * slotProj1 e i g (Submission.BoseGases.kcInsN n' i (y, r))).re
            = (star (g (Submission.BoseGases.kcInsN n' i (y, r)))
                * (∑ l : Fin m, e l y * (∫ w in Submission.BoseGases.acube ℓ, star (e l w)
                    * g (Submission.BoseGases.kcInsN n' i (w, r))))).re := by
        intro y
        rw [slotProj1_kcInsN_eq hℓ hbdd hsupp hgm hgb' i y r]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact inner_star_mul_eq hℓ he hbdd hsupp
        (F := fun w => g (Submission.BoseGases.kcInsN n' i (w, r)))
        (hgm.comp hins) ⟨C, fun w => hC _⟩
    -- the two box integrals agree
    have hB : (∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖slotProj1 e i g x‖ ^ 2)
        = ∫ r in Submission.BoseGases.abox n' ℓ,
            ∑ l : Fin m, ‖(∫ w in Submission.BoseGases.acube ℓ, star (e l w)
                * g (Submission.BoseGases.kcInsN n' i (w, r)))‖ ^ 2 := by
      rw [hpeel2]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun r => hInner2 r))
    have hA : (∫ x in Submission.BoseGases.abox (n'+1) ℓ,
          (star (g x) * slotProj1 e i g x).re)
        = ∫ r in Submission.BoseGases.abox n' ℓ,
            ∑ l : Fin m, ‖(∫ w in Submission.BoseGases.acube ℓ, star (e l w)
                * g (Submission.BoseGases.kcInsN n' i (w, r)))‖ ^ 2 := by
      rw [hpeel1]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
      exact hInner1 r
    have hkey : (∫ x in Submission.BoseGases.abox (n'+1) ℓ,
          (star (g x) * slotProj1 e i g x).re)
        = ∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖slotProj1 e i g x‖ ^ 2 :=
      hA.trans hB.symm
    -- the pointwise expansion
    have hpb : (∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖g x - slotProj1 e i g x‖ ^ 2)
        = (∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖g x‖ ^ 2)
          - 2 * (∫ x in Submission.BoseGases.abox (n'+1) ℓ,
              (star (g x) * slotProj1 e i g x).re)
          + ∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖slotProj1 e i g x‖ ^ 2 := by
      have hcongr : (fun x : Submission.BoseGases.X (n'+1) => ‖g x - slotProj1 e i g x‖ ^ 2)
          = (fun x : Submission.BoseGases.X (n'+1) =>
              (‖g x‖ ^ 2 - 2 * (star (g x) * slotProj1 e i g x).re)
                + ‖slotProj1 e i g x‖ ^ 2) := by
        funext x
        rw [norm_sub_sq_complex]
      calc (∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖g x - slotProj1 e i g x‖ ^ 2)
          = ∫ x in Submission.BoseGases.abox (n'+1) ℓ,
              ((‖g x‖ ^ 2 - 2 * (star (g x) * slotProj1 e i g x).re)
                + ‖slotProj1 e i g x‖ ^ 2) := by
            rw [hcongr]
        _ = (∫ x in Submission.BoseGases.abox (n'+1) ℓ,
                (‖g x‖ ^ 2 - 2 * (star (g x) * slotProj1 e i g x).re))
              + ∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖slotProj1 e i g x‖ ^ 2 :=
            MeasureTheory.integral_add (hIA.sub (hIB.const_mul 2)) hIC
        _ = ((∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖g x‖ ^ 2)
                - (∫ x in Submission.BoseGases.abox (n'+1) ℓ,
                    2 * (star (g x) * slotProj1 e i g x).re))
              + ∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖slotProj1 e i g x‖ ^ 2 := by
            rw [MeasureTheory.integral_sub hIA (hIB.const_mul 2)]
        _ = ((∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖g x‖ ^ 2)
                - 2 * (∫ x in Submission.BoseGases.abox (n'+1) ℓ,
                    (star (g x) * slotProj1 e i g x).re))
              + ∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖slotProj1 e i g x‖ ^ 2 := by
            rw [MeasureTheory.integral_const_mul]
        _ = (∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖g x‖ ^ 2)
              - 2 * (∫ x in Submission.BoseGases.abox (n'+1) ℓ,
                  (star (g x) * slotProj1 e i g x).re)
              + ∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖slotProj1 e i g x‖ ^ 2 := by
            ring
    have hfin : (∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖g x - slotProj1 e i g x‖ ^ 2)
        = (∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖g x‖ ^ 2)
          - ∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖slotProj1 e i g x‖ ^ 2 := by
      rw [hpb, hkey]
      ring
    rw [hfin]
    have hnn : 0 ≤ ∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖slotProj1 e i g x‖ ^ 2 :=
      MeasureTheory.integral_nonneg (fun x => by positivity)
    linarith

/-! ## 9. The target -/

theorem slotProj1_oneSub_contract_box {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {f : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ} (hf : MeasureTheory.MemLp f ⊤)
    (hf0 : ∀ x, x ∉ Submission.BoseGases.abox n ℓ → f x = 0) :
    (∫ x in Submission.BoseGases.abox n ℓ, ‖f x - Work.BoseBoxFock.slotProj1 e i f x‖ ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖f x‖ ^ 2 := by
  classical
  obtain ⟨g, C, hC0, hCb, hgsm, hgeq⟩ :=
    exists_bdd_sm_repr_aux (volume : Measure (Submission.BoseGases.X n)) hf
  have hPgeq : slotProj1 e i f
      =ᵐ[(volume : Measure (Submission.BoseGases.X n))] slotProj1 e i g :=
    slotProj1_ae_eq_congr_aux e i hgeq
  have hLHS : (∫ x in Submission.BoseGases.abox n ℓ,
        ‖f x - Work.BoseBoxFock.slotProj1 e i f x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, ‖g x - slotProj1 e i g x‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_ae (Submission.BoseGases.abox_measurable n ℓ) ?_
    filter_upwards [hgeq, hPgeq] with x hx1 hx2 _
    rw [hx1, hx2]
  have hRHS : (∫ x in Submission.BoseGases.abox n ℓ, ‖f x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, ‖g x‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_ae (Submission.BoseGases.abox_measurable n ℓ) ?_
    filter_upwards [hgeq] with x hx1 _
    rw [hx1]
  rw [hLHS, hRHS]
  exact oneSub_contract_bdd hℓ he hbdd hsupp i hgsm.measurable ⟨C, hCb⟩

end Work.BoseBoxFock.XwSlot

namespace Work.BoseBoxFock.XwSlot

open MeasureTheory

set_option autoImplicit false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 10. The contraction of the slot projection itself -/

/-- **The box pairing of a bounded measurable state with its slot projection**:
`∫_{abox} (star g · P_i g).re = ∫_{abox} ‖P_i g‖²`.  This is the box form of "`P_i` is an
orthogonal projection", obtained from the two per-fibre Parseval evaluations. -/
theorem inner_pair_eq_normSq_bdd {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Ω → ℂ}
    (he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {g : Submission.BoseGases.X n → ℂ}
    (hgm : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    (∫ x in Submission.BoseGases.abox n ℓ, (star (g x) * slotProj1 e i g x).re)
      = ∫ x in Submission.BoseGases.abox n ℓ, ‖slotProj1 e i g x‖ ^ 2 := by
  classical
  cases n with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n' =>
    have hgb' : ∃ C, ∀ x, ‖g x‖ ≤ C := hgb
    obtain ⟨C, hC⟩ := hgb
    have hC0 : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0)
    have hgmem : MemLp g ⊤ :=
      memLp_top_of_bound hgm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
    obtain ⟨CPg, hCPg⟩ := slotProj1_ae_bounded hbdd hsupp i hgmem
    have hPg_aesm : AEStronglyMeasurable (slotProj1 e i g)
        (volume : Measure (Submission.BoseGases.X (n'+1))) :=
      slotProj1_aesm (fun l => (hbdd l).aestronglyMeasurable) i hgm.aestronglyMeasurable
    -- integrability of the three pieces over the box
    have hIC : Integrable (fun x : Submission.BoseGases.X (n'+1) => ‖slotProj1 e i g x‖ ^ 2)
        ((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
          (Submission.BoseGases.abox (n'+1) ℓ)) := by
      haveI := finiteMeasure_restrict_abox (n'+1) ℓ hℓ
      refine MeasureTheory.Integrable.of_bound
        ((hPg_aesm.mono_measure Measure.restrict_le_self).norm.pow 2) (CPg ^ 2) ?_
      filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hCPg] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hIB : Integrable
        (fun x : Submission.BoseGases.X (n'+1) => (star (g x) * slotProj1 e i g x).re)
        ((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
          (Submission.BoseGases.abox (n'+1) ℓ)) := by
      haveI := finiteMeasure_restrict_abox (n'+1) ℓ hℓ
      refine MeasureTheory.Integrable.of_bound
        (((hgm.aestronglyMeasurable.star).mul hPg_aesm).re.mono_measure
          Measure.restrict_le_self) (C * CPg) ?_
      filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hCPg] with x hx
      calc ‖(star (g x) * slotProj1 e i g x).re‖
          = |(star (g x) * slotProj1 e i g x).re| := Real.norm_eq_abs _
        _ ≤ ‖star (g x) * slotProj1 e i g x‖ := Complex.abs_re_le_norm _
        _ = ‖g x‖ * ‖slotProj1 e i g x‖ := by rw [norm_mul, norm_star]
        _ ≤ C * CPg := mul_le_mul (hC x) hx (norm_nonneg _) hC0
    have hIA : Integrable (fun x : Submission.BoseGases.X (n'+1) => ‖g x‖ ^ 2)
        ((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
          (Submission.BoseGases.abox (n'+1) ℓ)) := by
      haveI := finiteMeasure_restrict_abox (n'+1) ℓ hℓ
      refine MeasureTheory.Integrable.of_bound
        ((hgm.aestronglyMeasurable.norm.pow 2).mono_measure Measure.restrict_le_self) (C ^ 2) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
    -- the peel of the box along the slot `i`
    have hpeel2 := Submission.BoseGases.abox_integral_peel (n := n') (ℓ := ℓ) i
      (fun x : Submission.BoseGases.X (n'+1) => ‖slotProj1 e i g x‖ ^ 2) hIC
    have hpeel1 := Submission.BoseGases.abox_integral_peel (n := n') (ℓ := ℓ) i
      (fun x : Submission.BoseGases.X (n'+1) => (star (g x) * slotProj1 e i g x).re) hIB
    -- the per-fibre evaluations
    have hInner2 : ∀ r : Submission.BoseGases.X n',
        (∫ y in Submission.BoseGases.acube ℓ,
            ‖slotProj1 e i g (Submission.BoseGases.kcInsN n' i (y, r))‖ ^ 2)
          = ∑ l : Fin m, ‖(∫ w in Submission.BoseGases.acube ℓ, star (e l w)
              * g (Submission.BoseGases.kcInsN n' i (w, r)))‖ ^ 2 := by
      intro r
      have hins : Measurable (fun w : Ω => Submission.BoseGases.kcInsN n' i (w, r)) :=
        (Submission.BoseGases.kcInsN n' i).measurable.comp
          (measurable_id.prodMk measurable_const)
      have hpt : ∀ y : Ω,
          ‖slotProj1 e i g (Submission.BoseGases.kcInsN n' i (y, r))‖ ^ 2
            = ‖∑ l : Fin m, e l y * (∫ w in Submission.BoseGases.acube ℓ, star (e l w)
                * g (Submission.BoseGases.kcInsN n' i (w, r)))‖ ^ 2 := by
        intro y
        rw [slotProj1_kcInsN_eq hℓ hbdd hsupp hgm hgb' i y r]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact inner_normSq_eq hℓ he hbdd hsupp
        (F := fun w => g (Submission.BoseGases.kcInsN n' i (w, r)))
        (hgm.comp hins) ⟨C, fun w => hC _⟩
    have hInner1 : ∀ r : Submission.BoseGases.X n',
        (∫ y in Submission.BoseGases.acube ℓ,
            (star (g (Submission.BoseGases.kcInsN n' i (y, r)))
              * slotProj1 e i g (Submission.BoseGases.kcInsN n' i (y, r))).re)
          = ∑ l : Fin m, ‖(∫ w in Submission.BoseGases.acube ℓ, star (e l w)
              * g (Submission.BoseGases.kcInsN n' i (w, r)))‖ ^ 2 := by
      intro r
      have hins : Measurable (fun w : Ω => Submission.BoseGases.kcInsN n' i (w, r)) :=
        (Submission.BoseGases.kcInsN n' i).measurable.comp
          (measurable_id.prodMk measurable_const)
      have hpt : ∀ y : Ω,
          (star (g (Submission.BoseGases.kcInsN n' i (y, r)))
              * slotProj1 e i g (Submission.BoseGases.kcInsN n' i (y, r))).re
            = (star (g (Submission.BoseGases.kcInsN n' i (y, r)))
                * (∑ l : Fin m, e l y * (∫ w in Submission.BoseGases.acube ℓ, star (e l w)
                    * g (Submission.BoseGases.kcInsN n' i (w, r))))).re := by
        intro y
        rw [slotProj1_kcInsN_eq hℓ hbdd hsupp hgm hgb' i y r]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact inner_star_mul_eq hℓ he hbdd hsupp
        (F := fun w => g (Submission.BoseGases.kcInsN n' i (w, r)))
        (hgm.comp hins) ⟨C, fun w => hC _⟩
    -- the two box integrals agree
    have hB : (∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖slotProj1 e i g x‖ ^ 2)
        = ∫ r in Submission.BoseGases.abox n' ℓ,
            ∑ l : Fin m, ‖(∫ w in Submission.BoseGases.acube ℓ, star (e l w)
                * g (Submission.BoseGases.kcInsN n' i (w, r)))‖ ^ 2 := by
      rw [hpeel2]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun r => hInner2 r))
    have hA : (∫ x in Submission.BoseGases.abox (n'+1) ℓ,
          (star (g x) * slotProj1 e i g x).re)
        = ∫ r in Submission.BoseGases.abox n' ℓ,
            ∑ l : Fin m, ‖(∫ w in Submission.BoseGases.acube ℓ, star (e l w)
                * g (Submission.BoseGases.kcInsN n' i (w, r)))‖ ^ 2 := by
      rw [hpeel1]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
      exact hInner1 r
    exact hA.trans hB.symm
/-- **The slot projection is an `L²`-contraction on the box**, for an everywhere bounded
measurable state: `∫_{abox} ‖P_i g‖² ≤ ∫_{abox} ‖g‖²`. -/
theorem contract_bdd {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Ω → ℂ}
    (he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {g : Submission.BoseGases.X n → ℂ}
    (hgm : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    (∫ x in Submission.BoseGases.abox n ℓ, ‖slotProj1 e i g x‖ ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖g x‖ ^ 2 := by
  classical
  cases n with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n' =>
    haveI := finiteMeasure_restrict_abox (n'+1) ℓ hℓ
    have hgb' : ∃ C, ∀ x, ‖g x‖ ≤ C := hgb
    obtain ⟨C, hC⟩ := hgb
    have hC0 : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0)
    have hgmem : MemLp g ⊤ :=
      memLp_top_of_bound hgm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
    obtain ⟨CPg, hCPg⟩ := slotProj1_ae_bounded hbdd hsupp i hgmem
    have hPg_aesm : AEStronglyMeasurable (slotProj1 e i g)
        (volume : Measure (Submission.BoseGases.X (n'+1))) :=
      slotProj1_aesm (fun l => (hbdd l).aestronglyMeasurable) i hgm.aestronglyMeasurable
    have hCPg' : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
        (Submission.BoseGases.abox (n'+1) ℓ)), ‖slotProj1 e i g x‖ ≤ CPg :=
      MeasureTheory.ae_mono Measure.restrict_le_self hCPg
    have hAc : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
        (Submission.BoseGases.abox (n'+1) ℓ)), ‖g x‖ ≤ C :=
      Filter.Eventually.of_forall hC
    have hI1 : Integrable
        (fun x : Submission.BoseGases.X (n'+1) => (star (g x) * slotProj1 e i g x).re)
        ((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
          (Submission.BoseGases.abox (n'+1) ℓ)) := by
      refine MeasureTheory.Integrable.of_bound
        (((hgm.aestronglyMeasurable.star).mul hPg_aesm).re.mono_measure Measure.restrict_le_self)
        (C * CPg) ?_
      filter_upwards [hCPg', hAc] with x hx1 hx2
      calc ‖(star (g x) * slotProj1 e i g x).re‖
          = |(star (g x) * slotProj1 e i g x).re| := Real.norm_eq_abs _
        _ ≤ ‖star (g x) * slotProj1 e i g x‖ := Complex.abs_re_le_norm _
        _ = ‖g x‖ * ‖slotProj1 e i g x‖ := by rw [norm_mul, norm_star]
        _ ≤ C * CPg := mul_le_mul hx2 hx1 (norm_nonneg _) hC0
    have hI2 : Integrable
        (fun x : Submission.BoseGases.X (n'+1) => ‖g x‖ * ‖slotProj1 e i g x‖)
        ((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
          (Submission.BoseGases.abox (n'+1) ℓ)) := by
      refine MeasureTheory.Integrable.of_bound
        ((hgm.aestronglyMeasurable.norm.mul hPg_aesm.norm).mono_measure Measure.restrict_le_self)
        (C * CPg) ?_
      filter_upwards [hCPg', hAc] with x hx1 hx2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul hx2 hx1 (norm_nonneg _) hC0
    have hI3 : Integrable (fun x : Submission.BoseGases.X (n'+1) => ‖g x‖ ^ 2)
        ((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
          (Submission.BoseGases.abox (n'+1) ℓ)) := by
      refine MeasureTheory.Integrable.of_bound
        ((hgm.aestronglyMeasurable.norm.pow 2).mono_measure Measure.restrict_le_self) (C ^ 2) ?_
      filter_upwards [hAc] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hI4 : Integrable (fun x : Submission.BoseGases.X (n'+1) => ‖slotProj1 e i g x‖ ^ 2)
        ((volume : Measure (Submission.BoseGases.X (n'+1))).restrict
          (Submission.BoseGases.abox (n'+1) ℓ)) := by
      refine MeasureTheory.Integrable.of_bound
        ((hPg_aesm.norm.pow 2).mono_measure Measure.restrict_le_self) (CPg ^ 2) ?_
      filter_upwards [hCPg'] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hkey := inner_pair_eq_normSq_bdd hℓ he hbdd hsupp i hgm hgb'
    have step1 : (∫ x in Submission.BoseGases.abox (n'+1) ℓ,
          (star (g x) * slotProj1 e i g x).re)
        ≤ ∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖g x‖ * ‖slotProj1 e i g x‖ :=
      MeasureTheory.integral_mono_ae hI1 hI2 (Filter.Eventually.of_forall (fun x => by
        calc (star (g x) * slotProj1 e i g x).re
            ≤ |(star (g x) * slotProj1 e i g x).re| := le_abs_self _
          _ ≤ ‖star (g x) * slotProj1 e i g x‖ := Complex.abs_re_le_norm _
          _ = ‖g x‖ * ‖slotProj1 e i g x‖ := by rw [norm_mul, norm_star]))
    have step2 : (∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖g x‖ * ‖slotProj1 e i g x‖)
        ≤ ∫ x in Submission.BoseGases.abox (n'+1) ℓ,
            (‖g x‖ ^ 2 + ‖slotProj1 e i g x‖ ^ 2) / 2 :=
      MeasureTheory.integral_mono_ae hI2 ((hI3.add hI4).div_const 2)
        (Filter.Eventually.of_forall (fun x => by
          have h := sq_nonneg (‖g x‖ - ‖slotProj1 e i g x‖)
          nlinarith [norm_nonneg (g x), norm_nonneg (slotProj1 e i g x)]))
    have hsum : (∫ x in Submission.BoseGases.abox (n'+1) ℓ,
          (‖g x‖ ^ 2 + ‖slotProj1 e i g x‖ ^ 2) / 2)
        = ((∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖g x‖ ^ 2)
            + ∫ x in Submission.BoseGases.abox (n'+1) ℓ, ‖slotProj1 e i g x‖ ^ 2) / 2 := by
      rw [MeasureTheory.integral_div, MeasureTheory.integral_add hI3 hI4]
    linarith [hkey, step1, step2, hsum]

/-- **The slot projection is an `L²`-contraction on the box** for an `L^∞` state supported in
the box. -/
theorem slotProj1_contract_box' {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {f : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ} (hf : MeasureTheory.MemLp f ⊤)
    (hf0 : ∀ x, x ∉ Submission.BoseGases.abox n ℓ → f x = 0) :
    (∫ x in Submission.BoseGases.abox n ℓ, ‖slotProj1 e i f x‖ ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖f x‖ ^ 2 := by
  classical
  obtain ⟨g, C, _hC0, hCb, hgsm, hgeq⟩ :=
    exists_bdd_sm_repr_aux (volume : Measure (Submission.BoseGases.X n)) hf
  have hPgeq : slotProj1 e i f
      =ᵐ[(volume : Measure (Submission.BoseGases.X n))] slotProj1 e i g :=
    slotProj1_ae_eq_congr_aux e i hgeq
  have hLHS : (∫ x in Submission.BoseGases.abox n ℓ, ‖slotProj1 e i f x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, ‖slotProj1 e i g x‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_ae (Submission.BoseGases.abox_measurable n ℓ) ?_
    filter_upwards [hPgeq] with x hx _
    rw [hx]
  have hRHS : (∫ x in Submission.BoseGases.abox n ℓ, ‖f x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, ‖g x‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_ae (Submission.BoseGases.abox_measurable n ℓ) ?_
    filter_upwards [hgeq] with x hx _
    rw [hx]
  rw [hLHS, hRHS]
  exact contract_bdd hℓ he hbdd hsupp i hgsm.measurable ⟨C, hCb⟩

end Work.BoseBoxFock.XwSlot
