import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PB3Aux
import Submission.Work.BoseBoxFock.PB3FibreQ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3Aux2` — the block-III first half: slot integrals and the per-pair bound
-/

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option linter.unusedVariables false

variable {n : ℕ} {ℓ : ℝ}

/-! ## 0. Pointwise facts about free-lattice pinned modes and slot means -/

/-- The pinned mode is supported in the box. -/
theorem pb3_pinQ_support {N : ℕ} {v : E3 → ℝ} {μ : ℝ} (k : Lab N) :
    Function.support (pinQ v μ N k) ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
  intro u hu
  rw [Function.mem_support] at hu
  by_contra hcon
  refine hu ?_
  have hchi : Work.BoseK15.corpusBox.chiLam (ellH v μ) u = 0 := by
    by_contra h
    exact hcon (Work.BoseB4.BoxData.chiLam_supp Work.BoseK15.corpusBox (ellH_pos v μ) h)
  rw [show pinQ v μ N k u = (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) *
      Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) N k) u from rfl]
  rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply,
    Work.BoseB4.BoxData.thetaFun_apply, if_neg hcon, mul_zero, sub_zero, hchi, Complex.ofReal_zero,
    mul_zero, mul_zero]

/-- The slot mean of a pointwise bounded state is pointwise bounded by the same constant. -/
theorem aPC_bound_pointwise {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Θ : Xn n → ℂ} {C : ℝ}
    (hC : ∀ x, ‖Θ x‖ ≤ C) (hC0 : 0 ≤ C) (x : Xn n) : ‖aPC ℓ i Θ x‖ ≤ C := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
  have hvol : ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).real Set.univ
      = ℓ ^ 3 := by
    rw [Measure.real, Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  have hbound : ‖∫ y : E3, Θ (Function.update x i y)
      ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))‖ ≤ C * ℓ ^ 3 := by
    calc ‖∫ y : E3, Θ (Function.update x i y)
          ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))‖
        ≤ C * ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).real Set.univ :=
          norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => hC _)
      _ = C * ℓ ^ 3 := by rw [hvol]
  have hmain : ‖aPC ℓ i Θ x‖ ≤ (1 / ℓ ^ 3) * (C * ℓ ^ 3) := by
    have hrew : aPC ℓ i Θ x = ((1 / ℓ ^ 3 : ℝ) : ℂ) *
        ∫ y : E3, Θ (Function.update x i y)
          ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := rfl
    rw [hrew, norm_mul]
    rw [show ‖((1 / ℓ ^ 3 : ℝ) : ℂ)‖ = 1 / ℓ ^ 3 from by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
    exact mul_le_mul_of_nonneg_left hbound (by positivity)
  calc ‖aPC ℓ i Θ x‖ ≤ (1 / ℓ ^ 3) * (C * ℓ ^ 3) := hmain
    _ = C := by
        field_simp

/-- The slot mean vanishes at a configuration whose slots other than `i` do not all lie in the
box. -/
theorem aPC_eq_zero_of_notMem {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Θ : Xn n → ℂ}
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) {x : Xn n}
    (hx : ∃ l : Fin n, l ≠ i ∧ x l ∉ Work.BoseK15.corpusBox.boxL ℓ) :
    aPC ℓ i Θ x = 0 := by
  obtain ⟨l, hl, hxl⟩ := hx
  have hzero : ∀ y : E3, Θ (Function.update x i y) = 0 := by
    intro y
    by_contra h
    have hmem := hΘs (Function.mem_support.mpr h)
    have hxl' : Function.update x i y l ∈ Work.BoseK15.corpusBox.boxL ℓ := by
      rw [corpusBox_boxL_eq_acube hℓ]; exact hmem l
    rw [Function.update_of_ne hl] at hxl'
    exact hxl hxl'
  have hz : (fun y : E3 => Θ (Function.update x i y)) = fun _ => (0 : ℂ) := funext hzero
  rw [aPC]
  rw [hz]
  simp

/-- The slot mean vanishes off the box in the slots other than `i`, hence off `abox` when the
state is supported in `abox` and `i` is the slot that is free. -/
theorem aPC_eq_zero_of_notMem_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Θ : Xn n → ℂ} (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) {x : Xn n}
    (hx : x j ∉ Work.BoseK15.corpusBox.boxL ℓ) : aPC ℓ i Θ x = 0 := by
  refine aPC_eq_zero_of_notMem hℓ i hΘs ⟨j, hij.symm, hx⟩

variable {n : ℕ} {ℓ : ℝ}

/-! ## 1. The slot integral of a compactly supported weight -/

/-- The slot integral `x ↦ ∫ u, conj (k u) · F (x[j ↦ u])` only sees `k` on the box. -/
theorem slotIntegral_eq_setIntegral {j : Fin n} {k : E3 → ℂ} {F : Xn n → ℂ}
    (hks : Function.support k ⊆ Work.BoseK15.corpusBox.boxL ℓ) (x : Xn n) :
    (∫ u : E3, (starRingEnd ℂ) (k u) * F (Function.update x j u))
      = ∫ u in Work.BoseK15.corpusBox.boxL ℓ,
          (starRingEnd ℂ) (k u) * F (Function.update x j u) := by
  have h0 : ∀ u : E3, u ∉ Work.BoseK15.corpusBox.boxL ℓ →
      (starRingEnd ℂ) (k u) * F (Function.update x j u) = 0 := by
    intro u hu
    have hk : k u = 0 := by
      by_contra h
      exact hu (hks (Function.mem_support.mpr h))
    rw [hk, map_zero, zero_mul]
  exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h0).symm

/-- Measurability of the slot integral of a measurable state. -/
theorem slotIntegral_measurable {j : Fin n} {k : E3 → ℂ} {F : Xn n → ℂ}
    (hF : Measurable F) (hkm : Measurable k)
    (hks : Function.support k ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    Measurable (fun x : Xn n => ∫ u : E3, (starRingEnd ℂ) (k u) * F (Function.update x j u)) := by
  have hfun : (fun x : Xn n => ∫ u : E3, (starRingEnd ℂ) (k u) * F (Function.update x j u))
      = fun x : Xn n => ∫ u in Work.BoseK15.corpusBox.boxL ℓ,
          (starRingEnd ℂ) (k u) * F (Function.update x j u) :=
    funext (slotIntegral_eq_setIntegral hks)
  rw [hfun]
  have hkm' : Measurable (fun p : Xn n × E3 => (starRingEnd ℂ) (k p.2)) :=
    Complex.continuous_conj.measurable.comp (hkm.comp measurable_snd)
  have hF' : StronglyMeasurable (fun p : Xn n × E3 => F (Function.update p.1 j p.2)) :=
    hF.stronglyMeasurable.comp_measurable (by fun_prop)
  have hj : StronglyMeasurable (fun p : Xn n × E3 =>
      (starRingEnd ℂ) (k p.2) * F (Function.update p.1 j p.2)) :=
    hkm'.stronglyMeasurable.mul hF'
  have hint : StronglyMeasurable (fun x : Xn n =>
      ∫ u : E3, (starRingEnd ℂ) (k u) * F (Function.update x j u)
        ∂((volume : Measure E3).restrict (Work.BoseK15.corpusBox.boxL ℓ))) :=
    StronglyMeasurable.integral_prod_right hj
  exact hint.measurable

/-- The slot integral of a bounded weight against a bounded state is bounded. -/
theorem slotIntegral_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {j : Fin n} {k : E3 → ℂ}
    {F : Xn n → ℂ} {Ck CF : ℝ}
    (hks : Function.support k ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hCk : ∀ u, ‖k u‖ ≤ Ck) (hCF : ∀ x, ‖F x‖ ≤ CF)
    (hCk0 : 0 ≤ Ck) (hCF0 : 0 ≤ CF) {x : Xn n} :
    ‖∫ u : E3, (starRingEnd ℂ) (k u) * F (Function.update x j u)‖ ≤ Ck * CF * ℓ ^ 3 := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Work.BoseK15.corpusBox.boxL ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top⟩
  have hvol : ((volume : Measure E3).restrict (Work.BoseK15.corpusBox.boxL ℓ)).real Set.univ
      = ℓ ^ 3 := by
    rw [Measure.real, Measure.restrict_apply_univ,
      Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ,
      ENNReal.toReal_ofReal (by positivity)]
  rw [slotIntegral_eq_setIntegral (ℓ := ℓ) (j := j) (k := k) (F := F) hks x]
  calc ‖∫ u in Work.BoseK15.corpusBox.boxL ℓ,
        (starRingEnd ℂ) (k u) * F (Function.update x j u)‖
      ≤ Ck * CF * ((volume : Measure E3).restrict (Work.BoseK15.corpusBox.boxL ℓ)).real
          Set.univ :=
        norm_integral_le_of_norm_le_const
          (Filter.Eventually.of_forall fun u => by
            rw [norm_mul, Complex.norm_conj]
            exact mul_le_mul (hCk u) (hCF _) (norm_nonneg _) hCk0)
    _ = Ck * CF * ℓ ^ 3 := by rw [hvol]

/-- The slot integral is invariant in the slot it replaces. -/
theorem slotIntegral_invariant {j : Fin n} (k : E3 → ℂ) (F : Xn n → ℂ) (x : Xn n) (v : E3) :
    (∫ u : E3, (starRingEnd ℂ) (k u) * F (Function.update (Function.update x j v) j u))
      = ∫ u : E3, (starRingEnd ℂ) (k u) * F (Function.update x j u) := by
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [pb3_update_update_self]

/-! ## 3. The per-pair, per-label identity -/

/-- The insertion at a slot distinct from `j`. -/
theorem pb3_insertCoord_of_ne {n : ℕ} (j : Fin n) (u : E3) (x' : {l : Fin n // l ≠ j} → E3)
    {l : Fin n} (hl : l ≠ j) : insertCoord j u x' l = x' ⟨l, hl⟩ := by
  rw [insertCoord_eq]
  simp only [dif_neg hl]

/-- **The per-`(i,j,k)` term is `ℓ⁻³` times the box mass of the slot integral.** -/
theorem pb3_pairTerm_eq {n N : ℕ} {v : E3 → ℝ} {μ : ℝ} (i j : Fin n) (hij : i ≠ j)
    (k : Lab N) {Θ : Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    (∫ x : Xn n, (starRingEnd ℂ) (Θ x)
        * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
            * aPC (ellH v μ) i Θ (Function.update x j u)))
      = (((ellH v μ) ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox n (ellH v μ),
          Complex.normSq (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
            * aPC (ellH v μ) i Θ (Function.update x j u)) : ℝ) : ℂ) := by
  classical
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨Ck, hCk0, hCk⟩ := pinQ_bdd v μ N k
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hΘb' : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C := ⟨CΘ, hCΘ⟩
  have hCΘ0 : 0 ≤ CΘ := le_trans (norm_nonneg _) (hCΘ (Classical.arbitrary (Xn n)))
  have hkm : Measurable (pinQ v μ N k) := pinQ_measurable v μ N k
  have hks : Function.support (pinQ v μ N k) ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) :=
    pb3_pinQ_support k
  set Ψ : Xn n → ℂ := aPC (ellH v μ) i Θ with hΨd
  have hΨm : Measurable Ψ := by rw [hΨd]; exact aPC_measurable' i hΘm
  have hΨb : ∀ x, ‖Ψ x‖ ≤ CΘ := by
    intro x; rw [hΨd]; exact aPC_bound_pointwise hℓ i hCΘ hCΘ0 x
  -- the integrand of the fibre identity is integrable
  have hInt : Integrable (fun x : Xn n => (starRingEnd ℂ) (Θ x)
      * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
          * Ψ (Function.update x j u))) (volume : Measure (Xn n)) := by
    have haesm : AEStronglyMeasurable (fun x : Xn n => (starRingEnd ℂ) (Θ x)
        * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
            * Ψ (Function.update x j u))) (volume : Measure (Xn n)) :=
      ((Complex.continuous_conj.measurable.comp hΘm).aestronglyMeasurable).mul
        (((hkm.comp (measurable_pi_apply j)).aestronglyMeasurable).mul
          (slotIntegral_measurable hΨm hkm hks).aestronglyMeasurable)
    have hbdd : ∀ᵐ x ∂(volume : Measure (Xn n)), ‖(starRingEnd ℂ) (Θ x)
        * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
            * Ψ (Function.update x j u))‖ ≤ CΘ * (Ck * (Ck * CΘ * (ellH v μ) ^ 3)) :=
      Filter.Eventually.of_forall fun x => by
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul (hCΘ x) (mul_le_mul (hCk _)
          (slotIntegral_bound hℓ hks hCk hΨb hCk0 hCΘ0)
          (norm_nonneg _) hCk0) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCΘ0
    exact (integrableOn_of_aesm_bound hℓ haesm hbdd).integrable_of_forall_notMem_eq_zero
      (fun x hx => by
        have hΘ0 : Θ x = 0 := by
          by_contra hc
          exact hx (hΘs (Function.mem_support.mpr hc))
        rw [hΘ0, map_zero, zero_mul])
  have hfib := fibre_part1 (j := j) (Ψ := Θ) (Ξ := Ψ) (w := pinQ v μ N k) hInt
  set Ŷ : Xn n → ℂ := (fun x => ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (Function.update x j u)) with hY
  set Zslot : Xn n → ℂ := (fun x => ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (Function.update x j u)) with hZ
  have hYm : Measurable Ŷ := slotIntegral_measurable hΘm hkm hks
  have hZm : Measurable Zslot := slotIntegral_measurable hΨm hkm hks
  have hYb : ∀ x, ‖Ŷ x‖ ≤ Ck * CΘ * (ellH v μ) ^ 3 := fun x =>
    slotIntegral_bound hℓ hks hCk hCΘ hCk0 hCΘ0
  have hZb : ∀ x, ‖Zslot x‖ ≤ Ck * CΘ * (ellH v μ) ^ 3 := fun x =>
    slotIntegral_bound hℓ hks hCk hΨb hCk0 hCΘ0
  have hYpeel : ∀ (w : E3) (x' : {l : Fin n // l ≠ j} → E3),
      Ŷ (insertCoord j w x') = ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
        * Θ (insertCoord j u x') := by
    intro w x'
    rw [hY]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [update_insertCoord]
  have hZpeel : ∀ (w : E3) (x' : {l : Fin n // l ≠ j} → E3),
      Zslot (insertCoord j w x') = ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
        * Ψ (insertCoord j u x') := by
    intro w x'
    rw [hZ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [update_insertCoord]
  have hZinv : ∀ x (u : E3), Zslot (Function.update x j u) = Zslot x :=
    fun x u => slotIntegral_invariant (pinQ v μ N k) Ψ x u
  -- the fibre integrand is supported in the slice box
  have hzero' : ∀ x' : {l : Fin n // l ≠ j} → E3,
      x' ∉ boxPiSet ({k : Fin n // k ≠ j}) (ellH v μ) →
      (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x'))
        * (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (insertCoord j u x')) = 0 := by
    intro x' hx'
    have hex : ∃ l : {l : Fin n // l ≠ j}, x' l ∉ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
      by_contra h
      push_neg at h
      exact hx' (by rw [boxPiSet]; exact fun i _ => h i)
    obtain ⟨l, hxl⟩ := hex
    have hΘ0 : ∀ u : E3, Θ (insertCoord j u x') = 0 := by
      intro u
      by_contra hc
      have hmem := hΘs (Function.mem_support.mpr hc)
      have hmem_l : insertCoord j u x' l.1 ∈ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
        rw [corpusBox_boxL_eq_acube hℓ]; exact hmem l.1
      rw [pb3_insertCoord_of_ne j u x' l.2] at hmem_l
      exact hxl (by simpa using hmem_l)
    have hA0 : (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x')) = 0 := by
      rw [show (fun u : E3 => (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x'))
          = fun _ => (0 : ℂ) from funext fun u => by rw [hΘ0 u, mul_zero]]
      simp
    rw [hA0, map_zero, zero_mul]
  have hsupp : (∫ x' : {l : Fin n // l ≠ j} → E3,
        (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x'))
          * (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (insertCoord j u x')))
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) (ellH v μ),
        (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x'))
          * (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (insertCoord j u x')) :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero').symm

  -- the peel
  have hpeel : (∫ x in Submission.BoseGases.abox n (ellH v μ), (starRingEnd ℂ) (Ŷ x) * Zslot x)
      = ∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
          ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) (ellH v μ),
            (starRingEnd ℂ) (Ŷ (insertCoord j w x')) * Zslot (insertCoord j w x') :=
    abox_slice_peel (ℓ := ellH v μ) j hℓ ((Complex.continuous_conj.measurable.comp hYm).mul hZm)
      ⟨(Ck * CΘ * (ellH v μ) ^ 3) * (Ck * CΘ * (ellH v μ) ^ 3), fun x => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hYb x) (hZb x) (norm_nonneg _) (le_trans (norm_nonneg _) (hYb x))⟩
  have hfibeq : (∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
          ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) (ellH v μ),
            (starRingEnd ℂ) (Ŷ (insertCoord j w x')) * Zslot (insertCoord j w x'))
      = (((ellH v μ) ^ 3 : ℝ) : ℂ) *
          ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) (ellH v μ),
            (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
                * Θ (insertCoord j u x'))
              * (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
                  * Ψ (insertCoord j u x')) := by
    have hvol : ((volume : Measure E3).restrict
          (Work.BoseK15.corpusBox.boxL (ellH v μ))).real Set.univ = (ellH v μ) ^ 3 := by
      rw [Measure.real, Measure.restrict_apply_univ,
        Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ,
        ENNReal.toReal_ofReal (by positivity)]
    have hinner : (fun w : E3 => ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) (ellH v μ),
            (starRingEnd ℂ) (Ŷ (insertCoord j w x')) * Zslot (insertCoord j w x'))
        = fun _ => ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) (ellH v μ),
            (starRingEnd ℂ) (Ŷ (insertCoord j 0 x')) * Zslot (insertCoord j 0 x') := by
      funext w
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
      have h1 : Ŷ (insertCoord j w x') = Ŷ (insertCoord j 0 x') := by
        simp only [hYpeel w x', hYpeel 0 x']
      have h2 : Zslot (insertCoord j w x') = Zslot (insertCoord j 0 x') := by
        simp only [hZpeel w x', hZpeel 0 x']
      simp only [h1, h2]
    rw [hinner, MeasureTheory.integral_const, hvol, Complex.real_smul]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
    simp only [hYpeel 0 x', hZpeel 0 x']

  -- the square identity
  have hsum : (∫ x in Submission.BoseGases.abox n (ellH v μ),
        (starRingEnd ℂ) (Ŷ x) * aPC (ellH v μ) i Ŷ x)
      = ∫ x in Submission.BoseGases.abox n (ellH v μ),
          ((Complex.normSq (aPC (ellH v μ) i Ŷ x) : ℝ) : ℂ) :=
    box_sum_sq hℓ i (le_trans (norm_nonneg _) (hYb 0)) hYm.aestronglyMeasurable
      (Filter.Eventually.of_forall hYb)
  have hŶeq : aPC (ellH v μ) i Ŷ = Zslot := by
    funext x
    rw [hY, hZ, hΨd]
    exact slotMean_fibre_eq i j hij k hΘm hΘb' x
  have hsq : (∫ x in Submission.BoseGases.abox n (ellH v μ), (starRingEnd ℂ) (Ŷ x) * Zslot x)
      = ((∫ x in Submission.BoseGases.abox n (ellH v μ), Complex.normSq (Zslot x) : ℝ) : ℂ) := by
    rw [← hŶeq, hsum]
    exact integral_ofReal
  -- assemble
  have hmain : (∫ x' in boxPiSet ({k : Fin n // k ≠ j}) (ellH v μ),
        (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x'))
          * (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (insertCoord j u x')))
      = ((((ellH v μ) ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox n (ellH v μ),
          Complex.normSq (Zslot x)) : ℝ) : ℂ) := by
    have h3 : (((ellH v μ) ^ 3 : ℝ) : ℂ) *
          (∫ x' in boxPiSet ({k : Fin n // k ≠ j}) (ellH v μ),
            (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
                * Θ (insertCoord j u x'))
              * (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (insertCoord j u x')))
        = ((∫ x in Submission.BoseGases.abox n (ellH v μ), Complex.normSq (Zslot x) : ℝ) : ℂ) := by
      rw [← hfibeq, ← hpeel, hsq]
    rw [Complex.ofReal_mul, Complex.ofReal_inv]
    rw [← h3, ← mul_assoc,
      inv_mul_cancel₀ (by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]
  rw [hfib, hsupp]
  rw [← Complex.ofReal_mul]
  exact hmain

end

end Work.BoseBoxFock
