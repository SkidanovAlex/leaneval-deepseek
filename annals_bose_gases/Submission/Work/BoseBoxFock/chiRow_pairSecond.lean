import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-! ## Helper lemmas for `chiRow_pairSecond`

The module proves the *transpose* (second) orientation of the FS `Q₁` `χ`-row sandwich with the
condensate number: pairing a box state `Φ` against `B(|e₀⟩⟨η_C|) (B(|e₀⟩⟨e₀|) Φ)` equals the
second half `pairHalfTwo` of the pair slot form at the pinned weight `chiW`.

The bookkeeping below is self-contained (the twin module `chiRow_muEvalAux` carries the same
analytic helpers for the `μ`-line, but is not imported here). -/

/-- On the cube, the real part of `conj (chiMode)` times a real number is `chiW` times it. -/
lemma pS_conj_chiMode_mul_ofReal_re {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) {z : Sp} {g : ℝ}
    (hz : z ∈ Submission.BoseGases.acube ℓ) :
    ((starRingEnd ℂ) (chiMode ℓ N z) * ((g : ℝ) : ℂ)).re = chiW ℓ N z * g := by
  have hre : (chiMode ℓ N z).re = chiW ℓ N z :=
    chiMode_re_of_theta_eq_one ℓ N (thetaFun_eq_one_of_mem_acube hℓ hz)
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre]

/-- **The `j`-th slot of `|e₀⟩⟨e₀|` evaluated on the box.**  If `e 0` is a.e. the pinned
condensate mode `(√ℓ³)⁻¹·θ_Λ` and `y` is a box configuration at which `e 0` already takes the
value `(√ℓ³)⁻¹`, then `uSlot (e 0) j (boxRestrictC ℓ Φ) y` is the complex slot mean
`↑(aP ℓ j Φ y)`. -/
lemma pS_uSlot_evalu {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Sp → ℂ}
    (huc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
      e 0 z = (((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ)) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    {Φ : Submission.BoseGases.X d → ℝ}
    {y : Submission.BoseGases.X d} (hy : y ∈ Submission.BoseGases.abox d ℓ)
    (hyu : ∀ k : Fin d, e 0 (y k) = (((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ))) (j : Fin d) :
    uSlot (e 0) j (boxRestrictC ℓ Φ) y
      = (((Submission.BoseGases.aP ℓ j Φ y : ℝ)) : ℂ) := by
  rw [uSlot_eq_mul_setIntegral hℓ huc j _ y, hyu j]
  have hpt : (∫ z in Submission.BoseGases.acube ℓ,
        boxRestrictC ℓ Φ (Function.update y j z))
      = ∫ z in Submission.BoseGases.acube ℓ, ((Φ (Function.update y j z) : ℝ) : ℂ) :=
    MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun z hz => by
        simp only [boxRestrictC, Set.indicator_of_mem
          (chiRow_update_mem_abox hy j hz), Complex.ofReal_one, mul_one])
  have haP : (∫ z in Submission.BoseGases.acube ℓ, Φ (Function.update y j z))
      = ℓ ^ 3 * Submission.BoseGases.aP ℓ j Φ y := by
    rw [Submission.BoseGases.aP]
    field_simp
  rw [hpt, integral_complex_ofReal, haP]
  have key : (((Real.sqrt (ℓ^3))⁻¹ : ℂ)) * (starRingEnd ℂ) (((Real.sqrt (ℓ^3))⁻¹ : ℂ))
      = (((ℓ^3 : ℝ)⁻¹ : ℂ)) := by
    rw [mul_comm]
    simpa using conj_inv_sqrt_mul_self hℓ
  rw [key, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_inj]
  rw [inv_mul_cancel_left₀ (by positivity : (ℓ:ℝ)^3 ≠ 0)]

/-- **The pinned `χ`-mode is a.e. strongly measurable**, from the pinning hypothesis. -/
lemma pS_chiMode_aesm {m : ℕ} {ℓ : ℝ} {N : ℕ} {e : Fin m → Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) {C : Fin m → ℝ}
    (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C z)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure Sp)] chiMode ℓ N) :
    MeasureTheory.AEStronglyMeasurable (chiMode ℓ N)
      (MeasureTheory.volume : MeasureTheory.Measure Sp) := by
  have heta : Measurable (Work.BoseDict.etaOf e C) := by
    show Measurable (fun z : Sp => ∑ l : Fin m, ((C l : ℝ) : ℂ) * e l z)
    exact Finset.measurable_sum _ (fun l _ => (hmeas l).const_mul ((C l : ℝ) : ℂ))
  exact (measurable_const.mul heta).aestronglyMeasurable.congr hC

/-- **The pinned `χ`-mode is a.e. bounded**, from the pinning hypothesis. -/
lemma pS_chiMode_bound_ae {m : ℕ} {ℓ : ℝ} {N : ℕ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) {C : Fin m → ℝ}
    (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C z)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure Sp)] chiMode ℓ N) :
    ∃ K : ℝ, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
      ‖chiMode ℓ N z‖ ≤ K := by
  choose B hB using hbdd
  refine ⟨‖(((Real.sqrt (ℓ^3)) : ℝ) : ℂ)‖ * ∑ l : Fin m, ‖((C l : ℝ) : ℂ)‖ * max (B l) 0,
    ?_⟩
  filter_upwards [hC] with z hz
  rw [← hz, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖Work.BoseDict.etaOf e C z‖
      = ‖∑ l : Fin m, ((C l : ℝ) : ℂ) * e l z‖ := rfl
    _ ≤ ∑ l : Fin m, ‖((C l : ℝ) : ℂ) * e l z‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin m, ‖((C l : ℝ) : ℂ)‖ * max (B l) 0 :=
        Finset.sum_le_sum (fun l _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left ((hB l z).trans (le_max_left _ _)) (norm_nonneg _))

/-- The complex box restriction of a continuous state is measurable. -/
lemma pS_boxRestrictC_measurable {n : ℕ} (ℓ : ℝ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) : Measurable (boxRestrictC ℓ Φ) := by
  have h : boxRestrictC ℓ Φ = fun x : Submission.BoseGases.X n =>
      ((Φ x : ℝ) : ℂ) *
        (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := rfl
  rw [h]
  exact (Complex.continuous_ofReal.measurable.comp hΦc.measurable).mul
    (Complex.continuous_ofReal.measurable.comp
      (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ)))

/-- **The complex box restriction of a continuous state is globally bounded.** -/
lemma pS_boxRestrictC_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    ∃ C : ℝ, ∀ x : Submission.BoseGases.X n, ‖boxRestrictC ℓ Φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
      (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) from rfl]
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx]
    simp only [Complex.ofReal_one, mul_one, Complex.norm_real]
    exact (hC x hx).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hx]
    simp

/-- The complex box restriction of a continuous state is supported in the box. -/
lemma pS_boxRestrictC_support {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    Function.support (boxRestrictC ℓ Φ) ⊆ Submission.BoseGases.abox n ℓ := by
  intro x hx
  by_contra h
  exact hx (by
    rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
      (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) from rfl]
    rw [Set.indicator_of_notMem h]
    simp)

/-- The real part of a set integral of a complex function. -/
theorem pS_setIntegral_re_gen {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℂ} (hf : IntegrableOn f s μ) :
    (∫ x in s, f x ∂μ).re = ∫ x in s, (f x).re ∂μ := by
  have h := integral_re (𝕜 := ℂ) (μ := μ.restrict s) (f := f) hf
  simpa using h.symm

/-- **The `cIPn` pairing against the box restriction is a real integral over the box.** -/
theorem pS_setIntegral_re_X {n : ℕ} {ℓ : ℝ} {f : Submission.BoseGases.X n → ℂ}
    (hf : IntegrableOn f (Submission.BoseGases.abox n ℓ)) :
    (∫ x in Submission.BoseGases.abox n ℓ, f x).re
      = ∫ x in Submission.BoseGases.abox n ℓ, (f x).re := by
  have h := integral_re (𝕜 := ℂ)
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ))
    (f := f) hf
  simpa using h.symm

theorem pS_cIPn_boxRestrictC_re {n : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    {G : Submission.BoseGases.X n → ℂ}
    (hG : IntegrableOn (fun x => (((Φ x : ℝ)) : ℂ) * G x) (Submission.BoseGases.abox n ℓ)) :
    (Work.BoseDict.cIPn n (boxRestrictC ℓ Φ) G).re
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * (G x).re := by
  have hpt : ∀ x : Submission.BoseGases.X n,
      (starRingEnd ℂ) (boxRestrictC ℓ Φ x) * G x
        = (Submission.BoseGases.abox n ℓ).indicator
            (fun x => (((Φ x : ℝ)) : ℂ) * G x) x := by
    intro x
    rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
        (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) from rfl]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  rw [Work.BoseDict.cIPn,
    show (∫ x, (starRingEnd ℂ) (boxRestrictC ℓ Φ x) * G x)
        = ∫ x, (Submission.BoseGases.abox n ℓ).indicator
            (fun x => (((Φ x : ℝ)) : ℂ) * G x) x from
      integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable n ℓ)]
  rw [pS_setIntegral_re_X hG]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp [Complex.mul_re]

/-- **Integrability of the interior integrand on the cube.**  Bounded (the pinned mode is
a.e. bounded, the slot means are bounded on the box) and a.e. strongly measurable on the cube of
finite measure. -/
theorem pS_integrableOn_conj_chiMode_mul_aPsum {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hm : MeasureTheory.AEStronglyMeasurable (chiMode ℓ N)
      (MeasureTheory.volume : MeasureTheory.Measure Sp))
    (hb : ∃ K : ℝ, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
        ‖chiMode ℓ N z‖ ≤ K)
    {x : Submission.BoseGases.X n} (hx : x ∈ Submission.BoseGases.abox n ℓ) (j : Fin n) :
    MeasureTheory.IntegrableOn
      (fun y : Sp =>
        (starRingEnd ℂ) (chiMode ℓ N y) *
          (((∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)) : ℝ) : ℂ))
      (Submission.BoseGases.acube ℓ) MeasureTheory.volume := by
  obtain ⟨K, hK⟩ := hb
  obtain ⟨CΦ, hCΦ⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  have hCΦ0 : 0 ≤ max CΦ 0 := le_max_right _ _
  have hFb : ∀ w ∈ Submission.BoseGases.abox n ℓ, |Φ w| ≤ max CΦ 0 :=
    fun w hw => (hCΦ w hw).trans (le_max_left _ _)
  have hupd : Measurable (Function.update x j) := measurable_update x (a := j)
  have hGm : Measurable (fun y : Sp =>
      ∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)) :=
    Finset.measurable_sum _ (fun j' _ =>
      ((Submission.BoseGases.aP_continuous hℓ j' hΦc).measurable).comp hupd)
  have hsm : MeasureTheory.AEStronglyMeasurable
      (fun y : Sp => (starRingEnd ℂ) (chiMode ℓ N y) *
        (((∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)) : ℝ) : ℂ))
      ((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
        (Submission.BoseGases.acube ℓ)) :=
    ((Complex.continuous_conj.comp_aestronglyMeasurable hm).restrict).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hGm.aestronglyMeasurable)
  refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le) hsm
    (K * ((n : ℝ) * max CΦ 0)) ?_
  filter_upwards [self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ),
    MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self hK] with y hyc hyK
  have hys : ∀ j' : Fin n,
      |Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)| ≤ max CΦ 0 :=
    fun j' => Submission.BoseGases.aP_abs_le hℓ j' hΦc hCΦ0 hFb _
      (chiRow_update_mem_abox hx j hyc)
  have hGs : |∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)|
      ≤ (n : ℝ) * max CΦ 0 := by
    calc |∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)|
        ≤ ∑ j' : Fin n, |Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j' : Fin n, max CΦ 0 := Finset.sum_le_sum (fun j' _ => hys j')
      _ = (n : ℝ) * max CΦ 0 := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul hyK hGs (abs_nonneg _) (le_trans (norm_nonneg _) hyK)

theorem chiRow_pairSecond {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l)) (hemem : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C : Fin m → ℝ} (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C z)
      =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.chiMode ℓ N)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C)
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
            (Work.BoseBoxFock.boxRestrictC ℓ Φ)))).re
      = Work.BoseBoxFock.pairHalfTwo n ℓ (Work.BoseBoxFock.chiW ℓ N) Φ := by
  have huc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
      e 0 z = (((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ)) * Work.BoseK15.corpusBox.thetaFun ℓ z := hpin
  have hAESM : MeasureTheory.AEStronglyMeasurable (Work.BoseBoxFock.chiMode ℓ N)
      (MeasureTheory.volume : MeasureTheory.Measure Sp) := pS_chiMode_aesm hmeas hC
  have hBnd : ∃ K : ℝ, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
      ‖Work.BoseBoxFock.chiMode ℓ N z‖ ≤ K := pS_chiMode_bound_ae hbdd hC
  set Ψ : Submission.BoseGases.X n → ℂ := Work.BoseBoxFock.boxRestrictC ℓ Φ with hΨdef
  have hΨm : Measurable Ψ := by rw [hΨdef]; exact pS_boxRestrictC_measurable ℓ hΦc
  have hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C := by
    rw [hΨdef]; exact pS_boxRestrictC_bound hℓ hΦc
  set Θ : Work.BoseDict.Xn n → ℂ :=
    Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m)) Ψ
    with hΘdef
  obtain ⟨hΘm, hΘb⟩ := Work.MB.boxSlotSum_measurable_bounded_ae
    (d := n) (ℓ := ℓ) (e := e) hmeas hbdd hsupp
    (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m)) Ψ hΨm hΨb
  set Z : Submission.BoseGases.X n → ℂ :=
    Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C) Θ
    with hZdef
  obtain ⟨hZm, hZb⟩ := Work.MB.boxSlotSum_measurable_bounded_ae
    (d := n) (ℓ := ℓ) (e := e) hmeas hbdd hsupp
    (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C) Θ hΘm hΘb
  -- ### the a.e. pinning facts
  have hGood : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      ∀ k : Fin n, e 0 (x k) = (((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ)) := by
    simpa using (Finset.eventually_all (Finset.univ : Finset (Fin n))).mpr
      (fun k _ => ae_u_eq_c_of_ae_eq_theta hℓ k huc)
  have hCubeGood : ∀ᵐ y ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)),
      e 0 y = (((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ)) := by
    filter_upwards [MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self huc,
      self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)] with y hy hyc
    rw [hy, thetaFun_eq_one_of_mem_acube hℓ hyc, mul_one]
  -- ### the value of `Θ` at box configurations in the pinned set
  have theta_value : ∀ (w : Submission.BoseGases.X n), w ∈ Submission.BoseGases.abox n ℓ →
      (∀ k : Fin n, e 0 (w k) = (((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ))) →
      Θ w = (((∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ w) : ℝ) : ℂ) := by
    intro w hw hwu
    have hΘeq : Θ = fun x => ∑ j : Fin n, uSlot (e 0) j Ψ x := by
      rw [hΘdef, Work.BoseBoxFock.rankOne_eq_rankOnePair,
        chiRow_slotSum_expand_weak hmeas hbdd hsupp (Work.BoseBoxFock.evec0 m)
          (Work.BoseBoxFock.evec0 m) Ψ hΨm hΨb]
      funext x
      simp only [Finset.sum_apply]
      exact Finset.sum_congr rfl
        (fun j _ => congrFun (Work.BoseBoxFock.boxSlotOf_evec0_eq_uSlot e j Ψ) x)
    rw [hΘeq]
    show (∑ j : Fin n, uSlot (e 0) j Ψ w) = _
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun j _ => pS_uSlot_evalu hℓ huc hw hwu j)
  -- ### the shifted a.e. statement, a.e. in the *cube* variable only
  have hThetaShift : ∀ j : Fin n,
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)),
        ∀ (w : Submission.BoseGases.X n), w ∈ Submission.BoseGases.abox n ℓ →
          (∀ k : Fin n, e 0 (w k) = (((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ))) →
          Θ (Function.update w j y)
            = (((∑ j' : Fin n,
                Submission.BoseGases.aP ℓ j' Φ (Function.update w j y)) : ℝ) : ℂ) := by
    intro j
    filter_upwards [hCubeGood,
      self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)]
      with y hyg hyc w hw hwu
    refine theta_value (Function.update w j y) (chiRow_update_mem_abox hw j hyc) ?_
    intro k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self]; exact hyg
    · rw [Function.update_of_ne hk]; exact hwu k
  -- ### the slot-sum dictionary of the outer word
  have hZae := chiRow_chiModeT_dict (d := n) (m := m) (ℓ := ℓ) hℓ hpin hmeas hbdd hsupp hC
    Θ hΘm hΘb
  -- ### the pointwise (a.e.) evaluation
  have hKey : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      (Z x).re = ∑ j : Fin n, (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseBoxFock.chiW ℓ N y *
          (∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)) := by
    filter_upwards [hZae, hGood,
      self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)] with x hxZ hxg hxm
    rw [hZdef]
    rw [hxZ, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hshift : ∀ᵐ y ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)),
        (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N y) * Θ (Function.update x j y)
          = (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N y) *
              (((∑ j' : Fin n,
                  Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)) : ℝ) : ℂ) :=
      (hThetaShift j).mono (fun y hy => by rw [hy x hxm hxg])
    have hAP : aPC ℓ j (fun y => (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N (y j)) * Θ y) x
        = ((1 / ℓ ^ 3 : ℝ) : ℂ) * ∫ y in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N y) * Θ (Function.update x j y) := by
      rw [aPC]
      congr 1
      show ∫ y in Submission.BoseGases.acube ℓ,
            (fun y => (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N (y j)) * Θ y)
              (Function.update x j y)
          = ∫ y in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N y) * Θ (Function.update x j y)
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      show (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N (Function.update x j y j))
            * Θ (Function.update x j y)
          = (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N y) * Θ (Function.update x j y)
      rw [Function.update_self]
    have hInt : Integrable (fun y : Sp => (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N y) *
        (((∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)) : ℝ) : ℂ))
        ((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
          (Submission.BoseGases.acube ℓ)) :=
      pS_integrableOn_conj_chiMode_mul_aPsum hℓ hΦc hAESM hBnd hxm j
    rw [hAP]
    calc (((((1 / ℓ ^ 3 : ℝ) : ℂ)) * ∫ y in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N y) * Θ (Function.update x j y))).re
        = (1 / ℓ ^ 3) * (∫ y in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N y) * Θ (Function.update x j y)).re := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          ring
      _ = (1 / ℓ ^ 3) * (∫ y in Submission.BoseGases.acube ℓ,
            (starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N y) *
              (((∑ j' : Fin n,
                  Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)) : ℝ) : ℂ)).re := by
          rw [integral_congr_ae hshift]
      _ = (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
            ((starRingEnd ℂ) (Work.BoseBoxFock.chiMode ℓ N y) *
              (((∑ j' : Fin n,
                  Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)) : ℝ) : ℂ)).re := by
          rw [pS_setIntegral_re_gen hInt]
      _ = (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
            Work.BoseBoxFock.chiW ℓ N y *
              (∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)) := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)]
            with y hy
          exact pS_conj_chiMode_mul_ofReal_re hℓ N hy
  -- ### integrability of the `cIPn` integrand
  have hIntZ : IntegrableOn (fun x => (((Φ x : ℝ)) : ℂ) * Z x)
      (Submission.BoseGases.abox n ℓ) := by
    obtain ⟨CZ, hCZ⟩ := hZb
    obtain ⟨CΦ, hCΦ⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      hΦc.continuousOn
    refine MeasureTheory.IntegrableOn.of_bound
      (Submission.BoseGases.abox_lt_top n ℓ hℓ.le) ?_ (max CΦ 0 * max CZ 0) ?_
    · exact ((Complex.continuous_ofReal.measurable.comp hΦc.measurable).mul hZm).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)]
        with x hx
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul ((hCΦ x hx).trans (le_max_left _ _))
        ((hCZ x).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  -- ### the LHS reduction and the a.e. evaluation
  have hLHS : (Work.BoseDict.cIPn n Ψ Z).re
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * (Z x).re := by
    rw [hΨdef]
    exact pS_cIPn_boxRestrictC_re hIntZ
  have hFin : (Work.BoseDict.cIPn n Ψ Z).re
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * (∑ j : Fin n, (1 / ℓ ^ 3) *
          ∫ y in Submission.BoseGases.acube ℓ, Work.BoseBoxFock.chiW ℓ N y *
            (∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y))) := by
    rw [hLHS]
    refine integral_congr_ae ?_
    filter_upwards [hKey] with x hx
    rw [hx]
  -- ### the RHS unfolding
  have hRHS : Work.BoseBoxFock.pairHalfTwo n ℓ (Work.BoseBoxFock.chiW ℓ N) Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * (∑ j : Fin n, (1 / ℓ ^ 3) *
          ∫ y in Submission.BoseGases.acube ℓ, Work.BoseBoxFock.chiW ℓ N y *
            (∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y))) := by
    rw [Work.BoseBoxFock.pairHalfTwo]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show Φ x * (∑ j : Fin n, (Submission.BoseGases.aP ℓ j
        (fun y => Work.BoseBoxFock.chiW ℓ N (y j) *
          (∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ y))) x)
      = Φ x * (∑ j : Fin n, (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
          Work.BoseBoxFock.chiW ℓ N y *
            (∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y)))
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Submission.BoseGases.aP]
    congr 1
    show ∫ y in Submission.BoseGases.acube ℓ,
          (fun y => Work.BoseBoxFock.chiW ℓ N (y j) *
            (∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ y)) (Function.update x j y)
        = ∫ y in Submission.BoseGases.acube ℓ, Work.BoseBoxFock.chiW ℓ N y *
            (∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    show Work.BoseBoxFock.chiW ℓ N (Function.update x j y j) *
          (∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y))
        = Work.BoseBoxFock.chiW ℓ N y *
          (∑ j' : Fin n, Submission.BoseGases.aP ℓ j' Φ (Function.update x j y))
    rw [Function.update_self]
  exact hFin.trans hRHS.symm

end Work.BoseBoxFock
