import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.frame_complex
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.integral_sliceRestore
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotJ_slice_excited
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotJ_slice_frame
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotU_measurable_sqIntegrable
import Submission.Work.MB.boxSlotSum_measurable_bounded_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PotCubicLowBandAux

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas for `slotBesselExcited`

The target reduces, slot by slot, to a one-particle inequality.  The bricks collected here are:

* the geometry of the configuration box `abox` (measurability, finite measure, the monotonicity
  `abox ℓ ⊆ abox |ℓ|`);
* the reduction of a set integral over `abox` to the global integral for functions supported in
  the box;
* the regularity (`Measurable`, bounded) of the single-slot expression `slotJ` of
  `slotBesselDefs`. -/

/-- The centred cube is monotone in `|ℓ|`: `acube ℓ ⊆ acube |ℓ|`. -/
theorem acube_subset_acube_abs (ℓ : ℝ) :
    Submission.BoseGases.acube ℓ ⊆ Submission.BoseGases.acube |ℓ| := by
  intro y hy
  rw [Submission.BoseGases.mem_acube_iff] at hy
  rw [Submission.BoseGases.mem_acube_iff]
  intro i
  have hyi := hy i
  rw [Set.mem_Icc] at hyi ⊢
  have h2 : |y.ofLp i| ≤ |ℓ| / 2 := by
    have h1 : |y.ofLp i| ≤ ℓ / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hyi.1], by linarith [hyi.2]⟩
    linarith [le_abs_self ℓ]
  have h3 := abs_le.mp h2
  exact ⟨by linarith [h3.1], by linarith [h3.2]⟩

/-- The `n`-particle configuration box has finite volume, for **every** side length `ℓ`
(the sub-box `abox |ℓ|` controls it). -/
theorem volume_abox_ne_top (n : ℕ) (ℓ : ℝ) :
    (volume : Measure (Submission.BoseGases.X n)) (Submission.BoseGases.abox n ℓ) ≠ ⊤ := by
  have hsub : Submission.BoseGases.abox n ℓ ⊆ Submission.BoseGases.abox n |ℓ| := by
    intro x hx
    rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
    exact fun i => acube_subset_acube_abs ℓ (hx i)
  have hle : (volume : Measure (Submission.BoseGases.X n)) (Submission.BoseGases.abox n ℓ)
      ≤ (volume : Measure (Submission.BoseGases.X n)) (Submission.BoseGases.abox n |ℓ|) :=
    MeasureTheory.measure_mono hsub
  rw [Submission.BoseGases.abox_volume n |ℓ| (abs_nonneg ℓ)] at hle
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)

/-- **A set integral of a function supported in the set is the global integral.** -/
theorem setIntegral_eq_integral_of_support_subset {n : ℕ}
    {s : Set (Work.BoseDict.Xn n)} (hs : MeasurableSet s) {f : Work.BoseDict.Xn n → ℝ}
    (hfs : Function.support f ⊆ s) : ∫ x in s, f x = ∫ x, f x := by
  rw [← MeasureTheory.integral_indicator hs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    exact (Function.notMem_support.mp fun h => hx (hfs h)).symm

/-- The single-slot expression `slotJ` written with the slot operators `boxSlotOf`. -/
theorem slotJ_eq_sum_boxSlotOf {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin n) (Θ : Work.BoseDict.Xn n → ℂ) :
    slotJ e T j Θ = fun x => ∑ l : Fin m, ∑ l' : Fin m,
      ((T (Work.BoseB4.evec m l')) l : ℂ)
        * Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x := by
  funext x
  simp only [slotJ, Work.BoseDict.boxSlotOf, Work.BoseB4.evec,
    Work.BoseDict.etaOf_pi_single, starRingEnd_apply]

/-- **A single slot is measurable** under the weak mode bundle. -/
theorem measurable_slotJ {m n : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin n)
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ) :
    Measurable (slotJ e T j Θ) := by
  have hupd : Measurable (fun p : Work.BoseDict.Xn n × Work.BoseDict.Sp =>
      Function.update p.1 j p.2) :=
    Work.BoseBoxFock.measurable_update_pair j
  have hres : ∀ l' : Fin m, Measurable (fun x : Work.BoseDict.Xn n =>
      ∫ z : Work.BoseDict.Sp, star (e l' z) * Θ (Function.update x j z)) := by
    intro l'
    have hjoint : Measurable (fun p : Work.BoseDict.Xn n × Work.BoseDict.Sp =>
        star (e l' p.2) * Θ (Function.update p.1 j p.2)) :=
      ((Complex.continuous_conj.measurable.comp
        ((hmeas l').comp measurable_snd)).mul (hΘm.comp hupd))
    exact hjoint.stronglyMeasurable.integral_prod_right'.measurable
  rw [slotJ_eq_sum_boxSlotOf]
  simp only [Work.BoseDict.boxSlotOf, Work.BoseB4.evec, Work.BoseDict.etaOf_pi_single,
    starRingEnd_apply]
  refine Finset.measurable_sum _ fun l _ => Finset.measurable_sum _ fun l' _ => ?_
  exact measurable_const.mul (((hmeas l).comp (measurable_pi_apply j)).mul (hres l'))

/-- **A single slot is bounded** under the weak mode bundle and a bounded state. -/
theorem exists_norm_slotJ_le {m n : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin n) {Θ : Work.BoseDict.Xn n → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    ∃ K : ℝ, ∀ x, ‖slotJ e T j Θ x‖ ≤ K := by
  choose K hK using fun l l' : Fin m =>
    (Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp
      (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ hΘm hΘb).2
  refine ⟨∑ l : Fin m, ∑ l' : Fin m,
    ‖(T (Work.BoseB4.evec m l')) l‖ * max (K l l') 0, fun x => ?_⟩
  rw [slotJ_eq_sum_boxSlotOf]
  calc ‖∑ l : Fin m, ∑ l' : Fin m, ((T (Work.BoseB4.evec m l')) l : ℂ)
        * Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖
      ≤ ∑ l : Fin m, ‖∑ l' : Fin m, ((T (Work.BoseB4.evec m l')) l : ℂ)
          * Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ l : Fin m, ∑ l' : Fin m, ‖((T (Work.BoseB4.evec m l')) l : ℂ)
          * Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ :=
        Finset.sum_le_sum fun l _ => norm_sum_le _ _
    _ ≤ ∑ l : Fin m, ∑ l' : Fin m,
        ‖(T (Work.BoseB4.evec m l')) l‖ * max (K l l') 0 := by
        refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun l' _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((hK l l' x).trans (le_max_left _ _)) (abs_nonneg _)

/-- The `x`-integrand of the `T`-row is supported in the configuration box. -/
theorem support_star_boxSlotSum_subset {m n : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Θ : Work.BoseDict.Xn n → ℂ}
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    Function.support (fun x : Work.BoseDict.Xn n =>
      (star (Θ x) * Work.BoseDict.boxSlotSum e T Θ x).re) ⊆
      Submission.BoseGases.abox n ℓ := by
  intro x hx
  by_contra hxab
  refine hx ?_
  have h0 : Θ x = 0 := by
    by_contra h
    exact hxab (hΘsupp (Function.mem_support.mpr h))
  simp [h0]

/-- The `x`-integrand of the `T`-row is integrable. -/
theorem integrable_star_boxSlotSum {m n : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Θ : Work.BoseDict.Xn n → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    Integrable (fun x : Work.BoseDict.Xn n =>
      (star (Θ x) * Work.BoseDict.boxSlotSum e T Θ x).re) := by
  obtain ⟨hbsm, KBS, hKBS⟩ := Work.MB.boxSlotSum_measurable_bounded_ae (d := n) hmeas hbdd
    hsupp T Θ hΘm hΘb
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hFc : Integrable (fun x : Work.BoseDict.Xn n =>
      star (Θ x) * Work.BoseDict.boxSlotSum e T Θ x) := by
    refine Work.MB.integrable_of_bdd_of_support
      (S := Submission.BoseGases.abox n ℓ) (C := max CΘ 0 * max KBS 0) ?_ ?_ ?_ ?_ ?_
    · exact Submission.BoseGases.abox_measurable n ℓ
    · exact volume_abox_ne_top n ℓ
    · exact ((Complex.continuous_conj.measurable.comp hΘm).mul hbsm).aestronglyMeasurable
    · intro x
      rw [norm_mul, norm_star]
      have h1 : ‖Θ x‖ ≤ max CΘ 0 := (hCΘ x).trans (le_max_left _ _)
      have h2 : ‖Work.BoseDict.boxSlotSum e T Θ x‖ ≤ max KBS 0 :=
        (hKBS x).trans (le_max_left _ _)
      exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
    · intro x hx
      have h0 : Θ x = 0 := by
        by_contra h
        exact hx (hΘsupp (Function.mem_support.mpr h))
      rw [h0, star_zero, zero_mul]
  simpa using Complex.reCLM.integrable_comp hFc

/-- The `x`-integrand of a single slot is integrable. -/
theorem integrable_slotJ_integrand {m n : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin n) {Θ : Work.BoseDict.Xn n → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    Integrable (fun x : Work.BoseDict.Xn n => (star (Θ x) * slotJ e T j Θ x).re) := by
  obtain ⟨K, hK⟩ := exists_norm_slotJ_le hmeas hbdd hsupp T j hΘm hΘb
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hFc : Integrable (fun x : Work.BoseDict.Xn n => star (Θ x) * slotJ e T j Θ x) := by
    refine Work.MB.integrable_of_bdd_of_support
      (S := Submission.BoseGases.abox n ℓ) (C := max CΘ 0 * max K 0) ?_ ?_ ?_ ?_ ?_
    · exact Submission.BoseGases.abox_measurable n ℓ
    · exact volume_abox_ne_top n ℓ
    · exact ((Complex.continuous_conj.measurable.comp hΘm).mul
        (measurable_slotJ hmeas T j hΘm)).aestronglyMeasurable
    · intro x
      rw [norm_mul, norm_star]
      have h1 : ‖Θ x‖ ≤ max CΘ 0 := (hCΘ x).trans (le_max_left _ _)
      have h2 : ‖slotJ e T j Θ x‖ ≤ max K 0 := (hK x).trans (le_max_left _ _)
      exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
    · intro x hx
      have h0 : Θ x = 0 := by
        by_contra h
        exact hx (hΘsupp (Function.mem_support.mpr h))
      rw [h0, star_zero, zero_mul]
  simpa using Complex.reCLM.integrable_comp hFc

theorem slotBesselExcited {m n : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Fin m → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hframe : ∀ w : Fin m → ℝ,
      ∑ k : ι, (Work.BoseB4.gram (f k) w) ^ 2 ≤ C * ∑ l : Fin m, (w l) ^ 2)
    (h0 : ∀ k : ι, f k 0 = 0)
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (star (Θ x) * Work.BoseDict.boxSlotSum e
          (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) Θ x).re)
      ≤ C * (∫ x in Submission.BoseGases.abox n ℓ,
        (star (Θ x) * Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x).re) := by
  classical
  -- local copies of the delegated inputs (replaced by the corresponding imports)
  have hsplit : ∀ (j : Fin n) (F : Work.BoseDict.Xn n → ℝ) (hF : Integrable F),
      ∫ x : Work.BoseDict.Xn n, F x
        = ∫ ŷ : ({i : Fin n // i ≠ j} → Work.BoseDict.Sp), ∫ a : Work.BoseDict.Sp,
            F (sliceRestore j a ŷ) := fun j F hF => integral_sliceRestore j hF
  have hsliceT : ∀ (j : Fin n) (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp),
      ∫ a : Work.BoseDict.Sp, (star (Θ (sliceRestore j a ŷ))
          * slotJ e (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) j Θ
            (sliceRestore j a ŷ)).re
        = ∑ k : ι, ‖∑ l : Fin m, (((f k) l : ℝ) : ℂ)
            * (∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ))‖ ^ 2 :=
    fun j ŷ => slotJ_slice_frame hmeas hbdd hsupp f j hΘm hΘb ŷ
  have hslice0 : ∀ (j : Fin n) (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp),
      ∫ a : Work.BoseDict.Sp, (star (Θ (sliceRestore j a ŷ))
          * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ (sliceRestore j a ŷ)).re
        = ∑ l ∈ (Finset.univ.erase (0 : Fin m)),
            ‖∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ)‖ ^ 2 :=
    fun j ŷ => slotJ_slice_excited hmeas hbdd hsupp j hΘm hΘb ŷ
  have hU : ∀ (j : Fin n),
      (∀ l : Fin m, AEMeasurable (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
          ∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ)))
        ∧ (∀ l : Fin m, Integrable (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
            ‖(∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ))‖ ^ 2)) :=
    fun j => slotU_measurable_sqIntegrable hmeas hbdd hsupp j hΘm hΘb hΘsupp
  -- 0. the box integrals are global integrals
  have hsupT : Function.support (fun x : Work.BoseDict.Xn n =>
      (star (Θ x) * Work.BoseDict.boxSlotSum e
        (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) Θ x).re)
      ⊆ Submission.BoseGases.abox n ℓ :=
    support_star_boxSlotSum_subset _ hΘsupp
  have hsup0 : Function.support (fun x : Work.BoseDict.Xn n =>
      (star (Θ x) * Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x).re)
      ⊆ Submission.BoseGases.abox n ℓ :=
    support_star_boxSlotSum_subset (Work.BoseBoxFock.boxT0 m) hΘsupp
  rw [setIntegral_eq_integral_of_support_subset
      (s := Submission.BoseGases.abox n ℓ) (Submission.BoseGases.abox_measurable n ℓ) hsupT,
    setIntegral_eq_integral_of_support_subset
      (s := Submission.BoseGases.abox n ℓ) (Submission.BoseGases.abox_measurable n ℓ) hsup0]
  -- 1. the slot expansions of the two rows
  have hdecT : (fun x : Work.BoseDict.Xn n => (star (Θ x) * Work.BoseDict.boxSlotSum e
        (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) Θ x).re)
      = fun x => ∑ j : Fin n, (star (Θ x) * slotJ e
          (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) j Θ x).re := by
    funext x
    rw [congrFun (boxSlotSum_eq_sum_slotJ e _ Θ) x, Finset.sum_apply, Finset.mul_sum]
    exact Complex.re_sum Finset.univ _
  have hdec0 : (fun x : Work.BoseDict.Xn n => (star (Θ x) * Work.BoseDict.boxSlotSum e
        (Work.BoseBoxFock.boxT0 m) Θ x).re)
      = fun x => ∑ j : Fin n, (star (Θ x) * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ x).re := by
    funext x
    rw [congrFun (boxSlotSum_eq_sum_slotJ e _ Θ) x, Finset.sum_apply, Finset.mul_sum]
    exact Complex.re_sum Finset.univ _
  -- 2. the decomposition of the two integrals
  have hLT : (∫ x : Work.BoseDict.Xn n, (star (Θ x) * Work.BoseDict.boxSlotSum e
        (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) Θ x).re)
      = ∑ j : Fin n, ∫ x : Work.BoseDict.Xn n, (star (Θ x) * slotJ e
          (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) j Θ x).re := by
    rw [hdecT]
    exact MeasureTheory.integral_finsetSum _ fun j _ =>
      integrable_slotJ_integrand hmeas hbdd hsupp _ j hΘm hΘb hΘsupp
  have hL0 : (∫ x : Work.BoseDict.Xn n, (star (Θ x) * Work.BoseDict.boxSlotSum e
        (Work.BoseBoxFock.boxT0 m) Θ x).re)
      = ∑ j : Fin n, ∫ x : Work.BoseDict.Xn n,
          (star (Θ x) * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ x).re := by
    rw [hdec0]
    exact MeasureTheory.integral_finsetSum _ fun j _ =>
      integrable_slotJ_integrand hmeas hbdd hsupp _ j hΘm hΘb hΘsupp
  -- 3. the per-slot inequality
  have hper : ∀ j : Fin n,
      (∫ x : Work.BoseDict.Xn n, (star (Θ x) * slotJ e
          (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) j Θ x).re)
        ≤ C * (∫ x : Work.BoseDict.Xn n,
            (star (Θ x) * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ x).re) := by
    intro j
    have hIT : Integrable (fun x : Work.BoseDict.Xn n => (star (Θ x) * slotJ e
        (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) j Θ x).re) :=
      integrable_slotJ_integrand hmeas hbdd hsupp _ j hΘm hΘb hΘsupp
    have hI0 : Integrable (fun x : Work.BoseDict.Xn n =>
        (star (Θ x) * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ x).re) :=
      integrable_slotJ_integrand hmeas hbdd hsupp _ j hΘm hΘb hΘsupp
    rw [hsplit j _ hIT, hsplit j _ hI0]
    obtain ⟨_, hIntU⟩ := hU j
    -- measurability of the mode integrals `ŷ ↦ ∫ z, conj(e_l z) Θ(σ z ŷ)`
    have hmeasU : ∀ l : Fin m, Measurable (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
        ∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ)) := by
      intro l
      have hsl : Measurable (fun p : ({i : Fin n // i ≠ j} → Work.BoseDict.Sp) ×
          Work.BoseDict.Sp => sliceRestore j p.2 p.1) := by
        refine measurable_pi_iff.mpr fun i => ?_
        simp only [sliceRestore]
        split_ifs with h
        · exact measurable_snd
        · exact (measurable_pi_apply (⟨i, h⟩ : {i : Fin n // i ≠ j})).comp measurable_fst
      have hjoint : Measurable (fun p : ({i : Fin n // i ≠ j} → Work.BoseDict.Sp) ×
          Work.BoseDict.Sp => star (e l p.2) * Θ (sliceRestore j p.2 p.1)) :=
        (Complex.continuous_conj.measurable.comp
          ((hmeas l).comp measurable_snd)).mul (hΘm.comp hsl)
      exact hjoint.stronglyMeasurable.integral_prod_right'.measurable
    -- the square sum of the excited modes is integrable
    have hG : Integrable (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
        ∑ l ∈ Finset.univ.erase (0 : Fin m),
          ‖(∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ))‖ ^ 2) :=
      integrable_finsetSum _ fun l _ => hIntU l
    -- the pointwise frame bound
    have hbound : ∀ ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp,
        (∑ k : ι, ‖∑ l : Fin m, (((f k) l : ℝ) : ℂ)
            * (∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ))‖ ^ 2)
          ≤ C * (∑ l ∈ Finset.univ.erase (0 : Fin m),
            ‖(∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ))‖ ^ 2) :=
      fun ŷ => frame_complex f C hframe h0 _
    -- the frame sum is integrable
    have hWk : ∀ k : ι, Measurable (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
        ‖∑ l : Fin m, (((f k) l : ℝ) : ℂ)
          * (∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ))‖ ^ 2) := by
      intro k
      have hsum : Measurable (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
          ∑ l : Fin m, (((f k) l : ℝ) : ℂ)
            * (∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ))) :=
        Finset.measurable_sum Finset.univ fun l _ => measurable_const.mul (hmeasU l)
      exact (hsum.norm).pow_const 2
    have hFSum : Integrable (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
        ∑ k : ι, ‖∑ l : Fin m, (((f k) l : ℝ) : ℂ)
          * (∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ))‖ ^ 2) := by
      have hsumm : Measurable (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
          ∑ k : ι, ‖∑ l : Fin m, (((f k) l : ℝ) : ℂ)
            * (∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ))‖ ^ 2) :=
        Finset.measurable_sum Finset.univ fun k _ => hWk k
      refine Integrable.mono' (hG.const_mul C) hsumm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ŷ => ?_)
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => by positivity)]
      exact hbound ŷ
    -- the pointwise inequality of the inner integrals
    have hpoint : ∀ ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp,
        (∫ a : Work.BoseDict.Sp, (star (Θ (sliceRestore j a ŷ))
            * slotJ e (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) j Θ
              (sliceRestore j a ŷ)).re)
          ≤ C * (∫ a : Work.BoseDict.Sp, (star (Θ (sliceRestore j a ŷ))
              * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ (sliceRestore j a ŷ)).re) := by
      intro ŷ
      rw [hsliceT j ŷ, hslice0 j ŷ]
      exact hbound ŷ
    -- integrability of the two outer integrands
    have hOutT : Integrable (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
        ∫ a : Work.BoseDict.Sp, (star (Θ (sliceRestore j a ŷ))
          * slotJ e (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) j Θ
            (sliceRestore j a ŷ)).re) :=
      hFSum.congr (Filter.Eventually.of_forall fun ŷ => by simp only [hsliceT j ŷ])
    have hOut0 : Integrable (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
        C * (∫ a : Work.BoseDict.Sp, (star (Θ (sliceRestore j a ŷ))
          * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ (sliceRestore j a ŷ)).re)) :=
      (hG.const_mul C).congr (Filter.Eventually.of_forall fun ŷ => by simp only [hslice0 j ŷ])
    calc (∫ ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp, (∫ a : Work.BoseDict.Sp,
            (star (Θ (sliceRestore j a ŷ)) * slotJ e
              (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) j Θ
                (sliceRestore j a ŷ)).re))
        ≤ ∫ ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp, C * (∫ a : Work.BoseDict.Sp,
            (star (Θ (sliceRestore j a ŷ)) * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ
              (sliceRestore j a ŷ)).re) :=
          MeasureTheory.integral_mono hOutT hOut0 hpoint
      _ = C * (∫ ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp, (∫ a : Work.BoseDict.Sp,
            (star (Θ (sliceRestore j a ŷ)) * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ
              (sliceRestore j a ŷ)).re)) :=
          MeasureTheory.integral_const_mul C _
  -- 4. assembly
  calc (∫ x : Work.BoseDict.Xn n, (star (Θ x) * Work.BoseDict.boxSlotSum e
          (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) Θ x).re)
      = ∑ j : Fin n, ∫ x : Work.BoseDict.Xn n, (star (Θ x) * slotJ e
          (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) j Θ x).re := hLT
    _ ≤ ∑ j : Fin n, C * ∫ x : Work.BoseDict.Xn n, (star (Θ x) * slotJ e
          (Work.BoseBoxFock.boxT0 m) j Θ x).re := Finset.sum_le_sum fun j _ => hper j
    _ = C * ∑ j : Fin n, ∫ x : Work.BoseDict.Xn n, (star (Θ x) * slotJ e
          (Work.BoseBoxFock.boxT0 m) j Θ x).re := by rw [Finset.mul_sum]
    _ = C * (∫ x : Work.BoseDict.Xn n, (star (Θ x) * Work.BoseDict.boxSlotSum e
          (Work.BoseBoxFock.boxT0 m) Θ x).re) := by rw [hL0]

end Work.BoseBoxFock.PotCubicLowBandAux
