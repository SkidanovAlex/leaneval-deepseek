import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.boxAnnOf_symm
import Submission.Work.BoseBoxFock.slotPairDefs
import Submission.Work.BoseDict.cIPn_boxAnnOf_eqInt
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.selfPairG` — the weak-bundle self-pairing of the
four-letter box word, in a **clash-free** cone

This is a copy of `Work.BoseBoxFock.cIPn_bW4_self_weak` with the (unused) import of the strong
twin `cIPn_bW4_self` removed and every declaration renamed by a `G` suffix.  The point: the
strong and weak twins both import `Work.BoseBoxFock.AVGoodState`, which contains
`etaOf_continuous`/`etaOf_hasCompactSupport` — the *same* two names as
`Work.BoseBoxFock.boxSlotSum_measurable_bounded`, which is in the import cone of
`Work.BoseBoxFock.PotCubicHonest`/`frkCore`.  Hence neither twin can be imported together with
the cubic chapter (`BLOCKER_nPlusC_duplicate.md`), and this copy supplies the identity

    `cIPn (d+2) Ψ (bW4 e w₁ w₂ v₁ v₂ d Ψ)
        = cIPn d (a_{w₂}a_{w₁}Ψ) (a_{v₁}a_{v₂}Ψ)`

in the cone of the cubic chapter.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The weak regularity class -/

/-- **The weak regularity class** of the honest box ↔ model bundle: measurable, everywhere
bounded, and supported in the `n`-particle corpus box `boxPow n ℓ` (a set of finite measure). -/
structure WRegG {n : ℕ} (ℓ : ℝ) (f : Xn n → ℂ) : Prop where
  meas : Measurable f
  bdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
  supp : Function.support f ⊆ Work.MB.boxPow n ℓ

/-- **A weakly regular function is integrable** (its support has finite measure). -/
theorem WRegG.integrable {n : ℕ} {ℓ : ℝ} {f : Xn n → ℂ} (h : WRegG ℓ f) :
    MeasureTheory.Integrable f := by
  obtain ⟨C, hC⟩ := h.bdd
  exact Work.MB.integrable_of_bdd_of_support (Work.MB.measurableSet_boxPow n ℓ)
    (Work.MB.volume_boxPow_lt_top n ℓ) h.meas.aestronglyMeasurable hC
    (fun x hx => Function.notMem_support.mp fun hxf => hx (h.supp hxf))

/-- The superposition `etaOf e w` of weakly regular modes is integrable, as is its norm. -/
theorem integrable_etaOf_weakG {m : ℕ} {e : Fin m → Sp → ℂ} {ℓ : ℝ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (w : Fin m → ℝ) :
    MeasureTheory.Integrable (etaOf e w)
      ∧ MeasureTheory.Integrable (fun z : Sp => ‖etaOf e w z‖) := by
  obtain ⟨C, hC0, hC⟩ := Work.MB.etaOf_weak_bound hbdd w
  have hin : MeasureTheory.Integrable (etaOf e w) :=
    Work.MB.integrable_of_bdd_of_support (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
      (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
      (Work.MB.etaOf_weak_measurable hmeas w).aestronglyMeasurable hC
      (fun z hz => Function.notMem_support.mp fun hzf => hz (Work.MB.etaOf_weak_support hsupp w hzf))
  exact ⟨hin, hin.norm⟩

/-- The continuous map `p ↦ Fin.cons p.2 p.1`. -/
theorem continuous_cons_swap {d : ℕ} :
    Continuous (fun p : Xn d × Sp => (Fin.cons p.2 p.1 : Xn (d + 1))) := by
  refine continuous_pi (fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using (continuous_snd : Continuous (fun p : Xn d × Sp => p.2))
  · exact (continuous_apply j).comp (continuous_fst : Continuous (fun p : Xn d × Sp => p.1))

/-- The continuous map `z ↦ Fin.cons z y` for a fixed `y`. -/
theorem continuous_cons_fixed {d : ℕ} (y : Xn d) :
    Continuous (fun z : Sp => (Fin.cons z y : Xn (d + 1))) := by
  refine continuous_pi (fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_id
  · exact continuous_const

/-- The continuous map `p ↦ Fin.cons p.1 p.2` on `Sp × Xn d`. -/
theorem continuous_cons_prod {d : ℕ} :
    Continuous (fun p : Sp × Xn d => (Fin.cons p.1 p.2 : Xn (d + 1))) := by
  refine continuous_pi (fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp continuous_snd

/-! ## 2. The weak regularity of `boxAnnOf` -/

/-- **`boxAnnOf` preserves the weak regularity class.** -/
theorem boxAnnOf_wregG {m d : ℕ} {e : Fin m → Sp → ℂ} {ℓ : ℝ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Θ : Xn (d + 1) → ℂ} (hΘ : WRegG ℓ Θ) : WRegG ℓ (boxAnnOf e w d Θ) := by
  have hΘm : Measurable Θ := hΘ.meas
  obtain ⟨CΘ, hΘb⟩ := hΘ.bdd
  have hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 1) ℓ := hΘ.supp
  have hηm : Measurable (etaOf e w) := Work.MB.etaOf_weak_measurable hmeas w
  obtain ⟨hηint, hηnint⟩ := integrable_etaOf_weakG hmeas hbdd hsupp w
  refine ⟨?_, ⟨‖(Real.sqrt ((d : ℝ) + 1) : ℂ)‖ * ((∫ z : Sp, ‖etaOf e w z‖) * max CΘ 0), ?_⟩, ?_⟩
  · -- measurability: parametric integral
    have hfm : Measurable (Function.uncurry
        (fun (y : Xn d) (z : Sp) => (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y))) := by
      apply Measurable.mul
      · exact (Complex.continuous_conj.measurable.comp (hηm.comp measurable_snd))
      · exact hΘm.comp (continuous_cons_swap (d := d)).measurable
    have := (hfm.stronglyMeasurable.integral_prod_right (ν := (volume : Measure Sp))).measurable
    exact this.const_mul _
  · -- boundedness
    intro y
    have hbound : ∀ z : Sp, ‖(starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)‖
        ≤ ‖etaOf e w z‖ * max CΘ 0 := by
      intro z
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left ((hΘb _).trans (le_max_left _ _)) (norm_nonneg _)
    have haesm : AEStronglyMeasurable
        (fun z : Sp => ‖(starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)‖) :=
      (((Complex.continuous_conj.measurable.comp hηm).mul
        (hΘm.comp (continuous_cons_fixed y).measurable)).norm).aestronglyMeasurable
    have hInt1 : MeasureTheory.Integrable
        (fun z : Sp => ‖(starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)‖) :=
      Integrable.mono' (hηnint.mul_const (max CΘ 0)) haesm
        (Filter.Eventually.of_forall (fun z => by simpa using hbound z))
    calc ‖Real.sqrt ((d : ℝ) + 1) * ∫ z : Sp, (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)‖
        = ‖(Real.sqrt ((d : ℝ) + 1) : ℂ)‖
            * ‖∫ z : Sp, (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)‖ := by
          rw [norm_mul]
      _ ≤ ‖(Real.sqrt ((d : ℝ) + 1) : ℂ)‖
            * ∫ z : Sp, ‖(starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)‖ := by
          refine mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
      _ ≤ ‖(Real.sqrt ((d : ℝ) + 1) : ℂ)‖ * ∫ z : Sp, ‖etaOf e w z‖ * max CΘ 0 := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact integral_mono hInt1 (hηnint.mul_const _) hbound
      _ = ‖(Real.sqrt ((d : ℝ) + 1) : ℂ)‖ * ((∫ z : Sp, ‖etaOf e w z‖) * max CΘ 0) := by
          rw [integral_mul_const]
  · -- support
    intro y hy
    by_contra hybox
    refine hy ?_
    have hzero : ∀ z : Sp, (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y) = 0 := by
      intro z
      have hcons : (Fin.cons z y : Xn (d + 1)) ∉ Work.MB.boxPow (d + 1) ℓ := by
        intro hmem
        refine hybox (fun i => ?_)
        have := (Work.MB.mem_boxPow_iff.mp hmem) (Fin.succ i)
        simpa using this
      rw [Function.notMem_support.mp (fun h => hcons (hΘsupp h)), mul_zero]
    simp only [boxAnnOf, hzero, integral_zero, mul_zero]


/-- **`boxCreOf` preserves the weak regularity class.** -/
theorem boxCreOf_wregG {m d : ℕ} {e : Fin m → Sp → ℂ} {ℓ : ℝ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Y : Xn d → ℂ} (hY : WRegG ℓ Y) : WRegG ℓ (boxCreOf e w d Y) := by
  have hYm : Measurable Y := hY.meas
  obtain ⟨CY, hYb⟩ := hY.bdd
  have hYsupp : Function.support Y ⊆ Work.MB.boxPow d ℓ := hY.supp
  have hηm : Measurable (etaOf e w) := Work.MB.etaOf_weak_measurable hmeas w
  obtain ⟨Cη, hCη0, hCη⟩ := Work.MB.etaOf_weak_bound hbdd w
  have hηsupp : Function.support (etaOf e w) ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
    Work.MB.etaOf_weak_support hsupp w
  refine ⟨?_, ⟨‖(1 / (Real.sqrt ((d : ℝ) + 1) : ℂ))‖ * (((d : ℝ) + 1) * Cη * CY), ?_⟩, ?_⟩
  · -- measurability: finite sum of products
    have hsum : Measurable (fun x : Xn (d + 1) => ∑ j : Fin (d + 1),
        etaOf e w (x j) * Y (fun i : Fin d => x (Fin.succAbove j i))) :=
      Finset.measurable_sum Finset.univ (fun j _ =>
        (hηm.comp (measurable_pi_apply j)).mul
          (hYm.comp (measurable_pi_iff.mpr
            (fun i => measurable_pi_apply (Fin.succAbove j i)))))
    exact hsum.const_mul _
  · -- boundedness
    intro x
    have hterm : ∀ j : Fin (d + 1), ‖etaOf e w (x j) * Y (fun i : Fin d => x (Fin.succAbove j i))‖
        ≤ Cη * CY := by
      intro j
      rw [norm_mul]
      exact mul_le_mul (hCη _) (hYb _) (norm_nonneg _) hCη0
    have hCYCη : 0 ≤ Cη * CY := mul_nonneg hCη0 (le_trans (norm_nonneg _) (hYb 0))
    calc ‖(1 / (Real.sqrt ((d : ℝ) + 1) : ℂ)) * ∑ j : Fin (d + 1),
          etaOf e w (x j) * Y (fun i : Fin d => x (Fin.succAbove j i))‖
        = ‖(1 / (Real.sqrt ((d : ℝ) + 1) : ℂ))‖
            * ‖∑ j : Fin (d + 1), etaOf e w (x j) * Y (fun i : Fin d => x (Fin.succAbove j i))‖ := by
          rw [norm_mul]
      _ ≤ ‖(1 / (Real.sqrt ((d : ℝ) + 1) : ℂ))‖ * ∑ j : Fin (d + 1),
            ‖etaOf e w (x j) * Y (fun i : Fin d => x (Fin.succAbove j i))‖ := by
          refine mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ ≤ ‖(1 / (Real.sqrt ((d : ℝ) + 1) : ℂ))‖ * ∑ _j : Fin (d + 1), Cη * CY := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hterm j)) (norm_nonneg _)
      _ = ‖(1 / (Real.sqrt ((d : ℝ) + 1) : ℂ))‖ * (((d : ℝ) + 1) * (Cη * CY)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ = ‖(1 / (Real.sqrt ((d : ℝ) + 1) : ℂ))‖ * (((d : ℝ) + 1) * Cη * CY) := by
          ring
  · -- support
    intro x hx
    by_contra hxbox
    refine hx ?_
    obtain ⟨i, hi⟩ : ∃ i : Fin (d + 1), x i ∉ Work.BoseK15.corpusBox.boxL ℓ := by
      by_contra hcon
      exact hxbox (Work.MB.mem_boxPow_iff.mpr (fun i => by
        by_contra hi
        exact hcon ⟨i, hi⟩))
    simp only [boxCreOf]
    have hsum0 : (∑ j : Fin (d + 1),
        etaOf e w (x j) * Y (fun k : Fin d => x (Fin.succAbove j k))) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases hji : j = i
      · subst hji
        rw [Function.notMem_support.mp (fun h => hi (hηsupp h)), zero_mul]
      · have hmem : (fun k : Fin d => x (Fin.succAbove j k)) ∉ Work.MB.boxPow d ℓ := by
          intro hmem
          obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (x := i) (y := j) (Ne.symm hji)
          exact hi (by rw [← hk]; exact (Work.MB.mem_boxPow_iff.mp hmem) k)
        rw [Function.notMem_support.mp (fun h => hmem (hYsupp h)), mul_zero]
    rw [hsum0, mul_zero]

/-! ## 3. The Fubini integrability of the η × state product -/

/-- **The weak twin of `integrable_etaOf_conj_cons_mul`**: the product
`(z,y) ↦ η_w(z)·conj (Θ (z,y))·Y y` is integrable whenever `η_w`, `Θ` and `Y` are weakly
regular. -/
theorem integrable_etaOf_conj_cons_mul_wregG {m d : ℕ} {e : Fin m → Sp → ℂ} {ℓ : ℝ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Θ : Xn (d + 1) → ℂ} (hΘ : WRegG ℓ Θ) {Y : Xn d → ℂ} (hY : WRegG ℓ Y) :
    MeasureTheory.Integrable (fun p : Sp × Xn d =>
      etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Y p.2) := by
  obtain ⟨Cη, hCη0, hCη⟩ := Work.MB.etaOf_weak_bound hbdd w
  obtain ⟨CΘ, hΘb⟩ := hΘ.bdd
  obtain ⟨CY, hYb⟩ := hY.bdd
  have hηsupp : Function.support (etaOf e w) ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
    Work.MB.etaOf_weak_support hsupp w
  have hηn : MeasureTheory.Integrable (fun z : Sp => ‖etaOf e w z‖) :=
    (integrable_etaOf_weakG hmeas hbdd hsupp w).2
  -- the majorant `‖η(z)‖ · (C · 1_{boxPow})` is integrable (a product of two integrable
  -- functions of the separate variables)
  have hind : MeasureTheory.Integrable (fun y : Xn d =>
      (max CΘ 0 * max CY 0) * (Work.MB.boxPow d ℓ).indicator (fun _ => (1 : ℝ)) y) :=
    ((integrable_indicator_iff (Work.MB.measurableSet_boxPow d ℓ)).mpr
      (integrableOn_const (Work.MB.volume_boxPow_lt_top d ℓ))).const_mul _
  have hmaj : MeasureTheory.Integrable (fun p : Sp × Xn d =>
      ‖etaOf e w p.1‖ *
        ((max CΘ 0 * max CY 0) * (Work.MB.boxPow d ℓ).indicator (fun _ => (1 : ℝ)) p.2)) :=
    hηn.mul_prod hind
  have haesm : AEStronglyMeasurable (fun p : Sp × Xn d =>
      etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Y p.2) :=
    ((((Work.MB.etaOf_weak_measurable hmeas w).comp measurable_fst).mul
      ((Complex.continuous_conj.measurable.comp
        (hΘ.meas.comp (continuous_cons_prod (d := d)).measurable)))).mul
      (hY.meas.comp measurable_snd)).aestronglyMeasurable
  refine hmaj.mono' haesm (Filter.Eventually.of_forall (fun p => ?_))
  have hηnn : 0 ≤ ‖etaOf e w p.1‖ := norm_nonneg _
  have hΘn : ‖Θ (Fin.cons p.1 p.2)‖ ≤ max CΘ 0 := (hΘb _).trans (le_max_left _ _)
  have hYn : ‖Y p.2‖ ≤ max CY 0 := (hYb _).trans (le_max_left _ _)
  by_cases hp2 : p.2 ∈ Work.MB.boxPow d ℓ
  · rw [Set.indicator_of_mem hp2, mul_one]
    calc ‖etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Y p.2‖
        = ‖etaOf e w p.1‖ * ‖Θ (Fin.cons p.1 p.2)‖ * ‖Y p.2‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj]
      _ ≤ ‖etaOf e w p.1‖ * (max CΘ 0 * max CY 0) := by
          calc ‖etaOf e w p.1‖ * ‖Θ (Fin.cons p.1 p.2)‖ * ‖Y p.2‖
              ≤ (‖etaOf e w p.1‖ * max CΘ 0) * max CY 0 :=
                mul_le_mul (mul_le_mul_of_nonneg_left hΘn hηnn) hYn (norm_nonneg _)
                  (mul_nonneg hηnn (le_max_right _ _))
            _ = ‖etaOf e w p.1‖ * (max CΘ 0 * max CY 0) := by ring
  · have h0 : Y p.2 = 0 := Function.notMem_support.mp (fun h => hp2 (hY.supp h))
    simp only [h0, mul_zero, norm_zero, Set.indicator_of_notMem hp2]
    exact le_rfl


/-! ## 4. The weak-bundle self-pairing of the four-letter word -/

/-- **The weak twin of `cIPn_bW4_self`**: the self-pairing of the four-letter box word against a
symmetric, box-supported, everywhere bounded box state (no continuity, no compact support). -/
theorem cIPn_bW4_selfG {m d : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbddE : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (w₁ w₂ v₁ v₂ : Fin m → ℝ) {Φ : Xn (d + 2) → ℂ}
    (hΦm : Measurable Φ) {CΦ : ℝ} (hΦb : ∀ x, ‖Φ x‖ ≤ CΦ)
    (hΦsupp : Function.support Φ ⊆ Work.MB.boxPow (d + 2) ℓ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin (d + 2)), (fun x => Φ (x ∘ σ)) = Φ) :
    cIPn (d + 2) Φ (bW4 e w₁ w₂ v₁ v₂ d Φ)
      = cIPn d (boxAnnOf e w₂ d (boxAnnOf e w₁ (d + 1) Φ))
          (boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) Φ)) := by
  have hΦW : WRegG ℓ Φ := ⟨hΦm, ⟨CΦ, hΦb⟩, hΦsupp⟩
  have hΘ₂ : WRegG ℓ (boxAnnOf e v₂ (d + 1) Φ) := boxAnnOf_wregG hmeas hbddE hsupp v₂ hΦW
  have hY : WRegG ℓ (boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) Φ)) :=
    boxAnnOf_wregG hmeas hbddE hsupp v₁ hΘ₂
  have hX : WRegG ℓ (boxCreOf e w₂ d (boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) Φ))) :=
    boxCreOf_wregG hmeas hbddE hsupp w₂ hY
  have hΘ₁ : WRegG ℓ (boxAnnOf e w₁ (d + 1) Φ) := boxAnnOf_wregG hmeas hbddE hsupp w₁ hΦW
  have hΦsym' : ∀ σ : Equiv.Perm (Fin (d + 2)), ∀ x : Xn (d + 2), Φ (x ∘ ⇑σ) = Φ x :=
    fun σ x => congrFun (hΦsym σ) x
  have hΘ₁sym : ∀ σ : Equiv.Perm (Fin (d + 1)), ∀ y : Xn (d + 1),
      boxAnnOf e w₁ (d + 1) Φ (y ∘ ⇑σ) = boxAnnOf e w₁ (d + 1) Φ y :=
    boxAnnOf_symm w₁ Φ hΦsym'
  have hInt₁ := integrable_etaOf_conj_cons_mul_wregG hmeas hbddE hsupp w₁ hΦW hX
  have hInt₂ := integrable_etaOf_conj_cons_mul_wregG hmeas hbddE hsupp w₂ hΘ₁ hY
  have h1 := cIPn_boxAnnOf_eqInt (d := d + 1) hbdd hsupp w₁ Φ hΦW.integrable hΦsym'
    (boxCreOf e w₂ d (boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) Φ))) hX.integrable hInt₁
  have h2 := cIPn_boxAnnOf_eqInt (d := d) hbdd hsupp w₂ (boxAnnOf e w₁ (d + 1) Φ)
    hΘ₁.integrable hΘ₁sym (boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) Φ)) hY.integrable hInt₂
  show cIPn (d + 2) Φ (boxCreOf e w₁ (d + 1)
      (boxCreOf e w₂ d (boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) Φ))))
    = cIPn d (boxAnnOf e w₂ d (boxAnnOf e w₁ (d + 1) Φ))
        (boxAnnOf e v₁ d (boxAnnOf e v₂ (d + 1) Φ))
  rw [← h1, ← h2]

end Work.BoseBoxFock

