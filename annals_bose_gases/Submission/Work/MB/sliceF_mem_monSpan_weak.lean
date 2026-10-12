import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sliceF_mem_monSpan
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.sliceF_mem_monSpan_weak` — the sector slice lies in the mode-monomial span (weak class)

The measurable/bounded ("weak") twin of `Work.BoseBoxFock.sliceF_mem_monSpan`: the sector slice

    `sliceF e S Φ y u = slotExact e S Φ (pairCoord S u y)`

of a state `Φ` is a finite linear combination of the mode monomials
`u ↦ ∏_{i : Fin S.card} e (l i) (u i)`, *without* assuming that the modes `e l` are continuous
with compact support — measurability, everywhere boundedness and support in the corpus box
`Work.BoseK15.corpusBox.boxL ℓ` suffice, and the state only has to be measurable and bounded.

This is exactly the bundle the honest modes of the box ↔ model bridge carry
(`Work.BoseBoxFock.exists_modes_honestModes_ae`; see
`Submission/Work/BoseBoxFock/FINDING_continuous_hypotheses_UNSATISFIABLE.md`: the strong
`Continuous`/`HasCompactSupport` hypotheses are *unsatisfiable* at the honest modes).

The argument is the strong one, verbatim, with the single change that the integrand of the fibre
integral is shown integrable by *boundedness + box support + finite measure of the box* instead of
by continuity + compact support:

* the product `∏_{i ∈ T} PV e (x i) (z i)` expands over multi-indices `L : ↥T → Fin m`
  (`Work.BoseBoxFock.prod_PV_eq_sum`), splitting into the `S`-factors (which give the monomial)
  and the `T \ S`-factors (which are absorbed, together with the state, into the coefficient);
* the coefficient `pairConst` is the fibre integral of `pairG`, and `pairG` is integrable in the
  weak class (`integrable_pairG_weak`): its only non-constant `z`-dependence is the product of the
  conjugated modes, which is bounded and supported in the fibre box `piBox ℓ T` of finite measure;
* `MeasureTheory.integral_finsetSum` then pulls the finite sum out of the fibre integral.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.MB

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The fibre box: finite measure, measurability -/

/-- The product of the one-particle corpus boxes over the slots of `T`: the support set of the
fibre integrand in the slot variables of `T`. -/
def piBox {n : ℕ} (ℓ : ℝ) (T : Finset (Fin n)) : Set ({i // i ∈ T} → Ω) :=
  Set.univ.pi (fun _ : {i // i ∈ T} => Work.BoseK15.corpusBox.boxL ℓ)

/-- The fibre box has finite volume. -/
theorem volume_piBox_ne_top {n : ℕ} (ℓ : ℝ) (T : Finset (Fin n)) :
    (volume : Measure ({i // i ∈ T} → Ω)) (piBox ℓ T) ≠ ⊤ := by
  have h : (volume : Measure ({i // i ∈ T} → Ω)) (piBox ℓ T)
      = ∏ _i : {i // i ∈ T}, (volume : Measure Ω) (Work.BoseK15.corpusBox.boxL ℓ) := by
    rw [piBox]
    change MeasureTheory.Measure.pi (fun _ : {i // i ∈ T} => (volume : Measure Ω))
      (Set.univ.pi (fun _ : {i // i ∈ T} => Work.BoseK15.corpusBox.boxL ℓ)) = _
    rw [MeasureTheory.Measure.pi_pi]
  rw [h]
  exact ENNReal.prod_ne_top fun _ _ =>
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne

/-- The fibre box is measurable. -/
theorem measurableSet_piBox {n : ℕ} (ℓ : ℝ) (T : Finset (Fin n)) :
    MeasurableSet (piBox ℓ T) := by
  rw [piBox]
  exact MeasurableSet.univ_pi fun _ =>
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ

/-- A finite family of everywhere bounded modes has a *uniform* bound. -/
theorem exists_uniform_bound_modes {m : ℕ} {e : Fin m → Ω → ℂ}
    (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ l x, ‖e l x‖ ≤ K := by
  choose C hC using hbdE
  refine ⟨∑ l : Fin m, max (C l) 0, Finset.sum_nonneg fun l _ => le_max_right _ _, fun l x => ?_⟩
  exact (hC l x).trans ((le_max_left (C l) 0).trans
    (Finset.single_le_sum (f := fun j : Fin m => max (C j) 0)
      (fun j _ => le_max_right _ _) (Finset.mem_univ l)))

/-- Measurability of the configuration in which the slots of `T` are the fibre variable `z` and
the remaining ones are the complement configuration `y`: the state factor of `pairG`. -/
theorem measurable_pairG_phi {n : ℕ} {S T : Finset (Fin n)} (hST : S ⊆ T)
    (y : {i // i ∉ S} → Ω) (Φ : (Fin n → Ω) → ℂ) (hΦm : Measurable Φ) :
    Measurable (fun z : {i // i ∈ T} → Ω =>
      Φ (fun j : Fin n => if h : j ∈ T then z ⟨j, h⟩ else y ⟨j, fun hj => h (hST hj)⟩)) := by
  refine hΦm.comp ?_
  rw [measurable_pi_iff]
  intro j
  by_cases h : j ∈ T
  · have hfun : (fun z : {i // i ∈ T} → Ω =>
        (fun j : Fin n => if h' : j ∈ T then z ⟨j, h'⟩ else y ⟨j, fun hj => h' (hST hj)⟩) j)
        = fun z => z ⟨j, h⟩ := by
      funext z
      simp only [dif_pos h]
    rw [hfun]
    exact measurable_pi_apply _
  · have hfun : (fun z : {i // i ∈ T} → Ω =>
        (fun j : Fin n => if h' : j ∈ T then z ⟨j, h'⟩ else y ⟨j, fun hj => h' (hST hj)⟩) j)
        = fun _ => y ⟨j, fun hj => h (hST hj)⟩ := by
      funext z
      simp only [dif_neg h]
    rw [hfun]
    exact measurable_const

/-! ## 2. Integrability of the pair integrand in the weak class -/

/-- The integrand `pairG` of the fibre integral is integrable in the weak class: the only
non-constant `z`-dependence is the product of the conjugated modes, which is bounded (uniform mode
bound) and supported in the fibre box `piBox ℓ T` of finite measure; the state factor is bounded
and measurable. -/
theorem integrable_pairG_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Φ : (Fin n → Ω) → ℂ) (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    {S T : Finset (Fin n)} (hST : S ⊆ T) (y : {i // i ∉ S} → Ω) (L : {i // i ∈ T} → Fin m) :
    Integrable (Work.BoseBoxFock.pairG e S T hST Φ y L) := by
  obtain ⟨K, _hK0, hK⟩ := exists_uniform_bound_modes hbdE
  obtain ⟨CΦ, hCΦ⟩ := hΦb
  have hPm : Measurable (fun z : {i // i ∈ T} → Ω =>
      Φ (fun j : Fin n => if h : j ∈ T then z ⟨j, h⟩ else y ⟨j, fun hj => h (hST hj)⟩)) :=
    measurable_pairG_phi hST y Φ hΦm
  have hPb : ∀ z : {i // i ∈ T} → Ω,
      ‖Φ (fun j : Fin n => if h : j ∈ T then z ⟨j, h⟩ else y ⟨j, fun hj => h (hST hj)⟩)‖
        ≤ max CΦ 0 :=
    fun z => (hCΦ _).trans (le_max_left _ _)
  have hGm : Measurable (fun z : {i // i ∈ T} → Ω =>
      ∏ i : {i // i ∈ T}, star (e (L i) (z i))) :=
    Finset.measurable_prod _ fun i _ =>
      Complex.continuous_conj.measurable.comp
        ((hmeas (L i)).comp (measurable_pi_apply i))
  have hGb : ∀ z : {i // i ∈ T} → Ω,
      ‖∏ i : {i // i ∈ T}, star (e (L i) (z i))‖ ≤ ∏ _i : {i // i ∈ T}, K := by
    intro z
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
    rw [norm_star]
    exact hK (L i) (z i)
  have hGs : ∀ z ∉ piBox ℓ T, (∏ i : {i // i ∈ T}, star (e (L i) (z i))) = 0 := by
    intro z hz
    rw [piBox, Set.mem_univ_pi] at hz
    push Not at hz
    obtain ⟨i, hi⟩ := hz
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [Function.notMem_support.mp (fun h => hi (hsupp (L i) h)), star_zero]
  have hGint : Integrable
      (fun z : {i // i ∈ T} → Ω => ∏ i : {i // i ∈ T}, star (e (L i) (z i))) :=
    integrable_of_bdd_of_support (measurableSet_piBox ℓ T) (volume_piBox_ne_top ℓ T)
      hGm.aestronglyMeasurable hGb hGs
  have hprod : Integrable (fun z : {i // i ∈ T} → Ω =>
      (∏ i : {i // i ∈ T}, star (e (L i) (z i))) *
        Φ (fun j : Fin n => if h : j ∈ T then z ⟨j, h⟩ else y ⟨j, fun hj => h (hST hj)⟩)) :=
    hGint.mul_bdd hPm.aestronglyMeasurable (Filter.Eventually.of_forall hPb)
  have hfun : Work.BoseBoxFock.pairG e S T hST Φ y L
      = fun z : {i // i ∈ T} → Ω =>
          (∏ i : {i // i ∈ T \ S},
              e (L ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩) (y ⟨i.1, (Finset.mem_sdiff.mp i.2).2⟩)) *
            ((∏ i : {i // i ∈ T}, star (e (L i) (z i))) *
              Φ (fun j : Fin n => if h : j ∈ T then z ⟨j, h⟩ else y ⟨j, fun hj => h (hST hj)⟩)) := by
    funext z
    simp only [Work.BoseBoxFock.pairG]
    ring
  rw [hfun]
  exact hprod.const_mul _

/-! ## 3. The pointwise expansion of a `slotProj` slice -/

/-- **The key computation** (weak class).  For `S ⊆ T`, the value of `slotProj e T Φ` at a
configuration `pairCoord S u y` which agrees with `u` on `S` and with `y` outside `S` depends on
`u` only through the monomials `∏_{i ∈ S} e (L i) (u i)`, with coefficients given by the fibre
integral `pairConst`. -/
theorem slotProj_pairCoord_eq_sum_weak {m n : ℕ} {ℓ : ℝ} (e : Fin m → Ω → ℂ)
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Φ : (Fin n → Ω) → ℂ) (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    {S T : Finset (Fin n)} (hST : S ⊆ T) (y : {i // i ∉ S} → Ω) (u : {i // i ∈ S} → Ω) :
    Work.BoseBoxFock.slotProj e T Φ (Work.BoseBoxFock.pairCoord S u y) =
      ∑ L : {i // i ∈ T} → Fin m,
        (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i)) *
          Work.BoseBoxFock.pairConst e S T hST Φ y L := by
  have hI : (fun z : {i // i ∈ T} → Ω =>
      (∏ i : {i // i ∈ T},
        Work.BoseBoxFock.PV e (Work.BoseBoxFock.pairCoord S u y i.1) (z i)) *
        Φ (fun j => if h : j ∈ T then z ⟨j, h⟩ else Work.BoseBoxFock.pairCoord S u y j))
      = fun z => ∑ L : {i // i ∈ T} → Fin m,
          (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i)) *
            Work.BoseBoxFock.pairG e S T hST Φ y L z := by
    funext z
    rw [Work.BoseBoxFock.prod_PV_eq_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun L _ => ?_)
    rw [Finset.prod_mul_distrib]
    rw [Work.BoseBoxFock.prod_subtype_sdiff (e := e) hST L (Work.BoseBoxFock.pairCoord S u y)]
    have hSp : (∏ i : {i // i ∈ S},
          e (L ⟨i.1, hST i.2⟩) (Work.BoseBoxFock.pairCoord S u y i.1))
        = ∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Work.BoseBoxFock.pairCoord_mem S u y i.1 i.2]
    have hTSp : (∏ i : {i // i ∈ T \ S},
          e (L ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩) (Work.BoseBoxFock.pairCoord S u y i.1))
        = ∏ i : {i // i ∈ T \ S},
          e (L ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩)
            (y ⟨i.1, (Finset.mem_sdiff.mp i.2).2⟩) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Work.BoseBoxFock.pairCoord_notMem S u y i.1 (Finset.mem_sdiff.mp i.2).2]
    have hPhi : Φ (fun j => if h : j ∈ T then z ⟨j, h⟩ else Work.BoseBoxFock.pairCoord S u y j)
        = Φ (fun j => if h : j ∈ T then z ⟨j, h⟩ else y ⟨j, fun hj => h (hST hj)⟩) := by
      congr 1
      funext j
      by_cases h : j ∈ T
      · simp [h]
      · simp only [dif_neg h]
        exact Work.BoseBoxFock.pairCoord_notMem S u y j (fun hj => h (hST hj))
    rw [hSp, hTSp, hPhi]
    simp only [Work.BoseBoxFock.pairG]
    ring
  calc Work.BoseBoxFock.slotProj e T Φ (Work.BoseBoxFock.pairCoord S u y)
      = ∫ z : {i // i ∈ T} → Ω,
          (∏ i : {i // i ∈ T},
            Work.BoseBoxFock.PV e (Work.BoseBoxFock.pairCoord S u y i.1) (z i)) *
            Φ (fun j => if h : j ∈ T then z ⟨j, h⟩ else Work.BoseBoxFock.pairCoord S u y j) := by
          rw [Work.BoseBoxFock.slotProj]
    _ = ∫ z : {i // i ∈ T} → Ω, ∑ L : {i // i ∈ T} → Fin m,
          (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i)) *
            Work.BoseBoxFock.pairG e S T hST Φ y L z := by
          rw [hI]
    _ = ∑ L : {i // i ∈ T} → Fin m, ∫ z : {i // i ∈ T} → Ω,
          (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i)) *
            Work.BoseBoxFock.pairG e S T hST Φ y L z := by
        rw [MeasureTheory.integral_finsetSum]
        intro L _
        exact (integrable_pairG_weak hmeas hbdE hsupp Φ hΦm hΦb hST y L).const_mul _
    _ = ∑ L : {i // i ∈ T} → Fin m,
        (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i)) *
          Work.BoseBoxFock.pairConst e S T hST Φ y L := by
        refine Finset.sum_congr rfl (fun L _ => ?_)
        rw [MeasureTheory.integral_const_mul]
        rfl

/-- The `T`-summand of the sector decomposition of the slice lies in the span of the mode
monomials (weak class). -/
theorem slotProj_pairCoord_mem_span_weak {m n : ℕ} {ℓ : ℝ} (e : Fin m → Ω → ℂ)
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Φ : (Fin n → Ω) → ℂ) (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    {S T : Finset (Fin n)} (hST : S ⊆ T) (y : {i // i ∉ S} → Ω) :
    (fun u : {i // i ∈ S} → Ω => Work.BoseBoxFock.slotProj e T Φ
        (Work.BoseBoxFock.pairCoord S u y)) ∈
      Submodule.span ℂ (Set.range (fun M : {i // i ∈ S} → Fin m =>
        fun u : {i // i ∈ S} → Ω => ∏ i, e (M i) (u i))) := by
  have hpt : (fun u : {i // i ∈ S} → Ω => Work.BoseBoxFock.slotProj e T Φ
        (Work.BoseBoxFock.pairCoord S u y))
      = ∑ L : {i // i ∈ T} → Fin m, (Work.BoseBoxFock.pairConst e S T hST Φ y L) •
          (fun u : {i // i ∈ S} → Ω => ∏ i, e (L ⟨i.1, hST i.2⟩) (u i)) := by
    funext u
    rw [slotProj_pairCoord_eq_sum_weak e hmeas hbdE hsupp Φ hΦm hΦb hST y u]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun L _ => by simp [smul_eq_mul, mul_comm])
  rw [hpt]
  refine Submodule.sum_mem _ (fun L _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨fun i => L ⟨i.1, hST i.2⟩, rfl⟩

/-! ## 4. The sector slice lies in the mode-monomial span -/

theorem sliceF_mem_monSpan_weak {m n : ℕ} {ℓ : ℝ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.sliceF e S Φ y ∈ Submodule.span ℂ
      (Set.range (fun l : Fin S.card → Fin m =>
        fun x : Fin S.card → EuclideanSpace ℝ (Fin 3) => ∏ i, e (l i) (x i))) := by
  classical
  have hSlice : Work.BoseBoxFock.sectorSlice e S Φ y ∈
      Submodule.span ℂ (Set.range (fun M : {i // i ∈ S} → Fin m =>
        fun u : {i // i ∈ S} → Ω => ∏ i, e (M i) (u i))) := by
    have hEq : Work.BoseBoxFock.sectorSlice e S Φ y =
        ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          ((-1 : ℂ) ^ (T.card - S.card)) • (fun u : {i // i ∈ S} → Ω =>
            Work.BoseBoxFock.slotProj e T Φ (Work.BoseBoxFock.pairCoord S u y)) := by
      funext u
      simp only [Work.BoseBoxFock.sectorSlice, Work.BoseBoxFock.slotExact, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
    rw [hEq]
    refine Submodule.sum_mem _ (fun T hT => ?_)
    rw [Finset.mem_filter] at hT
    exact Submodule.smul_mem _ _ (slotProj_pairCoord_mem_span_weak e hmeas hbdE hsupp Φ hΦm hΦb
      hT.2 y)
  have key : ∀ f ∈ (Submodule.span ℂ (Set.range (fun M : {i // i ∈ S} → Fin m =>
        fun u : {i // i ∈ S} → Ω => ∏ i, e (M i) (u i)))),
      (fun u' : Fin S.card → Ω => f (fun i => u' (S.equivFin i))) ∈
        Submodule.span ℂ (Set.range (fun l : Fin S.card → Fin m =>
          fun x : Fin S.card → Ω => ∏ i, e (l i) (x i))) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨M, rfl⟩ := hf
        refine Submodule.subset_span ⟨fun j => M (S.equivFin.symm j), ?_⟩
        funext u'
        exact (Fintype.prod_equiv S.equivFin _ _
          (fun i => by simp)).symm
    | zero => exact Submodule.zero_mem _
    | add f g _ _ ihf ihg =>
        have hfun : (fun u' : Fin S.card → Ω => (f + g) (fun i => u' (S.equivFin i)))
            = (fun u' : Fin S.card → Ω => f (fun i => u' (S.equivFin i))) +
              (fun u' : Fin S.card → Ω => g (fun i => u' (S.equivFin i))) := by
          funext u'
          simp
        rw [hfun]
        exact Submodule.add_mem _ ihf ihg
    | smul c f _ ihf =>
        have hfun : (fun u' : Fin S.card → Ω => (c • f) (fun i => u' (S.equivFin i)))
            = c • (fun u' : Fin S.card → Ω => f (fun i => u' (S.equivFin i))) := by
          funext u'
          simp
        rw [hfun]
        exact Submodule.smul_mem _ _ ihf
  exact key (Work.BoseBoxFock.sectorSlice e S Φ y) hSlice

end Work.MB
