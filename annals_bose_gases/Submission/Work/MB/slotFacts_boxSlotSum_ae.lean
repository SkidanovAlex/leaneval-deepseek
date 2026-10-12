import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotFactsInst
import Submission.Work.MB.boxSlotOf_slotProj1_bdd
import Submission.Work.MB.boxSlotSum_bdd
import Submission.Work.MB.slotExact_orth_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.slotFacts_boxSlotSum_ae` — the `SlotFacts` instance of the one-body slot sum, at the
weak (measurable, everywhere bounded, box supported) mode hypotheses

This is the measurable/bounded ("weak") twin of `Work.BoseBoxFock.SlotFacts.boxSlotSumFacts`.
That theorem assumes the modes `e l` are `Continuous` with `HasCompactSupport` and the state `Φc`
is continuous with compact support; those hypotheses are *unsatisfiable* at the honest modes of
the box ↔ model bridge (`FINDING_continuous_hypotheses_UNSATISFIABLE.md`: the condensate mode is
a.e. the box indicator `thetaFun ℓ`, which has no continuous representative).  Here the mode
bundle is the weak one

* `hmeas : ∀ l, Measurable (e l)`,
* `hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C` (everywhere bounded),
* `hsupp : ∀ l, Function.support (e l) ⊆ boxL ℓ` (supported in the corpus box),

together with `horth`/`hint` (orthonormality and the integrability of the mode products), and the
state hypotheses are `Measurable Φc`, `∃ C, ∀ x, ‖Φc x‖ ≤ C` and `tsupport Φc ⊆ abox n ℓ`.

The three fields of `Work.BoseBoxFock.SlotFacts` are then

* `good` — `Work.MB.boxSlotSum_measurable_bounded_ae` (measurability and everywhere boundedness
  of `boxSlotSum` in the weak class);
* `slice` — the pointwise decoupling `boxSlotSum_pairCoord_w` (the weak twin of
  `Work.BoseBoxFock.boxSlotSum_pairCoord`): on the `S`-sector, read at the assembled
  configuration `pairCoord S u y`, the slot sum is the `↥S`-slot sum of the slice;
* `split` — the weak twin of `Work.BoseBoxFock.slotSum_sector_split`: the quadratic form of
  `boxSlotSum e T` splits over the occupation sectors `slotExact e S`.

The sector splitting is proved here by a route that is *cheaper* than the strong one: instead of
the classification of the states fixed by all the single-slot projections (which needs the
commutation of `boxSlotSum` with `slotProj1`), the cross terms are killed directly from the
collapse of the slot sum onto the occupied slots together with the weak self-adjointness of the
one-slot projections.  Every private helper below is the weak twin of a lemma of the strong chain
(`slotProj1_slotExact_eq_zero`, `boxSlotSum_sector_eq_sum_mem`, `slotSum_sector_split`, …),
mirrored here so that this module rests only on the *stable* public weak algebra of the area
(`Work.MB.slotProj_mb_weak`, `Work.MB.slotProj1_linear_bdd`, `Work.MB.slotProj1_idem_weak`,
`Work.MB.boxSlotOf_slotProj1_bdd`, `Work.MB.boxSlotSum_bdd`, `Work.BoseBoxFock.slotProj_peel_bdd`,
…).
-/

namespace Work.MB

noncomputable section

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## 0. Elementary helpers -/

/-- Measurable and everywhere bounded functions are `L^∞`. -/
private theorem memLp_top_modes_w {m : ℕ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C) :
    ∀ l, MemLp (e l) ⊤ (volume : Measure E3) := by
  intro l
  obtain ⟨C, hC⟩ := hbdd l
  exact memLp_top_of_bound (hmeas l).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => hC x))

/-- An everywhere bound can be taken nonnegative. -/
private theorem exists_bound_max_w {α : Type*} {f : α → ℂ} (h : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- A finite sum of measurable, everywhere bounded functions is measurable and everywhere
bounded. -/
private theorem sum_measurable_bounded_w {ι : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι]
    (f : ι → (Fin d → E3) → ℂ) (hm : ∀ k, Measurable (f k))
    (hb : ∀ k, ∃ C, ∀ x, ‖f k x‖ ≤ C) :
    Measurable (fun x : Fin d → E3 => ∑ k, f k x) ∧
      ∃ C, ∀ x : Fin d → E3, ‖∑ k, f k x‖ ≤ C := by
  classical
  choose C hC using hb
  refine ⟨Finset.measurable_sum _ (fun k _ => hm k),
    ⟨∑ k, max (C k) 0, fun x => ?_⟩⟩
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum (fun k _ => (hC k x).trans (le_max_left _ _)))

/-- A finite sum of everywhere bounded functions is everywhere bounded. -/
private theorem exists_bound_finset_sum_w {ι α : Type*} (s : Finset ι) (c : ι → ℂ)
    {f : ι → α → ℂ} (hb : ∀ i ∈ s, ∃ C, ∀ x, ‖f i x‖ ≤ C) :
    ∃ C, ∀ x, ‖∑ i ∈ s, c i • f i x‖ ≤ C := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, fun x => by simp⟩
  | insert a s ha ih =>
      obtain ⟨C1, hC1⟩ := hb a (Finset.mem_insert_self a s)
      obtain ⟨C2, hC2⟩ := ih fun i hi => hb i (Finset.mem_insert_of_mem hi)
      refine ⟨‖c a‖ * max C1 0 + max C2 0, fun x => ?_⟩
      rw [Finset.sum_insert ha]
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_left ((hC1 x).trans (le_max_left _ _)) (norm_nonneg _)
      · exact (hC2 x).trans (le_max_left _ _)

/-- The support of a pointwise product is contained in the union of the supports. -/
private theorem support_mul_subset_w {α : Type*} {f g : α → ℂ} :
    Function.support (fun x => f x * g x) ⊆ Function.support f ∪ Function.support g := by
  intro x hx
  by_contra hx'
  have h1 : f x = 0 := Function.notMem_support.mp (fun h => hx' (Or.inl h))
  have h2 : g x = 0 := Function.notMem_support.mp (fun h => hx' (Or.inr h))
  exact hx (by show f x * g x = 0; rw [h1, zero_mul])

/-- A finite sum of everywhere bounded functions is everywhere bounded (pointwise form). -/
private theorem bdd_sum_bounded_w {ι α : Type*} [Fintype ι] (f : ι → α → ℂ)
    (hb : ∀ k, ∃ C, ∀ x, ‖f k x‖ ≤ C) :
    ∃ C, ∀ x, ‖∑ k, f k x‖ ≤ C := by
  classical
  choose C hC using hb
  exact ⟨∑ k, max (C k) 0, fun x => (norm_sum_le _ _).trans
    (Finset.sum_le_sum (fun k _ => (hC k x).trans (le_max_left _ _)))⟩

/-- A real multiple of an everywhere bounded function is everywhere bounded. -/
private theorem bdd_const_smul_w {α : Type*} {f : α → ℂ} (c : ℝ)
    (h : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ C, ∀ x, ‖c • f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨‖c‖ * C, fun x => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩

/-- A finite linear combination of functions supported in `B` is supported in `B`. -/
private theorem support_finset_sum_subset_w {ι α : Type*} (s : Finset ι) (c : ι → ℂ)
    {f : ι → α → ℂ} {B : Set α} (hf : ∀ i ∈ s, Function.support (f i) ⊆ B) :
    Function.support (fun x => ∑ i ∈ s, c i • f i x) ⊆ B := by
  intro x hx
  by_contra hxB
  refine hx ?_
  exact Finset.sum_eq_zero (fun i hi => by
    rw [Function.notMem_support.mp (fun h => hxB (hf i hi h)), smul_zero])

/-! ## 1. The box support of the projections -/

/-- The slot projection of a state vanishing outside `boxPow n ℓ` vanishes outside
`boxPow n ℓ`. -/
private theorem slotProj_support_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : Finset (Fin n)) {Ψ : (Fin n → E3) → ℂ}
    (hΨs : Function.support Ψ ⊆ boxPow n ℓ) :
    Function.support (Work.BoseBoxFock.slotProj e T Ψ) ⊆ boxPow n ℓ := by
  intro x hx
  by_contra hxnot
  have hex : ∃ i : Fin n, x i ∉ Work.BoseK15.corpusBox.boxL ℓ := by
    by_contra h
    exact hxnot (by
      rw [mem_boxPow_iff]
      intro i
      by_contra hi
      exact h ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hex
  refine hx ?_
  by_cases hiT : i ∈ T
  · have hz : (fun z : ↥T → E3 =>
        (∏ j : ↥T, Work.BoseBoxFock.PV e (x j.1) (z j)) *
          Ψ (fun j => if h : j ∈ T then z ⟨j, h⟩ else x j)) = fun _ => (0 : ℂ) := by
      funext z
      rw [Finset.prod_eq_zero (Finset.mem_univ (⟨i, hiT⟩ : ↥T))
        (Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL_fst hsupp hi), zero_mul]
    show Work.BoseBoxFock.slotProj e T Ψ x = 0
    rw [Work.BoseBoxFock.slotProj, hz, integral_zero]
  · have hz : (fun z : ↥T → E3 =>
        (∏ j : ↥T, Work.BoseBoxFock.PV e (x j.1) (z j)) *
          Ψ (fun j => if h : j ∈ T then z ⟨j, h⟩ else x j)) = fun _ => (0 : ℂ) := by
      funext z
      have hcoord : (fun j => if h : j ∈ T then z ⟨j, h⟩ else x j) i = x i := by
        simp only [dif_neg hiT]
      have hnotmem : (fun j => if h : j ∈ T then z ⟨j, h⟩ else x j) ∉ boxPow n ℓ := by
        intro hmem
        exact hi (by rw [← hcoord]; exact (mem_boxPow_iff.mp hmem) i)
      rw [Function.notMem_support.mp (fun h => hnotmem (hΨs h)), mul_zero]
    show Work.BoseBoxFock.slotProj e T Ψ x = 0
    rw [Work.BoseBoxFock.slotProj, hz, integral_zero]

/-- The sector of a state vanishing outside `boxPow n ℓ` vanishes outside `boxPow n ℓ`. -/
private theorem slotExact_support_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Ψ : (Fin n → E3) → ℂ}
    (hΨs : Function.support Ψ ⊆ boxPow n ℓ) :
    Function.support (Work.BoseBoxFock.slotExact e S Ψ) ⊆ boxPow n ℓ := by
  intro x hx
  by_contra hxnot
  refine hx ?_
  simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun T _ => ?_
  rw [Function.notMem_support.mp
    (fun h => hxnot (slotProj_support_w hsupp T hΨs h)), mul_zero]

/-- The one-slot projection of the zero state is zero. -/
private theorem slotProj1_zero_w {m n : ℕ} (e : Fin m → E3 → ℂ) (i : Fin n) :
    Work.BoseBoxFock.slotProj1 e i (0 : (Fin n → E3) → ℂ) = 0 := by
  funext x
  simp [Work.BoseBoxFock.slotProj1]

/-- The slot operator of the zero state is zero. -/
private theorem boxSlotOf_zero_w {m d : ℕ} (e : Fin m → E3 → ℂ) (w v : Fin m → ℝ)
    (j : Fin d) :
    Work.BoseDict.boxSlotOf e w v j (0 : (Fin d → E3) → ℂ) = 0 := by
  funext x
  simp [Work.BoseDict.boxSlotOf]

/-- The slot operator of a state vanishing outside `boxPow d ℓ` vanishes outside `boxPow d ℓ`. -/
private theorem boxSlotOf_support_w {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) {Θ : (Fin d → E3) → ℂ}
    (hΘs : Function.support Θ ⊆ boxPow d ℓ) :
    Function.support (Work.BoseDict.boxSlotOf e w v j Θ) ⊆ boxPow d ℓ := by
  intro x hx
  by_contra hxnot
  have hex : ∃ i : Fin d, x i ∉ Work.BoseK15.corpusBox.boxL ℓ := by
    by_contra h
    exact hxnot (by rw [mem_boxPow_iff]; intro i; by_contra hi; exact h ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hex
  refine hx ?_
  show Work.BoseDict.etaOf e w (x j) *
      (∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)) = 0
  by_cases hji : j = i
  · have hw : Work.BoseDict.etaOf e w (x j) = 0 := by
      by_contra hne
      have hmem : x i ∈ Work.BoseK15.corpusBox.boxL ℓ := by
        rw [← hji]
        exact etaOf_weak_support hsupp w (Function.mem_support.mpr hne)
      exact hi hmem
    rw [hw, zero_mul]
  · have hzero : (fun z : E3 => (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
        Θ (Function.update x j z)) = fun _ => (0 : ℂ) := by
      funext z
      have hcoord : Function.update x j z i = x i :=
        Function.update_of_ne (fun h : i = j => hji h.symm) z x
      have hnotmem : Function.update x j z ∉ boxPow d ℓ := by
        intro hmem
        exact hi (by rw [← hcoord]; exact (mem_boxPow_iff.mp hmem) i)
      rw [Function.notMem_support.mp (fun h => hnotmem (hΘs h)), mul_zero]
    rw [hzero, integral_zero, mul_zero]

/-- The slot sum of the zero state is zero. -/
private theorem boxSlotSum_zero_w {m d : ℕ} (e : Fin m → E3 → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Work.BoseDict.boxSlotSum e T (0 : (Fin d → E3) → ℂ) = 0 := by
  funext x
  simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_eq_zero (fun j _ =>
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun l' _ => ?_)))
  simp [Work.BoseDict.boxSlotOf]

/-! ## 2. Peel and absorption for the one-slot projection -/

/-- **Peel**, weak form: for `i ∉ U`, projecting the slot `i` after the slots of `U` is projecting
the slots of `insert i U`. -/
private theorem slotProj1_slotProj_peel_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {U : Finset (Fin n)} {i : Fin n} (hi : i ∉ U)
    {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotProj e U Ψ)
      = Work.BoseBoxFock.slotProj e (insert i U) Ψ := by
  obtain ⟨C, hC⟩ := hΨb
  exact (Work.BoseBoxFock.slotProj_peel_bdd (memLp_top_modes_w hmeas hbdd) hsupp hi hΨm hC).symm

/-- **Absorption**, weak form: for `i ∈ U`, projecting the slot `i` after the slots of `U`
changes nothing. -/
private theorem slotProj1_slotProj_self_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    {U : Finset (Fin n)} {i : Fin n} (hi : i ∈ U)
    {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotProj e U Ψ)
      = Work.BoseBoxFock.slotProj e U Ψ := by
  obtain ⟨C, hC⟩ := hΨb
  have hpeel := Work.BoseBoxFock.slotProj_peel_bdd (memLp_top_modes_w hmeas hbdd) hsupp
    (Finset.notMem_erase i U) hΨm hC
  have hins : insert i (U.erase i) = U := Finset.insert_erase hi
  obtain ⟨hm, hb⟩ := Work.MB.slotProj_mb_weak hmeas hbdd hsupp (U.erase i) hΨm ⟨C, hC⟩
  have hidem := Work.MB.slotProj1_idem_weak hmeas hbdd hsupp horth hm hb i
  rw [← hins, hpeel]
  exact hidem

/-! ## 3. The one-slot projection kills the sectors it does not belong to -/

/-- **The one-slot projection kills the sectors it does not belong to, and fixes the ones it
does** (weak twin of `Work.BoseBoxFock.slotProj1_slotExact_eq_zero`, with the `i ∈ S` case
included). -/
private theorem slotProj1_slotExact_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : E3 => star (e l z) * e l' z))
    (S : Finset (Fin n)) (i : Fin n) {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ)
    (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotExact e S Ψ)
      = if i ∈ S then Work.BoseBoxFock.slotExact e S Ψ else 0 := by
  classical
  have hmb : ∀ T : Finset (Fin n), Measurable (Work.BoseBoxFock.slotProj e T Ψ) ∧
      (∃ C, ∀ x, ‖Work.BoseBoxFock.slotProj e T Ψ x‖ ≤ C) := fun T =>
    Work.MB.slotProj_mb_weak hmeas hbdd hsupp T hΨm hΨb
  have hsumfun : Work.BoseBoxFock.slotExact e S Ψ =
      fun x => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
        (-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Ψ x := by
    funext x
    simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply]
  by_cases hiS : i ∈ S
  · rw [if_pos hiS, hsumfun]
    rw [(Work.MB.slotProj1_linear_bdd hmeas hbdd hsupp).1 i
      (Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T))
      (fun T => (-1 : ℂ) ^ (T.card - S.card))
      (fun T => Work.BoseBoxFock.slotProj e T Ψ) (fun T => (hmb T).1) (fun T => (hmb T).2)]
    funext x
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [congrFun (slotProj1_slotProj_self_w hmeas hbdd hsupp horth
      ((Finset.mem_filter.mp hT).2 hiS) hΨm hΨb) x]
  · rw [if_neg hiS, Work.BoseBoxFock.SecAux.slotExact_pair_form e S i hiS Ψ]
    rw [show (∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ i ∉ T),
          (-1 : ℂ) ^ (T.card - S.card) •
            (Work.BoseBoxFock.slotProj e T Ψ - Work.BoseBoxFock.slotProj e (insert i T) Ψ))
        = (fun x => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ i ∉ T),
          (-1 : ℂ) ^ (T.card - S.card) •
            (Work.BoseBoxFock.slotProj e T Ψ x
              - Work.BoseBoxFock.slotProj e (insert i T) Ψ x))
        from by funext x; simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply]]
    rw [(Work.MB.slotProj1_linear_bdd hmeas hbdd hsupp).1 i
      (Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ i ∉ T))
      (fun T => (-1 : ℂ) ^ (T.card - S.card))
      (fun T x => Work.BoseBoxFock.slotProj e T Ψ x
        - Work.BoseBoxFock.slotProj e (insert i T) Ψ x)
      (fun T => (hmb T).1.sub (hmb (insert i T)).1)
      (fun T => by
        obtain ⟨CF, hCF⟩ := (hmb T).2
        obtain ⟨CG, hCG⟩ := (hmb (insert i T)).2
        exact ⟨CF + CG, fun x => (norm_sub_le _ _).trans (add_le_add (hCF x) (hCG x))⟩)]
    funext x
    refine Finset.sum_eq_zero fun T hT => ?_
    have hiT : i ∉ T := (Finset.mem_filter.mp hT).2.2
    rw [congrFun ((Work.MB.slotProj1_linear_bdd hmeas hbdd hsupp).2 i
      (Work.BoseBoxFock.slotProj e T Ψ) (Work.BoseBoxFock.slotProj e (insert i T) Ψ)
      (hmb T).1 (hmb T).2 (hmb (insert i T)).1 (hmb (insert i T)).2) x]
    rw [congrFun (slotProj1_slotProj_peel_w hmeas hbdd hsupp hiT hΨm hΨb) x,
      congrFun (slotProj1_slotProj_self_w hmeas hbdd hsupp horth
        (Finset.mem_insert_self i T) hΨm hΨb) x, sub_self, smul_zero]

/-! ## 4. Regularity of the sector -/

/-- The sector of a measurable, everywhere bounded state is measurable and everywhere
bounded. -/
private theorem slotExact_mb_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ)
    (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Measurable (Work.BoseBoxFock.slotExact e S Ψ) ∧
      ∃ C, ∀ x, ‖Work.BoseBoxFock.slotExact e S Ψ x‖ ≤ C := by
  classical
  have hbase : ∀ (T : Finset (Fin n)), Measurable (Work.BoseBoxFock.slotProj e T Ψ) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Work.BoseBoxFock.slotProj e T Ψ x‖ ≤ C) := by
    intro T
    obtain ⟨hm, hb⟩ := Work.MB.slotProj_mb_weak hmeas hbdd hsupp T hΨm hΨb
    exact ⟨hm, exists_bound_max_w hb⟩
  have hfun : Work.BoseBoxFock.slotExact e S Ψ =
      fun x => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
        (-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Ψ x := by
    funext x
    simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply]
  constructor
  · rw [hfun]
    exact Finset.measurable_sum _
      (fun T _ => ((hbase T).1).const_smul ((-1 : ℂ) ^ (T.card - S.card)))
  · refine ⟨∑ T : Finset (Fin n), ‖(-1 : ℂ) ^ (T.card - S.card)‖ * (hbase T).2.choose,
      fun x => ?_⟩
    calc ‖Work.BoseBoxFock.slotExact e S Ψ x‖
        = ‖∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            (-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Ψ x‖ := by
          rw [show Work.BoseBoxFock.slotExact e S Ψ x
              = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
                (-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Ψ x from
            congrFun hfun x]
      _ ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            ‖(-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Ψ x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            ‖(-1 : ℂ) ^ (T.card - S.card)‖ * (hbase T).2.choose :=
          Finset.sum_le_sum (fun T _ => by
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left ((hbase T).2.choose_spec.2 x) (norm_nonneg _))
      _ ≤ ∑ T : Finset (Fin n), ‖(-1 : ℂ) ^ (T.card - S.card)‖ * (hbase T).2.choose :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun T _ _ => mul_nonneg (norm_nonneg _) (hbase T).2.choose_spec.1)

/-! ## 5. The slot operators kill the states with a vanishing slot projection -/

/-- If the `j`-th slot of `Θ` carries no `V`-component, the slot-`j` rank-one operator
`|e l⟩⟨e l'|` annihilates `Θ` (weak twin of
`Work.BoseBoxFock.boxSlotOf_eq_zero_of_slotProj1_eq_zero`). -/
private theorem boxSlotOf_eq_zero_w {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : E3 => star (e l z) * e l' z))
    (l l' : Fin m) (j : Fin d) {Θ : (Fin d → E3) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (h0 : Work.BoseBoxFock.slotProj1 e j Θ = 0) :
    Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ = 0 := by
  have h1 := (Work.MB.boxSlotOf_slotProj1_bdd hmeas hbdd hsupp horth hint hΘm hΘb).1 l l' j
  rw [h0] at h1
  rw [← h1]
  exact boxSlotOf_zero_w e _ _ j

/-! ## 6. The collapse of the slot sum onto the occupied slots -/

/-- **The slot sum collapses to `S` whenever the state has no `V`-component outside `S`** (weak
twin of `Work.BoseBoxFock.boxSlotSum_sector_eq_sum_mem`). -/
private theorem boxSlotSum_eq_sum_mem_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : E3 => star (e l z) * e l' z))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n)) (Θ : (Fin n → E3) → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (hΘ0 : ∀ j : Fin n, j ∉ S → Work.BoseBoxFock.slotProj1 e j Θ = 0) :
    Work.BoseDict.boxSlotSum e T Θ
      = ∑ j ∈ S, ∑ l : Fin m, ∑ l' : Fin m,
          T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ := by
  classical
  have hzero : ∀ j : Fin n, j ∉ S →
      (∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) = 0 := by
    intro j hj
    refine Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun l' _ => ?_))
    rw [boxSlotOf_eq_zero_w hmeas hbdd hsupp horth hint l l' j hΘm hΘb (hΘ0 j hj)]
    exact smul_zero _
  rw [Work.BoseDict.boxSlotSum]
  exact (Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hzero j hj)).symm

/-! ## 7. The pointwise decoupling -/

/-- **The slot sum of a sector, read at the assembled configuration, is the `↥S`-slot sum of its
slice** (weak twin of `Work.BoseBoxFock.boxSlotSum_pairCoord`). -/
private theorem boxSlotSum_pairCoord_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : E3 => star (e l z) * e l' z))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n))
    (Φ : (Fin n → E3) → ℂ) (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (u : {i // i ∈ S} → E3) (y : {i // i ∉ S} → E3) :
    Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φ)
        (Work.BoseBoxFock.pairCoord S u y)
      = Work.BoseBoxFock.slotSumSub e T S
          (Work.BoseBoxFock.sectorSlice e S Φ y) u := by
  classical
  obtain ⟨hΘm, hΘb⟩ := slotExact_mb_w hmeas hbdd hsupp S hΦm hΦb
  rw [boxSlotSum_eq_sum_mem_w hmeas hbdd hsupp horth hint T S
      (Work.BoseBoxFock.slotExact e S Φ) hΘm hΘb
      (fun j hj => by
        rw [slotProj1_slotExact_w hmeas hbdd hsupp horth hint S j hΦm hΦb, if_neg hj])]
  simp only [Work.BoseBoxFock.slotSumSub, Finset.sum_apply, Pi.smul_apply]
  rw [← Finset.sum_attach S (fun j => ∑ l : Fin m, ∑ l' : Fin m,
      T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
          (Work.BoseBoxFock.slotExact e S Φ) (Work.BoseBoxFock.pairCoord S u y))]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ =>
    Finset.sum_congr rfl (fun l' _ => by rw [Work.BoseBoxFock.boxSlotOf_pairCoord])))

/-! ## 8. Self-adjointness of the one-slot projection -/

/-- **Self-adjointness of `slotProj1 e i`** at the weak mode hypotheses (the `T = {i}` instance
of `Work.MB.slotProj_adjoint_bdd`). -/
private theorem slotProj1_adjoint_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {Φ Ψ : (Fin n → E3) → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (hΦs : Function.support Φ ⊆ boxPow n ℓ)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) (hΨs : Function.support Ψ ⊆ boxPow n ℓ) :
    ∫ x : Fin n → E3, star (Work.BoseBoxFock.slotProj1 e i Φ x) * Ψ x
      = ∫ x : Fin n → E3, star (Φ x) * Work.BoseBoxFock.slotProj1 e i Ψ x := by
  rw [← Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux e i Φ,
    ← Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux e i Ψ]
  exact Work.MB.slotProj_adjoint_bdd hmeas hbdd hsupp {i} Φ Ψ hΦm hΦb hΦs hΨm hΨb hΨs

/-! ## 9. Extracting a triple slot sum out of an integral -/

/-- **`∫ star Θ · Σ_j Σ_l Σ_l' c • boxSlotOf = Σ_j Σ_l Σ_l' c • ∫ star Θ · boxSlotOf`**: the
finite triple sum of the collapse of the slot sum is pulled out of the integral.  Only
measurability and everywhere boundedness of the states are used; the integrability of every
summand follows from the box support of `Θ` and the finiteness of the box. -/
private theorem integral_star_mul_sumTriple_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (Θ : (Fin n → E3) → ℂ) (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ boxPow n ℓ)
    (S : Finset (Fin n)) (Ψ : (Fin n → E3) → ℂ) (hΨm : Measurable Ψ)
    (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    (∫ x : Fin n → E3, star (Θ x) * (∑ j ∈ S, ∑ l : Fin m, ∑ l' : Fin m,
        T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x))
      = ∑ j ∈ S, ∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
          ∫ x : Fin n → E3, star (Θ x) * Work.BoseDict.boxSlotOf e
            (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x := by
  classical
  have hB : ∀ (j : Fin n) (l l' : Fin m),
      Measurable (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ) ∧
      (∃ C, ∀ x : Fin n → E3,
        ‖Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x‖ ≤ C) :=
    fun j l l' => Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdE hsupp
      (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ hΨm hΨb
  have hpack_m : ∀ j : Fin n, Measurable (fun x : Fin n → E3 =>
      ∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x) := by
    intro j
    refine Finset.measurable_sum _ (fun l _ => Finset.measurable_sum _ (fun l' _ => ?_))
    exact ((hB j l l').1).const_smul (T (Work.BoseB4.evec m l') l)
  have hpack_b : ∀ j : Fin n, ∃ C, ∀ x : Fin n → E3,
      ‖∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x‖ ≤ C := by
    intro j
    refine bdd_sum_bounded_w (fun l x => ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x) (fun l => ?_)
    exact bdd_sum_bounded_w (fun l' x => T (Work.BoseB4.evec m l') l •
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x)
      (fun l' => bdd_const_smul_w _ (hB j l l').2)
  have hinner_m : ∀ (j : Fin n) (l : Fin m), Measurable (fun x : Fin n → E3 =>
      ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x) := by
    intro j l
    refine Finset.measurable_sum _ (fun l' _ => ?_)
    exact ((hB j l l').1).const_smul (T (Work.BoseB4.evec m l') l)
  have hinner_b : ∀ (j : Fin n) (l : Fin m), ∃ C, ∀ x : Fin n → E3,
      ‖∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x‖ ≤ C := by
    intro j l
    exact bdd_sum_bounded_w (fun l' x => T (Work.BoseB4.evec m l') l •
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x)
      (fun l' => bdd_const_smul_w _ (hB j l l').2)
  rw [integral_star_mul_sum_weak (s := S)
    (G := fun j x => ∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x)
    (Θ := Θ) hΘm hΘb hΘs hpack_m hpack_b]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_star_mul_sum_weak (s := (Finset.univ : Finset (Fin m)))
    (G := fun l x => ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x)
    (Θ := Θ) hΘm hΘb hΘs (fun l => hinner_m j l) (fun l => hinner_b j l)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [integral_star_mul_sum_weak (s := (Finset.univ : Finset (Fin m)))
    (G := fun l' x => T (Work.BoseB4.evec m l') l •
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x)
    (Θ := Θ) hΘm hΘb hΘs
    (fun l' => ((hB j l l').1).const_smul (T (Work.BoseB4.evec m l') l))
    (fun l' => bdd_const_smul_w _ (hB j l l').2)]
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  rw [show (∫ x : Fin n → E3, star (Θ x) * (T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x))
      = ∫ x : Fin n → E3, T (Work.BoseB4.evec m l') l •
          (star (Θ x) * Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
            (Work.BoseB4.evec m l') j Ψ x) from
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by
      simp only [Complex.real_smul]
      ring))]
  rw [MeasureTheory.integral_smul]

/-! ## 10. The off-diagonal terms vanish -/

/-- **The cross term of the sector splitting vanishes**: the integral of one sector against the
slot sum of a *different* sector is zero.  The proof uses the collapse of the slot sum onto the
occupied slots and the weak self-adjointness of the one-slot projections: a slot `i` present in
exactly one of the two sectors moves the projection from one factor to the other and kills it. -/
private theorem boxSlotSum_cross_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : E3 => star (e l z) * e l' z))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Φ : (Fin n → E3) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (hΦs : Function.support Φ ⊆ boxPow n ℓ)
    (S S' : Finset (Fin n)) (hne : S ≠ S') :
    ∫ x : Fin n → E3, star (Work.BoseBoxFock.slotExact e S Φ x)
      * Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S' Φ) x = 0 := by
  classical
  have hSS := slotExact_mb_w hmeas hbdE hsupp S hΦm hΦb
  have hSS' := slotExact_mb_w hmeas hbdE hsupp S' hΦm hΦb
  have hSSs : Function.support (Work.BoseBoxFock.slotExact e S Φ) ⊆ boxPow n ℓ :=
    slotExact_support_w hsupp S hΦs
  have hSS's : Function.support (Work.BoseBoxFock.slotExact e S' Φ) ⊆ boxPow n ℓ :=
    slotExact_support_w hsupp S' hΦs
  have hslS : ∀ i : Fin n, Work.BoseBoxFock.slotProj1 e i
      (Work.BoseBoxFock.slotExact e S Φ)
      = if i ∈ S then Work.BoseBoxFock.slotExact e S Φ else 0 :=
    fun i => slotProj1_slotExact_w hmeas hbdE hsupp horth hint S i hΦm hΦb
  have hslS' : ∀ i : Fin n, Work.BoseBoxFock.slotProj1 e i
      (Work.BoseBoxFock.slotExact e S' Φ)
      = if i ∈ S' then Work.BoseBoxFock.slotExact e S' Φ else 0 :=
    fun i => slotProj1_slotExact_w hmeas hbdE hsupp horth hint S' i hΦm hΦb
  have hboxSS' := Work.MB.boxSlotOf_slotProj1_bdd hmeas hbdE hsupp horth hint hSS'.1 hSS'.2
  -- the per-slot-operator vanishing
  have hper : ∀ (l l' : Fin m) (j : Fin n), j ∈ S' →
      ∫ x : Fin n → E3, star (Work.BoseBoxFock.slotExact e S Φ x)
        * Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
            (Work.BoseBoxFock.slotExact e S' Φ) x = 0 := by
    intro l l' j hjS'
    obtain ⟨hΥm, hΥb⟩ := Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdE hsupp
      (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j (Work.BoseBoxFock.slotExact e S' Φ)
      hSS'.1 hSS'.2
    have hΥs : Function.support (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
        (Work.BoseB4.evec m l') j (Work.BoseBoxFock.slotExact e S' Φ)) ⊆ boxPow n ℓ :=
      boxSlotOf_support_w hsupp _ _ j hSS's
    -- the adjointness moves the projection from one factor to the other
    have hadj : ∀ (i : Fin n),
        Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotExact e S Φ) = 0 →
        Work.BoseBoxFock.slotProj1 e i (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
          (Work.BoseB4.evec m l') j (Work.BoseBoxFock.slotExact e S' Φ))
          = Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
              (Work.BoseBoxFock.slotExact e S' Φ) →
        ∫ x : Fin n → E3, star (Work.BoseBoxFock.slotExact e S Φ x)
          * Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
              (Work.BoseBoxFock.slotExact e S' Φ) x = 0 := by
      intro i h1 h2
      have h := slotProj1_adjoint_w hmeas hbdE hsupp i (hΦm := hSS.1) (hΦb := hSS.2)
        (hΦs := hSSs) (hΨm := hΥm) (hΨb := hΥb) (hΨs := hΥs)
      rw [h1, h2] at h
      simpa using h.symm
    have hadj' : ∀ (i : Fin n),
        Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotExact e S Φ)
          = Work.BoseBoxFock.slotExact e S Φ →
        Work.BoseBoxFock.slotProj1 e i (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
          (Work.BoseB4.evec m l') j (Work.BoseBoxFock.slotExact e S' Φ)) = 0 →
        ∫ x : Fin n → E3, star (Work.BoseBoxFock.slotExact e S Φ x)
          * Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
              (Work.BoseBoxFock.slotExact e S' Φ) x = 0 := by
      intro i h1 h2
      have h := slotProj1_adjoint_w hmeas hbdE hsupp i (hΦm := hSS.1) (hΦb := hSS.2)
        (hΦs := hSSs) (hΨm := hΥm) (hΨb := hΥb) (hΨs := hΥs)
      rw [h1, h2] at h
      simpa using h
    by_cases hA : ∃ i : Fin n, i ∈ S ∧ i ∉ S'
    · -- a slot present in `S` but not in `S'`: it fixes `A_S` and kills the slot operator
      obtain ⟨i, hiS, hiS'⟩ := hA
      have hji : i ≠ j := fun h => hiS' (h ▸ hjS')
      refine hadj' i (by rw [hslS i, if_pos hiS]) ?_
      rw [(hboxSS'.2.2.1 l l' i j hji).symm, hslS' i, if_neg hiS']
      exact boxSlotOf_zero_w e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
    · -- otherwise `S ⊆ S'`, and a slot `i` of `S'` outside `S` does the job
      push_neg at hA
      have hSsub : S ⊆ S' := fun i hi => hA i hi
      have hex : ∃ i : Fin n, i ∈ S' ∧ i ∉ S := by
        by_contra h
        push_neg at h
        exact hne (Finset.Subset.antisymm hSsub (fun i hi => h i hi))
      by_cases hjS : j ∈ S
      · obtain ⟨i, hiS', hiS⟩ := hex
        have hji : i ≠ j := fun h => hiS (h ▸ hjS)
        refine hadj i (by rw [hslS i, if_neg hiS]) ?_
        rw [(hboxSS'.2.2.1 l l' i j hji).symm, hslS' i, if_pos hiS']
      · -- here the slot `j` itself is outside `S`
        refine hadj j (by rw [hslS j, if_neg hjS]) ?_
        exact hboxSS'.2.1 l l' j
  -- collapse the slot sum and pull the triple sum out of the integral
  rw [boxSlotSum_eq_sum_mem_w hmeas hbdE hsupp horth hint T S'
    (Work.BoseBoxFock.slotExact e S' Φ) hSS'.1 hSS'.2 (fun j hj => by rw [hslS' j, if_neg hj])]
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [integral_star_mul_sumTriple_w hmeas hbdE hsupp T (Work.BoseBoxFock.slotExact e S Φ)
    hSS.1 hSS.2 hSSs S' (Work.BoseBoxFock.slotExact e S' Φ) hSS'.1 hSS'.2]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  refine Finset.sum_eq_zero (fun l _ => ?_)
  refine Finset.sum_eq_zero (fun l' _ => ?_)
  rw [hper l l' j hj, smul_zero]

/-! ## 11. The sector splitting of the quadratic form -/

/-- **The first-quantised slot sum splits over the occupation sectors** (weak twin of
`Work.BoseBoxFock.slotSum_sector_split`). -/
private theorem boxSlotSum_sector_split_w {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : E3 => star (e l z) * e l' z))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (Φc : (Fin n → E3) → ℂ) (hΦm : Measurable Φc) (hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C)
    (hΦs : Function.support Φc ⊆ boxPow n ℓ) :
    ∫ x : Fin n → E3, star (Φc x) * Work.BoseDict.boxSlotSum e T Φc x
      = ∑ S : Finset (Fin n), ∫ x : Fin n → E3,
          star (Work.BoseBoxFock.slotExact e S Φc x)
            * Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φc) x := by
  classical
  have hsec : ∀ S : Finset (Fin n), Measurable (Work.BoseBoxFock.slotExact e S Φc) ∧
      (∃ C, ∀ x, ‖Work.BoseBoxFock.slotExact e S Φc x‖ ≤ C) :=
    fun S => slotExact_mb_w hmeas hbdE hsupp S hΦm hΦb
  have hsecs : ∀ S : Finset (Fin n),
      Function.support (Work.BoseBoxFock.slotExact e S Φc) ⊆ boxPow n ℓ :=
    fun S => slotExact_support_w hsupp S hΦs
  have hAs : ∀ S : Finset (Fin n),
      Measurable (Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φc)) ∧
      (∃ C, ∀ x, ‖Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φc) x‖ ≤ C) ∧
      Function.support (Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φc))
        ⊆ boxPow n ℓ := by
    intro S
    obtain ⟨hm, hb, hs⟩ := (boxSlotSum_bdd hmeas hbdE hsupp T).2
      (Work.BoseBoxFock.slotExact e S Φc) (hsec S).1 (hsec S).2
    obtain ⟨C, hC0, hC⟩ := hb
    exact ⟨hm, ⟨C, hC⟩, hs (hsecs S)⟩
  -- (1) the pointwise expansion of the slot sum of `Φc` over the sectors
  have hApt_fun : Work.BoseDict.boxSlotSum e T Φc
      = fun x => ∑ S : Finset (Fin n),
          Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φc) x := by
    have hsum : Φc = (fun y : Fin n → E3 =>
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))), (1 : ℂ) •
          Work.BoseBoxFock.slotExact e S Φc y) := by
      funext y
      rw [← congrFun (Work.BoseBoxFock.slotExact_sum_eq e Φc) y]
      simp only [Finset.sum_apply, one_smul]
    conv_lhs => rw [hsum]
    rw [(boxSlotSum_bdd hmeas hbdE hsupp T).1 (s := Finset.univ)
      (c := fun _ => (1 : ℂ)) (Ψ := fun S => Work.BoseBoxFock.slotExact e S Φc)
      (fun S => (hsec S).1) (fun S => (hsec S).2)]
    funext x
    simp only [Finset.sum_apply, one_smul]
  have hApt : ∀ x : Fin n → E3, Work.BoseDict.boxSlotSum e T Φc x
      = ∑ S : Finset (Fin n),
          Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φc) x :=
    fun x => congrFun hApt_fun x
  -- (2) expand the left-hand side into the double sector sum
  have hYsum_m : Measurable (fun x : Fin n → E3 =>
      ∑ S' : Finset (Fin n),
        Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S' Φc) x) :=
    Finset.measurable_sum _ (fun S' _ => (hAs S').1)
  have hYsum_b : ∃ C, ∀ x : Fin n → E3, ‖∑ S' : Finset (Fin n),
      Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S' Φc) x‖ ≤ C := by
    choose Cb hCb using fun S' : Finset (Fin n) => (hAs S').2.1
    exact ⟨∑ S', max (Cb S') 0, fun x => (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun S' _ => (hCb S' x).trans (le_max_left _ _)))⟩
  have hYsum_s : Function.support (fun x : Fin n → E3 =>
      ∑ S' : Finset (Fin n),
        Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S' Φc) x) ⊆ boxPow n ℓ := by
    intro x hx
    by_contra hxnot
    refine hx ?_
    simp only [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun S' _ =>
      Function.notMem_support.mp (fun h => hxnot ((hAs S').2.2 h)))
  have hL : (∫ x : Fin n → E3, star (Φc x) * Work.BoseDict.boxSlotSum e T Φc x)
      = ∑ S : Finset (Fin n), ∑ S' : Finset (Fin n),
          ∫ x : Fin n → E3, star (Work.BoseBoxFock.slotExact e S Φc x)
            * Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S' Φc) x := by
    have hpt : ∀ x : Fin n → E3, star (Φc x) * Work.BoseDict.boxSlotSum e T Φc x
        = star (∑ S : Finset (Fin n), Work.BoseBoxFock.slotExact e S Φc x)
          * (∑ S' : Finset (Fin n),
              Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S' Φc) x) := by
      intro x
      have h1 : (∑ S : Finset (Fin n), Work.BoseBoxFock.slotExact e S Φc x) = Φc x := by
        rw [← congrFun (Work.BoseBoxFock.slotExact_sum_eq e Φc) x]
        simp only [Finset.sum_apply]
      rw [h1, hApt x]
    rw [show (∫ x : Fin n → E3, star (Φc x) * Work.BoseDict.boxSlotSum e T Φc x)
        = ∫ x : Fin n → E3,
            star (∑ S : Finset (Fin n), Work.BoseBoxFock.slotExact e S Φc x)
              * (∑ S' : Finset (Fin n),
                  Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S' Φc) x) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_star_sum_mul_weak (s := (Finset.univ : Finset (Finset (Fin n))))
      (G := fun S x => Work.BoseBoxFock.slotExact e S Φc x)
      (Ψ := fun x => ∑ S' : Finset (Fin n),
        Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S' Φc) x)
      (fun S => (hsec S).1) (fun S => (hsec S).2) hYsum_m hYsum_b hYsum_s]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [integral_star_mul_sum_weak (s := (Finset.univ : Finset (Finset (Fin n))))
      (G := fun S' x => Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S' Φc) x)
      (Θ := Work.BoseBoxFock.slotExact e S Φc) (hsec S).1 (hsec S).2 (hsecs S)
      (fun S' => (hAs S').1) (fun S' => (hAs S').2.1)]
  -- (3) each sector diagonalises the slot sum
  rw [hL]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_eq_single S]
  · intro S' _ hS'
    exact boxSlotSum_cross_w hmeas hbdE hsupp horth hint T Φc hΦm hΦb hΦs S S'
      (fun h => hS' h.symm)
  · intro hS
    exact absurd (Finset.mem_univ S) hS

/-! ## 12. The box containment -/

/-- `tsupport Φ ⊆ abox n ℓ` gives `support Φ ⊆ boxPow n ℓ` for `0 < ℓ`. -/
private theorem support_subset_boxPow_tsupport_w {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : (Fin n → E3) → ℂ} (hΦsupp : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ) :
    Function.support Φ ⊆ boxPow n ℓ := by
  intro x hx
  rw [mem_boxPow_iff]
  intro i
  exact Work.BoseBoxFock.acube_subset_boxL hℓ
    ((Submission.BoseGases.mem_abox_iff n ℓ x).mp (hΦsupp (subset_closure hx)) i)

end

/-! ## 13. The target -/

theorem slotFacts_boxSlotSum_ae {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ} (hℓ : 0 < ℓ)
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (Φc : Work.BoseDict.Xn n → ℂ) (hΦm : Measurable Φc)
    (hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C)
    (hΦsupp : tsupport Φc ⊆ Submission.BoseGases.abox n ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Work.BoseBoxFock.SlotFacts e Φc
      (fun Θ : Work.BoseDict.Xn n → ℂ => Work.BoseDict.boxSlotSum e T Θ)
      (fun S => Work.BoseBoxFock.slotSumSub e T S) := by
  classical
  have hΦs : Function.support Φc ⊆ boxPow n ℓ :=
    support_subset_boxPow_tsupport_w (n := n) (ℓ := ℓ) hℓ hΦsupp
  refine ⟨?_, ?_, ?_⟩
  · -- the slot sum preserves good states
    intro X hX
    exact boxSlotSum_measurable_bounded_ae hmeas hbdE hsupp T X hX.1 hX.2
  · -- the pointwise decoupling on a sector
    intro S u y
    exact boxSlotSum_pairCoord_w hmeas hbdE hsupp horth hint T S Φc hΦm hΦb u y
  · -- the sector splitting of the quadratic form
    have h := congrArg Complex.re
      (boxSlotSum_sector_split_w hmeas hbdE hsupp horth hint T Φc hΦm hΦb hΦs)
    have hsum : (∑ S : Finset (Fin n), ∫ x : Work.BoseDict.Xn n,
          star (Work.BoseBoxFock.slotExact e S Φc x)
            * Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φc) x).re
        = ∑ S : Finset (Fin n), (∫ x : Work.BoseDict.Xn n,
          star (Work.BoseBoxFock.slotExact e S Φc x)
            * Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φc) x).re := by
      simp
    exact h.trans hsum

end Work.MB
