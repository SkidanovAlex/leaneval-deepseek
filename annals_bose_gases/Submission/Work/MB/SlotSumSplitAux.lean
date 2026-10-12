import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSlotOf_slotProj1_comm
import Submission.Work.BoseBoxFock.slotProj1_boxSlotOf_self
import Submission.Work.BoseBoxFock.slotProj_peel_ae
import Submission.Work.MB.boxSlotOf_slotProj1_bdd
import Submission.Work.MB.boxSlotSum_bdd
import Submission.Work.MB.slotProj_adjoint_bdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.SlotSumSplitAux` — the weak-mode slot algebra behind `slotSum_sector_split_ae`

This module collects, for the *weak* mode hypotheses

    (hmeas : ∀ l, Measurable (e l))  (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)

(with `horth`/`hint` where the one-slot kernel algebra is used), the small derived facts and the
commutation statements needed by `Work.MB.slotSum_sector_split_ae`:

* the modes are in `L^∞` (`memLp_modes_weak`), so the pointwise weak peel and linearity lemmas of
  the shared tree apply;
* the slot projections, the one-slot projections and the sectors *preserve the box support*
  `boxPow n ℓ = (boxL ℓ)^n`;
* `slotProj1 e i` and `slotExact e S` preserve measurability and everywhere boundedness;
* `slotProj1 e i (slotExact e S Ψ) = if i ∈ S then slotExact e S Ψ else 0`;
* the first-quantised slot sum `boxSlotSum e T` commutes with every slot projection
  `slotProj e U`, hence with every sector `slotExact e S`.
-/

noncomputable section

namespace Work.MB

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. The modes are in `L^∞` -/

/-- Measurable and everywhere bounded modes are `L^∞`. -/
theorem memLp_modes_weak {m : ℕ} {e : Fin m → E3 → ℂ} (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C) : ∀ l, MemLp (e l) ⊤ (volume : Measure E3) := by
  intro l
  obtain ⟨C, hC⟩ := hbdd l
  exact memLp_top_of_bound (hmeas l).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => hC x))

/-! ## 2. Preservation of the box support -/

/-- The slot projection of a state vanishing outside `boxPow n ℓ` vanishes outside `boxPow n ℓ`. -/
theorem slotProj_support_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
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

/-- The one-slot projection of a state vanishing outside `boxPow n ℓ` vanishes outside
`boxPow n ℓ`. -/
theorem slotProj1_support_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {Ψ : (Fin n → E3) → ℂ} (hΨs : Function.support Ψ ⊆ boxPow n ℓ) :
    Function.support (Work.BoseBoxFock.slotProj1 e i Ψ) ⊆ boxPow n ℓ := by
  rw [← Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux e i Ψ]
  exact slotProj_support_weak hsupp {i} hΨs

/-- A bound `∃ C, ∀ x, ‖f x‖ ≤ C` can be taken with `0 ≤ C`. -/
theorem exists_bound_max {α : Type*} {f : α → ℂ} (h : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- The sector of a state vanishing outside `boxPow n ℓ` vanishes outside `boxPow n ℓ`. -/
theorem slotExact_support_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Ψ : (Fin n → E3) → ℂ}
    (hΨs : Function.support Ψ ⊆ boxPow n ℓ) :
    Function.support (Work.BoseBoxFock.slotExact e S Ψ) ⊆ boxPow n ℓ := by
  intro x hx
  by_contra hxnot
  refine hx ?_
  simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun T _ => ?_
  rw [Function.notMem_support.mp (fun h => hxnot (slotProj_support_weak hsupp T hΨs h)), mul_zero]

/-! ## 3. Measurability and boundedness of `slotProj1` and `slotExact` -/

/-- `slotProj1 e i` preserves measurability, everywhere boundedness and the box support. -/
theorem slotProj1_mb_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Measurable (Work.BoseBoxFock.slotProj1 e i Ψ) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Work.BoseBoxFock.slotProj1 e i Ψ x‖ ≤ C) ∧
    (Function.support Ψ ⊆ boxPow n ℓ →
      Function.support (Work.BoseBoxFock.slotProj1 e i Ψ) ⊆ boxPow n ℓ) := by
  obtain ⟨hm, hb⟩ := Work.MB.slotProj_mb_weak hmeas hbdd hsupp ({i} : Finset (Fin n)) hΨm hΨb
  refine ⟨?_, ?_, fun hs => slotProj1_support_weak hsupp i hs⟩
  · rwa [← Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux e i Ψ]
  · rw [← Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux e i Ψ]
    exact exists_bound_max hb

/-- `slotExact e S` preserves measurability, everywhere boundedness and the box support. -/
theorem slotExact_mb_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ)
    (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Measurable (Work.BoseBoxFock.slotExact e S Ψ) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Work.BoseBoxFock.slotExact e S Ψ x‖ ≤ C) ∧
    (Function.support Ψ ⊆ boxPow n ℓ →
      Function.support (Work.BoseBoxFock.slotExact e S Ψ) ⊆ boxPow n ℓ) := by
  have hbase : ∀ (T : Finset (Fin n)), Measurable (Work.BoseBoxFock.slotProj e T Ψ) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Work.BoseBoxFock.slotProj e T Ψ x‖ ≤ C) := by
    intro T
    obtain ⟨hm, hb⟩ := Work.MB.slotProj_mb_weak hmeas hbdd hsupp T hΨm hΨb
    exact ⟨hm, exists_bound_max hb⟩
  refine ⟨?_, ?_, fun hs => slotExact_support_weak hsupp S hs⟩
  · have hfun : Work.BoseBoxFock.slotExact e S Ψ =
        fun x => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          (-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Ψ x := by
      funext x
      simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply]
    rw [hfun]
    exact Finset.measurable_sum _
      (fun T _ => ((hbase T).1).const_smul ((-1 : ℂ) ^ (T.card - S.card)))
  · refine ⟨∑ T : Finset (Fin n), ‖(-1 : ℂ) ^ (T.card - S.card)‖ * (hbase T).2.choose,
      Finset.sum_nonneg (fun T _ => mul_nonneg (norm_nonneg _) (hbase T).2.choose_spec.1),
      fun x => ?_⟩
    calc ‖Work.BoseBoxFock.slotExact e S Ψ x‖
        ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            ‖(-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Ψ x‖ := by
          simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply]
          exact norm_sum_le _ _
      _ ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            ‖(-1 : ℂ) ^ (T.card - S.card)‖ * (hbase T).2.choose :=
          Finset.sum_le_sum fun T _ => by
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left ((hbase T).2.choose_spec.2 x) (norm_nonneg _)
      _ ≤ ∑ T : Finset (Fin n), ‖(-1 : ℂ) ^ (T.card - S.card)‖ * (hbase T).2.choose :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun T _ _ => mul_nonneg (norm_nonneg _) (hbase T).2.choose_spec.1)

/-! ## 4. The one-slot projection of a slot projection -/

/-- **Peel, in the `slotProj1`-first form**: for `i ∉ U`, projecting the slot `i` after the slots
of `U` is projecting the slots of `insert i U`. -/
theorem slotProj1_slotProj_peel_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {U : Finset (Fin n)} {i : Fin n} (hi : i ∉ U)
    {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotProj e U Ψ)
      = Work.BoseBoxFock.slotProj e (insert i U) Ψ := by
  obtain ⟨C, hC⟩ := hΨb
  exact (Work.BoseBoxFock.slotProj_peel_bdd (memLp_modes_weak hmeas hbdd) hsupp hi hΨm hC).symm

/-- The one-slot projection of the zero state is zero. -/
theorem slotProj1_zero_weak {m n : ℕ} (e : Fin m → E3 → ℂ) (i : Fin n) :
    Work.BoseBoxFock.slotProj1 e i (0 : (Fin n → E3) → ℂ) = 0 := by
  funext x
  simp [Work.BoseBoxFock.slotProj1]

/-- **Absorption**: for `i ∈ U`, projecting the slot `i` after the slots of `U` changes nothing. -/
theorem slotProj1_slotProj_self_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    {U : Finset (Fin n)} {i : Fin n} (hi : i ∈ U)
    {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotProj e U Ψ)
      = Work.BoseBoxFock.slotProj e U Ψ := by
  obtain ⟨C, hC⟩ := hΨb
  have hpeel := Work.BoseBoxFock.slotProj_peel_bdd (memLp_modes_weak hmeas hbdd) hsupp
    (Finset.notMem_erase i U) hΨm hC
  have hins : insert i (U.erase i) = U := Finset.insert_erase hi
  obtain ⟨hm, hb⟩ := Work.MB.slotProj_mb_weak hmeas hbdd hsupp (U.erase i) hΨm ⟨C, hC⟩
  have hidem := Work.MB.slotProj1_idem_weak hmeas hbdd hsupp horth hm hb i
  rw [← hins, hpeel]
  exact hidem

/-! ## 5. The single-slot projection kills the non-occupied sectors -/

/-- The sector as a pointwise finite sum. -/
theorem slotExact_eq_sum_fun {m n : ℕ} (e : Fin m → E3 → ℂ) (S : Finset (Fin n))
    (Ψ : (Fin n → E3) → ℂ) :
    Work.BoseBoxFock.slotExact e S Ψ =
      fun x => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
        (-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Ψ x := by
  funext x
  simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply]

/-- **The one-slot projection kills the sectors it does not belong to, and fixes the ones it does.**

`slotProj1 e i (slotExact e S Ψ) = if i ∈ S then slotExact e S Ψ else 0`.

The `i ∈ S` case is absorption: every `T ⊇ S` contains `i`, hence
`Q_i (P_T Ψ) = P_{insert i (T \ {i})} Ψ = P_T Ψ`.  The `i ∉ S` case uses the paired form
`Work.BoseBoxFock.SecAux.slotExact_pair_form`, in which every pair
`P_T Ψ - P_{insert i T} Ψ` (`i ∉ T`) is killed by `Q_i` because `Q_i (P_T Ψ) = P_{insert i T} Ψ`
(peel) and `Q_i (P_{insert i T} Ψ) = Q_i (Q_i (P_T Ψ)) = Q_i (P_T Ψ)` (idempotence). -/
theorem slotProj1_slotExact_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', Integrable (fun z : E3 => star (e l z) * e l' z))
    (S : Finset (Fin n)) (i : Fin n) {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ)
    (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotExact e S Ψ)
      = if i ∈ S then Work.BoseBoxFock.slotExact e S Ψ else 0 := by
  have hmb : ∀ T : Finset (Fin n), Measurable (Work.BoseBoxFock.slotProj e T Ψ) ∧
      (∃ C, ∀ x, ‖Work.BoseBoxFock.slotProj e T Ψ x‖ ≤ C) := fun T =>
    Work.MB.slotProj_mb_weak hmeas hbdd hsupp T hΨm hΨb
  by_cases hiS : i ∈ S
  · rw [if_pos hiS, slotExact_eq_sum_fun]
    rw [(Work.MB.slotProj1_linear_bdd hmeas hbdd hsupp).1 i
      (Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T))
      (fun T => (-1 : ℂ) ^ (T.card - S.card))
      (fun T => Work.BoseBoxFock.slotProj e T Ψ) (fun T => (hmb T).1) (fun T => (hmb T).2)]
    funext x
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [congrFun (slotProj1_slotProj_self_bdd hmeas hbdd hsupp horth
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
    rw [congrFun (slotProj1_slotProj_peel_bdd hmeas hbdd hsupp hiT hΨm hΨb) x,
      congrFun (slotProj1_slotProj_self_bdd hmeas hbdd hsupp horth
        (Finset.mem_insert_self i T) hΨm hΨb) x, sub_self, smul_zero]

/-! ## 6. The classification of the states fixed by all the single-slot projections -/

/-- **Classification.** If a measurable bounded state `Υ` is fixed by `slotProj1 e i` for `i ∈ S`
and killed by it for `i ∉ S`, then the sector `S` fixes it: `slotExact e S Υ = Υ`.

Proof by the peel lemma: induction on `T` shows `slotProj e T Υ = if T ⊆ S then Υ else 0`; the
sector is `Σ_{T ⊇ S} (-1)^{|T| - |S|} slotProj e T Υ` and only `T = S` survives. -/
theorem slotExact_eq_self_of_slotProj1 {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Υ : (Fin n → E3) → ℂ} (hΥm : Measurable Υ)
    (hΥb : ∃ C, ∀ x, ‖Υ x‖ ≤ C)
    (hiii : ∀ i : Fin n, Work.BoseBoxFock.slotProj1 e i Υ = if i ∈ S then Υ else 0) :
    Work.BoseBoxFock.slotExact e S Υ = Υ := by
  have hclass : ∀ T : Finset (Fin n),
      Work.BoseBoxFock.slotProj e T Υ = if T ⊆ S then Υ else 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [if_pos (Finset.empty_subset S)]
      rw [Work.BoseBoxFock.slotProj_eq_slotInt_fun]
      exact Work.BoseBoxFock.slotInt_empty e Υ
    | insert a T' ha ih =>
      have hpeel : Work.BoseBoxFock.slotProj e (insert a T') Υ
          = Work.BoseBoxFock.slotProj1 e a (Work.BoseBoxFock.slotProj e T' Υ) := by
        obtain ⟨C, hC⟩ := hΥb
        exact Work.BoseBoxFock.slotProj_peel_bdd (memLp_modes_weak hmeas hbdd) hsupp ha hΥm hC
      rw [hpeel, ih]
      by_cases hTS : T' ⊆ S
      · rw [if_pos hTS]
        by_cases haS : a ∈ S
        · rw [hiii a, if_pos haS, if_pos (Finset.insert_subset haS hTS)]
        · rw [hiii a, if_neg haS,
            if_neg (fun hc => haS (Finset.insert_subset_iff.mp hc).1)]
      · rw [if_neg hTS, slotProj1_zero_weak,
          if_neg (fun hc => hTS (Finset.insert_subset_iff.mp hc).2)]
  rw [slotExact_eq_sum_fun]
  funext x
  rw [Finset.sum_eq_single (S : Finset (Fin n))]
  · rw [hclass S, if_pos (Finset.Subset.refl S)]
    simp
  · intro T hT hTS
    rw [hclass T,
      if_neg (fun hc => hTS (Finset.Subset.antisymm hc (Finset.mem_filter.mp hT).2))]
    simp
  · intro hmem
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ S, Finset.Subset.refl S⟩) hmem

/-! ## 7. Integrability and the sector self-adjointness -/

/-- `star f · g` is integrable when `f` and `g` are measurable, everywhere bounded and supported
in `boxPow n ℓ`. -/
theorem integrable_star_mul_of_support_boxPow {n : ℕ} {ℓ : ℝ} {f g : (Fin n → E3) → ℂ}
    (hfm : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) (hfs : Function.support f ⊆ boxPow n ℓ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) (hgs : Function.support g ⊆ boxPow n ℓ) :
    Integrable (fun x => star (f x) * g x) := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  refine integrable_of_bdd_of_support (measurableSet_boxPow n ℓ) (volume_boxPow_lt_top n ℓ)
    ((Complex.continuous_conj.measurable.comp hfm).mul hgm).aestronglyMeasurable
    (C := max Cf 0 * max Cg 0) ?_ ?_
  · intro x
    rw [norm_mul, norm_star]
    exact mul_le_mul ((hCf x).trans (le_max_left _ _)) ((hCg x).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro x hx
    by_cases h : f x = 0
    · rw [h, star_zero, zero_mul]
    · exact absurd (hfs (Function.mem_support.mpr h)) hx

/-- **Self-adjointness of the sector `slotExact e S`** at the weak mode hypotheses: the finite
combination of the slot adjointnesses `Work.MB.slotProj_adjoint_bdd`. -/
theorem slotExact_adjoint_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Φ Ψ : (Fin n → E3) → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (hΦs : Function.support Φ ⊆ boxPow n ℓ)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) (hΨs : Function.support Ψ ⊆ boxPow n ℓ) :
    ∫ x, star (Work.BoseBoxFock.slotExact e S Φ x) * Ψ x
      = ∫ x, star (Φ x) * Work.BoseBoxFock.slotExact e S Ψ x := by
  have hstar_neg : ∀ k : ℕ, star ((-1 : ℂ) ^ k) = (-1 : ℂ) ^ k := by
    intro k
    rw [Complex.star_def, map_pow]
    simp
  set s : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T) with hs
  have hmb : ∀ T : Finset (Fin n), Measurable (Work.BoseBoxFock.slotProj e T Φ) ∧
      Measurable (Work.BoseBoxFock.slotProj e T Ψ) ∧
      (∃ C, ∀ x, ‖Work.BoseBoxFock.slotProj e T Φ x‖ ≤ C) ∧
      (∃ C, ∀ x, ‖Work.BoseBoxFock.slotProj e T Ψ x‖ ≤ C) := by
    intro T
    obtain ⟨hm, hb⟩ := Work.MB.slotProj_mb_weak hmeas hbdd hsupp T hΦm hΦb
    obtain ⟨hm', hb'⟩ := Work.MB.slotProj_mb_weak hmeas hbdd hsupp T hΨm hΨb
    exact ⟨hm, hm', hb, hb'⟩
  -- step 1 : expand the left-hand side
  have h1 : ∫ x, star (Work.BoseBoxFock.slotExact e S Φ x) * Ψ x
      = ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) *
          ∫ x, star (Work.BoseBoxFock.slotProj e T Φ x) * Ψ x := by
    have hpt : ∀ x, star (Work.BoseBoxFock.slotExact e S Φ x) * Ψ x
        = ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) *
            (star (Work.BoseBoxFock.slotProj e T Φ x) * Ψ x) := by
      intro x
      simp only [Work.BoseBoxFock.slotExact, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [star_mul, hstar_neg]
      ring
    rw [show (∫ x, star (Work.BoseBoxFock.slotExact e S Φ x) * Ψ x)
        = ∫ x, ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) *
            (star (Work.BoseBoxFock.slotProj e T Φ x) * Ψ x) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun T _ => ?_
      rw [MeasureTheory.integral_const_mul]
    · intro T _
      exact (integrable_star_mul_of_support_boxPow (hmb T).1 (hmb T).2.2.1
        (slotProj_support_weak hsupp T hΦs) hΨm hΨb hΨs).const_mul _
  -- step 2 : self-adjointness of each slot projection
  have h2 : ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) *
        ∫ x, star (Work.BoseBoxFock.slotProj e T Φ x) * Ψ x
      = ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) *
        ∫ x, star (Φ x) * Work.BoseBoxFock.slotProj e T Ψ x := by
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Work.MB.slotProj_adjoint_bdd hmeas hbdd hsupp T Φ Ψ hΦm hΦb hΦs hΨm hΨb hΨs]
  -- step 3 : fold the sum back
  have h3 : ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) *
        ∫ x, star (Φ x) * Work.BoseBoxFock.slotProj e T Ψ x
      = ∫ x, star (Φ x) * Work.BoseBoxFock.slotExact e S Ψ x := by
    have hpt : ∀ x, ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) *
          (star (Φ x) * Work.BoseBoxFock.slotProj e T Ψ x)
        = star (Φ x) * Work.BoseBoxFock.slotExact e S Ψ x := by
      intro x
      simp only [Work.BoseBoxFock.slotExact, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      ring
    have hsum : (∫ x, ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) *
          (star (Φ x) * Work.BoseBoxFock.slotProj e T Ψ x))
        = ∑ T ∈ s, (-1 : ℂ) ^ (T.card - S.card) *
          ∫ x, star (Φ x) * Work.BoseBoxFock.slotProj e T Ψ x := by
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun T _ => ?_
        rw [MeasureTheory.integral_const_mul]
      · intro T _
        exact (integrable_star_mul_of_support_boxPow hΦm hΦb hΦs (hmb T).2.1 (hmb T).2.2.2
          (slotProj_support_weak hsupp T hΨs)).const_mul _
    rw [← hsum]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [h1, h2, h3]

/-! ## 8. The corpus box contains the centred cube -/

/-- The centred cube of side `ℓ` is contained in the corpus box `boxL ℓ` for **every** `ℓ`
(for `0 < ℓ` they are equal, `Work.BoseBoxFock.boxL_eq_acube`; for `ℓ = 0` both are `{0}`; and
for `ℓ < 0` the centred cube is empty). -/
theorem acube_subset_boxL_all {ℓ : ℝ} :
    Submission.BoseGases.acube ℓ ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  rcases lt_trichotomy (0 : ℝ) ℓ with hlt | heq | hgt
  · exact Work.BoseBoxFock.acube_subset_boxL hlt
  · subst heq
    intro y hy
    have hy0 : y = 0 := by
      ext m
      have hm := (Submission.BoseGases.mem_acube_iff 0 y).mp hy m
      rw [Set.mem_Icc] at hm
      have h0 : y m = 0 := by linarith [hm.1, hm.2]
      simpa using h0
    rw [hy0, Work.BoseB4.BoxData.boxL]
    refine Set.mem_smul_set.mpr ⟨(0 : E3), ?_, by simp⟩
    show (0 : E3) ∈ Work.BoseB4.unitCell
    simp only [Work.BoseB4.unitCell, Set.mem_ofPred_eq]
    intro i
    rw [show (0 : E3) i = (0 : ℝ) from rfl]
    norm_num
  · intro y hy
    exfalso
    have h0 := ((Submission.BoseGases.mem_acube_iff ℓ y).mp hy 0 :
      (y 0) ∈ Set.Icc (-ℓ / 2) (ℓ / 2))
    rw [Set.mem_Icc] at h0
    linarith [h0.1, h0.2, hgt]

/-- `tsupport Φ ⊆ abox n ℓ` gives `support Φ ⊆ boxPow n ℓ`. -/
theorem support_subset_boxPow_of_tsupport {n : ℕ} {ℓ : ℝ} {Φ : (Fin n → E3) → ℂ}
    (hΦsupp : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ) :
    Function.support Φ ⊆ boxPow n ℓ := by
  intro x hx
  rw [mem_boxPow_iff]
  intro i
  exact acube_subset_boxL_all
    ((Submission.BoseGases.mem_abox_iff n ℓ x).mp (hΦsupp (subset_closure hx)) i)

/-! ## 9. The one-slot projection commutes with the first-quantised slot sum -/

/-- A finite sum of bounded functions is bounded. -/
theorem exists_bound_finset_sum {ι α : Type*} (s : Finset ι) {f : ι → α → ℂ}
    (hb : ∀ i ∈ s, ∃ C, ∀ x, ‖f i x‖ ≤ C) :
    ∃ C, ∀ x, ‖∑ i ∈ s, f i x‖ ≤ C := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, fun x => by simp⟩
  | insert a s ha ih =>
    obtain ⟨C1, hC1⟩ := hb a (Finset.mem_insert_self a s)
    obtain ⟨C2, hC2⟩ := ih fun i hi => hb i (Finset.mem_insert_of_mem hi)
    refine ⟨max C1 0 + max C2 0, fun x => ?_⟩
    rw [Finset.sum_insert ha]
    exact le_trans (norm_add_le _ _)
      (add_le_add ((hC1 x).trans (le_max_left _ _)) ((hC2 x).trans (le_max_left _ _)))

/-- A finite `•`-combination of bounded functions is bounded. -/
theorem exists_bound_finset_smul {ι α : Type*} (s : Finset ι) (c : ι → ℂ)
    {f : ι → α → ℂ} (hb : ∀ i ∈ s, ∃ C, ∀ x, ‖f i x‖ ≤ C) :
    ∃ C, ∀ x, ‖∑ i ∈ s, c i • f i x‖ ≤ C := by
  refine exists_bound_finset_sum s (f := fun i x => c i • f i x) fun i hi => ?_
  obtain ⟨C, hC⟩ := hb i hi
  exact ⟨‖c i‖ * max C 0, fun x => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left _ _)) (norm_nonneg _)⟩

/-- **Linearity of `slotProj1 e i` over a double finite sum.** -/
theorem slotProj1_sum2_bdd {m N : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin N) {κ₁ κ₂ : Type} [DecidableEq κ₁] [DecidableEq κ₂]
    (s₁ : Finset κ₁) (s₂ : Finset κ₂) (c : κ₁ → κ₂ → ℂ)
    (Θ : κ₁ → κ₂ → (Fin N → E3) → ℂ)
    (hm : ∀ a b, Measurable (Θ a b)) (hb : ∀ a b, ∃ C, ∀ x, ‖Θ a b x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (fun x => ∑ a ∈ s₁, ∑ b ∈ s₂, c a b • Θ a b x)
      = fun x => ∑ a ∈ s₁, ∑ b ∈ s₂, c a b • Work.BoseBoxFock.slotProj1 e i (Θ a b) x := by
  have hstep : ∀ a : κ₁, Work.BoseBoxFock.slotProj1 e i
      (fun y => ∑ b ∈ s₂, c a b • Θ a b y)
      = fun x => ∑ b ∈ s₂, c a b • Work.BoseBoxFock.slotProj1 e i (Θ a b) x := fun a =>
    (Work.MB.slotProj1_linear_bdd hmeas hbdd hsupp).1 i s₂ (c a) (fun b => Θ a b)
      (fun b => hm a b) (fun b => hb a b)
  calc Work.BoseBoxFock.slotProj1 e i (fun x => ∑ a ∈ s₁, ∑ b ∈ s₂, c a b • Θ a b x)
      = Work.BoseBoxFock.slotProj1 e i
          (fun x => ∑ a ∈ s₁, 1 •
            (fun (a' : κ₁) (y : Fin N → E3) => ∑ b ∈ s₂, c a' b • Θ a' b y) a x) := by
        congr 1
        funext x
        simp only [one_smul]
    _ = fun x => ∑ a ∈ s₁, 1 •
          Work.BoseBoxFock.slotProj1 e i
            ((fun (a' : κ₁) (y : Fin N → E3) => ∑ b ∈ s₂, c a' b • Θ a' b y) a) x :=
        (Work.MB.slotProj1_linear_bdd hmeas hbdd hsupp).1 i s₁ (fun _ => (1 : ℂ))
          (fun a' y => ∑ b ∈ s₂, c a' b • Θ a' b y)
          (fun a => Finset.measurable_sum _ (fun b _ => (hm a b).const_smul (c a b)))
          (fun a => exists_bound_finset_smul s₂ (c a) (fun b _ => hb a b))
    _ = fun x => ∑ a ∈ s₁, ∑ b ∈ s₂,
          c a b • Work.BoseBoxFock.slotProj1 e i (Θ a b) x := by
        funext x
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [one_smul]
        simpa using congrFun (hstep a) x

/-- **Linearity of `slotProj1 e i` over a triple finite sum.** -/
theorem slotProj1_sum3_bdd {m N : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin N) (s₁ : Finset (Fin N)) (s₂ s₃ : Finset (Fin m))
    (c : Fin N → Fin m → Fin m → ℂ) (Θ : Fin N → Fin m → Fin m → (Fin N → E3) → ℂ)
    (hm : ∀ a b cc, Measurable (Θ a b cc)) (hb : ∀ a b cc, ∃ C, ∀ x, ‖Θ a b cc x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i
        (fun x => ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ cc ∈ s₃, c a b cc • Θ a b cc x)
      = fun x => ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ cc ∈ s₃,
          c a b cc • Work.BoseBoxFock.slotProj1 e i (Θ a b cc) x := by
  have hstep : ∀ a : Fin N, Work.BoseBoxFock.slotProj1 e i
      (fun y => ∑ b ∈ s₂, ∑ cc ∈ s₃, c a b cc • Θ a b cc y)
      = fun x => ∑ b ∈ s₂, ∑ cc ∈ s₃,
          c a b cc • Work.BoseBoxFock.slotProj1 e i (Θ a b cc) x := fun a =>
    slotProj1_sum2_bdd hmeas hbdd hsupp i s₂ s₃ (c a) (fun b cc => Θ a b cc)
      (fun b cc => hm a b cc) (fun b cc => hb a b cc)
  calc Work.BoseBoxFock.slotProj1 e i
        (fun x => ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ cc ∈ s₃, c a b cc • Θ a b cc x)
      = Work.BoseBoxFock.slotProj1 e i
          (fun x => ∑ a ∈ s₁, 1 •
            (fun (a' : Fin N) (y : Fin N → E3) =>
              ∑ b ∈ s₂, ∑ cc ∈ s₃, c a' b cc • Θ a' b cc y) a x) := by
        congr 1
        funext x
        simp only [one_smul]
    _ = fun x => ∑ a ∈ s₁, 1 • Work.BoseBoxFock.slotProj1 e i
          ((fun (a' : Fin N) (y : Fin N → E3) =>
            ∑ b ∈ s₂, ∑ cc ∈ s₃, c a' b cc • Θ a' b cc y) a) x :=
        (Work.MB.slotProj1_linear_bdd hmeas hbdd hsupp).1 i s₁ (fun _ => (1 : ℂ))
          (fun a' y => ∑ b ∈ s₂, ∑ cc ∈ s₃, c a' b cc • Θ a' b cc y)
          (fun a => Finset.measurable_sum _ fun b _ =>
            Finset.measurable_sum _ fun cc _ => (hm a b cc).const_smul (c a b cc))
          (fun a => exists_bound_finset_sum s₂ fun b _ =>
            exists_bound_finset_smul s₃ (c a b) (fun cc _ => hb a b cc))
    _ = fun x => ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ cc ∈ s₃,
          c a b cc • Work.BoseBoxFock.slotProj1 e i (Θ a b cc) x := by
        funext x
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [one_smul]
        simpa using congrFun (hstep a) x

/-- **The first-quantised slot sum commutes with the one-slot projection.** -/
theorem boxSlotSum_slotProj1_bdd {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', Integrable (fun z : E3 => star (e l z) * e l' z))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    {Θ : (Fin d → E3) → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (i : Fin d) :
    Work.BoseBoxFock.slotProj1 e i (Work.BoseDict.boxSlotSum e T Θ)
      = Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotProj1 e i Θ) := by
  have hbox := Work.MB.boxSlotOf_slotProj1_bdd hmeas hbdd hsupp horth hint hΘm hΘb
  have hB : Work.BoseDict.boxSlotSum e T Θ
      = (fun x => ∑ j ∈ Finset.univ, ∑ l ∈ Finset.univ, ∑ l' ∈ Finset.univ,
          ((T (Work.BoseB4.evec m l') l : ℝ) : ℂ) • Work.BoseDict.boxSlotOf e
            (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x) := by
    funext x
    simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun l' _ => rfl
  have hBQ : Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotProj1 e i Θ)
      = (fun x => ∑ j ∈ Finset.univ, ∑ l ∈ Finset.univ, ∑ l' ∈ Finset.univ,
          ((T (Work.BoseB4.evec m l') l : ℝ) : ℂ) • Work.BoseDict.boxSlotOf e
            (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
            (Work.BoseBoxFock.slotProj1 e i Θ) x) := by
    funext x
    simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun l' _ => rfl
  rw [hB, hBQ,
    slotProj1_sum3_bdd hmeas hbdd hsupp i Finset.univ Finset.univ Finset.univ
      (fun j l l' => ((T (Work.BoseB4.evec m l') l : ℝ) : ℂ))
      (fun j l l' => Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
      (fun j l l' => (hbox.2.2.2 l l' j).1)
      (fun j l l' => (hbox.2.2.2 l l' j).2.imp (fun C hC => hC.2))]
  funext x
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun l' _ => ?_
  by_cases hji : j = i
  · subst hji
    rw [hbox.2.1 l l' j, hbox.1 l l' j]
  · rw [hbox.2.2.1 l l' i j (fun h => hji h.symm)]

/-- The first-quantised slot sum of the zero state is zero. -/
theorem boxSlotSum_zero_weak {m d : ℕ} (e : Fin m → E3 → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Work.BoseDict.boxSlotSum e T (0 : (Fin d → E3) → ℂ) = 0 := by
  funext x
  simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ =>
    Finset.sum_eq_zero fun l' _ => ?_
  simp [Work.BoseDict.boxSlotOf]

end Work.MB
