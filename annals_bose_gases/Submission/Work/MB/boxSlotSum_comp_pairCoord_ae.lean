import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSlotSum_comp_pairCoord
import Submission.Work.BoseBoxFock.slotProj_peel_ae
import Submission.Work.MB.boxSlotOf_slotProj1_bdd
import Submission.Work.MB.boxSlotSum_bdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.boxSlotSum_comp_pairCoord_ae` — the weak-mode pointwise decoupling of a composite
# slot sum

This is the measurable/bounded ("weak") twin of `Work.BoseBoxFock.boxSlotSum_comp_pairCoord`.
The strong version assumes the modes `e l` are `Continuous` with `HasCompactSupport` and the state
`Φ` is continuous with compact support; those hypotheses are *unsatisfiable* at the honest modes of
the box ↔ model bridge (`FINDING_continuous_hypotheses_UNSATISFIABLE.md`), so the bridge has to run
the whole slot calculus on the weak bundle

* `hmeas : ∀ l, Measurable (e l)`,
* `hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C` (everywhere bounded),
* `hsupp : ∀ l, support (e l) ⊆ boxL ℓ` (supported in the corpus box),

with a state `Φ` that is only measurable, everywhere bounded, and supported in the `n`-particle box
`abox n ℓ`.  The conclusion is the pointwise decoupling

    boxSlotSum e T₁ (boxSlotSum e T₂ (slotExact e S Φ)) (pairCoord S u y)
      = slotSumSub e T₁ S (slotSumSub e T₂ S (sectorSlice e S Φ y)) u .

The proof mirrors the strong one, with the weak slot algebra of `Submission/Work/MB/` in place of
the strong one:

* `slotExact_mb_weak` — the sector of a measurable bounded state is measurable and bounded;
* `Work.MB.boxSlotSum_bdd` — the slot sum preserves measurability and everywhere boundedness;
* `slotProj1_slotExact_bdd'` — the one-slot projection kills the sectors it does not belong to;
* `boxSlotSum_slotProj1_comm_bdd` — the slot sum commutes with every one-slot projection;
* `boxSlotSum_eq_sum_mem_of_slotProj1_eq_zero_bdd` — the slot sum collapses onto the occupied
  slots whenever the state carries no `V`-component outside `S`;
* `Work.BoseBoxFock.boxSlotOf_pairCoord(_gen)` — the pointwise identity on the assembled
  configuration.

The helpers are `private`: they are the weak twins of existing (strong) lemmas, mirrored here so
that this module rests only on the *stable* weak modules of the area.
-/

noncomputable section

namespace Work.MB

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 0. Elementary helpers -/

/-- Measurable and everywhere bounded functions are `L^∞`. -/
private theorem memLp_top_modes {m : ℕ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C) :
    ∀ l, MemLp (e l) ⊤ (volume : Measure E3) := by
  intro l
  obtain ⟨C, hC⟩ := hbdd l
  exact memLp_top_of_bound (hmeas l).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => hC x))

/-- An everywhere bound can be taken nonnegative. -/
private theorem exists_bound_max {α : Type*} {f : α → ℂ} (h : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- A finite sum of measurable, everywhere bounded functions is measurable and everywhere
bounded. -/
private theorem sum_measurable_bounded {ι : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι]
    (f : ι → (Fin d → E3) → ℂ) (hm : ∀ k, Measurable (f k))
    (hb : ∀ k, ∃ C, ∀ x, ‖f k x‖ ≤ C) :
    Measurable (∑ k, f k) ∧ ∃ C, ∀ x, ‖(∑ k, f k) x‖ ≤ C := by
  classical
  choose C hC using hb
  constructor
  · have h : Measurable (fun x : Fin d → E3 => ∑ k, f k x) :=
      Finset.measurable_sum _ (fun k _ => hm k)
    convert h using 1
    funext x
    simp only [Finset.sum_apply]
  · refine ⟨∑ k, max (C k) 0, fun x => ?_⟩
    rw [Finset.sum_apply]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun k _ => (hC k x).trans (le_max_left _ _)))

/-- The pointwise form of a function-valued finite scalar-weighted sum. -/
private theorem sum_smul_fun_eq {ι : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (f : ι → (Fin d → E3) → ℂ) :
    (∑ k, c k • f k) = fun x => ∑ k, c k • f k x := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply]

/-- **Linearity of the one-slot projection** over a finite `ℝ`-linear combination. -/
private theorem slotProj1_sum_smul_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {ι : Type*} [Fintype ι] (i : Fin n) (c : ι → ℝ) (f : ι → (Fin n → E3) → ℂ)
    (hm : ∀ k, Measurable (f k)) (hb : ∀ k, ∃ C, ∀ x, ‖f k x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (∑ k, c k • f k)
      = ∑ k, c k • Work.BoseBoxFock.slotProj1 e i (f k) := by
  classical
  funext x
  rw [Work.BoseBoxFock.slotProj1, Finset.sum_apply]
  simp only [Pi.smul_apply]
  rw [show (fun w : E3 => Work.BoseBoxFock.PV e (x i) w * (∑ k, c k • f k) (Function.update x i w))
      = (fun w : E3 => ∑ k, c k • (Work.BoseBoxFock.PV e (x i) w *
          f k (Function.update x i w))) from by
    funext w
    rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Pi.smul_apply, mul_smul_comm]]
  rw [MeasureTheory.integral_finsetSum]
  swap
  · intro k _
    exact (Work.MB.integrable_PV_mul_update hmeas hbdd hsupp (hm k) (hb k) i x).smul (c k)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_smul, Work.BoseBoxFock.slotProj1]

/-- **Linearity of the one-slot projection** over a finite sum. -/
private theorem slotProj1_sum_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i : Fin n) (f : ι → (Fin n → E3) → ℂ)
    (hm : ∀ k, Measurable (f k)) (hb : ∀ k, ∃ C, ∀ x, ‖f k x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (∑ k, f k)
      = ∑ k, Work.BoseBoxFock.slotProj1 e i (f k) := by
  classical
  have h := slotProj1_sum_smul_weak hmeas hbdd hsupp i (fun _ : ι => (1 : ℝ)) f hm hb
  simpa only [one_smul] using h

/-- Measurability and everywhere boundedness of the one-slot projection. -/
private theorem slotProj1_mb_weak' {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ)
    (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Measurable (Work.BoseBoxFock.slotProj1 e i Ψ) ∧
      ∃ C, ∀ x, ‖Work.BoseBoxFock.slotProj1 e i Ψ x‖ ≤ C := by
  obtain ⟨hm, hb⟩ := Work.MB.slotProj_mb_weak hmeas hbdd hsupp ({i} : Finset (Fin n)) hΨm hΨb
  have hb' : ∃ C, ∀ x, ‖Work.BoseBoxFock.slotProj1 e i Ψ x‖ ≤ C := by
    rw [← Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux e i Ψ]
    exact hb
  refine ⟨?_, hb'⟩
  rwa [← Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux e i Ψ]

/-! ## 1. Regularity of the sector -/

/-- The sector of a measurable, everywhere bounded state is measurable and everywhere
bounded. -/
private theorem slotExact_mb_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
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
    exact ⟨hm, exists_bound_max hb⟩
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

/-! ## 2. Peel and absorption for the one-slot projection -/

/-- **Peel**, weak form: for `i ∉ U`, projecting the slot `i` after the slots of `U` is projecting
the slots of `insert i U`. -/
private theorem slotProj1_slotProj_peel_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {U : Finset (Fin n)} {i : Fin n} (hi : i ∉ U)
    {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotProj e U Ψ)
      = Work.BoseBoxFock.slotProj e (insert i U) Ψ := by
  obtain ⟨C, hC⟩ := hΨb
  exact (Work.BoseBoxFock.slotProj_peel_bdd (memLp_top_modes hmeas hbdd) hsupp hi hΨm hC).symm

/-- **Absorption**, weak form: for `i ∈ U`, projecting the slot `i` after the slots of `U`
changes nothing. -/
private theorem slotProj1_slotProj_self_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    {U : Finset (Fin n)} {i : Fin n} (hi : i ∈ U)
    {Ψ : (Fin n → E3) → ℂ} (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotProj e U Ψ)
      = Work.BoseBoxFock.slotProj e U Ψ := by
  obtain ⟨C, hC⟩ := hΨb
  have hpeel := Work.BoseBoxFock.slotProj_peel_bdd (memLp_top_modes hmeas hbdd) hsupp
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
private theorem slotProj1_slotExact_bdd' {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
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
    rw [congrFun (slotProj1_slotProj_self_weak hmeas hbdd hsupp horth
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
    rw [congrFun (slotProj1_slotProj_peel_weak hmeas hbdd hsupp hiT hΨm hΨb) x,
      congrFun (slotProj1_slotProj_self_weak hmeas hbdd hsupp horth
        (Finset.mem_insert_self i T) hΨm hΨb) x, sub_self, smul_zero]

/-! ## 4. The slot operators kill the states with a vanishing slot projection -/

/-- If the `j`-th slot of `Θ` carries no `V`-component, the slot-`j` rank-one operator
`|e l⟩⟨e l'|` annihilates `Θ` (weak twin of
`Work.BoseBoxFock.boxSlotOf_eq_zero_of_slotProj1_eq_zero`). -/
private theorem boxSlotOf_eq_zero_of_slotProj1_eq_zero_bdd {m d : ℕ} {ℓ : ℝ}
    {e : Fin m → E3 → ℂ}
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
  funext x
  simp [Work.BoseDict.boxSlotOf]

/-! ## 5. The collapse of the slot sum onto the occupied slots -/

/-- **The slot sum collapses to `S` whenever the state has no `V`-component outside `S`** (weak
twin of `Work.BoseBoxFock.boxSlotSum_eq_sum_mem_of_slotProj1_eq_zero`). -/
private theorem boxSlotSum_eq_sum_mem_of_slotProj1_eq_zero_bdd {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → E3 → ℂ}
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
    rw [boxSlotOf_eq_zero_of_slotProj1_eq_zero_bdd hmeas hbdd hsupp horth hint l l' j
      hΘm hΘb (hΘ0 j hj)]
    exact smul_zero _
  rw [Work.BoseDict.boxSlotSum]
  exact (Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => hzero j hj)).symm

/-! ## 6. Regularity of the slot operator `slotOp` -/

/-- The `j`-th slot operator of the slot sum is measurable and bounded at the weak mode
bundle. -/
private theorem slotOp_mb_weak {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin d) (Θ : (Fin d → E3) → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    Measurable (Work.BoseBoxFock.slotOp e T j Θ) ∧
      ∃ C, ∀ x, ‖Work.BoseBoxFock.slotOp e T j Θ x‖ ≤ C := by
  have hbox : ∀ (l l' : Fin m),
      Measurable (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x : Fin d → E3,
          ‖Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ ≤ C :=
    fun l l' => by
      obtain ⟨hm, hb⟩ := Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp
        (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ hΘm hΘb
      exact ⟨hm, exists_bound_max hb⟩
  constructor
  · have h : Measurable (fun x : Fin d → E3 => ∑ l : Fin m, ∑ l' : Fin m,
        T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x) := by
      refine Finset.measurable_sum _ (fun l _ => ?_)
      refine Finset.measurable_sum _ (fun l' _ => ?_)
      exact ((hbox l l').1).const_smul (T (Work.BoseB4.evec m l') l)
    convert h using 1
    funext x
    simp only [Work.BoseBoxFock.slotOp, Finset.sum_apply, Pi.smul_apply]
  · choose Cb hCb using fun (l l' : Fin m) => (hbox l l').2
    refine ⟨∑ l : Fin m, ∑ l' : Fin m, |T (Work.BoseB4.evec m l') l| * max (Cb l l') 0,
      fun x => ?_⟩
    have h1 : ‖Work.BoseBoxFock.slotOp e T j Θ x‖ ≤ ∑ l : Fin m, ∑ l' : Fin m,
        ‖T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ := by
      simp only [Work.BoseBoxFock.slotOp, Finset.sum_apply, Pi.smul_apply]
      exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun l _ => norm_sum_le _ _))
    refine le_trans h1 ?_
    refine Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun l' _ => ?_))
    simp only [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (((hCb l l').2 x).trans (le_max_left _ _)) (abs_nonneg _)

/-! ## 7. Commutation of the slot sum with the one-slot projection -/

/-- **The slot sum commutes with every one-slot projection** (weak twin of
`Work.BoseBoxFock.boxSlotSum_slotProj1_comm`). -/
private theorem boxSlotSum_slotProj1_comm_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : E3 => star (e l z) * e l' z))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (Θ : (Fin n → E3) → ℂ) (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (i : Fin n) :
    Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotProj1 e i Θ)
      = Work.BoseBoxFock.slotProj1 e i (Work.BoseDict.boxSlotSum e T Θ) := by
  classical
  have hb_of : ∀ (l l' : Fin m) (j : Fin n),
      Measurable (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) ∧
      ∃ C, ∀ x, ‖Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ ≤ C :=
    fun l l' j => Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp
      (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ hΘm hΘb
  -- measurability and boundedness of the inner (`l'`-) sums, for an arbitrary state
  have hinner : ∀ (j : Fin n) (Θ' : (Fin n → E3) → ℂ), Measurable Θ' → (∃ C, ∀ x, ‖Θ' x‖ ≤ C) →
      (∀ l : Fin m, Measurable (∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ')) ∧
      (∀ l : Fin m, ∃ C, ∀ x,
        ‖(∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ') x‖
          ≤ C) := by
    intro j Θ' hΘ'm hΘ'b
    have hone : ∀ (l : Fin m), Measurable (∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ') ∧
        ∃ C, ∀ x, ‖(∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ') x‖ ≤ C :=
      fun l => sum_measurable_bounded
        (fun l' : Fin m => T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ')
        (fun l' => ((Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp
          (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ' hΘ'm hΘ'b).1).const_smul _)
        (fun l' => by
          obtain ⟨C, hC⟩ := (Work.MB.boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp
            (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ' hΘ'm hΘ'b).2
          exact ⟨‖T (Work.BoseB4.evec m l') l‖ * max C 0, fun x => by
            rw [Pi.smul_apply, norm_smul]
            exact mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left _ _))
              (norm_nonneg _)⟩)
    exact ⟨fun l => (hone l).1, fun l => (hone l).2⟩
  -- the per-slot commutation
  have hOpComm : ∀ j : Fin n, Work.BoseBoxFock.slotOp e T j (Work.BoseBoxFock.slotProj1 e i Θ)
      = Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotOp e T j Θ) := by
    intro j
    obtain ⟨hPm, hPb⟩ := slotProj1_mb_weak' hmeas hbdd hsupp i hΘm hΘb
    have hpkg := Work.MB.boxSlotOf_slotProj1_bdd hmeas hbdd hsupp horth hint hΘm hΘb
    have hR : Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotOp e T j Θ)
        = ∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
            Work.BoseBoxFock.slotProj1 e i
              (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
                (Work.BoseB4.evec m l') j Θ) := by
      rw [show Work.BoseBoxFock.slotOp e T j Θ
          = (∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
                (Work.BoseB4.evec m l') j Θ) from rfl]
      rw [slotProj1_sum_weak hmeas hbdd hsupp i
        (fun l => ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
        (fun l => (hinner j Θ hΘm hΘb).1 l) (fun l => (hinner j Θ hΘm hΘb).2 l)]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [slotProj1_sum_smul_weak hmeas hbdd hsupp i
        (fun l' => T (Work.BoseB4.evec m l') l)
        (fun l' => Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
        (fun l' => (hb_of l l' j).1) (fun l' => (hb_of l l' j).2)]
    rw [show Work.BoseBoxFock.slotOp e T j (Work.BoseBoxFock.slotProj1 e i Θ)
        = ∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
              (Work.BoseBoxFock.slotProj1 e i Θ) from rfl, hR]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => ?_))
    by_cases hji : j = i
    · subst hji
      rw [hpkg.1 l l' j, hpkg.2.1 l l' j]
    · rw [hpkg.2.2.1 l l' i j (fun h => hji h.symm)]
  rw [Work.BoseBoxFock.boxSlotSum_eq_sum_slotOp e T (Work.BoseBoxFock.slotProj1 e i Θ),
    Work.BoseBoxFock.boxSlotSum_eq_sum_slotOp e T Θ]
  rw [slotProj1_sum_weak hmeas hbdd hsupp i (fun j => Work.BoseBoxFock.slotOp e T j Θ)
    (fun j => (slotOp_mb_weak hmeas hbdd hsupp T j Θ hΘm hΘb).1)
    (fun j => (slotOp_mb_weak hmeas hbdd hsupp T j Θ hΘm hΘb).2)]
  exact Finset.sum_congr rfl (fun j _ => hOpComm j)

/-! ## 8. The slot sum of the zero state -/

/-- The slot sum of the zero state is zero. -/
private theorem boxSlotSum_zero_bdd {m d : ℕ} (e : Fin m → E3 → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Work.BoseDict.boxSlotSum e T (0 : (Fin d → E3) → ℂ) = 0 := by
  funext x
  simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_eq_zero (fun j _ =>
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun l' _ => ?_)))
  simp [Work.BoseDict.boxSlotOf]

/-! ## 9. The pointwise decoupling -/

/-- **The slot sum of a sector, read at the assembled configuration, is the `↥S`-slot sum of its
slice** (weak twin of `Work.BoseBoxFock.boxSlotSum_pairCoord`). -/
private theorem boxSlotSum_pairCoord_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
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
      = Work.BoseBoxFock.slotSumSub e T S (Work.BoseBoxFock.sectorSlice e S Φ y) u := by
  classical
  obtain ⟨hΘm, hΘb⟩ := slotExact_mb_weak hmeas hbdd hsupp S hΦm hΦb
  rw [boxSlotSum_eq_sum_mem_of_slotProj1_eq_zero_bdd hmeas hbdd hsupp horth hint T S
      (Work.BoseBoxFock.slotExact e S Φ) hΘm hΘb
      (fun j hj => by rw [slotProj1_slotExact_bdd' hmeas hbdd hsupp horth hint S j hΦm hΦb,
        if_neg hj])]
  simp only [Work.BoseBoxFock.slotSumSub, Finset.sum_apply, Pi.smul_apply]
  rw [← Finset.sum_attach S (fun j => ∑ l : Fin m, ∑ l' : Fin m,
      T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
          (Work.BoseBoxFock.slotExact e S Φ) (Work.BoseBoxFock.pairCoord S u y))]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ =>
    Finset.sum_congr rfl (fun l' _ => by rw [Work.BoseBoxFock.boxSlotOf_pairCoord])))

/-- **The pointwise decoupling for a state with no `V`-component outside `S`** (weak twin of
`Work.BoseBoxFock.boxSlotSum_pairCoord_gen`). -/
private theorem boxSlotSum_pairCoord_gen_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : E3 => star (e l z) * e l' z))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n)) (Ψ : (Fin n → E3) → ℂ)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C)
    (hΨ0 : ∀ j : Fin n, j ∉ S → Work.BoseBoxFock.slotProj1 e j Ψ = 0)
    (u : {i // i ∈ S} → E3) (y : {i // i ∉ S} → E3) :
    Work.BoseDict.boxSlotSum e T Ψ (Work.BoseBoxFock.pairCoord S u y)
      = Work.BoseBoxFock.slotSumSub e T S (fun u' => Ψ (Work.BoseBoxFock.pairCoord S u' y)) u := by
  classical
  rw [boxSlotSum_eq_sum_mem_of_slotProj1_eq_zero_bdd hmeas hbdd hsupp horth hint T S Ψ hΨm hΨb hΨ0]
  simp only [Work.BoseBoxFock.slotSumSub, Finset.sum_apply, Pi.smul_apply]
  rw [← Finset.sum_attach S (fun j => ∑ l : Fin m, ∑ l' : Fin m,
      T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ
          (Work.BoseBoxFock.pairCoord S u y))]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ =>
    Finset.sum_congr rfl (fun l' _ => by rw [Work.BoseBoxFock.boxSlotOf_pairCoord_gen])))

/-! ## 10. The target -/

theorem boxSlotSum_comp_pairCoord_ae {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (T₁ T₂ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n))
    (Φ : Work.BoseDict.Xn n → ℂ) (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΦsupp : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ)
    (u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3))
    (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) :
    (Work.BoseDict.boxSlotSum e T₁
        (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)))
      (Work.BoseBoxFock.pairCoord S u y)
      = Work.BoseBoxFock.slotSumSub e T₁ S
          (Work.BoseBoxFock.slotSumSub e T₂ S (Work.BoseBoxFock.sectorSlice e S Φ y)) u := by
  classical
  obtain ⟨hΘm, hΘb⟩ := slotExact_mb_weak hmeas hbdE hsupp S hΦm hΦb
  obtain ⟨hΨm, hΨb, -⟩ :=
    (Work.MB.boxSlotSum_bdd hmeas hbdE hsupp T₂).2 (Work.BoseBoxFock.slotExact e S Φ) hΘm hΘb
  have hΨb' : ∃ C, ∀ x,
      ‖Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ) x‖ ≤ C :=
    hΨb.imp (fun C hC => hC.2)
  have hΨ0 : ∀ j : Fin n, j ∉ S →
      Work.BoseBoxFock.slotProj1 e j
        (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) = 0 := by
    intro j hj
    rw [← boxSlotSum_slotProj1_comm_bdd hmeas hbdE hsupp horth hint T₂
      (Work.BoseBoxFock.slotExact e S Φ) hΘm hΘb j]
    rw [slotProj1_slotExact_bdd' hmeas hbdE hsupp horth hint S j hΦm hΦb, if_neg hj]
    exact boxSlotSum_zero_bdd e T₂
  rw [boxSlotSum_pairCoord_gen_bdd hmeas hbdE hsupp horth hint T₁ S
    (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) hΨm hΨb' hΨ0 u y]
  congr 1
  funext u'
  exact boxSlotSum_pairCoord_bdd hmeas hbdE hsupp horth hint T₂ S Φ hΦm hΦb u' y

end Work.MB

end
