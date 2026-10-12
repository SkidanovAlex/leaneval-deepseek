import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotExact_ae_bounded_of_bounded
import Submission.Work.BoseBoxFock.slotExact_comp
import Submission.Work.BoseBoxFock.slotExact_finsetSum_ae
import Submission.Work.MB.slotProj_comp_weak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.slotSectorWeak` — the sector algebra at the weak mode hypotheses

This module mirrors the strong-mode sector algebra of
`Submission/Work/BoseBoxFock/slotExact_comp.lean` (`sx_absorb`, `sx_proj_comp`, `sx_exact_mb`,
`sx_exact_double`, `sx_exact_comm`, `sx_zero`, `sx_zero_ne`, `sx_lin_exact`) at the *weak* mode
hypotheses that the honest modes of the box ↔ model bridge actually carry:

    `hmeas : ∀ l, Measurable (e l)`,  `hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C`,
    `hsupp : ∀ l, support (e l) ⊆ boxL ℓ`,   `horth : ∀ l l', ∫ star (e l) * e l' = δ`,

with states that are measurable and *everywhere* bounded.  The strong-mode proofs cannot be
reused because they call `slotInt_measurable_bounded`, `slotInt_comp`, `slotInt_peelMB` etc., all
of which require `Continuous`/`HasCompactSupport` modes; those hypotheses are *unsatisfiable* at
the honest modes (`FINDING_continuous_hypotheses_UNSATISFIABLE.md`).

The weak replacements are

* `Work.BoseBoxFock.slotProj_finsetSum_bdd` (linearity of `slotProj` in the state, *pointwise*,
  weak modes, bounded measurable states) — already proved;
* `Work.BoseBoxFock.slotProj_peel_bdd` (the peel identity, pointwise, weak modes) — already
  proved; used by the composition law `Work.MB.slotProj_comp_weak`;
* `Work.MB.slotProj_mb_weak` (measurability and everywhere boundedness of `slotProj`);
* `Work.MB.slotProj_comp_weak` (the composition law `P_S P_T = P_{S ∪ T}`).

Everything is proved pointwise (no a.e. qualifier is needed), because *every* state occurring in
the argument is measurable and everywhere bounded, so all the Bochner integrals involved are
honest.
-/

noncomputable section

namespace Work.MB

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. Auxiliary: `MemLp ⊤` from measurable and everywhere bounded -/

theorem memLp_top_of_measurable_bounded {f : Ω → ℂ} (hm : Measurable f)
    (hb : ∃ C, ∀ x, ‖f x‖ ≤ C) : MemLp f ⊤ (volume : Measure Ω) := by
  obtain ⟨C, hC⟩ := hb
  exact memLp_top_of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-! ## 2. Scalar multiple of the state -/

theorem slotProj_const_mul {m N : ℕ} (e : Fin m → Ω → ℂ) (T : Finset (Fin N))
    (Ψ : (Fin N → Ω) → ℂ) (c : ℂ) :
    Work.BoseBoxFock.slotProj e T (fun y => c * Ψ y)
      = fun x => c * Work.BoseBoxFock.slotProj e T Ψ x := by
  funext x
  simp only [Work.BoseBoxFock.slotProj_eq_slotInt_fun, Work.BoseBoxFock.slotInt]
  rw [show (fun z : (↥T → Ω) =>
        (∏ i : ↥T, Work.BoseBoxFock.PV e (x i.1) (z i)) * (c * Ψ (Function.updateFinset x T z)))
      = (fun z : (↥T → Ω) => c *
          ((∏ i : ↥T, Work.BoseBoxFock.PV e (x i.1) (z i)) *
            Ψ (Function.updateFinset x T z))) from by
    funext z; ring]
  rw [integral_const_mul]

/-! ## 3. Measurability and boundedness of the sectors -/

theorem sx_exact_mb_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Φ : (Fin n → Ω) → ℂ} (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Measurable (Work.BoseBoxFock.slotExact e S Φ)
      ∧ ∃ C, ∀ x, ‖Work.BoseBoxFock.slotExact e S Φ x‖ ≤ C := by
  classical
  have hmeas' : Measurable (Work.BoseBoxFock.slotExact e S Φ) := by
    have hfun : Work.BoseBoxFock.slotExact e S Φ
        = fun a => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            ((-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Φ) a := by
      funext a
      simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply]
    rw [hfun]
    exact Finset.measurable_sum (Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T))
      (fun T _ => (slotProj_mb_weak hmeas hbdE hsupp T hΦm hΦb).1.const_smul
        ((-1 : ℂ) ^ (T.card - S.card)))
  choose K hK using fun T : Finset (Fin n) =>
    (slotProj_mb_weak hmeas hbdE hsupp T hΦm hΦb).2
  refine ⟨hmeas', ∑ T : Finset (Fin n), max (K T) 0, fun x => ?_⟩
  simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc ‖∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
        (-1 : ℂ) ^ (T.card - S.card) * Work.BoseBoxFock.slotProj e T Φ x‖
      ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          ‖(-1 : ℂ) ^ (T.card - S.card) * Work.BoseBoxFock.slotProj e T Φ x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T), max (K T) 0 := by
        refine Finset.sum_le_sum fun T _ => ?_
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact (hK T x).trans (le_max_left _ _)
    _ ≤ ∑ T : Finset (Fin n), max (K T) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => le_max_right _ _)

/-! ## 4. Linearity of a single slot projection and of the sectors -/

theorem slotProj_lin_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : Finset (Fin n)) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {Ψ : ι → (Fin n → Ω) → ℂ} (hΨm : ∀ U, Measurable (Ψ U))
    (hΨb : ∀ U, ∃ C, ∀ x, ‖Ψ U x‖ ≤ C) :
    Work.BoseBoxFock.slotProj e T (fun y => ∑ U ∈ s, c U * Ψ U y)
      = fun x => ∑ U ∈ s, c U * Work.BoseBoxFock.slotProj e T (Ψ U) x := by
  classical
  have hbdd : ∀ l, MemLp (e l) ⊤ (volume : Measure Ω) :=
    fun l => memLp_top_of_measurable_bounded (hmeas l) (hbdE l)
  have h1 := Work.BoseBoxFock.slotProj_finsetSum_bdd (B := Work.BoseK15.corpusBox) e T hbdd hsupp s
    (G := fun U y => c U * Ψ U y)
    (fun U _ => (hΨm U).const_mul _)
    (fun U _ => by
      obtain ⟨C, hC⟩ := hΨb U
      exact ⟨‖c U‖ * max C 0, fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left _ _)) (norm_nonneg _)⟩)
  exact h1.trans (funext fun x => Finset.sum_congr rfl fun U _ =>
    congrFun (slotProj_const_mul e T (Ψ U) (c U)) x)

theorem sx_lin_exact_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {Ψ : ι → (Fin n → Ω) → ℂ} (hΨm : ∀ U, Measurable (Ψ U))
    (hΨb : ∀ U, ∃ C, ∀ x, ‖Ψ U x‖ ≤ C) :
    Work.BoseBoxFock.slotExact e S (fun x => ∑ U ∈ s, c U * Ψ U x)
      = fun x => ∑ U ∈ s, c U * Work.BoseBoxFock.slotExact e S (Ψ U) x := by
  classical
  have hinner : ∀ T : Finset (Fin n),
      Work.BoseBoxFock.slotProj e T (fun y => ∑ U ∈ s, c U * Ψ U y)
        = fun x => ∑ U ∈ s, c U * Work.BoseBoxFock.slotProj e T (Ψ U) x :=
    fun T => slotProj_lin_bdd hmeas hbdE hsupp T s c hΨm hΨb
  funext x
  have hL : Work.BoseBoxFock.slotExact e S (fun x => ∑ U ∈ s, c U * Ψ U x) x
      = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          (-1 : ℂ) ^ (T.card - S.card) *
            (∑ U ∈ s, c U * Work.BoseBoxFock.slotProj e T (Ψ U) x) := by
    simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [congrFun (hinner T) x]
  have hR : (∑ U ∈ s, c U * Work.BoseBoxFock.slotExact e S (Ψ U) x)
      = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          (-1 : ℂ) ^ (T.card - S.card) *
            (∑ U ∈ s, c U * Work.BoseBoxFock.slotProj e T (Ψ U) x) := by
    have hpush : (∑ U ∈ s, c U * Work.BoseBoxFock.slotExact e S (Ψ U) x)
        = ∑ U ∈ s, ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            c U * ((-1 : ℂ) ^ (T.card - S.card) *
              Work.BoseBoxFock.slotProj e T (Ψ U) x) := by
      refine Finset.sum_congr rfl fun U _ => ?_
      rw [show Work.BoseBoxFock.slotExact e S (Ψ U) x
          = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
              (-1 : ℂ) ^ (T.card - S.card) * Work.BoseBoxFock.slotProj e T (Ψ U) x from by
        simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
      rw [Finset.mul_sum]
    rw [hpush, Finset.sum_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U _ => ?_
    ring
  rw [hL, hR]

/-! ## 5. Absorption of a projected slot set -/

theorem sx_absorb_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (A B : Finset (Fin n)) (hAB : A ⊆ B)
    {Φ : (Fin n → Ω) → ℂ} (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj e A (Work.BoseBoxFock.slotExact e B Φ)
      = Work.BoseBoxFock.slotExact e B Φ := by
  classical
  have hmb : ∀ T : Finset (Fin n), Measurable (Work.BoseBoxFock.slotProj e T Φ)
      ∧ ∃ C, ∀ x, ‖Work.BoseBoxFock.slotProj e T Φ x‖ ≤ C :=
    fun T => slotProj_mb_weak hmeas hbdE hsupp T hΦm hΦb
  have hRHS : Work.BoseBoxFock.slotExact e B Φ
      = fun y => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => B ⊆ T),
          (-1 : ℂ) ^ (T.card - B.card) * Work.BoseBoxFock.slotProj e T Φ y := by
    funext y
    simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hlin : Work.BoseBoxFock.slotProj e A
        (fun y => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => B ⊆ T),
          (-1 : ℂ) ^ (T.card - B.card) * Work.BoseBoxFock.slotProj e T Φ y)
      = fun x => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => B ⊆ T),
          (-1 : ℂ) ^ (T.card - B.card) *
            Work.BoseBoxFock.slotProj e A (Work.BoseBoxFock.slotProj e T Φ) x :=
    slotProj_lin_bdd hmeas hbdE hsupp A
      (Finset.univ.filter (fun T : Finset (Fin n) => B ⊆ T))
      (fun T => (-1 : ℂ) ^ (T.card - B.card))
      (fun T => (hmb T).1) (fun T => (hmb T).2)
  rw [hRHS, hlin]
  funext x
  refine Finset.sum_congr rfl fun T hT => ?_
  have hBT : B ⊆ T := (Finset.mem_filter.mp hT).2
  rw [slotProj_comp_weak hmeas hbdE hsupp horth A T hΦm hΦb,
      Finset.union_eq_right.mpr (hAB.trans hBT)]

/-! ## 6. The double-sum expansion of a composition of sectors -/

theorem sx_exact_double_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (A B : Finset (Fin n)) {Φ : (Fin n → Ω) → ℂ} (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (x : Fin n → Ω) :
    Work.BoseBoxFock.slotExact e A (Work.BoseBoxFock.slotExact e B Φ) x =
      ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => A ⊆ T),
        ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => B ⊆ V),
          ((-1 : ℂ) ^ (T.card - A.card) * (-1 : ℂ) ^ (V.card - B.card)) •
            Work.BoseBoxFock.slotProj e (T ∪ V) Φ x := by
  classical
  have hmb : ∀ T : Finset (Fin n), Measurable (Work.BoseBoxFock.slotProj e T Φ)
      ∧ ∃ C, ∀ x, ‖Work.BoseBoxFock.slotProj e T Φ x‖ ≤ C :=
    fun T => slotProj_mb_weak hmeas hbdE hsupp T hΦm hΦb
  have hexp : Work.BoseBoxFock.slotExact e B Φ
      = fun y => ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => B ⊆ V),
          (-1 : ℂ) ^ (V.card - B.card) * Work.BoseBoxFock.slotProj e V Φ y := by
    funext y
    simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : Work.BoseBoxFock.slotExact e A (Work.BoseBoxFock.slotExact e B Φ) x =
      ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => A ⊆ T),
        (-1 : ℂ) ^ (T.card - A.card) •
          Work.BoseBoxFock.slotProj e T (Work.BoseBoxFock.slotExact e B Φ) x := by
    simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply]
  rw [h1]
  refine Finset.sum_congr rfl fun T _ => ?_
  have harg : Work.BoseBoxFock.slotProj e T (Work.BoseBoxFock.slotExact e B Φ)
      = Work.BoseBoxFock.slotProj e T (fun y =>
          ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => B ⊆ V),
            (-1 : ℂ) ^ (V.card - B.card) * Work.BoseBoxFock.slotProj e V Φ y) := by
    rw [hexp]
  rw [harg, congrFun (slotProj_lin_bdd hmeas hbdE hsupp T
      (Finset.univ.filter (fun V : Finset (Fin n) => B ⊆ V))
      (fun V => (-1 : ℂ) ^ (V.card - B.card))
      (fun V => (hmb V).1) (fun V => (hmb V).2)) x,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [slotProj_comp_weak hmeas hbdE hsupp horth T V hΦm hΦb, smul_eq_mul, smul_eq_mul]
  ring

/-! ## 7. The sectors commute -/

theorem sx_exact_comm_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (S S' : Finset (Fin n)) {Φ : (Fin n → Ω) → ℂ} (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Work.BoseBoxFock.slotExact e S (Work.BoseBoxFock.slotExact e S' Φ)
      = Work.BoseBoxFock.slotExact e S' (Work.BoseBoxFock.slotExact e S Φ) := by
  funext x
  calc Work.BoseBoxFock.slotExact e S (Work.BoseBoxFock.slotExact e S' Φ) x
      = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => S' ⊆ V),
            ((-1 : ℂ) ^ (T.card - S.card) * (-1 : ℂ) ^ (V.card - S'.card)) •
              Work.BoseBoxFock.slotProj e (T ∪ V) Φ x :=
        sx_exact_double_weak hmeas hbdE hsupp horth S S' hΦm hΦb x
    _ = ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => S' ⊆ V),
          ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            ((-1 : ℂ) ^ (T.card - S.card) * (-1 : ℂ) ^ (V.card - S'.card)) •
              Work.BoseBoxFock.slotProj e (T ∪ V) Φ x := Finset.sum_comm
    _ = ∑ V ∈ Finset.univ.filter (fun V : Finset (Fin n) => S' ⊆ V),
          ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
            ((-1 : ℂ) ^ (V.card - S'.card) * (-1 : ℂ) ^ (T.card - S.card)) •
              Work.BoseBoxFock.slotProj e (V ∪ T) Φ x := by
        refine Finset.sum_congr rfl fun V _ => Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.union_comm, mul_comm]
    _ = Work.BoseBoxFock.slotExact e S' (Work.BoseBoxFock.slotExact e S Φ) x :=
        (sx_exact_double_weak hmeas hbdE hsupp horth S' S hΦm hΦb x).symm

/-! ## 8. The vanishing of the mixed sectors -/

theorem sx_zero_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (S S' : Finset (Fin n)) {Φ : (Fin n → Ω) → ℂ} (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (i : Fin n) (hiS : i ∉ S) (hiS' : i ∈ S') :
    Work.BoseBoxFock.slotExact e S (Work.BoseBoxFock.slotExact e S' Φ) = 0 := by
  classical
  have hΨm : Measurable (Work.BoseBoxFock.slotExact e S' Φ) :=
    (sx_exact_mb_weak hmeas hbdE hsupp S' hΦm hΦb).1
  have hΨb : ∃ C, ∀ x, ‖Work.BoseBoxFock.slotExact e S' Φ x‖ ≤ C :=
    (sx_exact_mb_weak hmeas hbdE hsupp S' hΦm hΦb).2
  rw [Work.BoseBoxFock.SecAux.slotExact_pair_form e S i hiS (Work.BoseBoxFock.slotExact e S' Φ)]
  refine Finset.sum_eq_zero fun T hT => ?_
  have habs : Work.BoseBoxFock.slotProj e ({i} : Finset (Fin n))
      (Work.BoseBoxFock.slotExact e S' Φ) = Work.BoseBoxFock.slotExact e S' Φ :=
    sx_absorb_weak hmeas hbdE hsupp horth {i} S' (Finset.singleton_subset_iff.mpr hiS')
      hΦm hΦb
  have hsub : Work.BoseBoxFock.slotProj e T (Work.BoseBoxFock.slotExact e S' Φ)
      = Work.BoseBoxFock.slotProj e (insert i T) (Work.BoseBoxFock.slotExact e S' Φ) := by
    calc Work.BoseBoxFock.slotProj e T (Work.BoseBoxFock.slotExact e S' Φ)
        = Work.BoseBoxFock.slotProj e T
            (Work.BoseBoxFock.slotProj e ({i} : Finset (Fin n))
              (Work.BoseBoxFock.slotExact e S' Φ)) := by rw [habs]
      _ = Work.BoseBoxFock.slotProj e (T ∪ ({i} : Finset (Fin n)))
            (Work.BoseBoxFock.slotExact e S' Φ) :=
            slotProj_comp_weak hmeas hbdE hsupp horth T {i} hΨm hΨb
      _ = Work.BoseBoxFock.slotProj e (insert i T) (Work.BoseBoxFock.slotExact e S' Φ) := by
            rw [Finset.union_comm, ← Finset.insert_eq]
  rw [hsub, sub_self, smul_zero]

theorem sx_zero_ne_weak {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (S S' : Finset (Fin n)) {Φ : (Fin n → Ω) → ℂ} (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) (hne : S ≠ S') :
    Work.BoseBoxFock.slotExact e S (Work.BoseBoxFock.slotExact e S' Φ) = 0 := by
  by_cases hsub : S ⊆ S'
  · have hss : S ⊂ S' := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    obtain ⟨i, hiS', hiS⟩ := Finset.exists_of_ssubset hss
    exact sx_zero_weak hmeas hbdE hsupp horth S S' hΦm hΦb i hiS hiS'
  · obtain ⟨i, hiS, hiS'⟩ := Finset.not_subset.mp hsub
    rw [sx_exact_comm_weak hmeas hbdE hsupp horth S S' hΦm hΦb]
    exact sx_zero_weak hmeas hbdE hsupp horth S' S hΦm hΦb i hiS' hiS

end Work.MB
