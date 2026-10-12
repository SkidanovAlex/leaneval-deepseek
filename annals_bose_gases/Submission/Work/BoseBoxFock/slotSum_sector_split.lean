import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSlotOf_slotProj1_comm
import Submission.Work.BoseBoxFock.boxSlotOf_slotProj1_self
import Submission.Work.BoseBoxFock.boxSlotSum_finset_sum
import Submission.Work.BoseBoxFock.boxSlotSum_measurable_bounded
import Submission.Work.BoseBoxFock.slotExact_orth_gen
import Submission.Work.BoseBoxFock.slotProj1_boxSlotOf_self
import Submission.Work.BoseBoxFock.slotProj1_slotExact_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotSum_sector_split` — the first-quantised slot sum splits over the
occupation sectors

For orthonormal modes `e` and a one-body operator `T`, the first-quantised slot sum
`Work.BoseDict.boxSlotSum e T` (the box side of the box ↔ model dictionary) is block diagonal
with respect to the `S`-sector decomposition `slotExact e S` of the state: its quadratic form on
a continuous compactly supported state `Φ` is the sum of the quadratic forms on the sectors.

The proof is the one-slot analysis of the rank-one operators of the slot sum:

* `boxSlotOf_slotProj1_self`, `slotProj1_boxSlotOf_self`: the slot-`j` operator is absorbed by
  (and absorbs) the single-slot projection at slot `j` (`A_j = A_j P_j = P_j A_j`);
* `boxSlotOf_slotProj1_comm`: the slot-`j` operator commutes with the single-slot projection at a
  different slot `i`;
* `slotProj1_slotExact_eq_zero` (`P_i` kills the sector `S` for `i ∉ S`) and `sx_absorb`
  (`P_i` fixes it for `i ∈ S`) identify the sectors as the joint eigenspaces.

Consequently `boxSlotSum e T` commutes with `slotProj1 e i` (a finite sum of the `j`-slot
operators, `boxSlotSum_finset_sum`), so it maps each sector into itself; the sectors are
orthogonal (`slotExact_orth_gen`), which kills every off-diagonal matrix element, and
`boxSlotSum_finset_sum` expands both factors of the quadratic form over the resolution of the
identity `∑_S slotExact e S Φ = Φ` (`slotExact_sum_eq`).
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory
open Work.BoseDict

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

-- ============ MY HELPERS ============

/-- The `j`-th slot operator of `boxSlotSum` (as a function, sums at function level). -/
def slotOp {m d : ℕ} (e : Fin m → Ω → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin d) (Θ : (Fin d → Ω) → ℂ) :
    (Fin d → Ω) → ℂ :=
  ∑ l : Fin m, ∑ l' : Fin m,
    T (Work.BoseB4.evec m l') l •
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ

theorem boxSlotSum_eq_sum_slotOp {m d : ℕ} (e : Fin m → Ω → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : (Fin d → Ω) → ℂ) :
    Work.BoseDict.boxSlotSum e T Θ = ∑ j : Fin d, slotOp e T j Θ := by
  simp only [Work.BoseDict.boxSlotSum, slotOp]

/-- `slotOp` is measurable and bounded. -/
theorem slotOp_measurable_bounded {m d : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin d) (Θ : (Fin d → Ω) → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    Measurable (slotOp e T j Θ) ∧ ∃ C, ∀ x, ‖slotOp e T j Θ x‖ ≤ C := by
  have hbox : ∀ (l l' : Fin m),
      Measurable (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) ∧
        ∃ C, ∀ x, ‖Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
          (Work.BoseB4.evec m l') j Θ x‖ ≤ C :=
    fun l l' => boxSlotOf_measurable_bounded e he hec (Work.BoseB4.evec m l)
      (Work.BoseB4.evec m l') j Θ hΘm hΘb
  constructor
  · have hmeas : Measurable (fun x : Fin d → Ω => ∑ l : Fin m, ∑ l' : Fin m,
        T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x) := by
      refine Finset.measurable_sum _ (fun l _ => ?_)
      refine Finset.measurable_sum _ (fun l' _ => ?_)
      exact ((hbox l l').1).const_smul (T (Work.BoseB4.evec m l') l)
    convert hmeas using 1
    funext x
    simp only [slotOp, Finset.sum_apply, Pi.smul_apply]
  · choose Cb hCb using fun (l l' : Fin m) => (hbox l l').2
    refine ⟨∑ l : Fin m, ∑ l' : Fin m, |T (Work.BoseB4.evec m l') l| * max (Cb l l') 0, fun x => ?_⟩
    have h1 : ‖slotOp e T j Θ x‖ ≤ ∑ l : Fin m, ∑ l' : Fin m,
        ‖T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ := by
      simp only [slotOp, Finset.sum_apply, Pi.smul_apply]
      exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun l _ => norm_sum_le _ _))
    refine le_trans h1 ?_
    refine Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun l' _ => ?_))
    simp only [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hCb l l' x).trans (le_max_left _ _)) (abs_nonneg _)

/-- `boxSlotSum` of the zero state is zero. -/
theorem boxSlotSum_zero {m d : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Work.BoseDict.boxSlotSum e T (fun _ : Fin d → Ω => (0 : ℂ)) = fun _ => 0 := by
  funext x
  simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply]
  simp [Work.BoseDict.boxSlotOf]

/-- `slotProj1` of the zero state is zero. -/
theorem slotProj1_zero {m n : ℕ} (e : Fin m → Ω → ℂ) (i : Fin n) :
    slotProj1 e i (fun _ : Fin n → Ω => (0 : ℂ)) = fun _ => 0 := by
  funext x
  simp only [slotProj1]
  simp

/-- Homogeneity of `slotProj1`. -/
theorem slotProj1_smul {m n : ℕ} (e : Fin m → Ω → ℂ) (i : Fin n) (c : ℝ)
    (Ψ : (Fin n → Ω) → ℂ) : slotProj1 e i (c • Ψ) = c • slotProj1 e i Ψ := by
  funext x
  simp only [slotProj1, Pi.smul_apply]
  rw [show (fun w : Ω => PV e (x i) w * (c • Ψ (Function.update x i w)))
      = (fun w : Ω => c • (PV e (x i) w * Ψ (Function.update x i w))) from
    funext fun w => mul_smul_comm c (PV e (x i) w) (Ψ (Function.update x i w))]
  rw [integral_smul]

/-- Linearity of `slotProj1 e i` over finite sums (function level). -/
theorem slotProj1_finset_sum_fun {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l)) (i : Fin n)
    {ι : Type*} (s : Finset ι) (Ψ : ι → (Fin n → Ω) → ℂ)
    (hΨm : ∀ U, Measurable (Ψ U)) (hΨb : ∀ U, ∃ C, ∀ x, ‖Ψ U x‖ ≤ C) :
    slotProj1 e i (∑ U ∈ s, Ψ U) = ∑ U ∈ s, slotProj1 e i (Ψ U) := by
  funext x
  rw [slotProj1, Finset.sum_apply]
  rw [show (fun w : Ω => PV e (x i) w * (∑ U ∈ s, Ψ U) (Function.update x i w))
      = (fun w : Ω => ∑ U ∈ s, (PV e (x i) w * Ψ U (Function.update x i w))) from by
    funext w
    rw [Finset.sum_apply, Finset.mul_sum]]
  rw [integral_finsetSum]
  swap
  · intro U _
    exact integrable_mul_of_continuous_hasCompactSupport_of_bounded
      (continuous_PV_snd e he (x i)) (hasCompactSupport_PV_snd e hec (x i))
      (((hΨm U).comp (measurable_update (f := x) (a := i))).aestronglyMeasurable)
      ((hΨb U).imp (fun C hC w => hC _))
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [slotProj1]

/-- Linearity of `slotProj1 e i` over finite `ℝ`-linear combinations (function level). -/
theorem slotProj1_finset_sum_smul {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l)) (i : Fin n)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Ψ : ι → (Fin n → Ω) → ℂ)
    (hΨm : ∀ U, Measurable (Ψ U)) (hΨb : ∀ U, ∃ C, ∀ x, ‖Ψ U x‖ ≤ C) :
    slotProj1 e i (∑ U ∈ s, c U • Ψ U) = ∑ U ∈ s, c U • slotProj1 e i (Ψ U) := by
  funext x
  rw [slotProj1, Finset.sum_apply]
  simp only [Pi.smul_apply]
  rw [show (fun w : Ω => PV e (x i) w * (∑ U ∈ s, c U • Ψ U) (Function.update x i w))
      = (fun w : Ω => ∑ U ∈ s, c U • (PV e (x i) w * Ψ U (Function.update x i w))) from by
    funext w
    rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    rw [Pi.smul_apply, mul_smul_comm]]
  rw [integral_finsetSum]
  swap
  · intro U _
    exact (integrable_mul_of_continuous_hasCompactSupport_of_bounded
      (continuous_PV_snd e he (x i)) (hasCompactSupport_PV_snd e hec (x i))
      (((hΨm U).comp (measurable_update (f := x) (a := i))).aestronglyMeasurable)
      ((hΨb U).imp (fun C hC w => hC _))).smul (c U)
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [integral_smul, slotProj1]

/-- The singleton slot projection is the single-slot projection.

**Name note.**  `Submission/Work/BoseBoxFock/slotProj1_memLp_top.lean` proves the *unconditional*
version of this identity under the name `slotProj_singleton_eq_slotProj1`; the two declarations
cannot coexist in one import cone.  This one is therefore named `..._cont` (it needs the
continuity/compact-support/measurability data); the unconditional one is strictly stronger and
should eventually replace it — but that would add `slotProj1_memLp_top` to this file's cone. -/
theorem slotProj_singleton_eq_slotProj1_cont {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (i : Fin n) (Θ : (Fin n → Ω) → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    slotProj e ({i} : Finset (Fin n)) Θ = slotProj1 e i Θ := by
  have h := slotInt_peelMB e he hec (S := (∅ : Finset (Fin n))) (i := i) (by simp) Θ hΘm hΘb
  rw [Finset.empty_union, slotInt_empty] at h
  rw [slotProj_eq_slotInt_fun]
  exact h

-- ============ MAIN ============

theorem slotSum_sector_split {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) :
    ∫ x, star (Φ x) * Work.BoseDict.boxSlotSum e T Φ x
      = ∑ S : Finset (Fin n), ∫ x, star (Work.BoseBoxFock.slotExact e S Φ x)
          * Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φ) x := by
  classical
  have hΦm : Measurable Φ := hΦ.measurable
  have hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C := hΦ.bounded_above_of_compact_support hΦc
  have hsec : ∀ S : Finset (Fin n),
      Measurable (slotExact e S Φ) ∧ (∃ C, ∀ x, ‖slotExact e S Φ x‖ ≤ C) ∧
        HasCompactSupport (slotExact e S Φ) :=
    fun S => slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  have hAsec : ∀ S : Finset (Fin n),
      Measurable (boxSlotSum e T (slotExact e S Φ)) ∧
        (∃ C, ∀ x, ‖boxSlotSum e T (slotExact e S Φ) x‖ ≤ C) :=
    fun S => boxSlotSum_measurable_bounded e he hec T (slotExact e S Φ) (hsec S).1 (hsec S).2.1
  -- (1) pointwise: boxSlotSum e T Φ = Σ_S boxSlotSum e T (slotExact e S Φ)
  have hApt : ∀ x, boxSlotSum e T Φ x
      = ∑ S : Finset (Fin n), boxSlotSum e T (slotExact e S Φ) x := by
    intro x
    have hsum : (fun y : Fin n → Ω =>
        Finset.sum Finset.univ (fun S : Finset (Fin n) => (1 : ℂ) • slotExact e S Φ y)) = Φ := by
      funext y
      have h1 : (Finset.sum Finset.univ (fun S : Finset (Fin n) => slotExact e S Φ)) y = Φ y :=
        congrFun (slotExact_sum_eq e Φ) y
      simpa only [one_smul, Finset.sum_apply] using h1
    have h1 : boxSlotSum e T Φ
        = boxSlotSum e T (fun y : Fin n → Ω =>
            Finset.sum Finset.univ (fun S : Finset (Fin n) => (1 : ℂ) • slotExact e S Φ y)) :=
      congrArg (fun Ψ => boxSlotSum e T Ψ) hsum.symm
    have h2 := boxSlotSum_finset_sum e he hec T Finset.univ (fun _ => (1 : ℂ))
      (fun S => slotExact e S Φ) (fun S => (hsec S).1) (fun S => (hsec S).2.1)
    rw [h1, h2]
    simp
  -- (2) commutation of boxSlotSum with the single-slot projection
  have hcommA : ∀ (Θ : (Fin n → Ω) → ℂ), Measurable Θ → (∃ C, ∀ x, ‖Θ x‖ ≤ C) →
      ∀ i : Fin n, slotProj1 e i (boxSlotSum e T Θ) = boxSlotSum e T (slotProj1 e i Θ) := by
    intro Θ hΘm hΘb i
    have hbox : ∀ (l l' : Fin m) (j : Fin n),
        Measurable (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) ∧
          ∃ C, ∀ x, ‖Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
            (Work.BoseB4.evec m l') j Θ x‖ ≤ C :=
      fun l l' j => boxSlotOf_measurable_bounded e he hec (Work.BoseB4.evec m l)
        (Work.BoseB4.evec m l') j Θ hΘm hΘb
    have hOpComm : ∀ j : Fin n, slotProj1 e i (slotOp e T j Θ) = slotOp e T j (slotProj1 e i Θ) := by
      intro j
      have hinner : ∀ (l : Fin m),
          Measurable (∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
          ∧ ∃ C, ∀ x, ‖(∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) x‖ ≤ C := by
        intro l
        constructor
        · have hmeas : Measurable (fun x : Fin n → Ω => ∑ l' : Fin m,
              T (Work.BoseB4.evec m l') l •
                Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x) := by
            refine Finset.measurable_sum _ (fun l' _ => ?_)
            exact ((hbox l l' j).1).const_smul (T (Work.BoseB4.evec m l') l)
          convert hmeas using 1
          funext x
          simp only [Finset.sum_apply, Pi.smul_apply]
        · choose Cb hCb using fun l' : Fin m => (hbox l l' j).2
          refine ⟨∑ l' : Fin m, |T (Work.BoseB4.evec m l') l| * max (Cb l') 0, fun x => ?_⟩
          rw [Finset.sum_apply]
          refine le_trans (norm_sum_le _ _) ?_
          refine Finset.sum_le_sum (fun l' _ => ?_)
          simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left ((hCb l' x).trans (le_max_left _ _)) (abs_nonneg _)
      have hL : slotProj1 e i (slotOp e T j Θ)
          = ∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
              slotProj1 e i (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
                (Work.BoseB4.evec m l') j Θ) := by
        rw [slotOp]
        rw [slotProj1_finset_sum_fun e he hec i Finset.univ
          (fun l => ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
          (fun l => (hinner l).1) (fun l => (hinner l).2)]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [slotProj1_finset_sum_smul e he hec i Finset.univ
          (fun l' : Fin m => T (Work.BoseB4.evec m l') l)
          (fun l' => Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
          (fun l' => (hbox l l' j).1) (fun l' => (hbox l l' j).2)]
      have hR : slotOp e T j (slotProj1 e i Θ)
          = ∑ l : Fin m, ∑ l' : Fin m, T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
                (slotProj1 e i Θ) := rfl
      rw [hL, hR]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      refine Finset.sum_congr rfl (fun l' _ => ?_)
      by_cases hji : j = i
      · subst hji
        rw [slotProj1_boxSlotOf_self e l l' j he hec horth hint Θ hΘm hΘb]
        rw [boxSlotOf_slotProj1_self e l l' j he hec horth hint Θ hΘm hΘb]
      · rw [← boxSlotOf_slotProj1_comm e l l' i j (fun h => hji h.symm) he hec horth hint
          Θ hΘm hΘb]
    have hOp_m : ∀ j : Fin n, Measurable (slotOp e T j Θ) :=
      fun j => (slotOp_measurable_bounded e he hec T j Θ hΘm hΘb).1
    have hOp_b : ∀ j : Fin n, ∃ C, ∀ x, ‖slotOp e T j Θ x‖ ≤ C :=
      fun j => (slotOp_measurable_bounded e he hec T j Θ hΘm hΘb).2
    rw [boxSlotSum_eq_sum_slotOp e T Θ, boxSlotSum_eq_sum_slotOp e T (slotProj1 e i Θ),
      slotProj1_finset_sum_fun e he hec i Finset.univ (fun j => slotOp e T j Θ) hOp_m hOp_b]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hOpComm j]
  -- (3) the sector projection fixes `boxSlotSum e T (slotExact e S' Φ)`
  have hkey : ∀ (S' : Finset (Fin n)) (Υ : (Fin n → Ω) → ℂ), Measurable Υ →
      (∃ C, ∀ x, ‖Υ x‖ ≤ C) →
      (∀ i : Fin n, slotProj1 e i Υ = if i ∈ S' then Υ else 0) → slotExact e S' Υ = Υ := by
    intro S' Υ hΥm hΥb hiii
    have hclass : ∀ T : Finset (Fin n), slotProj e T Υ = if T ⊆ S' then Υ else 0 := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        rw [if_pos (Finset.empty_subset S')]
        rw [slotProj_eq_slotInt_fun]
        exact slotInt_empty e Υ
      | insert a T' ha ih =>
        have hpeel : slotProj e (insert a T') Υ = slotProj1 e a (slotProj e T' Υ) := by
          have h := slotInt_peelMB e he hec (S := T') (i := a) ha Υ hΥm hΥb
          rw [Finset.union_singleton] at h
          rw [slotProj_eq_slotInt_fun]
          exact h
        rw [hpeel, ih]
        by_cases hTS : T' ⊆ S'
        · by_cases haS : a ∈ S'
          · have hins : insert a T' ⊆ S' := Finset.insert_subset haS hTS
            rw [if_pos hTS, hiii a, if_pos haS, if_pos hins]
          · have hins : ¬ (insert a T' ⊆ S') := fun hc => haS (Finset.insert_subset_iff.mp hc).1
            rw [if_pos hTS, hiii a, if_neg haS, if_neg hins]
        · have hins : ¬ (insert a T' ⊆ S') := fun hc => hTS (Finset.insert_subset_iff.mp hc).2
          rw [if_neg hTS, if_neg hins]
          exact slotProj1_zero e a
    have hexp : slotExact e S' Υ = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S' ⊆ T),
        (-1 : ℂ) ^ (T.card - S'.card) • slotProj e T Υ := rfl
    rw [hexp]
    rw [Finset.sum_eq_single S']
    · rw [hclass S', if_pos (Finset.Subset.refl S')]
      simp
    · intro T hT hTS
      rw [hclass T,
        if_neg (fun hc => hTS (Finset.Subset.antisymm hc (Finset.mem_filter.mp hT).2)), smul_zero]
    · intro hmem
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ S', Finset.Subset.refl S'⟩) hmem
  have hfix : ∀ S' : Finset (Fin n),
      slotExact e S' (boxSlotSum e T (slotExact e S' Φ)) = boxSlotSum e T (slotExact e S' Φ) := by
    intro S'
    refine hkey S' (boxSlotSum e T (slotExact e S' Φ)) (hAsec S').1 (hAsec S').2 ?_
    intro i
    rw [hcommA (slotExact e S' Φ) (hsec S').1 (hsec S').2.1 i]
    by_cases hi : i ∈ S'
    · rw [if_pos hi]
      have hfix1 : slotProj1 e i (slotExact e S' Φ) = slotExact e S' Φ := by
        rw [← slotProj_singleton_eq_slotProj1_cont e he hec i (slotExact e S' Φ) (hsec S').1
          (hsec S').2.1]
        exact sx_absorb e he hec horth {i} S' (Finset.singleton_subset_iff.mpr hi) Φ hΦm hΦb
      rw [hfix1]
    · rw [if_neg hi]
      have hfix0 : slotProj1 e i (slotExact e S' Φ) = 0 :=
        slotProj1_slotExact_eq_zero e he hec horth S' i hi Φ hΦm hΦb
      rw [hfix0]
      exact boxSlotSum_zero e he hec T
  -- (4) off-diagonal vanishing
  have hOD : ∀ S S' : Finset (Fin n), S ≠ S' →
      ∫ x, star (slotExact e S Φ x) * boxSlotSum e T (slotExact e S' Φ) x = 0 := by
    intro S S' hne
    have h := slotExact_orth_gen e he hec horth S S' Φ hΦ hΦc
      (boxSlotSum e T (slotExact e S' Φ)) (hAsec S').1 (hAsec S').2
    rw [hfix S'] at h
    rw [h, if_neg hne]
  -- (5) expand the LHS into the double sector sum
  have hL : ∫ x, star (Φ x) * boxSlotSum e T Φ x
      = ∑ S : Finset (Fin n), ∑ S' : Finset (Fin n),
          ∫ x, star (slotExact e S Φ x) * boxSlotSum e T (slotExact e S' Φ) x := by
    have hpt : ∀ x, star (Φ x) * boxSlotSum e T Φ x
        = star (∑ S : Finset (Fin n), slotExact e S Φ x)
          * (∑ S' : Finset (Fin n), boxSlotSum e T (slotExact e S' Φ) x) := by
      intro x
      have h1 : (Finset.sum Finset.univ (fun S : Finset (Fin n) => slotExact e S Φ x)) = Φ x := by
        have h2 : (Finset.sum Finset.univ (fun S : Finset (Fin n) => slotExact e S Φ)) x = Φ x :=
          congrFun (slotExact_sum_eq e Φ) x
        simpa only [Finset.sum_apply] using h2
      rw [h1, hApt x]
    rw [show (∫ x, star (Φ x) * boxSlotSum e T Φ x)
        = ∫ x, star (∑ S : Finset (Fin n), slotExact e S Φ x)
            * (∑ S' : Finset (Fin n), boxSlotSum e T (slotExact e S' Φ) x) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_star_sum_mul_sum (Finset.univ : Finset (Finset (Fin n))) Finset.univ
      (fun S => slotExact e S Φ) (fun S' => boxSlotSum e T (slotExact e S' Φ))
      (fun S => (hsec S).2.2) (fun S => (hsec S).1) (fun S => (hsec S).2.1)
      (fun S => (hAsec S).1) (fun S => (hAsec S).2)]
  rw [hL]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_eq_single S]
  · intro S' _ hS'
    exact hOD S S' (fun h => hS' h.symm)
  · intro hS
    exact absurd (Finset.mem_univ S) hS

end Work.BoseBoxFock
