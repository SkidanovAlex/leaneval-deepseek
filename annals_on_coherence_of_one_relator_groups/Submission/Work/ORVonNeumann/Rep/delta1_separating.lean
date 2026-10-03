/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# `delta1` is separating for the group von Neumann algebra `N(G)`

The trace-form vector state on `N(G) = rho(G)'` (the commutant of the *right* regular
representation, `Work.ORVonNeumann.groupVonNeumann`) is `tau a = <a d1, d1>`.  It is faithful:
if `a d1 = 0` then `a = 0`.

The proof is elementary and does not need any von Neumann algebra closure argument.  Write
`d_g` for the indicator of the singleton `{g}` (`deltaG` below), so that `d_1` is
`Work.ORVonNeumann.delta1`.  The right translation operator `rho h` sends `d_1` to `d_{h^-1}`
(`rightRegOp_inv_delta1`).  Hence, for `T` in `N(G)`, i.e. `T` commuting with every `rho h`,

  `T d_g = T (rho (g^-1) d_1) = rho (g^-1) (T d_1) = 0`.

So `T` kills every basis vector `d_g` of `l2(G)`.  The span of the `d_g` is `Lp.simpleFunc`, a
dense subspace of `l2(G)`, so `T` vanishes on the whole of `l2(G)`: the induction principle
`MeasureTheory.Lp.induction` reduces to the case of `indicatorConstLp`, which is a finite sum of
the `d_g` (`indicatorConstLp_eq_sum_smul_deltaG`), together with closedness of the zero set
(`T` is continuous).  The identification `indicatorConstLp = sum of c . d_g` is proved pointwise;
for the counting measure on a countable type, equality a.e. is pointwise equality
(`MeasureTheory.Measure.ae_count_iff`).

## Main result

* `Work.ORVonNeumann.Rep.delta1_separating` -- `d_1` is separating for `N(G)`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann
import Submission.Work.ORVonNeumann.Rep.exists_rightRegular

namespace Work.ORVonNeumann.Rep

open MeasureTheory

-- the helper lemmas below share one `variable` block, so some of them do not mention
-- every instance variable of the block; this is intended, not dead code.
set_option linter.unusedSectionVars false

section Helpers

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The basis vector `d_g` in `l2(G)`, the indicator function of `{g}`, for `g : G`.
`deltaG 1` is `Work.ORVonNeumann.delta1`. -/
noncomputable def deltaG (g : G) : l2 G :=
  MeasureTheory.indicatorConstLp 2 (MeasurableSet.singleton g)
    (by rw [MeasureTheory.Measure.count_singleton]; exact ENNReal.one_ne_top) 1

/-- The coefficient function of `deltaG g` is the indicator function of `{g}`. -/
theorem deltaG_coeFn (g : G) : (deltaG g : G → ℂ) =ᵐ[(Measure.count : Measure G)]
    ({g} : Set G).indicator (fun _ => (1 : ℂ)) :=
  MeasureTheory.indicatorConstLp_coeFn

/-- The value of `deltaG g` at `g` is `1`. -/
theorem deltaG_apply_self (g : G) : (deltaG g : G → ℂ) g = 1 := by
  have h := MeasureTheory.Measure.ae_count_iff.mp (deltaG_coeFn (G := G) g)
  rw [h]
  simp

/-- The value of `deltaG g` away from `g` is `0`. -/
theorem deltaG_apply_of_ne {g x : G} (hx : x ≠ g) : (deltaG g : G → ℂ) x = 0 := by
  have h := MeasureTheory.Measure.ae_count_iff.mp (deltaG_coeFn (G := G) g)
  rw [h, Set.indicator_of_notMem (by simpa [Set.mem_singleton_iff] using hx)]

/-- `Work.ORVonNeumann.delta1` is `deltaG 1`. -/
theorem delta1_coeFn : (Work.ORVonNeumann.delta1 G : G → ℂ) =ᵐ[(Measure.count : Measure G)]
    ({1} : Set G).indicator (fun _ => (1 : ℂ)) :=
  deltaG_coeFn (1 : G)

/-- The right translation `rho g^-1` sends `d_1` to `d_g`. -/
theorem rightRegOp_inv_delta1 (g : G) :
    rightRegOp g⁻¹ (Work.ORVonNeumann.delta1 G) = deltaG g := by
  classical
  refine MeasureTheory.Lp.ext ?_
  rw [Filter.EventuallyEq, MeasureTheory.Measure.ae_count_iff]
  intro x
  rw [rightRegOp_apply]
  have hA : (MeasureTheory.Lp.compMeasurePreserving (fun h : G => h * g⁻¹)
      (MeasureTheory.measurePreserving_mul_right
        (MeasureTheory.Measure.count : MeasureTheory.Measure G) g⁻¹)
      (Work.ORVonNeumann.delta1 G) : G → ℂ) x
      = (Work.ORVonNeumann.delta1 G : G → ℂ) (x * g⁻¹) :=
    MeasureTheory.Measure.ae_count_iff.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving
      (μ := (MeasureTheory.Measure.count : Measure G))
      (μb := (MeasureTheory.Measure.count : Measure G))
      (f := (fun h : G => h * g⁻¹)) (Work.ORVonNeumann.delta1 G)
      (MeasureTheory.measurePreserving_mul_right
        (MeasureTheory.Measure.count : MeasureTheory.Measure G) g⁻¹)) x
  rw [hA]
  have hB := MeasureTheory.Measure.ae_count_iff.mp delta1_coeFn (x * g⁻¹)
  have hC := MeasureTheory.Measure.ae_count_iff.mp (deltaG_coeFn (G := G) g) x
  rw [hB, hC]
  by_cases hx : x = g
  · subst hx
    simp
  · have h1 : (x * g⁻¹) ∉ ({1} : Set G) := by
      simp only [Set.mem_singleton_iff]
      exact fun hh => hx (mul_inv_eq_one.mp hh)
    have h2 : x ∉ ({g} : Set G) := by simpa [Set.mem_singleton_iff] using hx
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

/-- Every element `T` of `N(G)` with `T d_1 = 0` kills every basis vector `d_g`. -/
theorem apply_deltaG_eq_zero (T : Work.ORVonNeumann.groupVonNeumann G)
    (hT : (T : Work.ORVonNeumann.boundedEnd G) (Work.ORVonNeumann.delta1 G) = 0) (g : G) :
    (T : Work.ORVonNeumann.boundedEnd G) (deltaG g) = 0 := by
  have hcomm := (Work.ORVonNeumann.mem_groupVonNeumann_iff (G := G)
    (T : Work.ORVonNeumann.boundedEnd G)).mp T.2 g⁻¹
  have h1 : (T : Work.ORVonNeumann.boundedEnd G)
      (rightRegOp g⁻¹ (Work.ORVonNeumann.delta1 G))
      = rightRegOp g⁻¹ ((T : Work.ORVonNeumann.boundedEnd G) (Work.ORVonNeumann.delta1 G)) := by
    simpa [mul_apply_eq_comp, rightRegHom] using congrArg (fun S : Work.ORVonNeumann.boundedEnd G =>
      S (Work.ORVonNeumann.delta1 G)) hcomm
  rw [hT, map_zero] at h1
  rwa [rightRegOp_inv_delta1] at h1

/-- A multiple of the indicator of a finite-measure set is the corresponding finite sum of the
basis vectors `deltaG g`.  (For the counting measure every measurable set of finite measure is
finite, so `indicatorConstLp` is a finite combination of the `deltaG g`.) -/
theorem indicatorConstLp_eq_sum_smul_deltaG {s : Set G} (hs : MeasurableSet s)
    (hμs : (Measure.count : Measure G) s ≠ ⊤) (c : ℂ) {t : Finset G} (ht : (↑t : Set G) = s) :
    MeasureTheory.indicatorConstLp 2 hs hμs c = ∑ g ∈ t, c • deltaG g := by
  classical
  refine MeasureTheory.Lp.ext ?_
  rw [Filter.EventuallyEq, MeasureTheory.Measure.ae_count_iff]
  intro x
  have hL := MeasureTheory.Measure.ae_count_iff.mp (MeasureTheory.indicatorConstLp_coeFn
    (p := 2) (μ := (MeasureTheory.Measure.count : Measure G)) (hs := hs) (hμs := hμs) (c := c)) x
  have hR := MeasureTheory.Measure.ae_count_iff.mp
    (MeasureTheory.Lp.coeFn_fun_finsetSum t (fun g => c • deltaG g)) x
  simp only [hL, hR]
  have hsum : ∑ g ∈ t, (c • deltaG g : l2 G) x
      = ∑ g ∈ t, c * (if x = g then (1 : ℂ) else 0) := by
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [MeasureTheory.Measure.ae_count_iff.mp (MeasureTheory.Lp.coeFn_smul c (deltaG g)) x,
      Pi.smul_apply, smul_eq_mul]
    congr 1
    by_cases h : x = g
    · rw [if_pos h, h, deltaG_apply_self]
    · rw [if_neg h, deltaG_apply_of_ne h]
  rw [hsum, Finset.sum_congr rfl (fun g _ => by rw [mul_ite, mul_one, mul_zero]),
    Finset.sum_ite_eq t x (fun _ => c), Set.indicator_apply, ← ht]
  simp

end Helpers

theorem delta1_separating {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (T : Work.ORVonNeumann.groupVonNeumann G) (h : (T : Work.ORVonNeumann.boundedEnd G) (Work.ORVonNeumann.delta1 G) = 0) : T = 0 := by
  have hdelta : ∀ g : G, (T : Work.ORVonNeumann.boundedEnd G) (deltaG g) = 0 :=
    apply_deltaG_eq_zero T h
  -- `T` kills every `indicatorConstLp` over a set of finite measure.
  have hInd : ∀ (c : ℂ) {s : Set G} (hs : MeasurableSet s)
      (hμs : (Measure.count : Measure G) s < ⊤),
      (T : Work.ORVonNeumann.boundedEnd G)
        (MeasureTheory.Lp.simpleFunc.indicatorConst 2 hs hμs.ne c) = 0 := by
    intro c s hs hμs
    have hfin : s.Finite := MeasureTheory.Measure.count_apply_lt_top.mp hμs
    rw [MeasureTheory.Lp.simpleFunc.coe_indicatorConst,
      indicatorConstLp_eq_sum_smul_deltaG hs hμs.ne c hfin.coe_toFinset, map_sum]
    refine Finset.sum_eq_zero (fun g _ => ?_)
    rw [map_smul, hdelta g, smul_zero]
  -- hence `T` kills the dense subspace of simple functions and, by continuity, all of `l2(G)`
  have key : ∀ f : l2 G, (T : Work.ORVonNeumann.boundedEnd G) f = 0 := by
    intro f
    exact MeasureTheory.Lp.induction (p := 2) (E := ℂ)
      (μ := (MeasureTheory.Measure.count : Measure G)) (by norm_num)
      (fun f => (T : Work.ORVonNeumann.boundedEnd G) f = 0) hInd (by
        intro f g _ _ _ hf0 hg0
        rw [map_add, hf0, hg0, add_zero]) (by
        have hset : {f : l2 G | (T : Work.ORVonNeumann.boundedEnd G) f = 0}
            = (T : Work.ORVonNeumann.boundedEnd G) ⁻¹' ({0} : Set (l2 G)) := rfl
        rw [hset]
        exact isClosed_singleton.preimage (T : Work.ORVonNeumann.boundedEnd G).continuous) f
  refine Subtype.ext ?_
  exact ContinuousLinearMap.ext fun f => key f

end Work.ORVonNeumann.Rep
