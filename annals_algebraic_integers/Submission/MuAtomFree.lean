import Submission.Serre
import Submission.SerreExample
import Submission.EquilibriumMeasure

/-!
# Atom-freeness of Serre's measure (C1a)

`μ = serreMeasure gSerre aSerre bSerre` is a convex combination of two
pushforwards of `uniform01` (Lebesgue on `(0,1]`) under the real-analytic
chart `u ↦ (c+d)/2 + (d−c)/2·cos(πu)` (for `μ_eq`) and under inversion of the
reciprocal chart (for `ν`).  The chart is strictly monotone on `(0,1]`
(`cos` is strictly decreasing on `[0,π]`), so the preimage of a point under
each of these maps is a finite set, whose Lebesgue measure is zero.  Hence
every singleton has measure zero, i.e. `μ` is atom-free.

Deliverable: `Submission.MuAtomFree.serre_atom_free`.
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal

namespace Submission.MuAtomFree

open Submission.Equilibrium
open Submission.Serre
open Submission.SerreExample

/-- The chart `u ↦ (c+d)/2 + (d−c)/2·cos(πu)` is injective on `(0,1]`
(for `c < d`, so the cosine factor is nonconstant). -/
lemma chart_injOn_Ioc {a b : ℝ} (hab : a < b) : Set.InjOn (chart a b) (Set.Ioc (0 : ℝ) 1) := by
  intro u hu v hv huv
  have hne : (b - a) / 2 ≠ 0 := by linarith
  have hdiff : chart a b u - chart a b v = 0 := by
    rw [huv]
    ring
  have hfac : chart a b u - chart a b v =
      (b - a) / 2 * (Real.cos (Real.pi * u) - Real.cos (Real.pi * v)) := by
    unfold chart
    ring
  have hz' : (b - a) / 2 * (Real.cos (Real.pi * u) - Real.cos (Real.pi * v)) = 0 := by
    rw [← hfac]
    exact hdiff
  have hcos : Real.cos (Real.pi * u) = Real.cos (Real.pi * v) := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left hne)
  have hcosinj : Set.InjOn Real.cos (Set.Icc (0 : ℝ) π) := Real.strictAntiOn_cos.injOn
  have hpu : Real.pi * u ∈ Set.Icc (0 : ℝ) π := by
    constructor
    · exact le_of_lt (mul_pos Real.pi_pos hu.1)
    · have : Real.pi * u ≤ Real.pi * 1 :=
        mul_le_mul_of_nonneg_left hu.2 (le_of_lt Real.pi_pos)
      simpa using this
  have hpv : Real.pi * v ∈ Set.Icc (0 : ℝ) π := by
    constructor
    · exact le_of_lt (mul_pos Real.pi_pos hv.1)
    · have : Real.pi * v ≤ Real.pi * 1 :=
        mul_le_mul_of_nonneg_left hv.2 (le_of_lt Real.pi_pos)
      simpa using this
  have hpi : Real.pi * u = Real.pi * v := hcosinj hpu hpv hcos
  exact mul_left_cancel₀ Real.pi_ne_zero hpi

/-- The equilibrium measure of `[a,b]` has zero mass on every singleton
(needs `a < b`: the chart is nonconstant). -/
lemma equilibrium_singleton_zero {a b : ℝ} (hab : a < b) (x : ℝ) :
    equilibrium a b {x} = 0 := by
  rw [equilibrium, uniform01]
  rw [Measure.map_apply (chart_measurable a b) (measurableSet_singleton x)]
  rw [Measure.restrict_apply ((chart_measurable a b) (measurableSet_singleton x))]
  -- the preimage of a point inside `(0,1]` has at most one element
  have hsub : (((chart a b) ⁻¹' ({x} : Set ℝ)) ∩ Set.Ioc (0 : ℝ) 1).Subsingleton := by
    intro u hu v hv
    exact chart_injOn_Ioc hab hu.2 hv.2 (by rw [hu.1, hv.1])
  exact hsub.measure_zero (volume : Measure ℝ)

/-- The inversion `t ↦ t⁻¹` has singleton preimages which are singletons. -/
lemma invMap_preimage_singleton (r : ℝ) : invMap ⁻¹' ({r} : Set ℝ) = ({r⁻¹} : Set ℝ) := by
  ext x
  constructor
  · intro hx
    have hxr : x⁻¹ = r := by simpa [invMap] using hx
    calc
      x = (x⁻¹)⁻¹ := by rw [inv_inv]
      _ = r⁻¹ := by rw [hxr]
  · intro hx
    have hxr : x = r⁻¹ := by simpa using hx
    calc
      x⁻¹ = (r⁻¹)⁻¹ := by rw [hxr]
      _ = r := by rw [inv_inv]

/-- Serre's `ν` measure on `[a,b]` has zero mass on every singleton
(needs `0 < a < b`). -/
lemma nu_singleton_zero {a b : ℝ} (ha : 0 < a) (hab : a < b) (x : ℝ) :
    nu a b {x} = 0 := by
  rw [nu]
  rw [Measure.map_apply invMap_measurable (measurableSet_singleton x)]
  rw [invMap_preimage_singleton x]
  have hb : 0 < b := lt_trans ha hab
  have hba : b⁻¹ < a⁻¹ := (inv_lt_inv₀ (a := b) (b := a) hb ha).2 hab
  exact equilibrium_singleton_zero hba (x⁻¹)

/-- Serre's measure is atom-free. -/
lemma serre_atom_free (r : ℝ) : serreMeasure gSerre aSerre bSerre {r} = 0 := by
  rw [serreMeasure]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [nu_singleton_zero aSerre_pos a_lt_b r]
  rw [equilibrium_singleton_zero a_lt_b r]
  simp

end Submission.MuAtomFree
