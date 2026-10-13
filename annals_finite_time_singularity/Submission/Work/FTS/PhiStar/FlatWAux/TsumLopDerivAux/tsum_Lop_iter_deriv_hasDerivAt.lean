/-
Auxiliary differentiability lemma for `Work.FTS.PhiStar.FlatWAux.TsumLopDeriv`.

The identity `TsumLopDeriv` differentiates the series
`θ ↦ ∑' m, c m * q m θ` term by term, `i` times, where the angular operator is
`Lop u θ = sin (2θ) · u'(θ)`.  The analytic input is the classical one:
on an *open* interval on which the derivatives converge and the derivatives of the
summands are uniformly dominated by a summable family, a `tsum` is differentiable with
the sum of the derivatives as its derivative (`hasDerivAt_tsum_of_isPreconnected`).

This file records the corresponding statement for the family
`θ ↦ c m · (Lop^[i]) (deriv (q m)) θ`, whose derivatives are dominated on a compact
subinterval `[a,b]` by `K' · B` and whose values are dominated by `Kv · B`, with
`∑_m |c m| B m < ∞`.

The only ingredient that is not immediate from the hypotheses is that each summand is
differentiable on `(a,b)`: the `q m` are only known to be `C^8` on `(0,π/2)`, and
`(Lop^[i]) (deriv (q m))` is `C^{7-i}` there, which is non-zero order because `i ≤ 6`.
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux.Defs
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Filter

namespace Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux

/-- Smoothness input in `HasDerivAt` form: if `q` is `C^8` on an open set `U` and `i ≤ 6`,
then `(Lop^[i]) (deriv q)` is differentiable at every point of `U`.

Indeed `deriv q = iteratedDeriv 1 q` is `C^7` on `U` (`contDiffOn_iteratedDeriv`) and
`Lop^[i]` costs `i` orders, so `(Lop^[i]) (deriv q)` is `C^{7-i} ⊆ C^1` on `U`. -/
theorem differentiableAt_Lop_iter_deriv {U : Set ℝ} (hU : IsOpen U) {q : ℝ → ℝ}
    (hq : ContDiffOn ℝ 8 q U) {i : ℕ} (hi : i ≤ 6) {y : ℝ} (hy : y ∈ U) :
    DifferentiableAt ℝ ((Work.Spaces.Lop^[i]) (deriv q)) y := by
  have h1 : ContDiffOn ℝ (((7 : ℕ)) : WithTop ℕ∞) (iteratedDeriv 1 q) U :=
    Work.FTS.PhiStar.FlatWAux.contDiffOn_iteratedDeriv hU 1 7 (by simpa using hq)
  have hsub : 7 - i + i = 7 := Nat.sub_add_cancel (by omega)
  have h3 : ContDiffOn ℝ (((7 - i : ℕ)) : WithTop ℕ∞)
      ((Work.Spaces.Lop^[i]) (iteratedDeriv 1 q)) U :=
    Work.FTS.PhiStar.FlatWAux.contDiffOn_Lop_iter i hU (7 - i) (by
      have hcast : (((7 - i + i : ℕ)) : WithTop ℕ∞) = (((7 : ℕ)) : WithTop ℕ∞) := by
        rw [hsub]
      rw [hcast]; exact h1)
  have h2 : ContDiffOn ℝ (((7 - i : ℕ)) : WithTop ℕ∞) ((Work.Spaces.Lop^[i]) (deriv q)) U := by
    simpa only [iteratedDeriv_one] using h3
  refine (h2.contDiffAt (hU.mem_nhds hy)).differentiableAt ?_
  have h : (1 : ℕ) ≤ 7 - i := by omega
  have h' : ((1 : ℕ) : WithTop ℕ∞) ≤ ((7 - i : ℕ) : WithTop ℕ∞) := Nat.cast_le.mpr h
  exact ne_of_gt (lt_of_lt_of_le (zero_lt_one : (0 : WithTop ℕ∞) < 1) h')

theorem tsum_Lop_iter_deriv_hasDerivAt (c : ℕ → ℝ) (q : ℕ → ℝ → ℝ) (B : ℕ → ℝ)
    (hcB : Summable fun m : ℕ => |c m| * B m)
    (hq : ∀ m : ℕ, ContDiffOn ℝ 8 (q m) (Set.Ioo 0 (Real.pi / 2)))
    (i : ℕ) (hi : i ≤ 6)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2)
    (K' Kv : ℝ) (hK' : 0 ≤ K') (hKv : 0 ≤ Kv)
    (hbnd : ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Icc a b →
      |deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) θ| ≤ K' * B m)
    (hbval : ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Icc a b →
      |(Work.Spaces.Lop^[i]) (deriv (q m)) θ| ≤ Kv * B m)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo a b) :
    HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * (Work.Spaces.Lop^[i]) (deriv (q m)) y)
      (∑' m : ℕ, c m * deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) θ) θ := by
  -- the interval `(a,b)` is an open neighbourhood of `θ` and sits inside the domain of `q m`
  have hsub : ∀ y ∈ Set.Ioo a b, y ∈ Set.Ioo 0 (Real.pi / 2) := fun y hy =>
    ⟨by linarith [hy.1, ha], by linarith [hy.2, hb]⟩
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun m : ℕ => |c m| * (K' * B m))
    (g := fun m (y : ℝ) => c m * (Work.Spaces.Lop^[i]) (deriv (q m)) y)
    (g' := fun m (y : ℝ) => c m * deriv ((Work.Spaces.Lop^[i]) (deriv (q m))) y)
    (t := Set.Ioo a b) (y₀ := θ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the dominating family `m ↦ |c m| * (K' * B m)` is summable
    exact (hcB.mul_left K').congr (fun m => by ring)
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · -- each summand is differentiable on `(a,b)`, with the announced derivative
    intro m y hy
    exact (differentiableAt_Lop_iter_deriv isOpen_Ioo (hq m) hi (hsub y hy)).hasDerivAt.const_mul
      (c m)
  · -- bound on the derivatives
    intro m y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hbnd m y ⟨le_of_lt hy.1, le_of_lt hy.2⟩) (abs_nonneg _)
  · exact ⟨hθ.1, hθ.2⟩
  · -- convergence of the series of values at `θ`
    refine Summable.of_norm_bounded (hcB.mul_left Kv) (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |c m| * |(Work.Spaces.Lop^[i]) (deriv (q m)) θ|
        ≤ |c m| * (Kv * B m) :=
          mul_le_mul_of_nonneg_left (hbval m θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (abs_nonneg _)
      _ = Kv * (|c m| * B m) := by ring
  · exact hθ

end Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux
