/-
# `E1Parts/RadAZop` — calculus of the iterates of `Zop u = z·u'`

The radial operator `D_z = z ∂_z` (as `Work.Spaces.Zop`, or `Work.Elliptic.DzdIter` for its
iterates) is used on functions of the radial variable alone.  This file collects the abstract
facts:

* `Zop_iter_congr_of_eqOn` / `DzdIter_congr_of_eqOn` — congruence on `(0,∞)`;
* `Zop_iter_add_of` / `DzdIter_add_of_diff` — additivity, from differentiability of the
  iterates one order below;
* `contDiffOn_deriv_of_succ`, `contDiffOn_Zop_iter'` — a `C^{b+k}` function has `C^k`
  `Zop`-iterates of order `b`;
* `differentiableAt_Zop_iter_of_contDiffOn`, `continuousOn_Zop_iter_of_contDiffOn` — the two
  specialisations used downstream.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Iterates of `Zop u = z·u'` agree on `(0,∞)` for functions agreeing there. -/
theorem Zop_iter_congr_of_eqOn (u v : ℝ → ℝ) (h : ∀ z ∈ Set.Ioi (0 : ℝ), u z = v z) :
    ∀ b : ℕ, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.Zop^[b] u z = Work.Spaces.Zop^[b] v z := by
  intro b
  induction b with
  | zero => exact h
  | succ k ih =>
      intro z hz
      have hev : Work.Spaces.Zop^[k] u =ᶠ[𝓝 z] Work.Spaces.Zop^[k] v := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih w hw
      have h1 : Work.Spaces.Zop^[k + 1] u = Work.Spaces.Zop (Work.Spaces.Zop^[k] u) :=
        Function.iterate_succ_apply' Work.Spaces.Zop k u
      have h2 : Work.Spaces.Zop^[k + 1] v = Work.Spaces.Zop (Work.Spaces.Zop^[k] v) :=
        Function.iterate_succ_apply' Work.Spaces.Zop k v
      rw [h1, h2]
      show z * deriv (Work.Spaces.Zop^[k] u) z = z * deriv (Work.Spaces.Zop^[k] v) z
      rw [hev.deriv_eq]

/-- **Additivity of the `Zop`-iterates** for functions whose iterates are differentiable on
`(0,∞)` up to one order below the level. -/
theorem Zop_iter_add_of (j : ℕ) (u v : ℝ → ℝ)
    (hu : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Spaces.Zop^[b] u) z)
    (hv : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Spaces.Zop^[b] v) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.Zop^[j] (u + v) z = Work.Spaces.Zop^[j] u z + Work.Spaces.Zop^[j] v z := by
  induction j with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      have hu' : ∀ b < k, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Spaces.Zop^[b] u) z :=
        fun b hb => hu b (by omega)
      have hv' : ∀ b < k, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Spaces.Zop^[b] v) z :=
        fun b hb => hv b (by omega)
      have hev : Work.Spaces.Zop^[k] (u + v)
          =ᶠ[𝓝 z] Work.Spaces.Zop^[k] u + Work.Spaces.Zop^[k] v := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih hu' hv' w hw
      have h1 : DifferentiableAt ℝ (Work.Spaces.Zop^[k] u) z := hu k (by omega) z hz
      have h2 : DifferentiableAt ℝ (Work.Spaces.Zop^[k] v) z := hv k (by omega) z hz
      have h3 : Work.Spaces.Zop^[k + 1] (u + v)
          = Work.Spaces.Zop (Work.Spaces.Zop^[k] (u + v)) :=
        Function.iterate_succ_apply' Work.Spaces.Zop k (u + v)
      have h4 : Work.Spaces.Zop^[k + 1] u = Work.Spaces.Zop (Work.Spaces.Zop^[k] u) :=
        Function.iterate_succ_apply' Work.Spaces.Zop k u
      have h5 : Work.Spaces.Zop^[k + 1] v = Work.Spaces.Zop (Work.Spaces.Zop^[k] v) :=
        Function.iterate_succ_apply' Work.Spaces.Zop k v
      rw [h3, h4, h5]
      show z * deriv (Work.Spaces.Zop^[k] (u + v)) z
        = z * deriv (Work.Spaces.Zop^[k] u) z + z * deriv (Work.Spaces.Zop^[k] v) z
      rw [hev.deriv_eq, deriv_add h1 h2]
      ring

/-- Additivity of the `DzdIter`s, in the vocabulary used by the Leibniz rule. -/
theorem DzdIter_add_of_diff (j : ℕ) (u v : ℝ → ℝ)
    (hu : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z)
    (hv : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b v) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j (u + v) z
        = Work.Elliptic.DzdIter j u z + Work.Elliptic.DzdIter j v z := by
  intro z hz
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j (u + v),
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j u,
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j v]
  refine Zop_iter_add_of j u v ?_ ?_ z hz
  · intro b hb z' hz'
    rw [← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b u]
    exact hu b hb z' hz'
  · intro b hb z' hz'
    rw [← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b v]
    exact hv b hb z' hz'

/-- Congruence of the `DzdIter`s for functions agreeing on `(0,∞)`. -/
theorem DzdIter_congr_of_eqOn (u v : ℝ → ℝ) (h : ∀ z ∈ Set.Ioi (0 : ℝ), u z = v z) (j : ℕ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter j u z = Work.Elliptic.DzdIter j v z := by
  intro z hz
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j u,
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j v]
  exact Zop_iter_congr_of_eqOn u v h j z hz

/-- The derivative of a `C^{n+1}` function on `(0,∞)` is `C^n`. -/
theorem contDiffOn_deriv_of_succ {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (n + 1) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ n (deriv u) (Set.Ioi (0 : ℝ)) := by
  have hfd : ContDiffOn ℝ n (fderiv ℝ u) (Set.Ioi (0 : ℝ)) :=
    hu.fderiv_of_isOpen isOpen_Ioi (by simp)
  have hev : ContDiffOn ℝ n (fun z : ℝ => (fderiv ℝ u z) 1) (Set.Ioi (0 : ℝ)) :=
    hfd.clm_apply contDiffOn_const
  refine hev.congr (fun z _ => ?_)
  rw [fderiv_apply_one_eq_deriv]

/-- A `C^{b+k}`-function has `C^k` `Zop`-iterates of order `b`. -/
theorem contDiffOn_Zop_iter' {u : ℝ → ℝ} (b k : ℕ)
    (hu : ContDiffOn ℝ (b + k) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ k (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) := by
  induction b generalizing k with
  | zero => simpa using hu
  | succ b ih =>
      have hu' : ContDiffOn ℝ (b + (k + 1)) u (Set.Ioi (0 : ℝ)) :=
        hu.of_le (by exact_mod_cast (by omega : b + (k + 1) ≤ (b + 1) + k))
      have h1 : ContDiffOn ℝ (k + 1) (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) := ih (k + 1) hu'
      have h2 : ContDiffOn ℝ k (deriv (Work.Spaces.Zop^[b] u)) (Set.Ioi (0 : ℝ)) :=
        contDiffOn_deriv_of_succ h1
      have h3 : ContDiffOn ℝ k
          (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z) (Set.Ioi (0 : ℝ)) :=
        (contDiff_id.contDiffOn).mul h2
      rw [Function.iterate_succ_apply']
      change ContDiffOn ℝ k (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z)
        (Set.Ioi (0 : ℝ))
      exact h3

/-- A `C^{b+1}`-function has differentiable `Zop`-iterate of order `b` on `(0,∞)`. -/
theorem differentiableAt_Zop_iter_of_contDiffOn {u : ℝ → ℝ} {b : ℕ}
    (hu : ContDiffOn ℝ (b + 1) u (Set.Ioi (0 : ℝ))) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Spaces.Zop^[b] u) z :=
  ((contDiffOn_Zop_iter' b 1 hu).differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- A `C^{b+n}`-function has continuous `Zop`-iterate of order `b` on `(0,∞)`. -/
theorem continuousOn_Zop_iter_of_contDiffOn {u : ℝ → ℝ} {b n : ℕ}
    (hu : ContDiffOn ℝ (b + n) u (Set.Ioi (0 : ℝ))) :
    ContinuousOn (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) :=
  (contDiffOn_Zop_iter' b n hu).continuousOn

end Work.FTS.CoercivityFix.Transfer.E1Parts
