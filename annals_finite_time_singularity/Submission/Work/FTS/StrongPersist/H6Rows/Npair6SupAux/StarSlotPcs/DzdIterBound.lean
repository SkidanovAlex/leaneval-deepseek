/-
# The `D_z`-iterates of `z ↦ (1-z)/(1+z)` are bounded on `[0,∞)`

The radial multiplier `X y = (1-y)/(1+y)` of the `D_zF_*`-slot has bounded `z∂_z`-iterates of
order `≤ 6`.  Since `X y = 2(1+y)⁻¹ - 1`, every iterate `k ≥ 1` is that of `2(1+y)⁻¹`, whose
`k`-th derivative is a constant multiple of `nInvClosed k`; the Stirling/Bell expansion
`D_z^k = ∑_m S(k,m) z^m ∂_z^m` (`Work.Spaces.DzIter_eq_sum_scoef`) together with the weighted
bound `|(1+z)^k nInvClosed k z| ≤ k!` then gives the uniform estimate
`|D_z^k X z| ≤ 250·1440` for `z ≥ 0`, `k ≤ 6`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.scoef
import Submission.Work.FTS.Nonlinear.FstarPkg.c2mInv_points
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Jets

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The Bell numbers of the rows `n ≤ 6`. -/
theorem bell_le_six_local {n : ℕ} (hn : n ≤ 6) : Work.Spaces.bell n ≤ 250 := by
  interval_cases n <;> decide

/-- The `k`-th derivative of `X y = (1-y)/(1+y)`, `k ≥ 1`, is that of `2(1+y)⁻¹`. -/
theorem deriv_iter_oneSubOneAdd : ∀ m : ℕ, 1 ≤ m → ∀ z : ℝ, -1 < z →
    deriv^[m] (fun y : ℝ => (1 - y) / (1 + y)) z
      = 2 * Work.FTS.Nonlinear.FstarPkg.nInvClosed m z := by
  intro m
  induction m with
  | zero => intro hm z hz; omega
  | succ m ih =>
    intro hm z hz
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      rw [Function.iterate_one]
      have hbase : HasDerivAt (fun y : ℝ => 2 * (1 + y)⁻¹ - 1)
          (2 * Work.FTS.Nonlinear.FstarPkg.nInvClosed 1 z) z := by
        have h0' : HasDerivAt (fun y : ℝ => (1 + y)⁻¹)
            (Work.FTS.Nonlinear.FstarPkg.nInvClosed 1 z) z := by
          have h := Work.FTS.Nonlinear.FstarPkg.hasDerivAt_nInvClosed 0 (z := z) (by linarith)
          have hfun : Work.FTS.Nonlinear.FstarPkg.nInvClosed 0 = fun y : ℝ => (1 + y)⁻¹ := by
            funext y
            simp [Work.FTS.Nonlinear.FstarPkg.nInvClosed]
          rwa [hfun] at h
        simpa using (h0'.const_mul 2).sub_const 1
      have hX : (fun y : ℝ => (1 - y) / (1 + y)) =ᶠ[𝓝 z]
          (fun y : ℝ => 2 * (1 + y)⁻¹ - 1) := by
        filter_upwards [isOpen_ne.mem_nhds (show z ≠ (-1 : ℝ) by linarith)] with y hy
        have hy' : (1 + y) ≠ 0 := by
          intro h; exact hy (by linarith)
        field_simp
        ring
      rw [Filter.EventuallyEq.deriv_eq hX, hbase.deriv]
    · rw [Function.iterate_succ_apply']
      have hev : deriv^[m] (fun y : ℝ => (1 - y) / (1 + y)) =ᶠ[𝓝 z]
          (fun y : ℝ => 2 * Work.FTS.Nonlinear.FstarPkg.nInvClosed m y) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
        exact ih hpos y hy
      rw [hev.deriv_eq]
      exact ((Work.FTS.Nonlinear.FstarPkg.hasDerivAt_nInvClosed m (z := z)
        (by linarith)).const_mul 2).deriv

/-- `|z^m ∂_z^m X z| ≤ 1440` for `z ≥ 0`, `m ≤ 6`, `X y = (1-y)/(1+y)`. -/
theorem zpow_deriv_oneSubOneAdd_le (m : ℕ) (hm : m ≤ 6) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ m * deriv^[m] (fun y : ℝ => (1 - y) / (1 + y)) z| ≤ 1440 := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    simp only [pow_zero, one_mul, Function.iterate_zero_apply]
    have h1 : |1 - z| ≤ 1 + z := by
      rw [abs_le]; constructor <;> linarith
    have h2 : |(1 - z) / (1 + z)| ≤ 1 := by
      rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + z),
        div_le_one (by linarith : (0 : ℝ) < 1 + z)]
      exact h1
    linarith
  · rw [deriv_iter_oneSubOneAdd m hpos z (by linarith : (-1 : ℝ) < z),
      abs_mul, abs_of_nonneg (pow_nonneg hz m), abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hmono : z ^ m ≤ (z + 1) ^ m := by
      apply pow_le_pow_left₀ hz; linarith
    have hb : z ^ m * |Work.FTS.Nonlinear.FstarPkg.nInvClosed m z|
        ≤ ((m.factorial : ℕ) : ℝ) := by
      have h2 : z ^ m * |Work.FTS.Nonlinear.FstarPkg.nInvClosed m z|
          ≤ (z + 1) ^ m * |Work.FTS.Nonlinear.FstarPkg.nInvClosed m z| :=
        mul_le_mul_of_nonneg_right hmono (abs_nonneg _)
      have h3 : (z + 1) ^ m * |Work.FTS.Nonlinear.FstarPkg.nInvClosed m z|
          = |(z + 1) ^ m * Work.FTS.Nonlinear.FstarPkg.nInvClosed m z| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) m)]
      rw [h3] at h2
      exact le_trans h2 (Work.FTS.Nonlinear.FstarPkg.nInvClosed_weighted m z hz)
    have h5 : ((m.factorial : ℕ) : ℝ) ≤ 720 := by
      interval_cases m <;> norm_num
    nlinarith [hb, h5]

/-- **The `D_z`-iterates of `z ↦ (1-z)/(1+z)` are uniformly bounded on `[0,∞)`.** -/
theorem DzdIter_oneSubOneAdd_le_local :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter k (fun y : ℝ => (1 - y) / (1 + y)) z| ≤ B := by
  let hfun : ℝ → ℝ → ℝ := fun y (_ : ℝ) => (1 - y) / (1 + y)
  refine ⟨250 * 1440, by norm_num, ?_⟩
  intro k hk z hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hsmooth : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z' : ℝ => hfun z' θ) (Set.Ioi (-1)) := by
    intro θ hθ
    have hfun' : (fun z' : ℝ => hfun z' θ) = fun z' : ℝ => (1 - z') / (1 + z') := rfl
    rw [hfun']
    exact (contDiffOn_const.sub contDiffOn_id).div (contDiffOn_const.add contDiffOn_id)
      (fun y hy => by
        have hy2 : (-1 : ℝ) < y := hy
        linarith)
  have hsum := Work.Spaces.DzIter_eq_sum_scoef (h := hfun) hsmooth k z hz1 0
    (by refine ⟨le_rfl, ?_⟩; linarith [Real.pi_pos])
  rw [← Work.Elliptic.DzIter_rad (fun y : ℝ => (1 - y) / (1 + y)) k z 0, hsum]
  have hb := Work.Spaces.abs_sum_scoef_mul_le k 1440
    (fun m => z ^ m * Work.Spaces.pzIter m hfun z 0)
    (fun m hm => by
      rw [show Work.Spaces.pzIter m hfun z 0
          = deriv^[m] (fun y : ℝ => (1 - y) / (1 + y)) z from
        Work.FTS.NonlinRows.pzIter_radial_fn
          (fun y : ℝ => (1 - y) / (1 + y)) m z 0]
      exact zpow_deriv_oneSubOneAdd_le m (le_trans hm hk) hz)
  have hbell : (Work.Spaces.bell k : ℝ) ≤ 250 := by exact_mod_cast bell_le_six_local hk
  calc |∑ m ∈ Finset.range (k + 1), (Work.Spaces.scoef k m : ℝ)
        * (z ^ m * Work.Spaces.pzIter m hfun z 0)|
      ≤ (Work.Spaces.bell k : ℝ) * 1440 := hb
    _ ≤ 250 * 1440 := mul_le_mul_of_nonneg_right hbell (by norm_num)

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
