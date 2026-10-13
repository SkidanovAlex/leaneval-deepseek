/-
# `FTS/PhiStar/CoreAux/F0_theta_coefs.lean` — the four angular coefficients belong to `F0`

`Work.FTS.PhiStar.F0 n K f` (see `CoreAux/Defs.lean`) says that all the mixed weighted
derivatives `(z+1)^k ∂_z^k D_θ^i f` with `k + i ≤ n` are bounded by `K` on the open quadrant
`Q0 = (0,∞)×(0,π/2)`.  This file shows that the four *angular coefficients* occurring in the
`StarPkgo2` assembly,

    sin²θ ,  cos²θ - 2 sin²θ ,  cos 2θ ,  sin 2θ ,

all belong to `F0 m` for a single positive constant `C` (one `C` for all four, for each `m`).

**The mathematics.**  Each of the four functions is `θ`-only, `f z θ = c θ`.  For such a
function

* `∂_z^k f = 0` for every `k ≥ 1` (`Psi0Est.pzIter_theta_only_succ`), so all slots with a
  radial derivative vanish identically;
* `D_θ^i f = dthU^[i] c` is again `θ`-only (`Psi0Est.DthIter_theta_only`), so the remaining
  slot `k = 0` is bounded by `sup_{θ∈Iθ} |dthU^[i] c θ|`, which is finite because `dthU^[i] c`
  is continuous on the compact interval `Iθ` for `i ≤ m` as soon as `c` is `C^m`
  (`CoreAux.LopIter_continuousOn_of_contDiff`).

The reduction is isolated in `exists_F0_of_theta_only_aux` below; the four coefficients are
then instances, and the single constant is the sum of the four individual ones.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.Psi0Est.Defs
import Submission.Work.FTS.PhiStar.CoreAux.LopIter_continuousOn_of_contDiff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

/-- **A `θ`-only function with `C^m` slice belongs to `F0 m`.**

If all the angular iterates `dthU^[i] c` (`i ≤ m`) are continuous on the compact interval
`Iθ`, then there is a positive constant `A` with `F0 m A (fun _ θ => c θ)`: indeed every slot
with a radial derivative vanishes, and the purely angular slots are bounded by the finitely
many suprema of the continuous functions `dthU^[i] c` on `Iθ`.

The constant produced is `(∑_{i ≤ m} B i) + 1`, where `B i` is a bound for `dthU^[i] c` on
`Iθ`; the `+1` makes it positive without any hypothesis on the signs of the `B i`. -/
theorem exists_F0_of_theta_only_aux (m : ℕ) (c : ℝ → ℝ)
    (hc : ∀ i ≤ m, ContinuousOn (fun θ => (Work.Spaces.dthU^[i]) c θ) Work.Spaces.Iθ) :
    ∃ A : ℝ, 0 < A ∧ Work.FTS.PhiStar.F0 m A (fun _ θ => c θ) := by
  have hbdd : ∀ i : ℕ, ∃ B : ℝ, i ≤ m → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.dthU^[i]) c θ| ≤ B := by
    intro i
    by_cases hi : i ≤ m
    · obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc i hi)
      exact ⟨B, fun _ θ hθ => by simpa [Real.norm_eq_abs] using hB θ hθ⟩
    · exact ⟨0, fun h => absurd h hi⟩
  classical
  choose B hB using hbdd
  have hB0 : ∀ i, i ≤ m → 0 ≤ B i := by
    intro i hi
    have h := hB i hi 0 (by
      simp only [Work.Spaces.Iθ, Set.mem_Icc]
      exact ⟨le_refl 0, by linarith [Real.pi_pos]⟩)
    linarith [abs_nonneg ((Work.Spaces.dthU^[i]) c 0)]
  have hsum : 0 ≤ ∑ i ∈ Finset.range (m + 1), B i :=
    Finset.sum_nonneg (fun i hi => hB0 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
  refine ⟨(∑ i ∈ Finset.range (m + 1), B i) + 1, by linarith, ?_⟩
  intro k i hki z θ hz hθ hθ'
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hi : i ≤ m := by omega
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ'.le⟩
    rw [Work.FTS.PhiStar.Psi0Est.DthIter_theta_only c i]
    simp only [Work.Spaces.pzIter_zero, pow_zero, one_mul]
    have h1 := hB i hi θ hθI
    have h2 : B i ≤ ∑ j ∈ Finset.range (m + 1), B j :=
      Finset.single_le_sum (fun j hj => hB0 j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
        (Finset.mem_range.mpr (by omega))
    linarith
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Work.FTS.PhiStar.Psi0Est.DthIter_theta_only c i,
        Work.FTS.PhiStar.Psi0Est.pzIter_theta_only_succ (Work.Spaces.dthU^[i] c) k']
    simp only [mul_zero, abs_zero]
    linarith

theorem F0_theta_coefs (m : ℕ) : ∃ C : ℝ, 0 < C ∧ Work.FTS.PhiStar.F0 m C (fun _ θ => Real.sin θ ^ 2) ∧ Work.FTS.PhiStar.F0 m C (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) ∧ Work.FTS.PhiStar.F0 m C (fun _ θ => Real.cos (2 * θ)) ∧ Work.FTS.PhiStar.F0 m C (fun _ θ => Real.sin (2 * θ)) := by
  have key : ∀ (c : ℝ → ℝ), ContDiff ℝ ((m : ℕ∞) : WithTop ℕ∞) c →
      ∃ A : ℝ, 0 < A ∧ Work.FTS.PhiStar.F0 m A (fun _ θ => c θ) := fun c hc =>
    exists_F0_of_theta_only_aux m c
      (fun i hi => LopIter_continuousOn_of_contDiff m c hc i hi)
  obtain ⟨A1, hA1, hF1⟩ := key (fun θ => Real.sin θ ^ 2) (by fun_prop)
  obtain ⟨A2, hA2, hF2⟩ := key (fun θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by fun_prop)
  obtain ⟨A3, hA3, hF3⟩ := key (fun θ => Real.cos (2 * θ)) (by fun_prop)
  obtain ⟨A4, hA4, hF4⟩ := key (fun θ => Real.sin (2 * θ)) (by fun_prop)
  refine ⟨A1 + A2 + A3 + A4, by linarith, ?_, ?_, ?_, ?_⟩
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) hF1
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) hF2
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) hF3
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) hF4

end Work.FTS.PhiStar.CoreAux
