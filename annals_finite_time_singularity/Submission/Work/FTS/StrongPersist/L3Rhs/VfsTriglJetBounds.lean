import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired
import Submission.Work.FTS.PhiStar.Psi0Est.exists_ZClass
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

set_option maxHeartbeats 800000

-- `VfsTriglJetBounds`: uniform bounds for the `dthU`-jets of order `≤ 4` of the two angular
-- profiles `sin 2θ` and `c₂(θ) = cos 2θ − sin²θ` on `Iθ = [0,π/2]`.
-- Intended namespace `Work.FTS.StrongPersist.L3Rhs`
-- (file `Submission/Work/FTS/StrongPersist/L3Rhs/VfsTriglJetBounds.lean`).
-- Route: `Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired` supplies a single
-- `b : ℕ → ℝ` with `|dthU^[j] (sin 2·) θ| ≤ b j · sin 2θ`, `|dthU^[j] (sin²) θ| ≤ b j · sin²θ`,
-- `|dthU^[j] (cos 2·) θ| ≤ b j` for `j ≤ 7` on `Iθ`; take `B := 2 * Σ_{j<5} b j + 1` and use
-- `c₂ = cos 2· − sin²` together with the linearity of the iterates
-- (`Work.FTS.PhiStar.Psi0Est.dthU_iter_sub_eqOn` on `Set.univ`, or a direct induction).
theorem VfsTriglJetBounds : ∃ B : ℝ, 0 < B ∧
    (∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin (2 * t)) θ| ≤ B * Real.sin (2 * θ)) ∧
    (∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ B) := by
  obtain ⟨b, hb0, hbsin, hbsinsq, _hbcossq, hbcos2⟩ :=
    Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired
  set S : ℝ := ∑ i ∈ Finset.range 5, b i with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]; exact Finset.sum_nonneg (fun i _ => hb0 i)
  refine ⟨2 * S + 1, by linarith, ?_, ?_⟩
  · -- the `sin 2θ`-profile: `b j ≤ S ≤ 2S+1`, and `sin 2θ ≥ 0` on `Iθ`
    intro j hj θ hθ
    have hbj : b j ≤ S := by
      rw [hSdef]
      exact Finset.single_le_sum (fun i _ => hb0 i) (Finset.mem_range.mpr (by omega))
    have hbB : b j ≤ 2 * S + 1 := by linarith
    have hsin2 : 0 ≤ Real.sin (2 * θ) := by
      apply Real.sin_nonneg_of_mem_Icc
      constructor
      · linarith [hθ.1]
      · linarith [hθ.2, Real.pi_pos]
    calc |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin (2 * t)) θ|
        ≤ b j * Real.sin (2 * θ) := hbsin j (by omega) θ hθ
      _ ≤ (2 * S + 1) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_right hbB hsin2
  · -- `c₂ = cos 2· − sin²`: linearity of the iterates plus the `cos 2·`- and `sin²`-bounds
    intro j hj θ hθ
    have hbj : b j ≤ S := by
      rw [hSdef]
      exact Finset.single_le_sum (fun i _ => hb0 i) (Finset.mem_range.mpr (by omega))
    have hbB : b j ≤ 2 * S + 1 := by linarith
    have hb0j : 0 ≤ b j := hb0 j
    have hc2m : Work.Construction.c2m = fun x : ℝ => Real.cos (2 * x) - Real.sin x ^ 2 := rfl
    have hlin := Work.FTS.PhiStar.Psi0Est.dthU_iter_sub_eqOn
      (f := fun t : ℝ => Real.cos (2 * t)) (g := fun t : ℝ => Real.sin t ^ 2)
      (U := Set.univ) isOpen_univ (by fun_prop) (by fun_prop) j
    have hlin' : Work.Spaces.dthU^[j] (fun x : ℝ => Real.cos (2 * x) - Real.sin x ^ 2) θ
        = Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ
          - Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ := hlin (Set.mem_univ θ)
    have hcos := hbcos2 j (by omega) θ hθ
    have hsinsq := hbsinsq j (by omega) θ hθ
    have hsin_sq_le : Real.sin θ ^ 2 ≤ 1 := by
      rw [Real.sin_sq]; linarith [sq_nonneg (Real.cos θ)]
    have habs : |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ
          - Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
        ≤ |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ|
          + |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := by
      calc |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ
              - Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
          = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ
              + (-(Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ))| := by ring_nf
        _ ≤ |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ|
              + |-(Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ)| := abs_add_le _ _
        _ = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ|
              + |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := by rw [abs_neg]
    calc |Work.Spaces.dthU^[j] Work.Construction.c2m θ|
        = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ
          - Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := by rw [hc2m, hlin']
      _ ≤ |Work.Spaces.dthU^[j] (fun t : ℝ => Real.cos (2 * t)) θ|
          + |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := habs
      _ ≤ b j + b j * Real.sin θ ^ 2 := add_le_add hcos hsinsq
      _ ≤ b j + b j * 1 := by
            have := mul_le_mul_of_nonneg_left hsin_sq_le hb0j
            linarith
      _ = 2 * b j := by ring
      _ ≤ 2 * S + 1 := by linarith

end Work.FTS.StrongPersist.L3Rhs
