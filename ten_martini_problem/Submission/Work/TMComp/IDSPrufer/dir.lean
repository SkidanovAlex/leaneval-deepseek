import Mathlib
import Submission.Work.TMComp.IDSDefs
import Submission.Work.TMComp.IDSPrufer.pruferStep_dir_half
import Submission.Work.TMComp.IDSPrufer.pruferStep_dir_nonhalf

/-!
# `dir` — the Prüfer angle of the Dirichlet state vector

The state vector `(u_n, u_{n-1})` of the Dirichlet solution of the AMO eigenvalue equation
is obtained from `(1,0)` by iterating the transfer matrices `[[a_j,-1],[1,0]]`, and
`pruferIter` is the lift of the corresponding projective iteration.  This file proves that
the two agree at the level of directions, with a *nonnegative* radius:

`(u_n, u_{n-1}) = ρ (cos (π t_n), sin (π t_n))`, `ρ ≥ 0`, `t_n = pruferIter α lam E n θ 0`.

The key input is the one-step fact about `pruferStep` (proved for the two branches of its
definition by `pruferStep_dir_half` / `pruferStep_dir_nonhalf`).
-/

noncomputable section

namespace Work.TMComp.IDSPrufer

open Work.TMContract

/-- The explicit Prüfer step moves directions correctly: the image of `(cos πt, sin πt)`
under the transfer `[[a,-1],[1,0]]` is a strictly positive multiple of
`(cos π (pruferStep a t), sin π (pruferStep a t))`. -/
theorem pruferStep_dir (a t : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      (a * Real.cos (Real.pi * t) - Real.sin (Real.pi * t), Real.cos (Real.pi * t)) =
        (r * Real.cos (Real.pi * pruferStep a t),
         r * Real.sin (Real.pi * pruferStep a t)) := by
  by_cases h : t - (⌊t + 1 / 2⌋ : ℝ) = -1 / 2
  · exact pruferStep_dir_half a t h
  · exact pruferStep_dir_nonhalf a t h

/-- The Dirichlet state vector `(u_n, u_{n-1})` at `θ` is a nonnegative multiple of
`(cos (π t_n), sin (π t_n))` where `t_n = pruferIter α lam E n θ 0` is the Prüfer angle. -/
theorem dir (α lam θ E : ℝ) (n : ℕ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧
      Work.TMComp.uSeq α lam θ E n
        = ρ * Real.cos (Real.pi * Work.TMContract.pruferIter α lam E n θ 0) ∧
      Work.TMComp.vSeq α lam θ E n
        = ρ * Real.sin (Real.pi * Work.TMContract.pruferIter α lam E n θ 0) := by
  -- Stronger auxiliary statement: the pair `jstate` equals a *positive* multiple of the
  -- direction vector `(cos (π t_n), sin (π t_n))`.
  have key : ∀ n : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
      Work.TMComp.jstate α lam θ E n =
        (ρ * Real.cos (Real.pi * Work.TMContract.pruferIter α lam E n θ 0),
         ρ * Real.sin (Real.pi * Work.TMContract.pruferIter α lam E n θ 0)) := by
    intro n
    induction n with
    | zero => exact ⟨1, one_pos, by simp [Work.TMComp.jstate, Work.TMContract.pruferIter]⟩
    | succ n ih =>
      obtain ⟨ρ, hρ, h⟩ := ih
      obtain ⟨r, hr, hr'⟩ :=
        pruferStep_dir (E - Work.TMComp.pot α lam θ n) (Work.TMContract.pruferIter α lam E n θ 0)
      refine ⟨ρ * r, mul_pos hρ hr, ?_⟩
      have hu : (Work.TMComp.jstate α lam θ E n).1
          = ρ * Real.cos (Real.pi * Work.TMContract.pruferIter α lam E n θ 0) :=
        congrArg Prod.fst h
      have hv : (Work.TMComp.jstate α lam θ E n).2
          = ρ * Real.sin (Real.pi * Work.TMContract.pruferIter α lam E n θ 0) :=
        congrArg Prod.snd h
      have hA : Work.TMContract.pruferIter α lam E (n + 1) θ 0 =
          Work.TMContract.pruferStep (E - Work.TMComp.pot α lam θ n)
            (Work.TMContract.pruferIter α lam E n θ 0) := by
        simp [Work.TMContract.pruferIter, Work.TMComp.pot]
      have h1 : (E - Work.TMComp.pot α lam θ n)
              * Real.cos (Real.pi * Work.TMContract.pruferIter α lam E n θ 0)
            - Real.sin (Real.pi * Work.TMContract.pruferIter α lam E n θ 0)
          = r * Real.cos (Real.pi * Work.TMContract.pruferStep (E - Work.TMComp.pot α lam θ n)
                (Work.TMContract.pruferIter α lam E n θ 0)) := congrArg Prod.fst hr'
      have h2 : Real.cos (Real.pi * Work.TMContract.pruferIter α lam E n θ 0)
          = r * Real.sin (Real.pi * Work.TMContract.pruferStep (E - Work.TMComp.pot α lam θ n)
                (Work.TMContract.pruferIter α lam E n θ 0)) := congrArg Prod.snd hr'
      have hj : Work.TMComp.jstate α lam θ E (n + 1) =
          ((E - Work.TMComp.pot α lam θ n) * (Work.TMComp.jstate α lam θ E n).1
              - (Work.TMComp.jstate α lam θ E n).2,
           (Work.TMComp.jstate α lam θ E n).1) := by simp [Work.TMComp.jstate]
      rw [hj, hA, hu, hv]
      refine Prod.ext ?_ ?_
      · rw [show (E - Work.TMComp.pot α lam θ n)
                * (ρ * Real.cos (Real.pi * Work.TMContract.pruferIter α lam E n θ 0))
              - ρ * Real.sin (Real.pi * Work.TMContract.pruferIter α lam E n θ 0)
            = ρ * ((E - Work.TMComp.pot α lam θ n)
                * Real.cos (Real.pi * Work.TMContract.pruferIter α lam E n θ 0)
              - Real.sin (Real.pi * Work.TMContract.pruferIter α lam E n θ 0)) by ring, h1]
        ring
      · rw [h2]; ring
  obtain ⟨ρ, hρ, h⟩ := key n
  exact ⟨ρ, le_of_lt hρ, congrArg Prod.fst h, congrArg Prod.snd h⟩

end Work.TMComp.IDSPrufer
