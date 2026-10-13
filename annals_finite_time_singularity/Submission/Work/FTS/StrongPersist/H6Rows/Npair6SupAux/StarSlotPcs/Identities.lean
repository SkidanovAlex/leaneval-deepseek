/-
# The two derivative identities of the star slots

`D_θF_* = α qfun θ·F_*` on `Iθ` (`Work.Spaces.dthU_Gam`) and
`D_zF_* = ((1-z)/(1+z))·F_*` on `Iz`, where `D_θ = sin 2θ ∂_θ`, `D_z = z ∂_z`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.Nonlinear.Pieces.Basic

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

/-- `D_θF_* = α qfun θ · F_*` on `Iθ`. -/
theorem Dth_Fstar_eq {α : ℝ} (hα : 0 < α) :
    ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        = α * Work.Spaces.qfun θ * Work.Construction.Fstar α z θ := by
  intro z θ hθ
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · have hfac : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          = (α * (2 * z / (1 + z) ^ 2) / Work.Spaces.c α)
              * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ := by
        simp only [Work.Spaces.Dth, Work.Spaces.pth, Work.Spaces.dthU,
          Work.Construction.Fstar, Work.FM.Fstar]
        rw [show (fun θ' => α * (Work.Spaces.Gam α θ' / Work.Spaces.c α)
              * (2 * z / (1 + z) ^ 2))
            = fun θ' => (α * (2 * z / (1 + z) ^ 2) / Work.Spaces.c α)
                * Work.Spaces.Gam α θ' from by funext θ'; ring]
        rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.deriv_const_mul']
        ring
      rw [hfac, Work.Spaces.dthU_Gam α θ hα ⟨h0, h1⟩,
        Work.Construction.Fstar, Work.FM.Fstar]
      ring
    · subst h1
      rw [Work.Spaces.Dth, Work.Spaces.pth,
        show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul]
      have hG := Work.Spaces.Gam_zero_right α (ne_of_gt hα)
      simp only [Work.Construction.Fstar, Work.FM.Fstar, hG, zero_div]
      ring
  · subst h0
    rw [Work.Spaces.Dth, Work.Spaces.pth, show (2 : ℝ) * 0 = 0 by ring,
      Real.sin_zero, zero_mul]
    have hG := Work.Spaces.Gam_zero_left α (ne_of_gt hα)
    simp only [Work.Construction.Fstar, Work.FM.Fstar, hG, zero_div]
    ring

/-- `z/(1+z)·D_zF_* = ((1-z)/(1+z))·(α·AK α)` on `Iz`. -/
theorem Dz_Fstar_eq {α : ℝ} :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        = (1 - z) / (1 + z) * (α * Work.Construction.AK α z θ) := by
  intro z hz θ _hθ
  have hfac : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = z * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * deriv Work.FM.Fstar z := by
    rw [Work.Spaces.Dz, Work.Spaces.pz]
    rw [show (fun z' => Work.Construction.Fstar α z' θ)
        = fun z' => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.FM.Fstar z' from by
          funext z'; simp only [Work.Construction.Fstar] <;> ring]
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.deriv_const_mul']
    ring
  have hz1 : (-1 : ℝ) < z := by
    have h := hz; simp only [Work.Spaces.Iz, Set.mem_Ici] at h; linarith
  rw [hfac, Work.FM.deriv_Fstar z hz1, Work.Construction.AK]
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp <;> ring

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
