import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Submission.Work.BoseBoxFock.bessel_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.gramOrthFrame` — Bessel's inequality for an orthonormal family

If a family `g : ι → Fin m → ℝ` of coordinate vectors is **orthonormal** for the Gram product
`Work.BoseB4.gram` (`⟪g s, g t⟫ = δ_{st}`), then its frame operator is dominated by the identity:

  `Σ_s ⟪g s, w⟫² ≤ Σ_l (w l)²`     for every `w : Fin m → ℝ`.

This is the `C = 1` case of the frame theorem `Work.BoseBoxFock.frame_of_synthesis`: it suffices
to exhibit the *synthesis* bound `Σ_l (Σ_k c_k g k l)² ≤ C Σ_k c_k²` with `C = 1`, which for an
orthonormal family is the elementary identity
`Σ_l (Σ_k c_k g k l)² = Σ_k Σ_t c_k c_t ⟪g k, g t⟫ = Σ_k c_k²`
(the square completion `Work.BoseB4.gram_quadForm_eq_sum_sq` followed by the Kronecker collapse).
-/

namespace Work.BoseBoxFock.FRK

theorem gramOrthFrame {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → Fin m → ℝ)
    (hg : ∀ s t : ι, Work.BoseB4.gram (g s) (g t) = if s = t then (1 : ℝ) else 0) :
    ∀ w : Fin m → ℝ, ∑ s : ι, (Work.BoseB4.gram (g s) w) ^ 2 ≤ ∑ l : Fin m, (w l) ^ 2 := by
  classical
  -- the synthesis bound at `C = 1`: expand the square as the Gram quadratic form and use
  -- orthonormality
  have hsyn : ∀ c : ι → ℝ, ∑ l : Fin m, (∑ k : ι, c k * g k l) ^ 2 ≤ ∑ k : ι, (c k) ^ 2 := by
    intro c
    rw [← Work.BoseB4.gram_quadForm_eq_sum_sq g c]
    refine le_of_eq ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [hg i i, if_pos rfl]; ring
    · intro j _ hji
      rw [hg i j, if_neg (fun h => hji h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  intro w
  have h := Work.BoseBoxFock.frame_of_synthesis g 1 (by norm_num)
    (fun c => by rw [one_mul]; exact hsyn c) w
  simpa using h

end Work.BoseBoxFock.FRK
