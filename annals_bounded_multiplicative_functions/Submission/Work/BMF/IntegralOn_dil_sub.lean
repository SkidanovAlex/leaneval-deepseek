import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- If the edge defect `gt` is integral on `(1/Qm)ℤ`, `G` is an integer constant, and
`G = gt + γ₂(p₁·) - γ₁(p₂·)`, then `γ₁(p₂·) - γ₂(p₁·)` is integer valued on `ℤ`. -/
theorem IntegralOn_dil_sub {p₁ p₂ Qm : ℕ} {G gt G1 G2 : Polynomial ℝ} {c : ℝ}
    (hQm : (0 : ℝ) < Qm)
    (hG : G = gt + dil (p₁ : ℝ) G2 - dil (p₂ : ℝ) G1)
    (hGc : G = Polynomial.C c)
    (hc : ∃ m : ℤ, c = m)
    (hint : IntegralOn (1 / (Qm : ℝ)) gt) :
    IntegralOn 1 (dil (p₂ : ℝ) G1 - dil (p₁ : ℝ) G2) := by
  have hQm0 : (Qm : ℝ) ≠ 0 := ne_of_gt hQm
  -- `hint`, read at the indices `Qm * n`, says `gt` is integral on all of `ℤ`.
  have hint1 : IntegralOn 1 gt := by
    intro n
    obtain ⟨m, hm⟩ := hint ((Qm : ℤ) * n)
    refine ⟨m, ?_⟩
    have harg : (1 / (Qm : ℝ)) * ((↑((Qm : ℤ) * n) : ℝ)) = 1 * (↑n : ℝ) := by
      push_cast
      field_simp
    rw [← harg]
    exact hm
  -- Evaluating the defining relation at `t`, the constant `G = c` gives
  -- `G₁(p₂ t) - G₂(p₁ t) = gt t - c`.
  have key : ∀ t : ℝ, G1.eval ((p₂ : ℝ) * t) - G2.eval ((p₁ : ℝ) * t) = gt.eval t - c := by
    intro t
    have h := congrArg (fun P : Polynomial ℝ => P.eval t) hG
    simp only [Polynomial.eval_add, Polynomial.eval_sub, dil, Polynomial.eval_comp,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h
    have hGc' : G.eval t = c := by rw [hGc]; simp
    rw [hGc'] at h
    linarith
  intro n
  obtain ⟨m0, hm0⟩ := hint1 n
  obtain ⟨m1, hm1⟩ := hc
  refine ⟨m0 - m1, ?_⟩
  have h1 : (dil (p₂ : ℝ) G1 - dil (p₁ : ℝ) G2).eval (1 * (↑n : ℝ))
      = G1.eval ((p₂ : ℝ) * (1 * (↑n : ℝ))) -
        G2.eval ((p₁ : ℝ) * (1 * (↑n : ℝ))) := by
    simp [dil]
  rw [h1, key (1 * (↑n : ℝ)), hm0, hm1]
  push_cast
  ring

end Work.BMF
