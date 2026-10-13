import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.LocUnif.V6Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- The child `D_z`-slot of the level-`(j+1)` slot `mixed j i g` is `z` times the plain
`z`-derivative of the parent: this is `D_z (D_z^j D_θ^i g) = z ∂_z (D_z^j D_θ^i g)`. -/
lemma mixed_succ_fst (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed (j + 1) i g
      = fun z θ => z * deriv (fun z' => Work.Spaces.mixed j i g z' θ) z := rfl

/-- The child `D_θ`-slot of the level-`(i+1)` slot `mixed 0 i g` is `sin(2θ)` times the
plain `θ`-derivative of the parent: this is `D_θ (D_θ^i g) = sin(2θ) ∂_θ (D_θ^i g)`. -/
lemma mixed_zero_succ (i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed 0 (i + 1) g
      = fun z θ => Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.mixed 0 i g z θ') θ := rfl

theorem level6_identities (α : ℝ) :
    (∀ (g : ℝ → ℝ → ℝ) (z θ : ℝ),
        Work.Spaces.HkIntegrand α 6 g z θ
          = Work.Spaces.HkIntegrand α 5 g z θ
            + Work.FTS.StrongEps.LocUnif.level6Z α g z θ
            + Work.FTS.StrongEps.LocUnif.level6T α g z θ) ∧
    (∀ (g : ℝ → ℝ → ℝ) (p : ℝ × ℝ),
        Work.FTS.StrongEps.LocUnif.level6Z α g p.1 p.2
          = ∑ k ∈ Finset.range 6,
              (deriv (fun z' => Work.Spaces.mixed (5 - k) k g z' p.2) p.1
                * (p.1 * Work.FTS.StrongEps.LocUnif.rho6 α k p.1 p.2)) ^ 2) ∧
    (∀ (g : ℝ → ℝ → ℝ) (p : ℝ × ℝ),
        Work.FTS.StrongEps.LocUnif.level6T α g p.1 p.2
          = (deriv (fun θ' => Work.Spaces.mixed 0 5 g p.1 θ') p.2
                * (Real.sin (2 * p.2) * Work.FTS.StrongEps.LocUnif.rho6 α 6 p.1 p.2)) ^ 2)
    := by
  refine ⟨?_, ?_, ?_⟩
  · -- The level-6 integrand is the level-5 integrand plus the six `D_z`-directed slots
    -- `mixed (6-i) i` (`0 ≤ i ≤ 5`, weight `rho6 α i`) and the `D_θ`-directed slot
    -- `mixed 0 6` (weight `rho6 α 6 = Wt α`).
    intro g z θ
    simp only [Work.Spaces.HkIntegrand, level6Z, level6T, rho6,
      Finset.sum_range_succ, Finset.sum_range_zero,
      Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right, Nat.reduceSub]
    simp
    ring
  · -- Each `D_z`-directed slot is `z ∂_z` of its level-5 parent.
    intro g p
    rw [level6Z]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ 5 := by simp [Finset.mem_range] at hk; omega
    have h6 : 6 - k = (5 - k) + 1 := by omega
    rw [h6, mixed_succ_fst]
    ring
  · -- The `D_θ`-directed slot is `sin(2θ) ∂_θ` of its level-5 parent.
    intro g p
    rw [level6T]
    have h : Work.Spaces.mixed 0 6 g
        = fun z θ => Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.mixed 0 5 g z θ') θ := rfl
    rw [h]
    ring

end Work.FTS.StrongEps.LocUnif
