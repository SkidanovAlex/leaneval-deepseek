import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Tactic.Group
import Submission.Work.SSGRoute.C6ValueFormula.coset_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGcrux

open Work.SSGRoute.C6ValueFormula

/-- **The value of a Dirac at a coset.** For a subgroup `H ≤ Γ`, a representation `W` of `↥H` on
which `↥H` acts trivially, the Dirac element of `coInd_H^Γ W` at `x` with value `a` takes the value
`a` exactly on the left coset `H x` (spelled `g * x⁻¹ ∈ H`) and `0` elsewhere. -/
theorem diracSubtypeApply {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ] {H : Subgroup Γ}
    [DecidablePred (· ∈ H)]
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H) (htriv : ∀ (n : ↥H) (x : W.V), W.ρ n x = x)
    (x : Γ) (a : W.V) (g : Γ) :
    (Work.SSGRoute.C6ValueFormula.dirac H.subtype W (fun n _ a => htriv n a) x a).1 g
      = if g * x⁻¹ ∈ H then a else 0 := by
  by_cases hg : g * x⁻¹ ∈ H
  · rw [if_pos hg]
    have hd : H.subtype ⟨g * x⁻¹, hg⟩ * x = g := by
      rw [Subgroup.subtype_apply]; group
    rw [dirac_apply_eq H.subtype W (fun n _ a => htriv n a) x a hd]
    exact htriv ⟨g * x⁻¹, hg⟩ a
  · rw [if_neg hg]
    rw [dirac_apply_of_not H.subtype W (fun n _ a => htriv n a) x a]
    · rintro ⟨d, hd⟩
      refine hg ?_
      have hgd : g * x⁻¹ = (d : Γ) := by rw [← hd, Subgroup.subtype_apply]; group
      rw [hgd]; exact d.2

end Work.SSGcrux
