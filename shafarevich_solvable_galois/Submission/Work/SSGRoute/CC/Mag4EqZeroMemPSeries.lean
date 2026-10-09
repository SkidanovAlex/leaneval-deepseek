import Mathlib
import Submission.Work.SSGRoute.CC.MagFourDefs
import Submission.Work.SSGRoute.oneStep.magLead_pSeries_divisible
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CC

open Work.SSGRoute.prop5

/-- **`mag4` kills `γ₄ ∩ P₅`.**

`mag4 X z` is the degree-`4` component, reduced mod `2`, of the Magnus image of `z` at truncation
`5` (defined in `Submission/Work/SSGRoute/magFourDefs.lean`).  Every element of
`γ₄ = lowerCentralSeries 3` which also lies in `P₅ = pCentralSeries 2 (FreeGroup X) 4` is killed by
`mag4`.

This is the well-definedness half: it makes `mag4` descend to `E(4,4) = γ₄P₅/P₅`.  Since
`γ₄ ∩ P₅ = γ₄²γ₅` (Schmidt–Wingberg Lemma 4(ii)), it suffices to show that `mag4` kills `γ₅`
(`prop5.magLead_eq_zero_of_mem_succ`) and the squares of `γ₄` (`prop5.magLead_pow` with `N = 5`,
`k = 4`, `p = 2`, giving `magLead 5 (x^2) = (2 : ℤ) • magLead 5 x`, whose degree-`4` mod-`2` part
vanishes); then `mag4` is additive on `γ₄` (`mag4_mul`) so it kills the generated subgroup.  A
direct proof from `Work.SSGRoute.oneStep.magLead_pSeries_divisible` (p = 2, i = 5, j = 4) is also
acceptable. -/
theorem mag4_eq_zero_of_mem_pSeries {X : Type} {t : FreeGroup X}
    (htγ : t ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3)
    (htP : t ∈ Work.Shrinking.pCentralSeries 2 (FreeGroup X) 4) :
    mag4 X t = 0 := by
  classical
  -- The Magnus leading term of `t` at truncation `5` is divisible by `2` inside `filq X 5 4`,
  -- because `t ∈ γ₄ ∩ P₅` (Magnus image has weight `5`).
  obtain ⟨a, _ha, haeq⟩ :=
    Work.SSGRoute.oneStep.magLead_pSeries_divisible (p := 2) X 5 4 (by norm_num) (by norm_num)
      htP htγ
  -- Lift `a` to `FreeAssoc X` and use it as a witness for `magLead 5 t`.
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (I := fil X 5) a
  have hlift : Ideal.Quotient.mk (fil X 5) ((2 : ℤ) • b) = magLead 5 t := by
    rw [map_zsmul, hb, haeq]
    norm_num
  rw [mag4_eq_of_mk hlift]
  -- `degPart 4 ((2 : ℤ) • b) = (2 : ℤ) • degPart 4 b`, and reduction mod `2` is `ℤ`-linear.
  simp only [map_zsmul]
  rw [two_zsmul]
  -- In characteristic `2`, `y + y = 0`.
  have h : red2 X (degPart (X := X) 4 b) + red2 X (degPart (X := X) 4 b) = 0 := by
    conv_lhs => rw [← one_smul (ZMod 2) (red2 X (degPart (X := X) 4 b)),
      ← one_smul (ZMod 2) (red2 X (degPart (X := X) 4 b)), ← add_smul]
    rw [show (1 : ZMod 2) + 1 = 0 from by decide, zero_smul]
  exact h

end Work.SSGRoute.CC
