import Mathlib
import Submission.Work.SSGRoute.CC.MagFourDefs
import Submission.Work.SSGRoute.CC.MagFourMap
import Submission.Work.SSGRoute.CC.MagFourFreeGroup
import Submission.Work.SSGRoute.CC.DoubleWordEqCommutator
import Submission.Work.SSGRoute.CC.MagLeadCommutatorInvPair
import Submission.Work.SSGRoute.magLead_inv_cube_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CC.LNS3

open Work.SSGRoute
open Work.SSGRoute.prop5

/-- **The class of the double witness.**

`doubleWord X σ g = (σ(g·σg))⁻¹(g·σg)` is the norm of the `σ`-paired element `g·σg`.
For an involution `σ` (`hσ`) and `g ∈ γ₂ = lowerCentralSeries 1`,
`mag4 X (doubleWord X σ g) = phi X (σ : X → X) (mag2 X g)`.

Proof: with `hσ`, `doubleWord X σ g = g⁻¹ * (σg)⁻¹ * g * (σg) = ⁅g⁻¹, (σg)⁻¹⁆`, and both entries
lie in `γ₂`, so `magLead_commutator_inv_pair` gives
`magLead 5 (doubleWord X σ g) = a * b - b * a` with `a = magLead 5 g`, `b = magLead 5 (σg)`.
Lifting `a`, `b` to elements of `fil X 2`, the degree-`4` component of `a * b` is the product of the
degree-`2` components (`degPart_mul_of_mem_fil`), and those are `mag2 X g` and
`mag2 X (σg) = sigA X σ (mag2 X g)` (`mag2_congr`).  Finally `-1 = 1` in `𝔽₂`. -/
theorem mag4_doubleWord_proved (X : Type) (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x) (g : FreeGroup X)
    (hg : g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 1) :
    Work.SSGRoute.CC.mag4 X (Work.SSGRoute.doubleWord X σ g)
      = Work.SSGRoute.CC.phi X (σ : X → X) (Work.SSGRoute.CC.mag2 X g) := by
  have hσg : FreeGroup.freeGroupCongr σ g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 1 :=
    Work.SSGRoute.CC.freeGroupCongr_mem_lowerCentralSeries_one X σ hg
  -- lifts of the two Magnus leading terms lying in `fil X 2`
  obtain ⟨a, ha, haeq⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X 5))
      (Ideal.Quotient.mk_surjective)).1
    (magLead_mem_filq (X := X) 5 2 (by norm_num) (by norm_num) hg)
  obtain ⟨b, hb, hbeq⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X 5))
      (Ideal.Quotient.mk_surjective)).1
    (magLead_mem_filq (X := X) 5 2 (by norm_num) (by norm_num) hσg)
  -- the commutator form of the double word and the bracket formula for its leading term
  have hcomm :=
    Work.SSGRoute.CC.magLead_commutator_inv_pair g (FreeGroup.freeGroupCongr σ g) hg hσg
  have hword := Work.SSGRoute.CC.doubleWord_eq_commutator σ hσ g
  have hkey : magLead 5 (Work.SSGRoute.doubleWord X σ g)
      = Ideal.Quotient.mk (fil X 5) (a * b - b * a) := by
    rw [hword, hcomm, ← haeq, ← hbeq, map_sub, map_mul, map_mul]
  -- `mag4` is the degree-`4` part of the lifted ring commutator
  have hdeg : Work.SSGRoute.CC.mag4 X (Work.SSGRoute.doubleWord X σ g)
      = red2 X (degPart (X := X) 4 (a * b - b * a)) := by
    rw [Work.SSGRoute.CC.mag4, hkey, degq_mk (j := 4) (by norm_num) X (a * b - b * a)]
  have h4a : degPart (X := X) 4 (a * b) = degPart (X := X) 2 a * degPart (X := X) 2 b :=
    degPart_mul_of_mem_fil ha hb
  have h4b : degPart (X := X) 4 (b * a) = degPart (X := X) 2 b * degPart (X := X) 2 a :=
    degPart_mul_of_mem_fil hb ha
  have hAg : red2 X (degPart (X := X) 2 a) = Work.SSGRoute.CC.mag2 X g := by
    rw [← degq_mk (j := 2) (by norm_num) X a, haeq, Work.SSGRoute.CC.mag2]
  have hAb :
      red2 X (degPart (X := X) 2 b) = sigA X (σ : X → X) (Work.SSGRoute.CC.mag2 X g) :=
    (degq_mk (j := 2) (by norm_num) X b).symm.trans (by
      rw [hbeq]
      exact Work.SSGRoute.CC.mag2_congr X σ g)
  have hred : red2 X (degPart (X := X) 4 (a * b - b * a))
      = Work.SSGRoute.CC.mag2 X g * sigA X (σ : X → X) (Work.SSGRoute.CC.mag2 X g)
        - sigA X (σ : X → X) (Work.SSGRoute.CC.mag2 X g) * Work.SSGRoute.CC.mag2 X g := by
    rw [show degPart (X := X) 4 (a * b - b * a)
        = degPart (X := X) 2 a * degPart (X := X) 2 b
          - degPart (X := X) 2 b * degPart (X := X) 2 a by rw [map_sub, h4a, h4b]]
    rw [map_sub, map_mul, map_mul, hAg, hAb]
  rw [hdeg, hred, Work.SSGRoute.CC.phi, sub_eq_add_neg, Work.SSGRoute.CC.neg_eq_self_zmodTwo]

end Work.SSGRoute.CC.LNS3
