import Submission.Work.Hering.HardCore.Defs
import Submission.Work.Hering.HardCore.abelian_case
import Submission.Work.Hering.V.ExponentTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The hard core of Hering's theorem

`Work.Hering.no_reduced_config`: no finite group carries the reduced configuration
`Work.Hering.ReducedConfig`. The proof splits into the abelian case
(`Work.Hering.HardCore.abelian_case`, proved in `HardCore/abelian_case.lean`) and the non-abelian
case `Work.Hering.NonAbelianCaseProp` (§4, whose classification input is named separately).
-/

set_option autoImplicit false

namespace Work.Hering

open LeanEval.GroupTheory.Defs

/-- **The hard core of Hering's theorem** (Peterfalvi I Ch. IV §3–§4): the reduced configuration
of §2 is impossible, given the non-abelian case `NonAbelianCaseProp` of §4.

In the abelian case we use `HardCore.abelian_case`: `Inv(G) = V#` already forces every involution
of `G` into `C_G(V)`, while §3 Prop. 2 produces an involution *outside* `C_G(V)`. -/
theorem no_reduced_config (hNonAb : ∀ {G : Type} [Group G] [Finite G], NonAbelianCaseProp (G := G)) :
    NoReducedConfigProp := by
  intro G _ _ hred
  obtain ⟨V, hVnorm, hcard, hexp, hinvG, hC2, hAut⟩ := hred
  set C : Subgroup G := Subgroup.centralizer ((V : Set G)) with hCdef
  have hVC : V ≤ C := le_centralizer_of_exponent_two hexp
  have hinvC : ∀ x ∈ C, orderOf x = 2 → x ∈ V := fun x _ hx => hinvG x hx
  have hnoinv : ∀ u : G, orderOf u = 2 → u ∈ C := fun u hu => hVC (hinvG u hu)
  by_cases hab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x
  · exact HardCore.abelian_case V C hVnorm hcard hexp hCdef hC2 hinvC hAut hab hnoinv
  · exact hNonAb V C hVnorm hcard hexp hCdef hC2 hinvC hAut hab

end Work.Hering
