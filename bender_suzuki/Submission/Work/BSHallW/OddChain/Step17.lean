import Mathlib
import Submission.Work.BSHallW.Defs
import Submission.Work.ThmF.ChV3.Step16Step12
import Submission.Work.ThmF.ChV3.Prove.cst_isPGroup
import Submission.Work.ThmF.ChV3.Prove.cst_center_sylow
import Submission.Work.ThmF.ChV3.Prove.T_sig_facts
import Submission.Work.ThmF.ChV3.Prove.cP_inf_cst
import Submission.Work.ThmF.ChV3.Prove.L_facts
import Submission.Work.ThmF.ChV3.Prove.W_V_on_L
import Submission.Work.ThmF.ChV3.Prove.P_on_L
import Submission.Work.ThmF.ChV3.Prove.A_LV_facts
import Submission.Work.ThmF.ChV3.Prove.A_stronglyReal_normalizer
import Submission.Work.ThmF.ChV3.Prove.A_weaklyClosed
import Submission.Work.ThmF.ChV3.Prove.normalizerA_hasNormalIndexP
import Submission.Work.ThmF.ChV3.Prove.G0_hasNormalIndexP_of_fixed_elementary
import Submission.Work.ThmF.ChV3.Prove.G2_card_sup_closure_pair_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Step16Step17` — §3 step (17): case (10-2) is impossible

The lead's pass-16 design (`ThmF/_design16/ThmF16.lean`, `step17`), with the leaves taken from
`Submission/Work/ThmF/ChV3/Prove/`.  `A = Z₁PΣ` is abelian (`A_LV_facts`) and weakly closed in the
Sylow 3-subgroup `C_G(st)` (`A_weaklyClosed`); Hall–Wielandt plus
`N_G(A)` having a normal subgroup of index 3 (`normalizerA_hasNormalIndexP`) give
`HasNormalIndexP 3 G`, against simplicity.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.BSHallW.OddChain

open Work.ThmF Work.ThmF.ChV3

variable {G : Type} [Group G] [Finite G]

/-- **§3 step (17)**: case (10-2) is impossible. -/
theorem step17 (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (hHW : HallWielandtOddProp)
    {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : CtxF H Q t s r P) (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P)
    (hpf : Nat.card P = orderOf (s * t)) {T : Subgroup G} (h11 : Step11Out H Q t P h15.R T)
    (d : Case102 H Q t s P) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := (Work.ThmF.ChV3.Prove.cst_center_sylow hFT hC4 c h15 h7 hpf h11 d).2
  have hsyl : Nat.card ↥(Cst s t) = 3 ^ (Nat.card G).factorization 3 := by
    rw [hcard]; rfl
  let S : Sylow 3 G := Sylow.ofCard (Cst s t) hsyl
  have hS : (S : Subgroup G) = Cst s t := Sylow.coe_ofCard (Cst s t) hsyl
  have hAS : Asub H P s t ≤ (S : Subgroup G) := hS ▸ Work.ThmF.ChV3.Prove.A_le_cst c
  have hwc := Work.ThmF.ChV3.Prove.A_weaklyClosed hFT hC4 c h15 h7 hpf h11 d
  have hab := comm_of_isMulCommutative
    (Work.ThmF.ChV3.Prove.A_LV_facts hFT hC4 c h15 h7 hpf h11 d).1
  have hiff := hHW G 3 Nat.prime_three (by norm_num) S (Asub H P s t) hAS
    (by intro g hg; rw [hS] at hg; exact hwc g hg) hab
  have hG : HasNormalIndexP 3 G :=
    hiff.mpr (Work.ThmF.ChV3.Prove.normalizerA_hasNormalIndexP hFT hC4 c h15 h7 hpf h11 d)
  exact Work.ThmF.Prove.simple_not_hasNormalIndexP Nat.prime_three (by norm_num) c.simple
    (even_card_G c) hG

end Work.BSHallW.OddChain
