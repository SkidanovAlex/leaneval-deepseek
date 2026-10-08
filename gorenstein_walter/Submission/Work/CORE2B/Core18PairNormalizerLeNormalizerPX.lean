import Mathlib
import Submission.Work.CORE2B.HallPerPrime_case2
import Submission.Work.CORE2B.C18PairNormalizerLeNormalizerPX_proved

/-!
# GW design 18, item A′, leaf H2: `N_S(⟨t,s⟩)` normalizes `X = O_p(U) ∩ C_G(s)`

Bender p. 222: "Clearly, `N_S(⟨t,s⟩) ≤ M`."

Sketch (0.1–0.2k).  Let `σ ∈ S` normalize `V = ⟨t,s⟩ = {1,t,s,ts}`.  `σ` normalizes `O_p(U)`
(`s_mem_normalizer_pCoreIn` + `mem_normalizer_U_of_mem_S`).  `σ t σ⁻¹ = t` (`t_central_in_S`), so
`σ s σ⁻¹ ∈ V` has order 2 and is `≠ t` (else `s = t ∈ S₀`), hence `∈ {s, ts}`.  Conjugation maps
`O_p(U) ∩ C(s)` to `O_p(U) ∩ C(σsσ⁻¹)`, and `O_p(U) ∩ C(ts) = O_p(U) ∩ C(s)` because `t`
centralizes `U` (`t_commutes_U`).  `orderOf s = 2` from `orderOf_eq_two_of_mem_S_notMem_S0`.
-/


namespace Work.GW18

open Subgroup

theorem Core18PairNormalizerLeNormalizerPX {G : Type} [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (s : G)
    (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (p : ℕ) [Fact p.Prime] :
    (B.S : Subgroup G) ⊓ Subgroup.normalizer ((Subgroup.closure ({B.t, s} : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Work.CORE2B.pX B s p : Subgroup G) : Set G) := Work.CORE2B.C18PairNormalizerLeNormalizerPX_proved hCtx B s hs hs0 p

end Work.GW18
