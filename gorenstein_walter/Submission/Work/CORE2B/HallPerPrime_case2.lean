import Mathlib
import Submission.Work.CORE2B.HallPerPrime_aux
import Submission.Work.CORE2B.HallPerPrime_Xodd
import Submission.Work.CORE2B.HallPerPrime_tSylow
import Submission.Work.CORE2B.HallPerPrime_pi_helpers
import Submission.Work.CORE2B.CentralizesNormalizer
import Submission.Work.CORE2B.dihedral_index_two

/-!
# The per-prime step of Bender's Theorem 2.10: the failure configuration produces Case 2

Write `X := O_p(U) ⊓ C_G(s)`.  Assuming `1 ≠ X ≠ O_p(U)`, Bender's argument runs
(1.1(ii)) to a `t`-invariant Sylow `p`-subgroup `P` of `O(C_G(s))` with `X ≤ P`,
then (1.1(iv), proved as `Work.CORE2B.CentralizesNormalizer`) to an element `y ∈ N_P(X)`
with `t y t⁻¹ ≠ y`, and finally applies Lemma 2.7 to a coatom `M ≥ N_G(X)`.  Since
`y ∈ N_G(X) ≤ M` we get `1 ≠ [t,y] ∈ [M,t] ⊆ F_{π'}(M)` with `[t,y]` a `p`-element,
`p ∈ π = π(F(Ĥ))` — a contradiction.  Hence `Case2 B` holds.
-/

open scoped commutatorElement

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {G : Type} [Group G] [Finite G]

/-- Notation: `X = O_p(U) ⊓ C_G(s)`. -/
abbrev pX (B : Work.GW2.BenderSetup G) (s : G) (p : ℕ) : Subgroup G :=
  Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G)

/-- `t` normalizes `O_p(U)`. -/
theorem t_mem_normalizer_pCoreIn (B : Work.GW2.BenderSetup G) (p : ℕ) [Fact p.Prime] :
    B.t ∈ Subgroup.normalizer ((Work.GW2.pCoreIn p B.U : Subgroup G) : Set G) := by
  have htN : B.t ∈ Subgroup.normalizer (B.U : Set G) :=
    mem_normalizer_U_of_mem_S B (B.S0_le B.t_mem)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_conj_pCoreIn (U := B.U) (p := p) htN)

/-- `s` normalizes `O_p(U)`. -/
theorem s_mem_normalizer_pCoreIn (B : Work.GW2.BenderSetup G) (s : G) (p : ℕ) [Fact p.Prime]
    (hsN : s ∈ Subgroup.normalizer (B.U : Set G)) :
    s ∈ Subgroup.normalizer ((Work.GW2.pCoreIn p B.U : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_conj_pCoreIn (U := B.U) (p := p) hsN)

/-- `t` commutes with `s` (both lie in `S`, `t` being central in `S`). -/
theorem t_mul_s_eq (B : Work.GW2.BenderSetup G) (s : G) (hs : s ∈ (B.S : Subgroup G)) :
    B.t * s = s * B.t := (t_central_in_S B s hs).symm

/-- `t` normalizes `X = O_p(U) ⊓ C_G(s)`: it normalizes `O_p(U)` and fixes `s`. -/
theorem t_mem_normalizer_pX (B : Work.GW2.BenderSetup G) (s : G) (p : ℕ) [Fact p.Prime]
    (hs : s ∈ (B.S : Subgroup G)) :
    B.t ∈ Subgroup.normalizer ((pX B s p : Subgroup G) : Set G) := by
  have htN : B.t ∈ Subgroup.normalizer (B.U : Set G) :=
    mem_normalizer_U_of_mem_S B (B.S0_le B.t_mem)
  have hconjs : (MulAut.conj B.t) s = s := by
    rw [MulAut.conj_apply, t_mul_s_eq B s hs]
    group
  erw [Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.map_inf (Work.GW2.pCoreIn p B.U) (Subgroup.centralizer ({s} : Set G))
      (MulAut.conj B.t).toMonoidHom (MulAut.conj B.t).injective,
    map_conj_pCoreIn (U := B.U) (p := p) htN,
    hallXodd_map_centralizer (MulAut.conj B.t) ({s} : Set G), Set.image_singleton, hconjs]

/-- `s` normalizes `X` (it normalizes `O_p(U)` and commutes with itself). -/
theorem s_mem_normalizer_pX (B : Work.GW2.BenderSetup G) (s : G) (p : ℕ) [Fact p.Prime]
    (hsN : s ∈ Subgroup.normalizer (B.U : Set G)) :
    s ∈ Subgroup.normalizer ((pX B s p : Subgroup G) : Set G) := by
  have hconjs : (MulAut.conj s) s = s := by
    rw [MulAut.conj_apply]
    group
  erw [Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.map_inf (Work.GW2.pCoreIn p B.U) (Subgroup.centralizer ({s} : Set G))
      (MulAut.conj s).toMonoidHom (MulAut.conj s).injective,
    map_conj_pCoreIn (U := B.U) (p := p) hsN,
    hallXodd_map_centralizer (MulAut.conj s) ({s} : Set G), Set.image_singleton, hconjs]

/-- `⟨t, s⟩ ≤ N_G(X)`: both generators normalize `X`. -/
theorem closure_pair_le_normalizer_pX (B : Work.GW2.BenderSetup G) (s : G) (p : ℕ)
    [Fact p.Prime] (hs : s ∈ (B.S : Subgroup G)) (hsN : s ∈ Subgroup.normalizer (B.U : Set G)) :
    Subgroup.closure ({B.t, s} : Set G) ≤
      Subgroup.normalizer ((pX B s p : Subgroup G) : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases hx with rfl | hx
  · exact t_mem_normalizer_pX B s p hs
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact s_mem_normalizer_pX B s p hsN

/-- `X ≤ F(U)`. -/
theorem pX_le_fittingIn_U (B : Work.GW2.BenderSetup G) (s : G) (p : ℕ) [Fact p.Prime] :
    pX B s p ≤ Work.GW2.fittingIn B.U :=
  inf_le_left.trans (pCoreIn_le_fittingIn_U B)

/-- `X ≤ F(Ĥ)`. -/
theorem pX_le_fittingIn_Hhat (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (s : G) (p : ℕ) [Fact p.Prime] :
    pX B s p ≤ Work.GW2.fittingIn B.Hhat :=
  (pX_le_fittingIn_U B s p).trans (fittingIn_U_le_fittingIn_Hhat h26 G hFT hCtx B)

end Work.CORE2B
