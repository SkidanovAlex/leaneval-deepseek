import Mathlib
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.A7IndexCalc
import Submission.Work.CORE4.A7UMCard
import Submission.Work.CORE4.fittingIn_eq_self_of_isPGroup

namespace Work.CORE4.NotA7

open Work.GW2 Subgroup

-- LEAF C10.A5' — Bender p. 226: "By (8), this proves A ⊴ U, hence |H : H∩M| = |U : U∩M| = 3."
-- Here `A = F ⊔ K` is the (3,3)-subgroup of `F × K`, and `A7Facts5 B C.D` is
-- `(B.H ⊓ C.D.M).relIndex B.H = 3 ∧ (B.U ⊓ C.D.M).relIndex B.U = 3 ∧
--  ((C.D.F ⊔ C.D.K).subgroupOf B.U).Normal`.
-- Corrected hypotheses: only `U` a 3-group and the exclusion of the exceptional case are needed
-- (not the `K = Z(U)` conjunct of `A7Facts3`); this is exactly the *proved* `Work.CORE4.A7IndexH`
-- (`Submission/Work/CORE4/A7IndexH.lean`, sorry-free) with `A7Facts3` cut to its first conjunct.
-- Route: apply `Case2EightAll` with `p = 3`, `P = F` (`|F| = 3` by A7Facts1).  `Case2InvNormal` is
-- refuted, so the second disjunct of `Case2EightFacts` holds: `Case2EightU B A ≤ 3`, `A ⊴ F(U)`,
-- and `¬ U ≤ M → 3 ≤ Case2EightP0 B P A`.  Since `U` is a 3-group, `F(U) = U`
-- (`fittingIn_eq_self_of_isPGroup`); `A ≤ F ⊔ K` with `|A| = 9 = |F ⊔ K|` gives `A = F ⊔ K`; so
-- `N_U(A) = U`, `N_U(P) = U ⊓ M` (Case2EightFacts) and `p₀ = |U : U ⊓ M| ≤ 3`; and `¬ U ≤ M`
-- because `H = U ⊔ S` (`I.toolkit.split`, `U ⊴ H`), `S ≤ E ≤ M` (A7Facts2) and `¬ H ≤ M`
-- (Case2Pre), so `3 ≤ p₀`.  Finally `|H : H ⊓ M| = |U : U ⊓ M|` from `H = U S`, `S ≤ M`.
-- Useful already-proved helpers (import them): `Submission.Work.CORE4.A7Split` (`A7Split`),
-- `Submission.Work.CORE4.A7IndexCalc` (`A7IndexCalc`), `Submission.Work.CORE4.A7UMCard`
-- (`A7UMCard_b0_le_normalizer`, `A7UMCard_inf`, `A7UMCard_card`, `A7UMCard`),
-- `Submission.Work.CORE4.fittingIn_eq_self_of_isPGroup`, `Submission.Work.CORE4.EightIdxDefs`.
-- IMPORTANT: import ONLY modules that do not declare clashing `Work.GW2.*` names:
-- `Submission.Work.CORE4.*`, `Submission.Work.FUS.*`, `Submission.Work.RED.*`,
-- `Submission.Work.Dihedral.Defs`, `Submission.OddOrder.*`.
theorem A5Weak (I : Work.GW2.C4Inputs) : ∀ (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
    Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
      Work.GW2.A7Facts2 B C.D → IsPGroup 3 B.U → ¬ Work.GW2.Case2InvNormal B C.D →
        Work.GW2.A7Facts5 B C.D := by
  intro G _ _ B C hHyp hA7 h1F h2F hU3 h4F
  obtain ⟨hbc, hcase2, hplus, hseven, height⟩ := hHyp
  obtain ⟨hKcard, hFcard, hK0eq, hpi⟩ := h1F
  obtain ⟨hV4, hVeq, hSleE, hScard, hNVE⟩ := h2F
  -- Bender's `p = 3`, `P = F`, and the objects `A` of (8)
  have h3prime : Nat.Prime 3 := by norm_num
  obtain ⟨A, hObj, hFactsA⟩ := height 3 C.D.F h3prime le_rfl hFcard
  obtain ⟨hObjPrime, hPleF, hPcard, hAleFK, hAcard, hAexp, hPleA, hAuniq⟩ := hObj
  obtain ⟨hK0dvd, hAleFK0, hNormF, hNormPleNormA, hp0odd, hp0lep1, hp1lep, hp0lep,
    hrel8, hcase⟩ := hFactsA
  -- the exceptional branch `I_U(s) ⊴ Ĥ` of (8) is refuted by the hypothesis
  obtain ⟨hu3, hAnormFit, hcond⟩ :
      Work.GW2.Case2EightU B A ≤ 3 ∧
        (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal ∧
        (¬ B.U ≤ C.D.M → 3 ≤ Work.GW2.Case2EightP0 B C.D.F A) := by
    rcases hcase with h | h
    · exact absurd h h4F
    · exact h
  have h2F' : Work.GW2.A7Facts2 B C.D := ⟨hV4, hVeq, hSleE, hScard, hNVE⟩
  have hSleM : (B.S : Subgroup G) ≤ C.D.M := le_trans hSleE (layerIn_le C.D.M)
  have hSplit : B.H = B.U ⊔ (B.S : Subgroup G) := A7Split I hbc h2F'
  -- `F(U) = U` for the 3-group `U`, so `A ⊴ U` and `B₀ = F`
  letI : Fact (Nat.Prime 3) := ⟨h3prime⟩
  have hfit : Work.GW2.fittingIn B.U = B.U := fittingIn_eq_self_of_isPGroup hU3
  have hB0leU : C.D.B0 ≤ B.U := le_trans (C.D.B0_le B) inf_le_left
  have hB0F : C.D.B0 = C.D.F := by
    rw [C.D.F_def, hfit, inf_eq_left.mpr hB0leU]
  have hAleU : A ≤ B.U :=
    le_trans hAleFK (sup_le (Case2Data.F_le_U B C.D) (Case2Data.K_le_U B C.D))
  have hAnormU : (A.subgroupOf B.U).Normal := by
    have h := hAnormFit
    rw [hfit] at h
    exact h
  have hUleNA : B.U ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAleU).mp hAnormU
  have hUinfNA : B.U ⊓ Subgroup.normalizer (A : Set G) = B.U := inf_eq_left.mpr hUleNA
  -- hence `p₀ = |U : N_U(A)| = |U : U ∩ M|`, and `3 ≤ p₀ ≤ 3` since `¬ U ≤ M`
  have hp0eq : Work.GW2.Case2EightP0 B C.D.F A = (B.U ⊓ C.D.M).relIndex B.U := by
    show (B.U ⊓ Subgroup.normalizer (C.D.F : Set G)).relIndex
      (B.U ⊓ Subgroup.normalizer (A : Set G)) = (B.U ⊓ C.D.M).relIndex B.U
    rw [hNormF, hUinfNA]
  have hUnotleM : ¬ B.U ≤ C.D.M := by
    intro hUM
    exact C.pre.1 (by rw [hSplit]; exact sup_le hUM hSleM)
  have hp0ge : 3 ≤ Work.GW2.Case2EightP0 B C.D.F A := hcond hUnotleM
  have hb : (B.U ⊓ C.D.M).relIndex B.U = 3 := by
    rw [← hp0eq]
    omega
  have ha : (B.H ⊓ C.D.M).relIndex B.H = 3 := by
    rw [inf_comm, A7IndexCalc hSplit hSleM, hb]
  -- `A = F ⊔ K` (both have order `9` inside `F ⊔ K`), hence `F ⊔ K ⊴ U`
  have hFKcard : Nat.card ↥(C.D.F ⊔ C.D.K) = 9 := A7UMCard hB0F hKcard hFcard
  have hAeq : A = C.D.F ⊔ C.D.K := by
    refine Subgroup.eq_of_le_of_card_ge hAleFK ?_
    rw [hFKcard, hAcard]
    norm_num
  have hc : ((C.D.F ⊔ C.D.K).subgroupOf B.U).Normal := by
    rw [← hAeq]
    exact hAnormU
  exact ⟨ha, hb, hc⟩

end Work.CORE4.NotA7
