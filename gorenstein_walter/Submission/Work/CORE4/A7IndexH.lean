import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.A7IndexCalc
import Submission.Work.CORE4.A7UMCard
import Submission.Work.CORE4.fittingIn_eq_self_of_isPGroup

namespace Work.CORE4

open Subgroup

/-- **LEAF C10.A5 `A7IndexH`** (Bender p. 226): "By (8), this proves `A ⊲ U`, hence
`|H : H∩M| = |U : U∩M| = 3`."  Here `A = F × K`, so `F ⊔ K ⊴ U`.

`A7IndexHProp I` gives, from `Hyp9 G B C`, `IsA7Case C.D`, `A7Facts1`–`A7Facts4`:

    A7Facts5 B C.D  =  (B.H ⊓ C.D.M).relIndex B.H = 3  ∧  (B.U ⊓ C.D.M).relIndex B.U = 3  ∧
                       (C.D.F ⊔ C.D.K) ⊴ B.U   (as `(C.D.F ⊔ C.D.K).subgroupOf B.U`)

Route (design pass 10 §3.2, A5): `Case2EightAll` at `P = F`, `p = 3` (`A7Facts1`), with the
exceptional clause refuted by `A7Facts4` (`Case2EightFacts` then gives
`A ⊴ F(U)`, `u ≤ p`, `N_U(P) = U ∩ M`, `¬ U ≤ M → 3 ≤ p₀`); `F(U) = U` by `A7Facts3`, so
`A = F ⊔ K ⊴ U` and `u = 1`; from `p₀ = |U : N_U(A)| = |U : U ∩ M| = 3`; and
`|H : H ∩ M| = |U : U ∩ M|` because `H = U·S` (`I.toolkit.split`) and `S ≤ M` (`A7Facts2`).

Formalisation: the four isolated steps are separate (proved) lemmas, imported above —
`Work.CORE4.A7Split` (`H = U ⊔ S`, via `I.thm26`, a four-group inside `S`, so `S` is not cyclic
and hence `S ≃* D₄` by `BenderCtx.sylow`, then `I.toolkit.split`), `Work.CORE4.A7IndexCalc`
(`|H : H ⊓ M| = |U : U ⊓ M|` from `H = U ⊔ S`, `S ≤ M`),
`Work.CORE4.fittingIn_eq_self_of_isPGroup` (so that `F(U) = U` for the 3-group `U`, turning
`A ⊴ F(U)` from (8) into `A ⊴ U`), and `Work.CORE4.A7UMCard` (`|F ⊔ K| = 9`, the two
eigenspaces of `s` on `U ⊓ M`), which gives `A = F ⊔ K`. -/
theorem A7IndexH (I : Work.GW2.C4Inputs) : Work.GW2.A7IndexHProp I := by
  intro G _ _ B C hHyp hA7 h1F h2F h3F h4F
  obtain ⟨hbc, hcase2, hplus, hseven, height⟩ := hHyp
  obtain ⟨hKcard, hFcard, hK0eq, hpi⟩ := h1F
  obtain ⟨hV4, hVeq, hSleE, hScard, hNVE⟩ := h2F
  obtain ⟨hU3, hB0F, hoddCoreF, hKUZ, hXbound⟩ := h3F
  -- Bender's `p = 3`, `P = F`, and the objects `A` of (8)
  have h3prime : Nat.Prime 3 := by norm_num
  obtain ⟨A, hObj, hFactsA⟩ := height 3 C.D.F h3prime le_rfl hFcard
  obtain ⟨hObjPrime, hPleF, hPcard, hAleFK, hAcard, hAexp, hPleA, hAuniq⟩ := hObj
  obtain ⟨hK0dvd, hAleFK0, hNormF, hNormPleNormA, hp0odd, hp0lep1, hp1lep, hp0lep,
    hrel8, hcase⟩ := hFactsA
  -- the exceptional branch `I_U(s) ⊴ Ĥ` of (8) is refuted by `A7Facts4`
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
  -- `F(U) = U` for the 3-group `U`, so `A ⊴ U`
  letI : Fact (Nat.Prime 3) := ⟨h3prime⟩
  have hfit : Work.GW2.fittingIn B.U = B.U := fittingIn_eq_self_of_isPGroup hU3
  have hAleU : A ≤ B.U :=
    le_trans hAleFK (sup_le (Work.GW2.Case2Data.F_le_U B C.D) (Work.GW2.Case2Data.K_le_U B C.D))
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

end Work.CORE4
