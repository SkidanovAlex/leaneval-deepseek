import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.SectionsV3
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.exists_setup45
import Submission.Work.NormalComplement.sec4_lemma1ab
import Submission.Work.NormalComplement.section2_prop1_nokinv
import Submission.Work.NormalComplement.sec5_final_clean
import Submission.Work.NormalComplement.sec4_prop1_star
import Submission.Work.NormalComplement.sec4_P2d
import Submission.Work.NormalComplement.p3Normal_of_chIIFourP3Subnormal
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.NormalComplement.NC4.Defs
import Submission.Work.NormalComplement.NC4.prop2a
import Submission.Work.NormalComplement.NC4.prop2b
import Submission.Work.NormalComplement.NC4.prop2cd
import Submission.Work.NormalComplement.S5K.Defs
import Submission.Work.NormalComplement.S5K.lemma1d_v3
import Submission.Work.NormalComplement.S5K.prop1_step1
import Submission.Work.NormalComplement.S5K.prop1_step2
import Submission.Work.NormalComplement.S5K.prop1_step3
import Submission.Work.NormalComplement.S5K.prop1_step4
import Submission.Work.NormalComplement.S5K.prop1_step5
import Submission.Work.NormalComplement.S5K.prop1_concl
import Submission.Work.NormalComplement.S5K.prop2cd_w2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- **End of Ch. III §4, in the `Section2Prop'` (no `KInvariantUnderD`) form**: `Setup45A` yields
`Setup5`.  This is the assembly of `exists_setup5_kinv` with the one place that consumed
`KInvariantUnderD H t` (namely `S5K.lemma1d`, §4 Lemma 1 (d)) replaced by `S5K.lemma1d_v3`, which
derives the same conclusion from `Section2Prop'` alone (the lead's reordered case split of §2
Prop. 1, cf. `NOTES_LEAD_bs_appxgap.md`).  Every remaining §4 input (`S5K.prop1_step1..5`,
`S5K.prop1_concl`, `NC4.prop2a/b/cd`) is independent of `KInvariantUnderD`. -/
theorem exists_setup5_nokinv (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hCC : Work.NormalComplement.ControlCorollaryProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hVII : Work.NormalComplement.Design.AppVIIProp)
    (hTrans : Work.NormalComplement.TransferProp)
    (hStrat : Work.NormalComplement.StrategyProp)
    (hS2 : Work.NormalComplement.Section2Prop') {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A) :
    ∃ r : ℕ, Work.NormalComplement.Design.Setup5 G H t W p P A r := by
  classical
  -- §4 Lemma 1 (d), from `Section2Prop'` (no `KInvariantUnderD` needed).
  have h1d : NC4.Lemma1dConc H t W p P A := S5K.lemma1d_v3 hFT hTrans hStrat hS2 h
  have hPsyl : IsSylowIn p P (Submission.Blueprint.twoPoint H t) := h1d.1
  -- §4 Prop. 1, steps 1–5 and the two structural clauses.
  have h1 : S5K.Step1Conc H t p P A := S5K.prop1_step1 hFT hP3 hCC h hPsyl
  have h2 : S5K.Step2Conc H t p P A := S5K.prop1_step2 hFT hP3 hCC hStrat h hPsyl h1
  have h3 : S5K.Step3Conc H t p P A := S5K.prop1_step3 hFT hC4 hP3 hCC hIII h hPsyl h1 h2
  have h4 : S5K.Step4Conc H t p P A := S5K.prop1_step4 hFT hC4 hP3 hCC hIII h hPsyl h3
  have h5 : S5K.Step5Conc H t p P A := S5K.prop1_step5 hFT hC4 hP3 hCC hIII hVII h hPsyl h4
  obtain ⟨h6a, h6b⟩ := S5K.prop1_concl hFT hC4 hP3 hCC hIII hVII h hPsyl h4 h5
  have hP1 : NC4.Prop1Conc H t W p P A := ⟨h4, h5, h6a, h6b⟩
  -- §4 Prop. 2 (a), (b), (c), (d).
  have h2a : NC4.Prop2aConc H t W p P A := NC4.prop2a hFT h h1d hP1
  have h2b : NC4.Prop2bConc H t W p P A := NC4.prop2b hFT hC4 h h1d hP1 h2a
  obtain ⟨r, a, hr, ha, hrdvd, hKcard, hfitV, hfitVne, hfitVsyl⟩ :=
    NC4.prop2cd hFT hC4 h h1d hP1 h2a h2b
  refine ⟨r, { toSetup45A := h,
               P_syl := hPsyl,
               E_eq := h1d.2.2.symm,
               E'_inf := h1d.2.1,
               E'_eq := h2a.2.1,
               E'V := h2a.2.2,
               E'_nil := h2b.1,
               E'_hall := h2b.2.1,
               E'_primes := h2b.2.2,
               CAP_cop := fun q hq hqdvd => (h4 q hq hqdvd).2.2.2,
               r_prime := hr,
               r_dvd := hrdvd,
               K_card := ⟨a, ha, hKcard⟩,
               fitV := hfitV,
               fitV_ne := hfitVne,
               fitV_syl := hfitVsyl }⟩

/-- **Ch. III §4–§5 assembled** (pp. 179–187): `Work.NormalComplement.Section45Prop`, i.e. the
minimal `W` satisfying (D1) and (D2) is contradictory.  Pure glue:
`exists_setup45` → `sec4_lemma1ab` → `exists_setup5_nokinv` (fed by the `KInvariantUnderD`-free
§2 Prop. 1 `section2_prop1_nokinv`) → `sec5_final_clean`. -/
theorem section45Prop_of (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hV : Work.NormalComplement.AppVProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hVII : Work.NormalComplement.Design.AppVIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop)
    (hBC : Work.NormalComplement.Design.BurnsideClassProp)
    (hCC : Work.NormalComplement.ControlCorollaryProp)
    (hBP : Work.NormalComplement.BenderPrelimProp)
    (hTrans : Work.NormalComplement.TransferProp)
    (hStrat : Work.NormalComplement.StrategyProp)
    (hS2 : Work.NormalComplement.Section2Prop) :
    Work.NormalComplement.Section45Prop := by
  intro G _ _ hSit H hH t ht2 htH W hmin hEne hD1 hD2
  -- §4 entry: a prime `p ∣ |E : E'|` and a subgroup `P` of order `p` of `V ∩ E`.
  obtain ⟨p, P, h45⟩ := exists_setup45 hFT hSit hH ht2 htH hmin hEne hD1 hD2
  -- §4 Lemma 1 (a),(b): the complement `A` of `P` in `V`, giving `Setup45A`.
  obtain ⟨A, h45A⟩ := sec4_lemma1ab hFT hC4 hMod hV h45
  -- §2 Prop. 1 without the (undischargeable) `KInvariantUnderD` input, then §4 → `Setup5`.
  have hS2' : Work.NormalComplement.Section2Prop' := section2_prop1_nokinv hFT hBP hC4 hP3
  obtain ⟨r, h5⟩ := exists_setup5_nokinv hFT hC4 hP3 hCC hIII hVII hTrans hStrat hS2' h45A
  -- §5: `Setup5` is contradictory.
  exact sec5_final_clean hFT hA hC hC4 hP3 hIII hVII hMF2 hCor1 hBC hBP h5

end Work.NormalComplement
