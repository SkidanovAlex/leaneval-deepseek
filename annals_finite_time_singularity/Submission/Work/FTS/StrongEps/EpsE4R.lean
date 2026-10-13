/-
# `StrongEps/EpsE4R.lean` — **E4, new frozen form** (OPEN LEAF)

curric-46 lead install (2026-10-11), `cbc/fts_strongeps_c1c5_ruling.md` §6 (room / `C₀`).
Replaces `EpsODE.EpsUniform_of_data` / `EpsE4Thr` on the `theorem_1_v2` cone (both stay, off the
cone).  The constant `C★` comes BEFORE `C₀`; the threshold `α₄` AFTER `C₀, Ce, Cs, ρ` and BEFORE
`K, Φs, E, g₀` — the order in which `FinalV2.fts_inputs'` fixes them (the wire sets `C₀ := C★`).
`EpsE4Thr` + `EpsUniformMem.mono` would give this with `C★ = 1`, so it is weaker than `EpsE4Thr`.
Notes for the prover: run the barrier/local step at the class ball `C₁ := 2·C₀` with
`MuLamOK α C₁` from `EpsE4Thr.MuLamOK_of_hEll_hstar` (α₄ ≤ its threshold); `α₄` must be uniform
in `K, Φs, E, g₀`.  The conjunct `L12 g₀ 0 = 0` of `EpsUniformMem` is NOT a hypothesis: derive it
from `hd` (`ClassC (J_ε g₀)`, field `l12`) + `L12_Jeps_sub_le4` (ε → 0), with `HkMem α 4 g₀` from
`HkMem α 6` + `SmoothOpen` (`HkMem_mono_of_contDiffOn`) (review F4).

**2026-10-12 (curric-46, `cbc/fts_e5swap_e4chapters.md` + REVIEW):** `EpsDecay` was edited in place
(bounded blocks), and `EpsE4R` is now PROVED from the three corrected chapters by
`E4R3.EpsE4R3_of_chapters`; its open leaves are `E4R3.localStepChapter3_leaf`,
`E4R3.aprioriChapter3_leaf`, `E4R3.decayChapter3_leaf` (`StrongEps/E4R3/`).

**2026-10-12 later (curric-46, `cbc/fts_apriori6_ruling.md` §4 + REVIEW):** `AprioriChapter3` is
unprovable as stated (no ε-uniform `ℋ⁶` producer).  `EpsE4R` is RESTATED with two added
hypotheses — kernel symmetry `∀ p, ρ (-p) = ρ p` and `StarPkg6 α Cs Φs` — and proved by
`E4R4.EpsE4R4_of_chapters` with `E4R4.aprioriChapter4_leaf` (`StrongEps/E4R3/Apriori4.lean`).
`E4R3.aprioriChapter3_leaf` is superseded (off the cone).

**2026-10-12 later still (curric-46, `cbc/fts_regularity_interface.md` + REVIEW): statement
UNCHANGED; proof re-pointed** to the flow-class assembly `E4R5.EpsE4R5_of_chapters`
(`E4R3/Flow5.lean`, PROVED): the local step from `E4R5.localStepChapter5_of_XStepInvariant`
(`E4R3/Flow5Local.lean`; LEAF-A `epsFlowP_of_xball`) with `XStepInvariant` from
`E4R5.XStepInvariant_of_regD` (`EpsE4Thr/XStepAssemblyD.lean`; LEAF-D `regFromVolterra'`, LEAF-D2
`regData_of_xball`), the a-priori chapter from the halves `E4R5.fourthChapterBF_leaf`
(`E4R3/Fourth5.lean`) and `E4R5.sixthChapterBF_leaf` (`E4R3/Sixth5.lean`).  `localStepChapter3_leaf`
and `E4R4.aprioriChapter4_leaf` are now off the cone (left in place).
-/
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStepAssemblyWired
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsODEDefs
import Submission.Work.FTS.StrongEps.E4R3.Flow5
import Submission.Work.FTS.StrongEps.E4R3.Flow5Local
import Submission.Work.FTS.StrongEps.E4R3.Sixth5
import Submission.Work.FTS.StrongEps.E4R3.Fourth5
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStepAssemblyD
import Submission.Work.FTS.StrongEps.E4R3.Decay3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **E4 (room ruling, restated 2026-10-12 with kernel symmetry + `StarPkg6`)**.  Proved from the
corrected chapters (`StrongEps/E4R3/`, a-priori chapter v4). -/
theorem EpsE4R : ∀ {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}, IsSmoothKernel ρ → (∀ p : ℝ × ℝ, ρ (-p) = ρ p) →
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C₀ : ℝ, Cstar ≤ C₀ → ∃ α₄ : ℝ, 0 < α₄ ∧
    ∀ α ∈ Set.Ioc 0 α₄, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}, 0 ≤ K →
    (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    MuLamOK α C₀ Φs E →
    (∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀) →
    Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2 →
    Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K * α ^ 2 →
    EpsUniformMem α ρ Φs E g₀ C₀ K := fun hρ hρs =>
  EpsE4Thr.E4R5.EpsE4R5_of_chapters hρ
    (EpsE4Thr.E4R5.localStepChapter5_of_XStepInvariant hρ (fun C₀ hC₀ =>
      ⟨1, one_pos, le_rfl, fun _ _ =>
        EpsE4Thr.XStepWired.XStepInvariant_of_regDW (C₀ := C₀) (by linarith) hρ⟩))
    (EpsE4Thr.E4R5.aprioriChapter5_of_halves (EpsE4Thr.E4R5.fourthChapterBF_leaf hρ)
      (EpsE4Thr.E4R5.sixthChapterBF_leaf hρ hρs))
    (EpsE4Thr.E4R3.decayChapter3_leaf hρ)

end Work.FTS.StrongEps
