-- NOTE (WilC5 / S4OnePoint_general): a clash-free *copy* of `Submission/Work/WilC5/StepSeqLogPres.lean`
-- (proved by colleagues): every import in the `StepSeqLogClosure`/`StepSeqLogPres` chain is
-- redirected to the corresponding `…Cut` copy (in which the auxiliary definition `canonSyn` is
-- renamed), because the original `Work.WilC5.canonSyn` clashes with the identically named
-- definition of `Submission/Work/WilC5/StepKeyOfValProp.lean`, which is imported transitively by
-- `Submission/Work/WilC5/ExistsStepSeq.lean`; both are needed by the final assembly of vdDMM
-- Lemma 4.4 (`StepSeqTower.lean`).

import Mathlib
import Submission.Work.WilC5.StepSeqLogPresCoreCut
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.StepSeqDecomp
import Submission.Work.WilC5.StepSeqLogClosureCut
import Submission.Work.WilC5.S4ExpG.OrderEmbed
import Submission.Work.WilC5.S4ExpG.EmbedComm
import Submission.Work.WilC5.S4ExpG.Glue
import Submission.Work.WilC5.StepNoNewAux.logFun_one_add_map_of_modelComplete
import Submission.Work.WilC5.StepNoNewAux.isInfinitesimal_map_of_modelComplete
import Submission.Work.WilC5.StepNoNewAux.absLeOne_two_mul_of_isInfinitesimal
import Submission.Work.WilC5.StepNoNewAux.logFun_one_add_mem_dcl
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.S4ExpF.logFun_zpow
import Submission.Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.leEL_iff_le

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.WilC5

/-- **vdDMM Lemma 4.4, Claim 5 (the log-preservation half)**
(`sources/wilkiesC/DMM.txt`): the embedding of the `n`-th stage of the tower is log-preserving at
the level of the `(n+1)`-st stage.

`K, L ⊨ TE`, `B ≤ K` is `Dcl`-closed and log-closed, `τ : B → L` is a log-preserving embedding,
`S : StepSeq B` is the sequence of the extension step (`xᵢ = S.xs i`, `βᵢ = S.beta i`, signs
`S.pos i`) with the invariants `hnew`, `hunb`, `hdom`, `hchain` and `hind` (Claim 2), `ys` is the
`L`-side sequence with the defining relations `log yᵢ = τ βᵢ ± y_{i+1}` (`hysrel`, which is
`Work.WilC5.StepSeq.ys_rel`, a theorem), and `σ : Fₙ → L`, `σ' : F_{n+1} → L` are the
`LRc`-embeddings of two consecutive stages, agreeing on `B` (`hσB`, `hσ'B`), sending `xᵢ ↦ yᵢ`
(`hσxs`, `hσ'xs`) and with `σ'` extending `σ` (`hσ'ext`).

If `w ∈ Fₙ` and `log w ∈ F_{n+1}` (the latter is the *other* half of Claim 5, proved separately as
`Work.WilC5.StepSeqLogClosure`), then `σ'` commutes with the definable logarithm at `w`:
`σ'(log w) = log (σ' w)`. -/
theorem StepSeqLogPres
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (hK : K ⊨ WilkiesDesign.CG.TE) (hL : L ⊨ WilkiesDesign.CG.TE)
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels) (hVI : WilkiesDesign.CG.ValIneq)
    (hrexpK : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (honeK : (Work.WilC5.oneE : K) = 1)
    (hlenegK : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (hrexpL : ∀ x : L, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL L _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeL : (Work.WilC5.oneE : L) = 1)
    (hlenegL : ∀ x y : L, Work.WilC5.leE x y ↔ x ≤ y)
    {B : WilkiesDesign.CG.LRc.Substructure K}
    (hBdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) ⊆ (B : Set K))
    (hBlog : ∀ x ∈ (B : Set K), Work.WilC5.logFun x ∈ (B : Set K))
    (τ : WilkiesDesign.CG.LRc.Embedding ↥B L)
    (hτlog : ∀ b : ↥B,
      τ ⟨Work.WilC5.logFun (b : K), hBlog (b : K) b.2⟩ = Work.WilC5.logFun (τ b))
    (S : Work.WilC5.StepSeq B)
    (hnew : Work.WilC5.StepSeq.ValueNewAll S)
    (hunb : Work.WilC5.StepSeq.Unbounded S)
    (hdom : Work.WilC5.StepSeq.LogDominated S)
    (hchain : ∀ n : ℕ, Work.WilC5.VLe (Work.WilC5.logFun (S.xs n)) (S.xs (n + 1)))
    (hind : ∀ (n : ℕ) (q : Fin n → ℤ),
      (∃ c ∈ (B : Set K), c ≠ 0 ∧ WilkiesDesign.CG.IsUnitVal
        (c * ∏ i : Fin n, S.xs (i : ℕ) ^ (q i))) → q = 0)
    {y0 : L}
    (hysrel : ∀ i : ℕ, Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 i) =
      (if S.pos i then (τ (S.beta i) : L) + Work.WilC5.StepSeq.ys B τ S y0 (i + 1)
       else (τ (S.beta i) : L) - Work.WilC5.StepSeq.ys B τ S y0 (i + 1)))
    {n : ℕ}
    (σ : WilkiesDesign.CG.LRc.Embedding ↥(Work.WilC5.StepSeq.Fsub hK S n) L)
    (σ' : WilkiesDesign.CG.LRc.Embedding ↥(Work.WilC5.StepSeq.Fsub hK S (n + 1)) L)
    (hσB : ∀ b : ↥B, σ ⟨(b : K), Work.WilC5.StepSeq.B_mem_Fsub hK S n b.2⟩ = τ b)
    (hσxs : ∀ (i : ℕ) (hi : i < n),
      σ ⟨S.xs i, Work.WilC5.StepSeq.xs_mem_Fsub hK S hi⟩ = Work.WilC5.StepSeq.ys B τ S y0 i)
    (hσ'B : ∀ b : ↥B, σ' ⟨(b : K), Work.WilC5.StepSeq.B_mem_Fsub hK S (n + 1) b.2⟩ = τ b)
    (hσ'xs : ∀ (i : ℕ) (hi : i < n + 1),
      σ' ⟨S.xs i, Work.WilC5.StepSeq.xs_mem_Fsub hK S hi⟩ = Work.WilC5.StepSeq.ys B τ S y0 i)
    (hσ'ext : ∀ (w : K) (hw : w ∈ Work.WilC5.StepSeq.Fset S n),
      σ' ⟨w, (Work.WilC5.StepSeq.Fset_mem_Fsub hK S (n + 1)).mp
        (Work.WilC5.StepSeq.Fset_mono S (Nat.le_succ n) hw)⟩ =
      σ ⟨w, (Work.WilC5.StepSeq.Fset_mem_Fsub hK S n).mp hw⟩)
    {w : K} (hw : w ∈ Work.WilC5.StepSeq.Fset S n)
    (hwlog : Work.WilC5.logFun w ∈ Work.WilC5.StepSeq.Fset S (n + 1)) :
    σ' ⟨Work.WilC5.logFun w, (Work.WilC5.StepSeq.Fset_mem_Fsub hK S (n + 1)).mp hwlog⟩ =
      Work.WilC5.logFun (σ' ⟨w, (Work.WilC5.StepSeq.Fset_mem_Fsub hK S (n + 1)).mp
        (Work.WilC5.StepSeq.Fset_mono S (Nat.le_succ n) hw)⟩) := by
  exact StepSeqLogPresCore hK hL hMCr hOM hVI haddK hmulK honeK hlenegK haddL hmulL honeL hlenegL
    hBdcl hBlog τ hτlog S hind hysrel σ' hσ'B hσ'xs hw hwlog

end Work.WilC5
