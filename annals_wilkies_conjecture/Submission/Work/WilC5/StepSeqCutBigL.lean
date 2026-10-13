/-
  WilC5 — the two min-rule computations of vdDMM Lemma 4.4, Claim 4, for a positive `w ∈ Fₙ`.

  `sscb_cut_pos` is Claim 4 apart from the trivial case `w ≤ 0`: given the power decomposition
  `w^Q = z · ∏ xᵢ^{Nᵢ} · (1+ε)` of `StepSeqDecomp`, it produces the cut realisation of `xₙ` over
  `Fₙ` by `yₙ`.  If some `Nᵢ ≠ 0`, the least such index `m` is decided by two min-rule
  computations (`Work.WilC5.CutComp`), one on `K` and one on `L`, glued by order-preservation of
  `σ`; if all `Nᵢ = 0` then `w` lies in the archimedean class of an element of `B`, and the claim
  is `hcutB` transported by `sscb_same_arch_cut`.
-/
import Mathlib
import Submission.Work.WilC5.StepSeqCutBigAux
import Submission.Work.WilC5.StepSeqCutBigEmb
import Submission.Work.WilC5.DclRoot
import Submission.Work.WilC5.StepSeqYVLe
import Submission.Work.WilC5.ClassArith
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.StepSeqIndep
import Submission.Work.WilC5.StepSeqCutStep
import Submission.Work.WilC5.StepSeqChain
import Submission.Work.WilC5.StepSeqEstimates
import Submission.Work.WilC5.CutComp
import Submission.Work.WilC5.LogDominatedOfInfinite
import Submission.Work.WilC5.FOV.SubfieldClosureL
import Submission.Work.WilC5.S4ExpF.logFun_pow_nat
import Submission.Work.WilC5.S4ExpF.logFun_zpow
import Submission.Work.WilC5.LogUnitFinite
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.StepSeqCutBigLA
import Submission.Work.WilC5.StepSeqCutBigLB

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

theorem sscb_cut_pos
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (hK : K ⊨ WilkiesDesign.CG.TE) (hL : L ⊨ WilkiesDesign.CG.TE)
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
    (hxbig : ∀ (i N : ℕ), (N : K) < S.xs i)
    (hlogsm : ∀ i j : ℕ, i ≤ j → Work.WilC5.VLe (S.xs i) (Work.WilC5.logFun (S.xs j)) ∧
      ¬ Work.WilC5.VLe (Work.WilC5.logFun (S.xs j)) (S.xs i))
    (hbetasm : ∀ i : ℕ, Work.WilC5.VLe (S.xs i) (S.beta i : K) ∧
      ¬ Work.WilC5.VLe (S.beta i : K) (S.xs i))
    {y0 : L}
    (hcutB : ∀ i : ℕ, ∀ b : ↥B,
      (((b : K) < S.xs i ↔ (τ b : L) < Work.WilC5.StepSeq.ys B τ S y0 i) ∧
       (S.xs i < (b : K) ↔ Work.WilC5.StepSeq.ys B τ S y0 i < (τ b : L))))
    {n : ℕ}
    (σ : WilkiesDesign.CG.LRc.Embedding ↥(Work.WilC5.StepSeq.Fsub hK S n) L)
    (hσB : ∀ b : ↥B, σ ⟨(b : K), Work.WilC5.StepSeq.B_mem_Fsub hK S n b.2⟩ = τ b)
    (hσxs : ∀ (i : ℕ) (hi : i < n),
      σ ⟨S.xs i, Work.WilC5.StepSeq.xs_mem_Fsub hK S hi⟩ = Work.WilC5.StepSeq.ys B τ S y0 i)
    {w : ↥(Work.WilC5.StepSeq.Fsub hK S n)} (hwpos : 0 < (w : K))
    {Q : ℤ} (hQpos : 0 < Q) {N : Fin n → ℤ}
    {z : K} (hzB : z ∈ (B : Set K)) (hz0 : z ≠ 0)
    {ε : K} (hεinf : Work.WilC5.IsInfinitesimal ε)
    (hdec : (w : K) ^ Q = z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε)) :
    (((w : K) < S.xs n ↔ (σ w : L) < Work.WilC5.StepSeq.ys B τ S y0 n) ∧
     (S.xs n < (w : K) ↔ Work.WilC5.StepSeq.ys B τ S y0 n < (σ w : L))) := by
  classical
  by_cases hNex : ∃ k : ℕ, ∃ hk : k < n, N ⟨k, hk⟩ ≠ 0
  · exact sscb_cut_pos_A hK hL hrexpK haddK hmulK honeK hlenegK hrexpL haddL hmulL honeL
      hlenegL hBdcl hBlog τ hτlog S hnew hxbig hlogsm hbetasm hcutB σ hσB hσxs
      hwpos hQpos hzB hz0 hεinf hdec hNex
  · exact sscb_cut_pos_B hK hL hrexpK haddK hmulK honeK hlenegK hrexpL haddL hmulL honeL
      hlenegL hBdcl hBlog τ hτlog S hnew hxbig hlogsm hbetasm hcutB σ hσB hσxs
      hwpos hQpos hzB hz0 hεinf hdec hNex

end Work.WilC5
