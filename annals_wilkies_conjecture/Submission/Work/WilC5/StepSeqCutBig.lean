import Mathlib
import Submission.Work.WilC5.StepSeqCutBigAux
import Submission.Work.WilC5.StepSeqCutBigEmb
import Submission.Work.WilC5.DclRoot
import Submission.Work.WilC5.StepSeqYVLe
import Submission.Work.WilC5.ClassArith
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.StepSeqDecomp
import Submission.Work.WilC5.StepSeqIndep
import Submission.Work.WilC5.StepSeqCutStep
import Submission.Work.WilC5.StepSeqChain
import Submission.Work.WilC5.StepSeqEstimates
import Submission.Work.WilC5.CutComp
import Submission.Work.WilC5.LogDominatedOfInfinite
import Submission.Work.WilC5.S4ExpG.OrderEmbed
import Submission.Work.WilC5.S4ExpG.EmbedComm
import Submission.Work.WilC5.FOV.SubfieldClosureL
import Submission.Work.WilC5.S4ExpF.logFun_pow_nat
import Submission.Work.WilC5.S4ExpF.logFun_zpow
import Submission.Work.WilC5.LogUnitFinite
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.realizes_cut_order_preserving
import Submission.Work.WilC5.StepSeqCutBigL

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## The main theorem -/

/-- **vdDMM Lemma 4.4, Claim 4** (`sources/wilkiesC/DMM.txt`): the cut of `xₙ` over
`Fₙ = Dcl (B ∪ {x₀, …, x_{n-1}})` is realised by `yₙ`.

See `Submission/Work/WilC5/DESIGN.md`, and the auxiliary modules
`StepSeqCutBigAux`/`StepSeqCutBigEmb`, for the supporting lemmas.  The proof is the min-rule
computation of the source: after a power, each `w ∈ Fₙ` decomposes as `u (1+ε) ∏ xᵢ^{qᵢ}`
(`StepSeqDecomp`); the least index `m` with `qₘ ≠ 0` decides the archimedean comparisons, and
`CutComp` converts this into the criterion `w < xₙ ↔ 1 < z·xₘ^{Nₘ}` (and its mirror image), whose
`L`-side counterpart is `1 < τ z·yₘ^{Nₘ}` — the two agree because `σ` is an ordered ring
embedding of `Fₙ` into `L` sending `z ↦ τ z` and `xᵢ ↦ yᵢ`. -/
theorem StepSeqCutBig
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
    (hcutB : ∀ i : ℕ, ∀ b : ↥B,
      (((b : K) < S.xs i ↔ (τ b : L) < Work.WilC5.StepSeq.ys B τ S y0 i) ∧
       (S.xs i < (b : K) ↔ Work.WilC5.StepSeq.ys B τ S y0 i < (τ b : L))))
    {n : ℕ}
    (σ : WilkiesDesign.CG.LRc.Embedding ↥(Work.WilC5.StepSeq.Fsub hK S n) L)
    (hσB : ∀ b : ↥B, σ ⟨(b : K), Work.WilC5.StepSeq.B_mem_Fsub hK S n b.2⟩ = τ b)
    (hσxs : ∀ (i : ℕ) (hi : i < n),
      σ ⟨S.xs i, Work.WilC5.StepSeq.xs_mem_Fsub hK S hi⟩ = Work.WilC5.StepSeq.ys B τ S y0 i) :
    ∀ w : ↥(Work.WilC5.StepSeq.Fsub hK S n),
      (((w : K) < S.xs n ↔ (σ w : L) < Work.WilC5.StepSeq.ys B τ S y0 n) ∧
       (S.xs n < (w : K) ↔ Work.WilC5.StepSeq.ys B τ S y0 n < (σ w : L))) := by
  classical
  haveI : K ⊨ WilkiesDesign.CG.TE := hK
  haveI : L ⊨ WilkiesDesign.CG.TE := hL
  have hsubEL : ∀ x y : L, Work.WilC5.subE x y = x - y :=
    fun x y => Work.WilC5.S4ExpF.subE_eq_sub hL haddL x y
  have hzeroK : (Work.WilC5.zeroE : K) = 0 := Work.WilC5.S4ExpF.zeroE_eq_zero hK haddK
  have hzeroL : (Work.WilC5.zeroE : L) = 0 := Work.WilC5.S4ExpF.zeroE_eq_zero hL haddL
  have hnegEK : ∀ x : K, Work.WilC5.negE x = -x :=
    fun x => Work.WilC5.S4ExpF.negE_eq_neg hK haddK x
  have hnatK : ∀ N : ℕ, Work.WilC5.realConst K (N : ℝ) = (N : K) :=
    sscb_realConst_natCast hK hrexpK haddK hmulK honeK hlenegK
  have hxpos : ∀ i : ℕ, 0 < S.xs i := fun i => sscb_xs_pos hK haddK hlenegK S i
  have hxbig : ∀ (i N : ℕ), (N : K) < S.xs i :=
    fun i N => sscb_xs_big hlenegK hnatK hunb i N
  obtain ⟨-, hlogsm, hbetasm⟩ :=
    Work.WilC5.StepSeqEstimates hrexpK haddK hmulK honeK hlenegK S hnew hdom
  obtain ⟨hB0, -, -, -, -, -⟩ :=
    Work.WilC5.FOV.SubfieldClosureL hrexpK haddK hmulK honeK hlenegK B hBdcl
  obtain ⟨hF0, hF1, hFneg, hFinv, hFadd, hFmul⟩ :=
    Work.WilC5.FOV.SubfieldClosureL hrexpK haddK hmulK honeK hlenegK
      (Work.WilC5.StepSeq.Fsub hK S n) (Work.WilC5.StepSeq.Fsub_dcl hK S n)
  have hτ0 : τ ⟨(0 : K), hB0⟩ = (0 : L) := sscb_emb_zero hzeroK hzeroL hB0 τ
  have hσ0 : σ ⟨(0 : K), hF0⟩ = (0 : L) := sscb_emb_zero hzeroK hzeroL hF0 σ
  have hypos : ∀ i : ℕ, 0 < Work.WilC5.StepSeq.ys B τ S y0 i := by
    intro i
    have h := (hcutB i ⟨(0 : K), hB0⟩).1
    rw [hτ0] at h
    exact h.mp (hxpos i)
  have hleEL_L : ∀ x y : L, Work.WilC5.leEL x y → x ≤ y := by
    intro x y hxy
    obtain ⟨c, hc⟩ := hxy
    have h1 : c * c = y - x := by rw [← hsubEL, ← hmulL]; exact hc
    have h2 : (0 : L) ≤ y - x := by rw [← h1]; exact mul_self_nonneg c
    linarith
  have hsubF : ∀ a b : K, a ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) →
      b ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) →
      a - b ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) := by
    intro a b ha hb; rw [sub_eq_add_neg]; exact hFadd _ ha _ (hFneg _ hb)
  have hrootF : ∀ a : K, a ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) → 0 < a →
      ∃ c : K, c ∈ ((Work.WilC5.StepSeq.Fsub hK S n) : Set K) ∧ c * c = a := by
    intro a ha hapos
    obtain ⟨b, hbF, -, hb2⟩ :=
      Work.WilC5.DclRoot (K := K) hK hrexpK haddK hmulK honeK hlenegK
        (Work.WilC5.StepSeq.Fsub_dcl hK S n) ha hapos (Q := 2) (by norm_num)
    exact ⟨b, hbF, by rw [← hb2]; ring⟩
  have hσord : ∀ a b : ↥(Work.WilC5.StepSeq.Fsub hK S n),
      (((a : K) ≤ (b : K)) ↔ ((σ a : L) ≤ (σ b : L))) :=
    sscb_emb_order haddK hmulK hnegEK hleEL_L hsubF hrootF σ
  intro w
  by_cases hwle : (w : K) ≤ 0
  · have hσw0 : (σ w : L) ≤ 0 := by
      have h := (hσord w ⟨(0 : K), hF0⟩).mp hwle
      rwa [hσ0] at h
    exact ⟨⟨fun _ => lt_of_le_of_lt hσw0 (hypos n), fun _ => lt_of_le_of_lt hwle (hxpos n)⟩,
      ⟨fun h => absurd h (not_lt.mpr (le_trans hwle (le_of_lt (hxpos n)))),
       fun h => absurd h (not_lt.mpr (le_trans hσw0 (le_of_lt (hypos n))))⟩⟩
  · have hwpos : 0 < (w : K) := not_le.mp hwle
    obtain ⟨Q, hQpos, N, z, hzB, hz0, ε, hεinf, hdec⟩ :=
      Work.WilC5.StepSeqDecomp (hrexp := hrexpK) haddK hmulK honeK hlenegK hMCr hOM hVI B hBdcl
        (fun i : Fin n => S.xs (i : ℕ)) (fun i => ne_of_gt (hxpos _))
        (fun q hq => hind n q hq)
        ((Work.WilC5.StepSeq.Fset_mem_Fsub hK S n).mpr w.2) (ne_of_gt hwpos)
    exact Work.WilC5.sscb_cut_pos hK hL hrexpK haddK hmulK honeK hlenegK hrexpL haddL hmulL
      honeL hlenegL hBdcl hBlog τ hτlog S hnew hxbig hlogsm hbetasm hcutB σ hσB hσxs
      hwpos hQpos hzB hz0 hεinf hdec

end Work.WilC5
