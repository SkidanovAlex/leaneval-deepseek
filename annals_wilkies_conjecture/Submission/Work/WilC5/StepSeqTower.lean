/-
  WilC5 — **the tower of the proof of vdDMM Lemma 4.4** (`Work.WilC5.S4StepNew`).

  This file assembles the proof of the hard step of §4 of van den Dries–Macintyre–Marker
  (`sources/wilkiesC/DMM.txt`, Lemma 4.4) from its pieces:

  * `Work.WilC5.ExistsStepSeq` — the sequence `x₀, x₁, …` of the extension step
    (`log xₙ = βₙ + εₙ x_{n+1}`, `βₙ ∈ B`), with `xₙ` value-new over `B`;
  * `Work.WilC5.StepSeqChain`, `Work.WilC5.StepSeqVLeLog`, `Work.WilC5.LogDominatedOfInfinite`
    — the chain invariants of that sequence;
  * `Work.WilC5.StepSeqIndepVLe` — Claim 2 (independence of the values of the `xᵢ` modulo `v(B^×)`);
  * `Work.WilC5.StepSeqCutStep` — the transport of the cut along `exp`/`log`;
  * `Work.WilC5.StepSeqCutBig` — Claim 4 (the cut of `xₙ` over `Fₙ`);
  * `Work.WilC5.StepSeqLogClosure`, `Work.WilC5.StepSeqLogPres` — Claim 5 (log-closure of the tower
    and log-preservation of the union);
  * `Work.WilC5.RealizesCutReduct`, `Work.WilC5.DclExtensionReduct` — the o-minimality input;
  * `Work.WilC5.EmbeddingTowerGlue` — gluing the tower to a single embedding.

  The tower is built by recursion: `Fₙ = Dcl (B ∪ {x₀, …, x_{n-1}})` (`Work.WilC5.StepSeq.Fset` /
  `Fsub`), the `L`-side sequence `yₙ = ys B τ S y₀` realises the cuts of the `xᵢ` over `B`
  (`hcutB`), Claim 4 gives the cut of `xₙ` over `Fₙ`, `DclExtensionReduct` extends `σₙ` from `Fₙ`
  to `Fₙ₊₁ = Dcl (Fₙ ∪ {xₙ})`, and the union `A' = ⋃ₙ Fₙ` with the glued embedding `σ'` is the
  required partial extension.
-/
import Mathlib
import Submission.Work.WilC5.StepSeqTowerStubs
import Submission.Work.WilC5.ExistsStepSeq
import Submission.Work.WilC5.StepSeqChain
import Submission.Work.WilC5.StepSeqVLeLog
import Submission.Work.WilC5.StepSeqIndepVLe
import Submission.Work.WilC5.StepSeqLogClosureCut
import Submission.Work.WilC5.StepSeqCutStep
import Submission.Work.WilC5.StepSeqDecomp
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.dcl_iUnion_chain

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

attribute [local instance] Work.WilC5.reductStruct


/-- Positivity of the elements of a `StepSeq`, in the field order. -/
theorem StepSeq.xs_pos {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {B : WilkiesDesign.CG.LRc.Substructure K} (S : Work.WilC5.StepSeq B) (n : ℕ) :
    0 < S.xs n :=
  (Work.WilC5.S4ExpF.leE_zero_iff (K := K) inferInstance hadd hleneg (S.xs n)).mp (S.hpos n)

/-! ## The assembly: from the pieces to `Work.WilC5.S4StepNew` -/

open WilkiesDesign WilkiesDesign.CG

/-- **The final assembly of vdDMM Lemma 4.4.**  The proof of `Work.WilC5.S4StepNew`: from the
fortified situation (`B = p.dom` is `Dcl`-closed, log-closed, exp-closed, with every `y ∉ B`
value-new) and `x ∉ B`, construct the sequence `S` (`Work.WilC5.ExistsStepSeq`), its invariants
(`Work.WilC5.StepSeqLogDominated`, `Work.WilC5.StepSeqVLeLog`,
`Work.WilC5.StepSeqIndepVLe`), the tower of embeddings (`Work.WilC5.StepSeqTowerExists`), the union
substructure `A' = ⋃ₙ Fₙ`, the glued embedding `σ'` (`Work.WilC5.EmbeddingTowerGlue`), its
log-preservation (`Work.WilC5.StepSeqLogPres`), and hence the S4Pair `q ≥ p` with `x ∈ q.dom`. -/
theorem StepSeqS4Pair
    (hMCr : ModelComplete TR) (hOM : OMinModels) (hVI : ValIneq) (hVP : Work.WilC5.ValProp)
    {K L : Type} [LEc.Structure K] [LEc.Structure L]
    (hK : K ⊨ TE) (hL : L ⊨ TE)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk K < κ)
    (hsat : @IsSaturated LEc L _ κ)
    {A₀ : LRc.Substructure K} {σ₀ : @Embedding LRc ↥A₀ L _ (reductStruct L)}
    (p : S4Pair A₀ σ₀)
    (hexp : ∀ b : ↥p.dom, expE (b : K) ∈ (p.dom : Set K))
    (hvalnew : ∀ y : K, y ∉ (p.dom : Set K) →
      ¬ (∀ w : K, w ∈ Work.WilC2.Dcl ((p.dom : Set K) ∪ {y}) →
          ∃ b : ↥p.dom, SameVal K hK (b : K) w))
    {x : K} (hx : x ∉ (p.dom : Set K)) :
    ∃ q : S4Pair A₀ σ₀, p ≤ q ∧ ∃ b : ↥q.dom, (b : K) = x := by
  classical
  ---------------------------------------------------------------------------- #
  -- 1. the canonical ordered-field data on `K` and `L`, and its bridges        #
  ---------------------------------------------------------------------------- #
  letI : LRc.Structure K := reductStruct K
  letI : LRc.Structure L := reductStruct L
  letI : Language.ring.Structure K := lrcRingReduct K
  letI : Language.ring.Structure L := lrcRingReduct L
  have hKTR : @Theory.Model LRc K (reductStruct K) TR := reduct_model_TR K hK
  have hLTR : @Theory.Model LRc L (reductStruct L) TR := reduct_model_TR L hL
  haveI hKfld : @Theory.Model ring K (lrcRingReduct K) Theory.field := tr_ring_field K hKTR
  haveI hLfld : @Theory.Model ring L (lrcRingReduct L) Theory.field := tr_ring_field L hLTR
  letI : Field K := cField K hK
  letI : LinearOrder K := cLin K hK
  letI : IsStrictOrderedRing K := tr_isStrictOrderedRing K hKTR
  letI : Ring.CompatibleRing K := FirstOrder.Field.compatibleRingOfModelField K
  letI : Field L := cField L hL
  letI : LinearOrder L := cLin L hL
  letI : IsStrictOrderedRing L := tr_isStrictOrderedRing L hLTR
  letI : Ring.CompatibleRing L := FirstOrder.Field.compatibleRingOfModelField L
  have hstrK : (reductStruct K : LRc.Structure K) = canonField K := by
    ext n f y
    · rcases f with (g | c)
      · rcases g with (g | r)
        · rfl
        · cases r; show rexpFromExp (y 0) = _; rfl
      · rfl
    · nomatch f
  have hstrL : (reductStruct L : LRc.Structure L) = canonField L := by
    ext n f y
    · rcases f with (g | c)
      · rcases g with (g | r)
        · rfl
        · cases r; show rexpFromExp (y 0) = _; rfl
      · rfl
    · nomatch f
  have hKTRcan : @Theory.Model LRc K (canonField K) TR := hstrK ▸ hKTR
  have hLTRcan : @Theory.Model LRc L (canonField L) TR := hstrL ▸ hLTR
  have haddK : ∀ u v : K, addE u v = u + v := by
    intro u v; rw [addE]; exact FirstOrder.Ring.CompatibleRing.funMap_add ![u, v]
  have hmulK : ∀ u v : K, mulE u v = u * v := by
    intro u v; rw [mulE]; exact FirstOrder.Ring.CompatibleRing.funMap_mul ![u, v]
  have honeK : (oneE : K) = 1 := by
    rw [oneE]; exact FirstOrder.Ring.CompatibleRing.funMap_one ![]
  haveI hKm : TE.Model K := hK
  haveI hzeroI : (zeroE : K) = 0 := by
    rw [zeroE]; exact FirstOrder.Ring.CompatibleRing.funMap_zero ![]
  have hzeroK : (zeroE : K) = 0 := by
    rw [zeroE]; exact FirstOrder.Ring.CompatibleRing.funMap_zero ![]
  have hnegK : ∀ u : K, negE u = -u := fun u => by
    rw [negE]; exact FirstOrder.Ring.CompatibleRing.funMap_neg ![u]
  have hsubK : ∀ u v : K, subE u v = u - v := by
    intro u v; rw [subE, haddK u (negE v), hnegK v, sub_eq_add_neg]
  have hleEK : ∀ u v : K, leE u v ↔ u ≤ v := by
    intro u v
    rw [leE, isSquare]
    constructor
    · rintro ⟨z, hz⟩
      rw [hmulK z z, hsubK v u] at hz
      nlinarith [mul_self_nonneg z]
    · intro h
      obtain ⟨z, hz⟩ := Work.WilC2.model_exists_sq (M := K) hKTRcan (v - u) (sub_nonneg.mpr h)
      exact ⟨z, by rw [hmulK z z, hsubK v u]; exact hz.symm⟩
  have haddL : ∀ u v : L, addE u v = u + v := by
    intro u v; rw [addE]; exact FirstOrder.Ring.CompatibleRing.funMap_add ![u, v]
  have hmulL : ∀ u v : L, mulE u v = u * v := by
    intro u v; rw [mulE]; exact FirstOrder.Ring.CompatibleRing.funMap_mul ![u, v]
  have honeL : (oneE : L) = 1 := by
    rw [oneE]; exact FirstOrder.Ring.CompatibleRing.funMap_one ![]
  have hnegL : ∀ u : L, negE u = -u := fun u => by
    rw [negE]; exact FirstOrder.Ring.CompatibleRing.funMap_neg ![u]
  have hsubL : ∀ u v : L, subE u v = u - v := by
    intro u v; rw [subE, haddL u (negE v), hnegL v, sub_eq_add_neg]
  have hleEL : ∀ u v : L, leE u v ↔ u ≤ v := by
    intro u v
    rw [leE, isSquare]
    constructor
    · rintro ⟨z, hz⟩
      rw [hmulL z z, hsubL v u] at hz
      nlinarith [mul_self_nonneg z]
    · intro h
      obtain ⟨z, hz⟩ := Work.WilC2.model_exists_sq (M := L) hLTRcan (v - u) (sub_nonneg.mpr h)
      exact ⟨z, by rw [hmulL z z, hsubL v u]; exact hz.symm⟩
  have hrexpK : ∀ x : K, @Structure.funMap rexpL K _ 1 rexpFunc.rexp ![x] = rexpFromExp x :=
    fun x => rfl
  have hrexpL : ∀ x : L, @Structure.funMap rexpL L _ 1 rexpFunc.rexp ![x] = rexpFromExp x :=
    fun x => rfl
  ---------------------------------------------------------------------------- #
  -- 2. the sequence of the extension step and its invariants                    #
  ---------------------------------------------------------------------------- #
  have hvalnew' : ∀ y : K, y ∉ (p.dom : Set K) →
      ¬ (∀ w : K, w ∈ @Work.WilC2.Dcl K (reductStruct K) ((p.dom : Set K) ∪ {y}) →
          ∃ b : ↥p.dom, SameArch (b : K) w) := by
    intro y hy hc
    exact hvalnew y hy (fun w hw => hc w hw)
  obtain ⟨S, hnewall, hunb, hDclEq⟩ :=
    ExistsStepSeq (B := p.dom) hrexpK haddK hmulK honeK hleEK hMCr hOM hVI hVP
      p.h4.dcl_closed (fun y hy => hexp ⟨y, hy⟩) hvalnew' hx
  have hdom : StepSeq.LogDominated S :=
    StepSeqLogDominated hrexpK haddK hmulK honeK hleEK S hunb
  have hchain : ∀ n : ℕ, VLe (logFun (S.xs n)) (S.xs (n + 1)) :=
    StepSeqVLeLog hrexpK haddK hmulK honeK hleEK p.dom S hnewall hdom
  have hind : ∀ (n : ℕ) (q : Fin n → ℤ),
      (∃ c ∈ (p.dom : Set K), c ≠ 0 ∧ IsUnitVal (c * ∏ i : Fin n, S.xs (i : ℕ) ^ (q i))) →
        q = 0 :=
    fun n q hq => StepSeqIndepVLe hrexpK haddK hmulK honeK hleEK p.dom p.h4.dcl_closed
      p.h4.log_closed S hnewall hunb hdom hchain n q hq
  have hdec : ∀ (n : ℕ) {w : K}, w ∈ @Work.WilC2.Dcl K (reductStruct K)
      ((p.dom : Set K) ∪ Set.range (fun i : Fin n => S.xs (i : ℕ))) → w ≠ 0 →
      ∃ Q : ℤ, 0 < Q ∧ ∃ N : Fin n → ℤ, ∃ z ∈ (p.dom : Set K), z ≠ 0 ∧ ∃ ε : K,
        IsInfinitesimal ε ∧
          w ^ Q = z * (∏ i : Fin n, S.xs (i : ℕ) ^ (N i)) * (1 + ε) := by
    intro n w hw hw0
    exact StepSeqDecomp hrexpK haddK hmulK honeK hleEK hMCr hOM hVI p.dom p.h4.dcl_closed
      (fun i : Fin n => S.xs (i : ℕ))
      (fun i => ne_of_gt (StepSeq.xs_pos haddK hleEK S (i : ℕ)))
      (fun q hq => hind n q hq) hw hw0
  ---------------------------------------------------------------------------- #
  -- 3. `τ` preserves the exponential                                           #
  ---------------------------------------------------------------------------- #
  have hτexp : ∀ b : ↥p.dom, p.emb ⟨expE (b : K), hexp b⟩ = expE (p.emb b) :=
    LogPreservingExp hK hL p.h4.log_closed (fun y hy => hexp ⟨y, hy⟩) p.emb p.logpres
  ---------------------------------------------------------------------------- #
  -- 4. the tower of embeddings of `Fₙ = Dcl (B ∪ {x₀, …, x_{n-1}})`             #
  ---------------------------------------------------------------------------- #
  obtain ⟨y0, hcutB, σt, hσB, hσxs, hcoh⟩ :=
    StepSeqTowerExists hK hL hMCr hOM hVI hrexpK haddK hmulK honeK hleEK hrexpL haddL hmulL
      honeL hleEL hstrK hstrL hKTR hLTR p.h4.dcl_closed p.h4.log_closed
      (fun y hy => hexp ⟨y, hy⟩) p.emb p.logpres hτexp S hnewall hunb hdom hchain hind κ hκ hsat
  ---------------------------------------------------------------------------- #
  -- 5. the union `A' = ⋃ₙ Fₙ` and the glued embedding                           #
  ---------------------------------------------------------------------------- #
  let Asub : LRc.Substructure K :=
    { carrier := ⋃ n : ℕ, (StepSeq.Fsub hK S n : Set K)
      fun_mem := by
        intro m f y hy
        choose nn hnn using fun k => Set.mem_iUnion.mp (hy k)
        refine Set.mem_iUnion.mpr ⟨Finset.univ.sup nn, ?_⟩
        have hmem : ∀ k, y k ∈ (StepSeq.Fsub hK S (Finset.univ.sup nn) : Set K) := by
          intro k
          exact StepSeq.Fset_mono S (Finset.le_sup (Finset.mem_univ k)) (hnn k)
        exact (StepSeq.Fsub hK S (Finset.univ.sup nn)).fun_mem f y hmem }
  have hAsub : (Asub : Set K) = ⋃ n : ℕ, (StepSeq.Fsub hK S n : Set K) := rfl
  have hmono : ∀ m n : ℕ, m ≤ n → StepSeq.Fsub hK S m ≤ StepSeq.Fsub hK S n :=
    fun m n h => StepSeq.Fset_mono S h
  obtain ⟨σ', hσ'agree⟩ :=
    EmbeddingTowerGlue (T := fun n : ℕ => StepSeq.Fsub hK S n) hmono σt hcoh Asub hAsub
  ---------------------------------------------------------------------------- #
  -- 6. `A'` is `Dcl`-closed and log-closed                                     #
  ---------------------------------------------------------------------------- #
  have hAsub_dcl : @Work.WilC2.Dcl K (reductStruct K) (Asub : Set K) ⊆ (Asub : Set K) :=
    dcl_iUnion_chain (A := fun n : ℕ => (StepSeq.Fsub hK S n : Set K)) hmono
      (fun n => StepSeq.Fsub_dcl hK S n)
  have hB0 : (0 : K) ∈ (p.dom : Set K) := by
    have h : (Work.WilC5.zeroE : K) ∈ (p.dom : Set K) :=
      p.dom.fun_mem (Sum.inl (Sum.inl Ring.zeroFunc)) (fun i : Fin 0 => i.elim0)
        (fun i => i.elim0)
    rwa [hzeroK] at h
  have hzero_mem : (0 : K) ∈ (Asub : Set K) :=
    Set.mem_iUnion.mpr ⟨0, StepSeq.B_subset_Fset S 0 hB0⟩
  have hAsub_log : ∀ w ∈ (Asub : Set K), logFun w ∈ (Asub : Set K) := by
    intro w hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    by_cases hw0 : w = 0
    · subst hw0
      have hz : logFun (0 : K) = 0 :=
        S4ExpF.logFun_eq_zero_of_not_pos hK haddK honeK hleEK 0 (by simp)
      rw [hz]
      exact hzero_mem
    · exact Set.mem_iUnion.mpr ⟨n + 1,
        StepSeqLogClosureCut hrexpK haddK hmulK honeK hleEK p.dom p.h4.dcl_closed
          p.h4.log_closed S hdec n hn hw0⟩
  ---------------------------------------------------------------------------- #
  -- 7. `σ'` is log-preserving                                                  #
  ---------------------------------------------------------------------------- #
  have hσ'ext : ∀ (n : ℕ) (w : K) (hw : w ∈ StepSeq.Fset S n),
      σt (n + 1) ⟨w, (StepSeq.Fset_mem_Fsub hK S (n + 1)).mp
        (StepSeq.Fset_mono S (Nat.le_succ n) hw)⟩ =
      σt n ⟨w, (StepSeq.Fset_mem_Fsub hK S n).mp hw⟩ := by
    intro n w hw
    exact hcoh n (n + 1) (Nat.le_succ n) w ((StepSeq.Fset_mem_Fsub hK S n).mp hw)
      ((StepSeq.Fset_mem_Fsub hK S (n + 1)).mp (StepSeq.Fset_mono S (Nat.le_succ n) hw))
  have hlogpres : ∀ u : ↥Asub, σ' ⟨logFun (u : K), hAsub_log (u : K) u.2⟩ = logFun (σ' u) := by
    intro u
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp u.2
    have hlogmem : logFun (u : K) ∈ StepSeq.Fset S (n + 1) := by
      by_cases hu0 : (u : K) = 0
      · rw [hu0, S4ExpF.logFun_eq_zero_of_not_pos hK haddK honeK hleEK 0 (by simp)]
        exact StepSeq.B_subset_Fset S (n + 1) hB0
      · exact StepSeqLogClosureCut hrexpK haddK hmulK honeK hleEK p.dom p.h4.dcl_closed
          p.h4.log_closed S hdec n hn hu0
    have hmemA : logFun (u : K) ∈ (Asub : Set K) := Set.mem_iUnion.mpr ⟨n + 1, hlogmem⟩
    have hmemF : logFun (u : K) ∈ (StepSeq.Fsub hK S (n + 1) : Set K) :=
      (StepSeq.Fset_mem_Fsub hK S (n + 1)).mp hlogmem
    have hmemF' : (u : K) ∈ (StepSeq.Fsub hK S (n + 1) : Set K) :=
      (StepSeq.Fset_mem_Fsub hK S (n + 1)).mp (StepSeq.Fset_mono S (Nat.le_succ n) hn)
    have helem : (⟨logFun (u : K), hAsub_log (u : K) u.2⟩ : ↥Asub) =
        ⟨logFun (u : K), hmemA⟩ := Subtype.ext rfl
    rw [helem]
    have h1 : σ' ⟨logFun (u : K), hmemA⟩ = σt (n + 1) ⟨logFun (u : K), hmemF⟩ :=
      hσ'agree (n + 1) (logFun (u : K)) hmemF hmemA
    have h2 : σt (n + 1) ⟨logFun (u : K), hmemF⟩ =
        logFun (σt (n + 1) ⟨(u : K), hmemF'⟩) :=
      StepSeqLogPres hK hL hMCr hOM hVI hrexpK haddK hmulK honeK hleEK hrexpL haddL hmulL
        honeL hleEL p.h4.dcl_closed p.h4.log_closed p.emb p.logpres S hnewall hunb hdom
        hchain hind (StepSeq.ys_rel p.dom p.emb S y0) (σt n) (σt (n + 1))
        (fun b => hσB n b) (fun i hi => hσxs n i hi) (fun b => hσB (n + 1) b)
        (fun i hi => hσxs (n + 1) i hi) (hσ'ext n) hn hlogmem
    have h3 : σt (n + 1) ⟨(u : K), hmemF'⟩ = σ' ⟨(u : K), u.2⟩ :=
      (hσ'agree (n + 1) (u : K) hmemF' u.2).symm
    rw [h1, h2, h3]
  ---------------------------------------------------------------------------- #
  -- 8. the S4Pair                                                              #
  ---------------------------------------------------------------------------- #
  have hxmem : x ∈ (Asub : Set K) := by
    have hx1 : x ∈ StepSeq.Fset S 1 := by
      have hrange : Set.range (fun i : Fin 1 => S.xs (i : ℕ)) = ({S.xs 0} : Set K) := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i
          exact Set.mem_singleton _
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          exact ⟨0, hz.symm⟩
      show x ∈ @Work.WilC2.Dcl K (reductStruct K)
        ((p.dom : Set K) ∪ Set.range (fun i : Fin 1 => S.xs (i : ℕ)))
      rw [hrange, ← hDclEq]
      exact StepSeq.subset_dcl (Or.inr (Set.mem_singleton x))
    exact Set.mem_iUnion.mpr ⟨1, hx1⟩
  refine ⟨{ dom := Asub
            emb := σ'
            h4 := ⟨hAsub_dcl, hAsub_log⟩
            logpres := hlogpres
            le_dom := ?_
            agrees := ?_ }, ?_, ⟨⟨x, hxmem⟩, rfl⟩⟩
  · intro a ha
    exact Set.mem_iUnion.mpr ⟨0, StepSeq.B_subset_Fset S 0 (p.le_dom ha)⟩
  · intro a
    have h1 : σ' ⟨(a : K), Set.mem_iUnion.mpr ⟨0, StepSeq.B_subset_Fset S 0 (p.le_dom a.2)⟩⟩ =
        σt 0 ⟨(a : K), (StepSeq.Fset_mem_Fsub hK S 0).mp (StepSeq.B_subset_Fset S 0 (p.le_dom a.2))⟩ :=
      hσ'agree 0 (a : K) (StepSeq.B_subset_Fset S 0 (p.le_dom a.2)) _
    have h2 : σt 0 ⟨(a : K), (StepSeq.Fset_mem_Fsub hK S 0).mp (StepSeq.B_subset_Fset S 0 (p.le_dom a.2))⟩ =
        p.emb ⟨(a : K), p.le_dom a.2⟩ :=
      hσB 0 ⟨(a : K), p.le_dom a.2⟩
    rw [h1, h2]
    exact p.agrees a
  · refine ⟨?_, ?_⟩
    · intro a ha
      exact Set.mem_iUnion.mpr ⟨0, StepSeq.B_subset_Fset S 0 ha⟩
    · intro a
      have h1 : σ' ⟨(a : K), Set.mem_iUnion.mpr ⟨0, StepSeq.B_subset_Fset S 0 a.2⟩⟩ =
          σt 0 ⟨(a : K), (StepSeq.Fset_mem_Fsub hK S 0).mp (StepSeq.B_subset_Fset S 0 a.2)⟩ :=
        hσ'agree 0 (a : K) (StepSeq.B_subset_Fset S 0 a.2) _
      have h2 : σt 0 ⟨(a : K), (StepSeq.Fset_mem_Fsub hK S 0).mp (StepSeq.B_subset_Fset S 0 a.2)⟩ =
          p.emb ⟨(a : K), a.2⟩ :=
        hσB 0 ⟨(a : K), a.2⟩
      rw [h1, h2]

end Work.WilC5
