import Mathlib
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.StepSeqCutBig
import Submission.Work.WilC5.StepSeqCutOverB
import Submission.Work.WilC5.StepSeqCutStep
import Submission.Work.WilC5.DclExtensionCast
import Submission.Work.WilC5.DclExtRedAlign_probe
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.EmbeddingTowerGlue

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## Helper lemmas for `Work.WilC5.StepSeqTowerExists`

Two ingredients are needed on top of the imported material:

* `Work.WilC5.canonField_eq_canonTS` — the alignment hypotheses `hstrK`/`hstrL` of the statement
  are phrased with `Work.WilC5.canonField`, whereas the o-minimality input
  `Work.WilC5.DclExtensionReductAlign` is phrased with `Work.WilC5.canonTS`; the two canonical
  structures agree once the `rexp`-alignment `hrexp` is known (the ring parts agree
  definitionally, and `hstr` identifies the constant-symbol part of `canonField` with the one coming
  from the `LEc`-reduct).
* `Work.WilC5.LRc.Embedding.ofSetEq` — an `LRc`-embedding is transported along an equality of the
  carriers of two substructures of a common ambient structure (`LRc` has no relation symbols, and
  the induced structure computes function symbols by restriction to the ambient structure). -/

/-- **The two canonical `LRc`-structures of area C5 agree.**  `canonTS M` is the structure
synthesised from the ordered-field data together with the `rexp`- and constant-reducts of the
`LEc`-structure, and `canonField M` is the same synthesis from the ordered-field data together with
the `rexp`- and constant-structures given as hypotheses.  The hypothesis `hstr` (the `hstrK`/`hstrL`
of the statement) identifies the constant symbol interpretations, and `hrexp` identifies the `rexp`
symbol interpretation. -/
theorem canonField_eq_canonTS {M : Type} [LEc.Structure M] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [rexpL.Structure M]
    [(constantsOn ℝ).Structure M]
    (hstr : (reductStruct M : LRc.Structure M) = canonField M)
    (hrexp : ∀ x : M, @Structure.funMap rexpL M inferInstance 1 rexpFunc.rexp ![x] =
      rexpFromExp x) :
    canonField M = canonTS M := by
  have hc : ∀ {n : ℕ} (c : (constantsOn ℝ).Functions n) (y : Fin n → M),
      @Structure.funMap LRc M (canonTS M) n (Sum.inr c) y
        = @Structure.funMap LRc M (reductStruct M) n (Sum.inr c) y := fun c y => rfl
  ext n f y
  · rcases f with (g | r) | c
    · rfl
    · cases r
      have hy : (y : Fin 1 → M) = ![y 0] := by funext i; fin_cases i; rfl
      rw [hy]
      rw [show @Structure.funMap LRc M (canonField M) 1 (Sum.inl (Sum.inr rexpFunc.rexp)) ![y 0]
          = @Structure.funMap rexpL M (@lrcRexpReduct M (canonField M)) 1 rexpFunc.rexp ![y 0]
          from rfl]
      rw [show @Structure.funMap LRc M (canonTS M) 1 (Sum.inl (Sum.inr rexpFunc.rexp)) ![y 0]
          = @Structure.funMap rexpL M (@lrcRexpReduct M (canonTS M)) 1 rexpFunc.rexp ![y 0]
          from rfl]
      rw [show @Structure.funMap rexpL M (@lrcRexpReduct M (canonField M)) 1 rexpFunc.rexp ![y 0]
          = @Structure.funMap rexpL M inferInstance 1 rexpFunc.rexp ![y 0] from rfl]
      rw [show @Structure.funMap rexpL M (@lrcRexpReduct M (canonTS M)) 1 rexpFunc.rexp ![y 0]
          = rexpFromExp (y 0) from rfl]
      exact hrexp (y 0)
    · rw [funMap_congr_LRc hstr (Sum.inr c) y]
      exact (hc c y).symm
  · exact isEmptyElim f

/-- Transfer of membership across an equality of sets (used to move between the carriers of the
substructures `B`, `S'` and `Fₙ`). -/
theorem carrier_mem {M : Type} {S T : Set M} (h : S = T) {x : M} (hx : x ∈ S) : x ∈ T :=
  (Set.ext_iff.mp h x).mp hx

/-- **The ordered-field canonical `LRc`-structure, in the syntactic form used by the o-minimality
input.**  `Work.WilC5.canonField K` is the same structure, but it is a `def`; the typeclass search
of `Work.WilC5.model_TR_of_dcl_closed` unfolds only `reducible` definitions, so it is convenient
to have the same term as an `abbrev`. -/
abbrev canonSynth (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FirstOrder.Ring.CompatibleRing K] [rexpL.Structure K] [(constantsOn ℝ).Structure K] :
    LRc.Structure K :=
  @Language.withConstantsStructure LR K
    (@Language.sumStructure Language.ring rexpL K
      (FirstOrder.Ring.CompatibleRing.toStructure (R := K))
      (inferInstance : rexpL.Structure K))
    ℝ (inferInstance : (constantsOn ℝ).Structure K)

/-- `canonField` is `canonSynth` (definitionally). -/
theorem canonField_eq_canonSynth {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FirstOrder.Ring.CompatibleRing K] [rexpL.Structure K] [(constantsOn ℝ).Structure K] :
    canonField K = canonSynth K := rfl

namespace LRc

/-- **Transport of an `LRc`-embedding along an equality of carriers.**  If two substructures `S`,
`T` of a common ambient structure have the same carrier and `σ : ↥T → N` is an `LRc`-embedding,
then so is `a ↦ σ ⟨a, ·⟩` on `↥S`.  (The two induced structures compute function symbols by
restriction to the ambient structure, so the required commutation with function symbols reduces to
`Subtype.ext rfl`; `LRc` has no relation symbols.) -/
def Embedding.ofSetEq {M N : Type} [LRc.Structure M] [LRc.Structure N]
    {S T : LRc.Substructure M} (h : (S : Set M) = (T : Set M)) (σ : LRc.Embedding ↥T N) :
    LRc.Embedding ↥S N where
  toEmbedding :=
    { toFun := fun a => σ ⟨(a : M), carrier_mem h a.2⟩
      inj' := by
        intro a b hab
        have h1 : (⟨(a : M), carrier_mem h a.2⟩ : ↥T) = ⟨(b : M), carrier_mem h b.2⟩ :=
          σ.injective hab
        have h2 : (a : M) = (b : M) := congrArg (fun t : ↥T => (t : M)) h1
        exact Subtype.ext h2 }
  map_fun' := by
    intro n f x
    have h1 : (fun a : ↥S => σ ⟨(a : M), carrier_mem h a.2⟩) (Structure.funMap f x)
        = σ (Structure.funMap f (fun i => (⟨(x i : M), carrier_mem h (x i).2⟩ : ↥T))) := by
      refine congrArg σ (Subtype.ext ?_)
      rfl
    refine h1.trans ?_
    rw [σ.map_fun f (fun i => (⟨(x i : M), carrier_mem h (x i).2⟩ : ↥T))]
    rfl
  map_rel' := by intro n r x; exact isEmptyElim r

@[simp] theorem Embedding.ofSetEq_apply {M N : Type} [LRc.Structure M] [LRc.Structure N]
    {S T : LRc.Substructure M} (h : (S : Set M) = (T : Set M)) (σ : LRc.Embedding ↥T N)
    (a : ↥S) :
    Embedding.ofSetEq h σ a = σ ⟨(a : M), carrier_mem h a.2⟩ := rfl

end LRc

/-- **vdDMM Lemma 4.4, the tower** (Claim 3 assumed): given the `L`-side cut realisation `hcutB`,
the tower of `LRc`-embeddings `σₙ : Fₙ → L` exists, extends `τ` on `B`, sends `xᵢ ↦ yᵢ` and is
coherent.  The recursion is that of the source: `σ₀` is `τ` on `F₀ = B`, and `σ_{n+1}` extends `σₙ`
by Claim 4 (`Work.WilC5.StepSeqCutBig`) followed by the o-minimality input
(`Work.WilC5.DclExtensionReductAlign`), the carrier `F_{n+1} = Dcl (Fₙ ∪ {xₙ})` being rewritten
with `Work.WilC5.StepSeq.Fset_succ_shift`. -/
private theorem stepSeqTower_exists'
    {K L : Type} [LEc.Structure K] [LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [rexpL.Structure K] [(constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [rexpL.Structure L] [(constantsOn ℝ).Structure L]
    (hK : K ⊨ TE) (hL : L ⊨ TE)
    (hMCr : ModelComplete TR)
    (hOM : OMinModels) (hVI : ValIneq)
    (hrexpK : ∀ x : K, @Structure.funMap rexpL K inferInstance 1 rexpFunc.rexp ![x] =
      rexpFromExp x)
    (haddK : ∀ x y : K, addE x y = x + y)
    (hmulK : ∀ x y : K, mulE x y = x * y)
    (honeK : (oneE : K) = 1)
    (hlenegK : ∀ x y : K, leE x y ↔ x ≤ y)
    (hrexpL : ∀ x : L, @Structure.funMap rexpL L inferInstance 1 rexpFunc.rexp ![x] =
      rexpFromExp x)
    (haddL : ∀ x y : L, addE x y = x + y)
    (hmulL : ∀ x y : L, mulE x y = x * y)
    (honeL : (oneE : L) = 1)
    (hlenegL : ∀ x y : L, leE x y ↔ x ≤ y)
    (hstrK : (reductStruct K : LRc.Structure K) = canonField K)
    (hstrL : (reductStruct L : LRc.Structure L) = canonField L)
    (hKTR : K ⊨ TR) (hLTR : L ⊨ TR)
    {B : LRc.Substructure K}
    (hBdcl : @Work.WilC2.Dcl K (reductStruct K) (B : Set K) ⊆ (B : Set K))
    (hBlog : ∀ x ∈ (B : Set K), logFun x ∈ (B : Set K))
    (hBexp : ∀ x ∈ (B : Set K), expE x ∈ (B : Set K))
    (τ : LRc.Embedding ↥B L)
    (hτlog : ∀ b : ↥B, τ ⟨logFun (b : K), hBlog (b : K) b.2⟩ = logFun (τ b))
    (hτexp : ∀ b : ↥B, τ ⟨expE (b : K), hBexp (b : K) b.2⟩ = expE (τ b))
    (S : StepSeq B)
    (hnew : StepSeq.ValueNewAll S)
    (hunb : StepSeq.Unbounded S)
    (hdom : StepSeq.LogDominated S)
    (hchain : ∀ n : ℕ, VLe (logFun (S.xs n)) (S.xs (n + 1)))
    (hind : ∀ (n : ℕ) (q : Fin n → ℤ),
      (∃ c ∈ (B : Set K), c ≠ 0 ∧ IsUnitVal (c * ∏ i : Fin n, S.xs (i : ℕ) ^ (q i))) → q = 0)
    {y0 : L}
    (hcutB : ∀ i : ℕ, ∀ b : ↥B,
      (((b : K) < S.xs i ↔ (τ b : L) < StepSeq.ys B τ S y0 i) ∧
       (S.xs i < (b : K) ↔ StepSeq.ys B τ S y0 i < (τ b : L)))) :
    ∃ σ : ∀ n : ℕ, LRc.Embedding ↥(StepSeq.Fsub hK S n) L,
      (∀ n : ℕ, ∀ b : ↥B,
        σ n ⟨(b : K), StepSeq.B_mem_Fsub hK S n b.2⟩ = τ b) ∧
      (∀ (n i : ℕ) (hi : i < n),
        σ n ⟨S.xs i, StepSeq.xs_mem_Fsub hK S hi⟩ = StepSeq.ys B τ S y0 i) ∧
      (∀ (m n : ℕ) (h : m ≤ n) (a : K)
        (hm : a ∈ (StepSeq.Fsub hK S m : Set K))
        (hn : a ∈ (StepSeq.Fsub hK S n : Set K)),
        σ n ⟨a, hn⟩ = σ m ⟨a, hm⟩) := by
  classical
  haveI : K ⊨ TE := hK
  haveI : L ⊨ TE := hL
  haveI : K ⊨ TR := hKTR
  haveI : L ⊨ TR := hLTR
  have hstrK' : (reductStruct K : LRc.Structure K) = canonTS K :=
    hstrK.trans (canonField_eq_canonTS hstrK hrexpK)
  have hstrL' : (reductStruct L : LRc.Structure L) = canonTS L :=
    hstrL.trans (canonField_eq_canonTS hstrL hrexpL)
  -- The bundle of data maintained at every level of the recursion.
  let Bund : (n : ℕ) → Type := fun n =>
    {σ : LRc.Embedding ↥(StepSeq.Fsub hK S n) L //
      (∀ b : ↥B, σ ⟨(b : K), StepSeq.B_mem_Fsub hK S n b.2⟩ = τ b) ∧
      (∀ (i : ℕ) (hi : i < n),
        σ ⟨S.xs i, StepSeq.xs_mem_Fsub hK S hi⟩ = StepSeq.ys B τ S y0 i)}
  -- ## The one-step extension, with its coherence with the previous level.
  have step_exists : ∀ (n : ℕ) (σn : LRc.Embedding ↥(StepSeq.Fsub hK S n) L),
      (∀ b : ↥B, σn ⟨(b : K), StepSeq.B_mem_Fsub hK S n b.2⟩ = τ b) →
      (∀ (i : ℕ) (hi : i < n),
        σn ⟨S.xs i, StepSeq.xs_mem_Fsub hK S hi⟩ = StepSeq.ys B τ S y0 i) →
      ∃ (σ' : LRc.Embedding ↥(StepSeq.Fsub hK S (n + 1)) L),
        (∀ b : ↥B, σ' ⟨(b : K), StepSeq.B_mem_Fsub hK S (n + 1) b.2⟩ = τ b) ∧
        (∀ (i : ℕ) (hi : i < n + 1),
          σ' ⟨S.xs i, StepSeq.xs_mem_Fsub hK S hi⟩ = StepSeq.ys B τ S y0 i) ∧
        (∀ (a : K) (ha : a ∈ (StepSeq.Fsub hK S n : Set K))
          (ha' : a ∈ (StepSeq.Fsub hK S (n + 1) : Set K)),
          σ' ⟨a, ha'⟩ = σn ⟨a, ha⟩) := by
    intro n σn hσB hσxs
    -- Claim 4: the cut of `xₙ` over `Fₙ` is realised by `yₙ`.
    have hcutn : ∀ w : ↥(StepSeq.Fsub hK S n),
        (((w : K) < S.xs n ↔ (σn w : L) < StepSeq.ys B τ S y0 n) ∧
         (S.xs n < (w : K) ↔ StepSeq.ys B τ S y0 n < (σn w : L))) :=
      StepSeqCutBig hK hL hMCr hOM hVI hrexpK haddK hmulK honeK hlenegK hrexpL haddL hmulL
        honeL hlenegL hBdcl hBlog τ hτlog S hnew hunb hdom hchain hind hcutB σn hσB hσxs
    -- `Fₙ` is a model of `TR` (it is `Dcl`-closed): transport the substructure to the syntactic
    -- canonical ordered-field structure, where `Work.WilC5.model_TR_of_dcl_closed` is stated.
    have hX : (reductStruct K : LRc.Structure K) = canonSynth K :=
      hstrK.trans (canonField_eq_canonSynth (K := K))
    let Fcanon : @LRc.Substructure K (canonSynth K) :=
      SubCast (reductStruct K) (canonSynth K) hX (StepSeq.Fsub hK S n)
    have hFcanondcl : @Work.WilC2.Dcl K (canonSynth K) (Fcanon : Set K) ⊆ (Fcanon : Set K) := by
      intro z hz
      refine StepSeq.Fsub_dcl hK S n ?_
      rw [Dcl_congr hX]
      exact hz
    have hFcanonTR :
        @Theory.Model LRc ↥Fcanon (@Substructure.inducedStructure LRc K (canonSynth K) Fcanon)
          TR := by
      haveI : @Theory.Model LRc K (canonSynth K) TR := hX ▸ hKTR
      exact model_TR_of_dcl_closed (M := K) hOM Fcanon hFcanondcl
    have hFTR : ↥(StepSeq.Fsub hK S n) ⊨ TR := by
      rw [show (@Substructure.inducedStructure LRc K (reductStruct K) (StepSeq.Fsub hK S n))
          = (@Substructure.inducedStructure LRc K (canonSynth K) Fcanon)
          from (induced_SubCast (reductStruct K) (canonSynth K) hX
            (StepSeq.Fsub hK S n)).symm]
      exact hFcanonTR
    -- The cut of `xₙ` over `Fₙ` in the form required by `Work.WilC5.DclExtensionReductAlign`.
    have hcutpair : ((∀ f : ↥(StepSeq.Fsub hK S n),
          ((f : K) < S.xs n ↔ (σn f : L) < StepSeq.ys B τ S y0 n)) ∧
        (∀ f : ↥(StepSeq.Fsub hK S n),
          (S.xs n < (f : K) ↔ StepSeq.ys B τ S y0 n < (σn f : L)))) :=
      ⟨fun f => (hcutn f).1, fun f => (hcutn f).2⟩
    -- The o-minimality input of vdDMM Lemma 4.2.
    obtain ⟨S', hS', hS'dcl, hle, hxS', σ'', hσ''F, hσ''x⟩ :=
      DclExtensionReductAlign hstrK' hstrL' hMCr hOM hKTR hLTR (StepSeq.Fsub hK S n) hFTR
        (StepSeq.Fsub_dcl hK S n) σn hcutpair
    -- `F_{n+1} = Dcl (Fₙ ∪ {xₙ})` has the carrier of `S'`.
    have hcarrier : (StepSeq.Fsub hK S (n + 1) : Set K) = (S' : Set K) := by
      rw [StepSeq.Fsub_coe, StepSeq.Fset_succ_shift (K := K) hK S n, hS']
      rfl
    let σ' : LRc.Embedding ↥(StepSeq.Fsub hK S (n + 1)) L :=
      LRc.Embedding.ofSetEq hcarrier σ''
    have hσ'B : ∀ b : ↥B, σ' ⟨(b : K), StepSeq.B_mem_Fsub hK S (n + 1) b.2⟩ = τ b := by
      intro b
      have hb1 : (⟨(b : K), carrier_mem hcarrier (StepSeq.B_mem_Fsub hK S (n + 1) b.2)⟩ : ↥S')
          = ⟨(b : K), hle (StepSeq.B_mem_Fsub hK S n b.2)⟩ := Subtype.ext rfl
      rw [LRc.Embedding.ofSetEq_apply, hb1]
      exact (hσ''F ⟨(b : K), StepSeq.B_mem_Fsub hK S n b.2⟩).trans (hσB b)
    have hσ'xs : ∀ (i : ℕ) (hi : i < n + 1),
        σ' ⟨S.xs i, StepSeq.xs_mem_Fsub hK S hi⟩ = StepSeq.ys B τ S y0 i := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · have hb1 : (⟨S.xs i, carrier_mem hcarrier (StepSeq.xs_mem_Fsub hK S hi)⟩ : ↥S')
            = ⟨S.xs i, hle (StepSeq.xs_mem_Fsub hK S h)⟩ := Subtype.ext rfl
        rw [LRc.Embedding.ofSetEq_apply, hb1]
        exact (hσ''F ⟨S.xs i, StepSeq.xs_mem_Fsub hK S h⟩).trans (hσxs i h)
      · have hb1 : (⟨S.xs i, carrier_mem hcarrier (StepSeq.xs_mem_Fsub hK S hi)⟩ : ↥S')
            = ⟨S.xs n, hxS'⟩ := Subtype.ext (congrArg S.xs h)
        have hy : StepSeq.ys B τ S y0 i = StepSeq.ys B τ S y0 n := by rw [h]
        rw [hy, LRc.Embedding.ofSetEq_apply, hb1]
        exact hσ''x
    have hσ'coh : ∀ (a : K) (ha : a ∈ (StepSeq.Fsub hK S n : Set K))
        (ha' : a ∈ (StepSeq.Fsub hK S (n + 1) : Set K)),
        σ' ⟨a, ha'⟩ = σn ⟨a, ha⟩ := by
      intro a ha ha'
      have hb1 : (⟨a, carrier_mem hcarrier ha'⟩ : ↥S') = ⟨a, hle ha⟩ := Subtype.ext rfl
      rw [LRc.Embedding.ofSetEq_apply, hb1]
      exact hσ''F ⟨a, ha⟩
    exact ⟨σ', hσ'B, hσ'xs, hσ'coh⟩
  -- ## The recursion.
  let step : ∀ n : ℕ, Bund n → Bund (n + 1) := fun n Bn =>
    Subtype.mk (Classical.choose (step_exists n Bn.1 Bn.2.1 Bn.2.2))
      ⟨(Classical.choose_spec (step_exists n Bn.1 Bn.2.1 Bn.2.2)).1,
       (Classical.choose_spec (step_exists n Bn.1 Bn.2.1 Bn.2.2)).2.1⟩
  have step_coh : ∀ (n : ℕ) (Bn : Bund n) (a : K)
      (ha : a ∈ (StepSeq.Fsub hK S n : Set K))
      (ha' : a ∈ (StepSeq.Fsub hK S (n + 1) : Set K)),
      (step n Bn).1 ⟨a, ha'⟩ = Bn.1 ⟨a, ha⟩ := fun n Bn a ha ha' =>
    (Classical.choose_spec (step_exists n Bn.1 Bn.2.1 Bn.2.2)).2.2 a ha ha'
  -- ## The base of the recursion: `σ₀ = τ`, via `F₀ = B`.
  have hB0 : (StepSeq.Fsub hK S 0 : Set K) = (B : Set K) := by
    rw [StepSeq.Fsub_coe, StepSeq.Fset_zero S hBdcl]
  have base : Bund 0 :=
    Subtype.mk (LRc.Embedding.ofSetEq hB0 τ)
      ⟨by
        intro b
        have hb1 : (⟨(b : K), carrier_mem hB0 (StepSeq.B_mem_Fsub hK S 0 b.2)⟩ : ↥B) = b :=
          Subtype.ext rfl
        rw [LRc.Embedding.ofSetEq_apply, hb1], by
        intro i hi
        exact absurd hi (Nat.not_lt_zero i)⟩
  let tower : (n : ℕ) → Bund n := fun n => Nat.rec base (fun k bk => step k bk) n
  -- ## The coherence of the tower, by induction from the one-step coherence.
  have coh : ∀ (n m : ℕ) (hmn : m ≤ n) (a : K)
      (hn : a ∈ (StepSeq.Fsub hK S n : Set K))
      (hm : a ∈ (StepSeq.Fsub hK S m : Set K)),
      (tower n).1 ⟨a, hn⟩ = (tower m).1 ⟨a, hm⟩ := by
    intro n
    induction n with
    | zero =>
        intro m hm0 a hn hm
        obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hm0
        exact congrArg (tower 0).1 (Subtype.ext rfl)
    | succ k ih =>
        intro m hmk a hn hm
        rcases Nat.lt_or_eq_of_le hmk with h | h
        · have hmk' : m ≤ k := Nat.le_of_lt_succ h
          have hk : a ∈ (StepSeq.Fsub hK S k : Set K) := by
            rw [StepSeq.Fsub_coe] at hm ⊢
            exact StepSeq.Fset_mono S hmk' hm
          have hs : (tower (k + 1)).1 ⟨a, hn⟩ = (tower k).1 ⟨a, hk⟩ :=
            step_coh k (tower k) a hk hn
          rw [hs]
          exact ih m hmk' a hk hm
        · subst h
          exact congrArg (tower (k + 1)).1 (Subtype.ext rfl)
  refine ⟨fun n => (tower n).1, fun n b => (tower n).2.1 b, fun n i hi => (tower n).2.2 i hi,
    fun m n hmn a hm hn => coh n m hmn a hn hm⟩

/-- **vdDMM Lemma 4.4: the tower of the proof** (`sources/wilkiesC/DMM.txt`).  In the fortified
situation of the source (`B ≤ K` `Dcl`-closed, log-closed and closed under the exponential,
`τ : B → L` log-preserving with the exponential, and a sequence `S : StepSeq B` of the extension
step with value-new `xₙ` (`hnew`), `Unbounded`, `LogDominated`, the chain invariant `hchain` and
the independence `hind` of Claim 2), there is an `L`-side sequence `yₙ = ys B τ S y₀` and a coherent
tower of `LRc`-embeddings

  `σₙ : Fₙ = Dcl (B ∪ {x₀, …, x_{n-1}}) → L`

which extends `τ` on `B`, sends `xᵢ ↦ yᵢ`, and is compatible across levels.

* the first conjunct is Claim 3: every `yᵢ` realises the image under `τ` of the cut of `xᵢ` over `B`
  (`Work.WilC5.StepSeqCutOverB`);
* `σ₀` is `τ` (via `Fset S 0 = B`, `Work.WilC5.StepSeq.Fset_zero`), and `σ_{n+1}` is obtained from
  `σₙ` by Claim 4 (`Work.WilC5.StepSeqCutBig`, the cut of `xₙ` over `Fₙ` realised by `yₙ`)
  followed by the o-minimality input, i.e. the aligned form of `Work.WilC5.DclExtension` (the
  transport lemmas are `Submission/Work/WilC5/DclExtensionCast.lean`, the completed proof is
  `Work.WilC5.DclExtensionReductAlign` in `Submission/Work/WilC5/DclExtRedAlign_probe.lean`), the
  carrier being rewritten with `Work.WilC5.StepSeq.Fset_succ_shift`.

The hypotheses `hstrK`, `hstrL` are the alignment between the `rexp`-reduct and the ordered-field
structure `Work.WilC5.canonField` needed by that o-minimality input (they are `Structure.ext` +
`rfl` in the canonical setting of `StepNoNew.lean`).

The coherence clause (compatibility of `σₙ` with `σₘ` for `m ≤ n`) is the input of
`Work.WilC5.EmbeddingTowerGlue`, which glues the tower to a single embedding of `⋃ₙ Fₙ`.  The
natural proof is the recursion `TowerBundle n := (σ : Embedding ↥(Fsub hK S n) L) × (σ agrees with
τ on B) × (σ sends xᵢ to yᵢ for i < n)` with a `step` function built from Claim 4 and
`DclExtensionReductAlign` by `Classical.choose`, and the general coherence derived from the
one-step coherence by induction. -/
theorem StepSeqTowerExists
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
    (hstrK : (Work.WilC5.reductStruct K : WilkiesDesign.CG.LRc.Structure K) = Work.WilC5.canonField K)
    (hstrL : (Work.WilC5.reductStruct L : WilkiesDesign.CG.LRc.Structure L) = Work.WilC5.canonField L)
    (hKTR : K ⊨ WilkiesDesign.CG.TR) (hLTR : L ⊨ WilkiesDesign.CG.TR)
    {B : WilkiesDesign.CG.LRc.Substructure K}
    (hBdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) ⊆ (B : Set K))
    (hBlog : ∀ x ∈ (B : Set K), Work.WilC5.logFun x ∈ (B : Set K))
    (hBexp : ∀ x ∈ (B : Set K), Work.WilC5.expE x ∈ (B : Set K))
    (τ : WilkiesDesign.CG.LRc.Embedding ↥B L)
    (hτlog : ∀ b : ↥B,
      τ ⟨Work.WilC5.logFun (b : K), hBlog (b : K) b.2⟩ = Work.WilC5.logFun (τ b))
    (hτexp : ∀ b : ↥B,
      τ ⟨Work.WilC5.expE (b : K), hBexp (b : K) b.2⟩ = Work.WilC5.expE (τ b))
    (S : Work.WilC5.StepSeq B)
    (hnew : Work.WilC5.StepSeq.ValueNewAll S)
    (hunb : Work.WilC5.StepSeq.Unbounded S)
    (hdom : Work.WilC5.StepSeq.LogDominated S)
    (hchain : ∀ n : ℕ, Work.WilC5.VLe (Work.WilC5.logFun (S.xs n)) (S.xs (n + 1)))
    (hind : ∀ (n : ℕ) (q : Fin n → ℤ),
      (∃ c ∈ (B : Set K), c ≠ 0 ∧ WilkiesDesign.CG.IsUnitVal
        (c * ∏ i : Fin n, S.xs (i : ℕ) ^ (q i))) → q = 0)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk K < κ)
    (hsat : @Work.WilC5.IsSaturated WilkiesDesign.CG.LEc L _ κ) :
    ∃ y0 : L,
      (∀ i : ℕ, ∀ b : ↥B,
        (((b : K) < S.xs i ↔ (τ b : L) < Work.WilC5.StepSeq.ys B τ S y0 i) ∧
         (S.xs i < (b : K) ↔ Work.WilC5.StepSeq.ys B τ S y0 i < (τ b : L)))) ∧
      ∃ σ : ∀ n : ℕ, WilkiesDesign.CG.LRc.Embedding ↥(Work.WilC5.StepSeq.Fsub hK S n) L,
        (∀ n : ℕ, ∀ b : ↥B,
          σ n ⟨(b : K), Work.WilC5.StepSeq.B_mem_Fsub hK S n b.2⟩ = τ b) ∧
        (∀ (n i : ℕ) (hi : i < n),
          σ n ⟨S.xs i, Work.WilC5.StepSeq.xs_mem_Fsub hK S hi⟩ =
            Work.WilC5.StepSeq.ys B τ S y0 i) ∧
        (∀ (m n : ℕ) (h : m ≤ n) (a : K)
          (hm : a ∈ (Work.WilC5.StepSeq.Fsub hK S m : Set K))
          (hn : a ∈ (Work.WilC5.StepSeq.Fsub hK S n : Set K)),
          σ n ⟨a, hn⟩ = σ m ⟨a, hm⟩) := by
  classical
  haveI : K ⊨ WilkiesDesign.CG.TE := hK
  haveI : L ⊨ WilkiesDesign.CG.TE := hL
  -- Claim 3: the `L`-side sequence realises the cuts over `B`.
  obtain ⟨y0, hcutB⟩ :=
    StepSeqCutOverB (K := K) (L := L) hMCr hOM hrexpK haddK hmulK honeK hlenegK
      hrexpL haddL hmulL honeL hlenegL hBdcl hBlog hBexp τ hτlog hτexp S κ hκ hsat
  exact ⟨y0, hcutB,
    stepSeqTower_exists' hK hL hMCr hOM hVI hrexpK haddK hmulK honeK hlenegK
      hrexpL haddL hmulL honeL hlenegL hstrK hstrL hKTR hLTR hBdcl hBlog hBexp τ hτlog hτexp
      S hnew hunb hdom hchain hind hcutB⟩

end Work.WilC5
