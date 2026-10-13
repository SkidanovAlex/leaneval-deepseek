import Mathlib
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.StepSeqCutStep
import Submission.Work.WilC5.DclExtRedAlign_probe
import Submission.Work.WilC5.LRcSatOfLEcSat
import Submission.Work.WilC5.RealizesCutOrderPreserving
import Submission.Work.WilC5.StepSeqCutStepSub

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- The `LRc`-structure `κ`-layer of the `§4` layer reads `LR.withConstantsStructure ℝ` as: ring
part the `LRc`-reduct `Work.WilC5.lrcRingReduct K`, `rexp` part the given `rexpL`-structure of `K`,
constants the constants-reduct `Work.WilC5.lrcConstReduct K`.  (The `rexp` part is the given
instance, not the reduct of `reductStruct K`; the two agree by the alignment hypothesis `hrexpK`.) -/
private noncomputable def synStruct (K : Type) [WilkiesDesign.CG.LEc.Structure K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K] :
    LRc.Structure K :=
  @Language.withConstantsStructure LR K
    (@Language.sumStructure Language.ring rexpL K (Work.WilC5.lrcRingReduct K)
      (inferInstanceAs (WilkiesDesign.CG.rexpL.Structure K)))
    ℝ (Work.WilC5.lrcConstReduct K)

/-- **The `κ`-syntactic structure is the reduct.**  With the `rexp`-alignment hypothesis
`hrexpK` (the only field in which the two differ), the structure at which `LR.withConstantsStructure ℝ`
is read is the reduct `Work.WilC5.reductStruct K` itself. -/
private theorem synStruct_eq_reduct {K : Type} [WilkiesDesign.CG.LEc.Structure K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hrexpK : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
      WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x) :
    (synStruct K : LRc.Structure K) = (Work.WilC5.reductStruct K : LRc.Structure K) := by
  ext n f y
  · rcases f with (g | c)
    · rcases g with (g | r)
      · rfl
      · cases r
        show @Structure.funMap rexpL K (inferInstanceAs (rexpL.Structure K)) 1 rexpFunc.rexp y
          = rexpFromExp (y 0)
        rw [show y = ![y 0] from by funext i; fin_cases i <;> rfl]
        exact hrexpK (y 0)
    · rfl
  · nomatch f

/-- **The `LRc`-embedding `τ : ↥B → L` of the vdDMM §4 layer is order preserving for the field
orders.**  `K, L ⊨ TE`; `B ≤ K` is an `LRc`-substructure closed under the definable logarithm
`logFun` and under the exponential `expE`; `τ : ↥B → L` is an `LRc`-embedding commuting with `expE`
(and hence with the ring operations); the `LEc`-order `leE` is the field order on both `K` and `L`,
and `addE` is field addition.  Then `a ≤ b` in `K` implies `τ a ≤ τ b` in `L`: if `a < b`, then
`d = b - a ∈ B` is positive, `d = expE (logFun d)` with `logFun d ∈ B`, so
`τ d = expE (τ (logFun d)) > 0` in `L` by positivity of the exponential, while `τ d = τ b - τ a`
since `τ` commutes with subtraction; hence `τ a < τ b`.

(The same argument is used inside `Work.WilC5.StepSeqCutStep`.) -/
theorem tauOrderPreserving
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (hTEK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hTEL : FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TE)
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hlenegK : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hlenegL : ∀ x y : L, Work.WilC5.leE x y ↔ x ≤ y)
    {B : WilkiesDesign.CG.LRc.Substructure K}
    (hBlog : ∀ x ∈ (B : Set K), Work.WilC5.logFun x ∈ (B : Set K))
    (hBexp : ∀ x ∈ (B : Set K), Work.WilC5.expE x ∈ (B : Set K))
    (τ : WilkiesDesign.CG.LRc.Embedding ↥B L)
    (hτexp : ∀ b : ↥B,
      τ ⟨Work.WilC5.expE (b : K), hBexp (b : K) b.2⟩ = Work.WilC5.expE (τ b)) :
    ∀ a b : ↥B, (a : K) ≤ (b : K) → (τ a : L) ≤ (τ b : L) := by
  classical
  -- ## 0. bridges between the `LEc` symbols and the field operations
  have hzeroK : (Work.WilC5.zeroE : K) = 0 := Work.WilC5.S4ExpF.zeroE_eq_zero hTEK haddK
  have hnegK : ∀ x : K, Work.WilC5.negE x = -x :=
    fun x => Work.WilC5.S4ExpF.negE_eq_neg hTEK haddK x
  have hzeroL : (Work.WilC5.zeroE : L) = 0 := Work.WilC5.S4ExpF.zeroE_eq_zero hTEL haddL
  have hnegL : ∀ x : L, Work.WilC5.negE x = -x :=
    fun x => Work.WilC5.S4ExpF.negE_eq_neg hTEL haddL x
  -- ## 1. the ring operations of `↥B` and of `L` are the field ones
  have hcoe_add : ∀ u v : ↥B, ((Work.WilC5.addEL u v : ↥B) : K) = (u : K) + (v : K) := by
    intro u v
    show B.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥B _ 2
        (Work.WilC5.ringSymL FirstOrder.Ring.addFunc) ![u, v]) = (u : K) + (v : K)
    have h := (FirstOrder.Language.Substructure.subtype B).map_fun
      (Work.WilC5.ringSymL FirstOrder.Ring.addFunc) ![u, v]
    have h2 : (B.subtype ∘ ![u, v]) = ![(u : K), (v : K)] := by
      funext i; fin_cases i <;> rfl
    rw [h2] at h
    rw [h]
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc K _ 2
        (Sum.inl (Sum.inl FirstOrder.Ring.addFunc)) ![(u : K), (v : K)] = (u : K) + (v : K)
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact haddK (u : K) (v : K)
  have hcoe_neg : ∀ u : ↥B, ((Work.WilC5.negEL u : ↥B) : K) = -(u : K) := by
    intro u
    show B.subtype (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥B _ 1
        (Work.WilC5.ringSymL FirstOrder.Ring.negFunc) ![u]) = -(u : K)
    have h := (FirstOrder.Language.Substructure.subtype B).map_fun
      (Work.WilC5.ringSymL FirstOrder.Ring.negFunc) ![u]
    have h2 : (B.subtype ∘ ![u]) = ![(u : K)] := by
      funext i; fin_cases i <;> rfl
    rw [h2] at h
    rw [h]
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc K _ 1
        (Sum.inl (Sum.inl FirstOrder.Ring.negFunc)) ![(u : K)] = -(u : K)
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact hnegK (u : K)
  have hcoe_sub : ∀ u v : ↥B, ((Work.WilC5.subEL u v : ↥B) : K) = (u : K) - (v : K) := by
    intro u v
    show ((Work.WilC5.addEL u (Work.WilC5.negEL v) : ↥B) : K) = (u : K) - (v : K)
    rw [hcoe_add u (Work.WilC5.negEL v), hcoe_neg v]
    ring
  have haddEL_L : ∀ u v : L, @Work.WilC5.addEL L (Work.WilC5.reductStruct L) u v = u + v := by
    intro u v
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc L
        (Work.WilC5.reductStruct L) 2 (Sum.inl (Sum.inl FirstOrder.Ring.addFunc)) ![u, v] = u + v
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact haddL u v
  have hnegEL_L : ∀ u : L, @Work.WilC5.negEL L (Work.WilC5.reductStruct L) u = -u := by
    intro u
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc L
        (Work.WilC5.reductStruct L) 1 (Sum.inl (Sum.inl FirstOrder.Ring.negFunc)) ![u] = -u
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact hnegL u
  have hsubEL_L : ∀ u v : L, @Work.WilC5.subEL L (Work.WilC5.reductStruct L) u v = u - v := by
    intro u v
    show @Work.WilC5.addEL L (Work.WilC5.reductStruct L) u
      (@Work.WilC5.negEL L (Work.WilC5.reductStruct L) v) = u - v
    rw [haddEL_L u (@Work.WilC5.negEL L (Work.WilC5.reductStruct L) v), hnegEL_L v,
      sub_eq_add_neg]
  -- ## 2. the strict monotonicity of `τ`
  have strictFwd : ∀ a b : ↥B, (a : K) < (b : K) → τ a < τ b := by
    intro a b hab
    let d : ↥B := Work.WilC5.subEL b a
    have hd : (d : K) = (b : K) - (a : K) := hcoe_sub b a
    have hdpos : (0 : K) < (d : K) := by rw [hd]; linarith
    have hlogd : Work.WilC5.logFun (d : K) ∈ (B : Set K) := hBlog (d : K) d.2
    have hexp : Work.WilC5.expE (Work.WilC5.logFun (d : K)) = (d : K) :=
      Work.WilC5.expE_logFun_of_pos_of_model hTEK
        ((Work.WilC5.S4ExpF.leE_zero_iff hTEK haddK hlenegK (d : K)).mpr hdpos)
    have hdEq : d = ⟨Work.WilC5.expE (Work.WilC5.logFun (d : K)),
        hBexp (Work.WilC5.logFun (d : K)) hlogd⟩ :=
      Subtype.ext hexp.symm
    have hτd : (τ d : L) = Work.WilC5.expE (τ ⟨Work.WilC5.logFun (d : K), hlogd⟩) := by
      have h1 : τ d = τ ⟨Work.WilC5.expE (Work.WilC5.logFun (d : K)),
          hBexp (Work.WilC5.logFun (d : K)) hlogd⟩ := congrArg τ hdEq
      rw [h1, hτexp ⟨Work.WilC5.logFun (d : K), hlogd⟩]
    have hpos : (0 : L) < (τ d : L) := by
      rw [hτd]
      exact (Work.WilC5.S4ExpF.leE_zero_iff hTEL haddL hlenegL _).mp
        (Work.WilC5.expE_pos_of_model hTEL _)
    have hτd' : (τ d : L) = (τ b : L) - (τ a : L) := by
      have h1 : τ d = Work.WilC5.subEL (τ b) (τ a) := by
        rw [show d = Work.WilC5.subEL b a from rfl]
        exact Work.WilC5.map_subEL τ b a
      rw [h1]
      exact hsubEL_L (τ b) (τ a)
    rw [hτd'] at hpos
    linarith
  -- ## 3. the conclusion
  intro a b hab
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact le_of_lt (strictFwd a b hlt)
  · rw [Subtype.ext heq]

/-- **vdDMM Lemma 4.4, Claim 3 (in the form used by the tower).**  `K, L ⊨ TE`, `L` is
`κ`-saturated for `LEc` with `κ > |K|`, `B ≤ K` is `Dcl`-closed, log-closed and closed under the
exponential, `τ : B → L` is an `LRc`-embedding commuting with the definable logarithm and with the
exponential on `B`, and `S : StepSeq B` is the sequence of the extension step of Lemma 4.4
(`log xₙ = βₙ ± x_{n+1}` with `βₙ ∈ B`).

Then there is `y₀ ∈ L` such that, for *every* `i`, the element `yᵢ := ys B τ S y₀ i` of the
`L`-side sequence realises the image under `τ` of the cut of `xᵢ` over `B`:
`b < xᵢ ↔ τ b < yᵢ` and `xᵢ < b ↔ yᵢ < τ b` for every `b ∈ B`.

The proof is the induction of the source's Claim 3: the case `i = 0` is the realisation of the cut
of `x₀` in the saturated model, with `F := B` — using `Work.WilC5.model_TR_of_dcl_closed` for
`↥B ⊨ TR`, the transfer of `LEc`- to `LRc`-saturation `Work.WilC5.lrcSaturated_of_lecSaturated`,
and the alignment facts `hrexpK`, `haddK`, `hmulK`, `honeK`, `hlenegK` which identify the
`LRc`-definable order `leEL` with the field order (`Work.WilC5.leEL_iff_le`); a completed, aligned
version of that base case is `Work.WilC5.DclExtensionReductAlign`'s sibling machinery in
`Submission/Work/WilC5/DclExtRed_probe.lean` (the cut form is
`Submission/Work/WilC5/DclExtRed_probe.lean`'s aligned `RealizesCutReduct`).  The step is
`Work.WilC5.StepSeqCutStep`, applied in the two sign cases of `S.pos i` (for `S.pos i = false` one
first rewrites the relation as `log xᵢ = βᵢ + (−x_{i+1})` using `subE = addE ∘ negE`, gets the cut
realisation of `−x_{i+1}` by `−y_{i+1}`, and then negates both sides, using that `B` is closed under
negation). -/
theorem StepSeqCutOverB
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TE]
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
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
    (hBexp : ∀ x ∈ (B : Set K), Work.WilC5.expE x ∈ (B : Set K))
    (τ : WilkiesDesign.CG.LRc.Embedding ↥B L)
    (hτlog : ∀ b : ↥B,
      τ ⟨Work.WilC5.logFun (b : K), hBlog (b : K) b.2⟩ = Work.WilC5.logFun (τ b))
    (hτexp : ∀ b : ↥B,
      τ ⟨Work.WilC5.expE (b : K), hBexp (b : K) b.2⟩ = Work.WilC5.expE (τ b))
    (S : Work.WilC5.StepSeq B)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk K < κ)
    (hsat : @Work.WilC5.IsSaturated WilkiesDesign.CG.LEc L _ κ) :
    ∃ y0 : L, ∀ i : ℕ, ∀ b : ↥B,
      (((b : K) < S.xs i ↔ (τ b : L) < Work.WilC5.StepSeq.ys B τ S y0 i) ∧
       (S.xs i < (b : K) ↔ Work.WilC5.StepSeq.ys B τ S y0 i < (τ b : L))) := by
  classical
  -- ## 0. the two models parse as models of `TR` at the `rexp`-reduct
  have hTEK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE :=
    inferInstanceAs (FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
  have hTEL : FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TE :=
    inferInstanceAs (FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TE)
  haveI hKTR : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR :=
    Work.WilC5.reduct_model_TR K hTEK
  haveI hLTR : FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR :=
    Work.WilC5.reduct_model_TR L hTEL
  -- ## 1. `LRc`-saturation of `L` and the cardinality bound
  have hsatL : @Work.WilC5.IsSaturated WilkiesDesign.CG.LRc L (Work.WilC5.reductStruct L) κ :=
    Work.WilC5.lrcSaturated_of_lecSaturated κ hsat
  have hcard : Cardinal.mk ↥B < κ :=
    lt_of_le_of_lt
      (Cardinal.mk_le_of_injective (f := fun b : ↥B => (b : K)) Subtype.coe_injective) hκ
  -- ## 2. the base case of the induction: the cut of `x₀` over `B`
  have hord : ∀ a b : ↥B, (a : K) ≤ (b : K) → (τ a : L) ≤ (τ b : L) :=
    Work.WilC5.tauOrderPreserving hTEK hTEL haddK hlenegK haddL hlenegL hBlog hBexp τ hτexp
  have hleL : ∀ a b : L, Work.WilC5.leEL a b ↔ a ≤ b := fun a b => hlenegL a b
  obtain ⟨y0, hy0⟩ :=
    Work.WilC5.RealizesCutOrderPreserving B τ (S.xs 0) hord hleL κ hcard hsatL
  -- ## 3. the induction step
  have hstep : ∀ i : ℕ,
      (∀ b : ↥B, (((b : K) < S.xs i ↔ (τ b : L) < Work.WilC5.StepSeq.ys B τ S y0 i) ∧
        (S.xs i < (b : K) ↔ Work.WilC5.StepSeq.ys B τ S y0 i < (τ b : L)))) →
      (∀ b : ↥B, (((b : K) < S.xs (i + 1) ↔
          (τ b : L) < Work.WilC5.StepSeq.ys B τ S y0 (i + 1)) ∧
        (S.xs (i + 1) < (b : K) ↔
          Work.WilC5.StepSeq.ys B τ S y0 (i + 1) < (τ b : L)))) := by
    intro i ih
    -- The `LRc`-structure at which `StepSeqCutStep` states its (unused) `Dcl`-hypothesis is
    -- `Work.WilC5.synStruct K`, which the `rexp`-alignment hypothesis `hrexpK` identifies with the
    -- reduct `Work.WilC5.reductStruct K` at which `hBdcl` is stated.  The `letI` makes the
    -- elaborator choose the constants-reduct for the constant instance of that structure.
    letI : (FirstOrder.Language.constantsOn ℝ).Structure K := Work.WilC5.lrcConstReduct K
    have hBdcl' : @Work.WilC2.Dcl K (Work.WilC5.synStruct K) (B : Set K) ⊆ (B : Set K) := by
      rw [Work.WilC5.synStruct_eq_reduct (K := K) hrexpK]
      exact hBdcl
    by_cases hp : S.pos i = true
    · -- the `+` case: `StepSeqCutStep`
      have hrel : Work.WilC5.logFun (S.xs i) =
          Work.WilC5.addE (S.beta i : K) (S.xs (i + 1)) := by
        have h := S.hrel i
        simpa [hp] using h
      have hrelL : Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 i) =
          Work.WilC5.addE (τ (S.beta i)) (Work.WilC5.StepSeq.ys B τ S y0 (i + 1)) := by
        have h := Work.WilC5.StepSeq.ys_rel B τ S y0 i
        have h' : Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 i) =
            (τ (S.beta i) : L) + Work.WilC5.StepSeq.ys B τ S y0 (i + 1) := by
          simpa [hp] using h
        rw [h', haddL]
      exact Work.WilC5.StepSeqCutStep hMCr hOM hTEK hTEL hrexpK haddK hmulK honeK hlenegK
        hrexpL haddL hmulL honeL hlenegL B hBdcl' hBlog hBexp τ hτlog hτexp (S.beta i)
        hrel hrelL ih
    · -- the `-` case: `StepSeqCutStepSub`
      have hpf : S.pos i = false := by
        cases hi : S.pos i
        · rfl
        · exact absurd hi hp
      have hrel : Work.WilC5.logFun (S.xs i) =
          Work.WilC5.subE (S.beta i : K) (S.xs (i + 1)) := by
        have h := S.hrel i
        simpa [hpf] using h
      have hrelL : Work.WilC5.logFun (Work.WilC5.StepSeq.ys B τ S y0 i) =
          (τ (S.beta i) : L) - Work.WilC5.StepSeq.ys B τ S y0 (i + 1) := by
        have h := Work.WilC5.StepSeq.ys_rel B τ S y0 i
        simpa [hpf] using h
      exact Work.WilC5.StepSeqCutStepSub hMCr hOM hTEK hTEL hrexpK haddK hmulK honeK
        hlenegK hrexpL haddL hmulL honeL hlenegL B hBdcl' hBlog hBexp τ hτlog hτexp (S.beta i)
        hrel hrelL ih
  -- ## 4. assemble
  refine ⟨y0, fun i => ?_⟩
  induction i with
  | zero => intro b; exact ⟨hy0.1 b, hy0.2 b⟩
  | succ i ih => exact hstep i ih

end Work.WilC5
