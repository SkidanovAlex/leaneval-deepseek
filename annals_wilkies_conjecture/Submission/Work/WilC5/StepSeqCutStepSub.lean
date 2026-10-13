import Mathlib
import Submission.Work.WilC5.StepSeqCutStep
import Submission.Work.WilC5.embedding_map_leEL
import Submission.Work.WilC5.S4StepNewSetup

namespace Work.WilC5

/-- **vdDMM Lemma 4.4, the `−`-case of the cut transport.**  Companion of
`Work.WilC5.StepSeqCutStep` (same context and hypotheses, which are kept here so that the companion
applies literally): if `log x = β − x'` on the `K`-side and `log y = τ β − y'` on the `L`-side, then
the cut realisation of `x` by `y` over `B` transfers to `x'` and `y'`.

This is the case `εₙ = −1` of the extension step of Lemma 4.4 (`log xₙ = βₙ − x_{n+1}`), which
`Work.WilC5.StepSeqCutStep` — stated for `log x = β + x'` — does not cover directly.

*Proof.*  Put `x'' = negE x'` and `y'' = -y'`.  Since `subE x z = addE x (negE z)`, `hrel` is
`log x = addE β x''` definitionally; `hrelL` becomes `log y = addE (τ β) y''` after `haddL` and
`sub_eq_add_neg` (`x - y'' = x + y''` since `y'' = -y'`).  So `Work.WilC5.StepSeqCutStep` with
`(x'', y'')` gives the cut realisation of `x''` by `y''` over `B`, i.e. for every `b : B`,
`(b:K) < negE x' ↔ (τ b:L) < -y'` and `negE x' < (b:K) ↔ -y' < τ b`.  Now apply these to the
*negated* element `c : B` with `(c : K) = -(b : K)` (a substructure is closed under the ring
operations, and `negE` of `K` composed with the coercion of `↥B` is the coercion of `negEL b`) and
negate the resulting inequalities: `negE (negE x') = x'` in the field order means
`-(-x') = x'`, and `tau` commutes with negation (`Work.WilC5.map_negEL`) so `τ c = -(τ b)`. -/
theorem StepSeqCutStepSub
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (hTEK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hTEL : FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TE)
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
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) (B : Set K)
      ⊆ (B : Set K))
    (hBlog : ∀ x ∈ (B : Set K), Work.WilC5.logFun x ∈ (B : Set K))
    (hBexp : ∀ x ∈ (B : Set K), Work.WilC5.expE x ∈ (B : Set K))
    (τ : WilkiesDesign.CG.LRc.Embedding B L)
    (hτlog : ∀ x : B, τ ⟨Work.WilC5.logFun (x : K), hBlog (x : K) x.2⟩ = Work.WilC5.logFun (τ x))
    (hτexp : ∀ x : B, τ ⟨Work.WilC5.expE (x : K), hBexp (x : K) x.2⟩ = Work.WilC5.expE (τ x))
    {x x' : K} {y y' : L} (a : B)
    (hrel : Work.WilC5.logFun x = Work.WilC5.subE (a : K) x')
    (hrelL : Work.WilC5.logFun y = (τ a : L) - y')
    (hcut : ∀ b : B, ((b : K) < x ↔ (τ b : L) < y) ∧ (x < (b : K) ↔ y < τ b)) :
    ∀ b : B, ((b : K) < x' ↔ (τ b : L) < y') ∧ (x' < (b : K) ↔ y' < τ b) := by
  classical
  -- ## 0. `LEc`-negation is field negation on both sides
  have hnegK : ∀ z : K, Work.WilC5.negE z = -z :=
    fun z => Work.WilC5.S4ExpF.negE_eq_neg hTEK haddK z
  have hnegL : ∀ z : L, Work.WilC5.negE z = -z :=
    fun z => Work.WilC5.S4ExpF.negE_eq_neg hTEL haddL z
  -- ## 1. `LRc`-negation is field negation on both sides
  have hnegEL_K : ∀ u : K, @Work.WilC5.negEL K (Work.WilC5.reductStruct K) u = -u := by
    intro u
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc K
        (Work.WilC5.reductStruct K) 1
        (Sum.inl (Sum.inl FirstOrder.Ring.negFunc)) ![u] = -u
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact hnegK u
  have hnegEL_L : ∀ u : L, @Work.WilC5.negEL L (Work.WilC5.reductStruct L) u = -u := by
    intro u
    show @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc L
        (Work.WilC5.reductStruct L) 1
        (Sum.inl (Sum.inl FirstOrder.Ring.negFunc)) ![u] = -u
    rw [Work.WilC5.reductStruct_funMap_ring]
    exact hnegL u
  -- ## 2. the `L`-side relation re-expressed with the `LEc` addition symbol
  have hrelL' : Work.WilC5.logFun y = Work.WilC5.addE (τ a) (-y') := by
    rw [hrelL, sub_eq_add_neg, ← haddL]
  -- ## 3. the companion `+`-case, applied to `negE x'` and `-y'`
  have hstep := StepSeqCutStep hMCr hOM hTEK hTEL hrexpK haddK hmulK honeK hlenegK
    hrexpL haddL hmulL honeL hlenegL B hBdcl hBlog hBexp τ hτlog hτexp a
    (show Work.WilC5.logFun x = Work.WilC5.addE (a : K) (Work.WilC5.negE x') from hrel)
    hrelL' hcut
  -- ## 4. transport along the negated element of `B`
  intro b
  have hcK : ((Work.WilC5.negEL b : ↥B) : K) = -(b : K) := by
    show B.subtype (Work.WilC5.negEL b) = -(B.subtype b)
    rw [Work.WilC5.map_negEL B.subtype b, hnegEL_K (B.subtype b)]
  have hτc : (τ (Work.WilC5.negEL b) : L) = -(τ b : L) := by
    rw [Work.WilC5.map_negEL τ b, hnegEL_L (τ b)]
  have hc := hstep (Work.WilC5.negEL b)
  constructor
  · have h := hc.2
    rw [hcK, hnegK x', hτc] at h
    rwa [neg_lt_neg_iff, neg_lt_neg_iff] at h
  · have h := hc.1
    rw [hcK, hnegK x', hτc] at h
    rwa [neg_lt_neg_iff, neg_lt_neg_iff] at h

end Work.WilC5
