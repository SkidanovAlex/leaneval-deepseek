import Mathlib
import Submission.Work.WilC5.StepSeqChain

namespace Work.WilC5

/-- **The chain invariant of the vdDMM Lemma 4.4 sequence, in the direction used by the source.**
`K ⊨ TE`, `B ≤ K`, `S : StepSeq B` the sequence of the extension step (`xₙ = S.xs n`,
`βₙ = S.beta n`, `log xₙ = βₙ + εₙ x_{n+1}`), value-new (`hnew`) with `v(xₙ) < v(log xₙ)`
(`hdom`).  Then `v(log xₙ) ≤ v(x_{n+1})`, i.e. `VLe (log xₙ) (x_{n+1})`.

Indeed `Work.WilC5.StepSeqChain` gives `VLe (log xₙ) βₙ` (`|βₙ| ≤ N|log xₙ|`), and
`log xₙ = βₙ ± x_{n+1}` gives `|x_{n+1}| ≤ |log xₙ| + |βₙ| ≤ (N+1)|log xₙ|`.

(This is the hypothesis `hchain` of `Work.WilC5.StepSeqCutBig` / `Work.WilC5.StepSeqLogPres` /
`Work.WilC5.StepSeqIndepVLe`.  Note it is the *opposite* direction to the identically named
hypothesis of `Work.WilC5.StepSeqIndep`: the source's chain is
`v(xₙ) < v(log xₙ) < v(xₙ₊₁) ≤ 0`, i.e. `x_{n+1}` is closer to finite than `log xₙ`.) -/
theorem StepSeqVLeLog
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (S : Work.WilC5.StepSeq B)
    (hnew : Work.WilC5.StepSeq.ValueNewAll S)
    (hdom : Work.WilC5.StepSeq.LogDominated S) :
    ∀ n : ℕ, Work.WilC5.VLe (Work.WilC5.logFun (S.xs n)) (S.xs (n + 1)) := by
  have hTE : K ⊨ WilkiesDesign.CG.TE := inferInstance
  -- the addition/subtraction symbols of `TE` agree with the field operations
  have hsub : ∀ x y : K, Work.WilC5.subE x y = x - y :=
    fun x y => Work.WilC5.S4ExpF.subE_eq_sub hTE hadd x y
  -- dissect the defining relation `log xₙ = βₙ + εₙ x_{n+1}` of the sequence
  have hrel_n : ∀ n : ℕ, Work.WilC5.logFun (S.xs n) = (S.beta n : K) + S.xs (n + 1) ∨
      Work.WilC5.logFun (S.xs n) = (S.beta n : K) - S.xs (n + 1) := by
    intro n
    rw [S.hrel n]
    cases hb : S.pos n with
    | false => exact Or.inr (hsub _ _)
    | true => exact Or.inl (hadd _ _)
  -- `Work.WilC5.StepSeqChain` gives that `log xₙ` dominates `βₙ`
  have hA : ∀ n : ℕ, Work.WilC5.VLe (Work.WilC5.logFun (S.xs n)) (S.beta n : K) :=
    fun n => (StepSeqChain hrexp hadd hmul hone hleneg B S hnew hdom).1 n
  intro n
  -- `|x_{n+1}| = |log xₙ - βₙ| ≤ |log xₙ| + |βₙ| ≤ (C + 1)|log xₙ|`
  exact StepSeqChainAux.vle_chain_of_rel (hA n) (hrel_n n) (VLe_refl _)

end Work.WilC5
