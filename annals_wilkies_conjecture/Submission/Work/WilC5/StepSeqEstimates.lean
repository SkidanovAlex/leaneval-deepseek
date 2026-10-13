import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValueOrder
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.StepSeq
import Submission.Work.WilC5.StepSeqChain
import Submission.Work.WilC5.S4ExpF.Bridge

namespace Work.WilC5

/-- The elementary archimedean estimates for the sequence of vdDMM Lemma 4.4: the sequence `xₙ`
is archimedean-decreasing (`VLe (x i) (x j)` for `i ≤ j`), every `log x j` is archimedean-strictly
dominated by the earlier `x i` (`i ≤ j`), and the approximations `β i ∈ B` are strictly dominated by
`x i`.  `VLe a b` means "`b` is bounded by a natural multiple of `a`", i.e. `a` is at least as big
as `b` in the archimedean sense. -/
theorem StepSeqEstimates {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {B : WilkiesDesign.CG.LRc.Substructure K} (S : Work.WilC5.StepSeq B)
    (hnew : Work.WilC5.StepSeq.ValueNewAll S) (hdom : Work.WilC5.StepSeq.LogDominated S) :
    (∀ i j : ℕ, i ≤ j → Work.WilC5.VLe (S.xs i) (S.xs j)) ∧
    (∀ i j : ℕ, i ≤ j → Work.WilC5.VLe (S.xs i) (Work.WilC5.logFun (S.xs j)) ∧
      ¬ Work.WilC5.VLe (Work.WilC5.logFun (S.xs j)) (S.xs i)) ∧
    (∀ i : ℕ, Work.WilC5.VLe (S.xs i) (S.beta i : K) ∧
      ¬ Work.WilC5.VLe (S.beta i : K) (S.xs i)) := by
  -- vdDMM Lemma 4.4's chain step: `log xₙ` dominates `βₙ`, and `xₙ` dominates `x_{n+1}`.
  obtain ⟨hlogbeta, hstep⟩ := StepSeqChain hrexp hadd hmul hone hleneg B S hnew hdom
  -- the sequence is decreasing in the value order
  have hmono_step : ∀ i k : ℕ, VLe (S.xs i) (S.xs (i + k)) := by
    intro i k
    induction k with
    | zero => simpa using VLe_refl (S.xs i)
    | succ k ih =>
        rw [Nat.add_succ]
        exact VLe_trans ih (hstep (i + k))
  have hmono : ∀ i j : ℕ, i ≤ j → VLe (S.xs i) (S.xs j) := by
    intro i j hij
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact hmono_step i k
  refine ⟨hmono, ?_, ?_⟩
  · -- `x i` dominates `log x j` (chain `x i ≤ x j ≤ log x j`) and `log x j` does not dominate
    -- `x i` (else it would dominate `x j`, contradicting `LogDominated`)
    intro i j hij
    exact ⟨VLe_trans (hmono i j hij) (hdom j).1,
      fun h => (hdom j).2 (VLe_trans h (hmono i j hij))⟩
  · -- `x i` dominates `β i ∈ B` via `x i ≤ log x i ≤ β i`, and strictly, since otherwise
    -- `β i` would have the same value as `x i`, against `ValueNewAll`
    intro i
    refine ⟨VLe_trans (hdom i).1 (hlogbeta i), ?_⟩
    intro h
    exact hnew i (S.beta i) ((SameArch_iff_VLe _ _).mpr ⟨h, VLe_trans (hdom i).1 (hlogbeta i)⟩)

end Work.WilC5
