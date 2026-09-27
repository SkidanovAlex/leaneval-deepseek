import Mathlib
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.zassDefs

namespace Work.Mostow

-- File: Submission/Work/Mostow/simpleCommNormBound.lean.
-- Useful imports: import Submission.Work.Mostow.StabLift (LambdaMat),
--                  import Submission.Work.Mostow.zassDefs (Work.Mostow.SimpleCommSet).
-- The contraction inequality `hcomm` is passed in as a hypothesis so the file needs nothing else.
-- Mathematical content: with `SimpleCommSet X 0 = X` and
-- `SimpleCommSet X (k+1) = {⁅c,x⁆ | c ∈ SimpleCommSet X k, x ∈ X}`, one has
-- ‖LambdaMat c - 1‖ ≤ ε(4ε)^k for every c of weight k.  Induction on k: the base case is `hX`;
-- in the step `c = ⁅a, x⁆` with `‖Λa - 1‖ ≤ ε(4ε)^k` and `‖Λx - 1‖ ≤ ε`, both ≤ 1/4 since
-- 4ε ≤ 1/4 ≤ 1, so `hcomm` gives 4·ε(4ε)^k·ε = ε(4ε)^{k+1}.  Use `SimpleCommSet`'s recursion
-- equation (mem_SimpleCommSet_succ) and induction on k.
open scoped Matrix.Norms.Operator
open scoped commutatorElement
open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem simpleCommNormBound (n : ℕ) (hA : POActionProp n)
    (hcomm : ∀ g h : PO n 1,
      ‖Work.Mostow.LambdaMat g - 1‖ ≤ 1 / 4 →
      ‖Work.Mostow.LambdaMat h - 1‖ ≤ 1 / 4 →
      ‖Work.Mostow.LambdaMat ⁅g, h⁆ - 1‖ ≤
        4 * ‖Work.Mostow.LambdaMat g - 1‖ * ‖Work.Mostow.LambdaMat h - 1‖)
    (X : Set (PO n 1)) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 16)
    (hX : ∀ x ∈ X, ‖Work.Mostow.LambdaMat x - 1‖ ≤ ε) :
    ∀ k : ℕ, ∀ c ∈ Work.Mostow.SimpleCommSet X k,
      ‖Work.Mostow.LambdaMat c - 1‖ ≤ ε * (4 * ε) ^ k := by
  have h4ε0 : 0 ≤ 4 * ε := by linarith
  have h4ε1 : 4 * ε ≤ 1 := by linarith
  intro k
  induction k with
  | zero =>
    intro c hc
    have hc' := hX c hc
    simpa using hc'
  | succ k ih =>
    intro c hc
    obtain ⟨a, ha, x, hx, rfl⟩ := (mem_SimpleCommSet_succ X k c).mp hc
    have ha' : ‖LambdaMat a - 1‖ ≤ ε * (4 * ε) ^ k := ih a ha
    have hx' : ‖LambdaMat x - 1‖ ≤ ε := hX x hx
    have hpow : (4 * ε) ^ k ≤ 1 := pow_le_one₀ h4ε0 h4ε1
    have ha'' : ‖LambdaMat a - 1‖ ≤ 1 / 4 := by
      calc ‖LambdaMat a - 1‖ ≤ ε * (4 * ε) ^ k := ha'
        _ ≤ ε * 1 := by gcongr
        _ = ε := by ring
        _ ≤ 1 / 16 := hε'
        _ ≤ 1 / 4 := by norm_num
    have hx'' : ‖LambdaMat x - 1‖ ≤ 1 / 4 := by
      calc ‖LambdaMat x - 1‖ ≤ ε := hx'
        _ ≤ 1 / 16 := hε'
        _ ≤ 1 / 4 := by norm_num
    calc ‖LambdaMat ⁅a, x⁆ - 1‖ ≤ 4 * ‖LambdaMat a - 1‖ * ‖LambdaMat x - 1‖ :=
          hcomm a x ha'' hx''
      _ ≤ 4 * (ε * (4 * ε) ^ k) * ε := by gcongr
      _ = ε * (4 * ε) ^ (k + 1) := by rw [pow_succ]; ring

end Work.Mostow
