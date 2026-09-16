import Mathlib.Algebra.Field.ZMod
import Submission.ZagierHoffmanProof.LSeriesDepth
import Submission.ZagierHoffmanProof.LSeriesRegression
import Submission.Commons.FieldTheory.RatFunc.charP_completionAtInfty

/-!
# Regression checks: the depth-`r` `L`-series

Concrete instantiations of the results of `LSeriesFold.lean` and `LSeriesDepth.lean` over
`F = ZMod 2` and `F = ZMod 3`, with `K = F(t)_∞`, `θ = X` and `ω = θ⁻¹Ω̃`.
-/

set_option autoImplicit false
open Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq
attribute [local instance] Commons.FieldTheory.RatFunc.charP_completionAtInfty

noncomputable section

/-- The `k`-fold recursion of the depth-one `L`-series over `F₂`. -/
example (k : ℕ) :
    atL1 2 (omegaSmall 2 (thetaOf (ZMod 2))) 1 (omegaSmall 2 (thetaOf (ZMod 2)))
      = (∑ i ∈ Finset.range k, frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) i
            (omegaSmall 2 (thetaOf (ZMod 2)) ^ 1 * omegaSmall 2 (thetaOf (ZMod 2))))
        + frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) k
            (atL1 2 (omegaSmall 2 (thetaOf (ZMod 2))) 1 (omegaSmall 2 (thetaOf (ZMod 2)))) :=
  atL1_fold (by norm_num)
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num))
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)) 1 k

/-- The `L`-series is small, so the construction iterates. -/
example : IsSmall (atL1 3 (omegaSmall 3 (thetaOf (ZMod 3))) 2 (omegaSmall 3 (thetaOf (ZMod 3)))) :=
  isSmall_atL1 (by norm_num)
    (isSmall_omegaSmall 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num))
    (isSmall_omegaSmall 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num)) 2

/-- The depth-two `L`-series is small over `F₂`. -/
example : IsSmall (atLr 2 (omegaSmall 2 (thetaOf (ZMod 2)))
    [(1, omegaSmall 2 (thetaOf (ZMod 2))), (1, omegaSmall 2 (thetaOf (ZMod 2)))]) :=
  isSmall_atLr (q := 2) (ω := omegaSmall 2 (thetaOf (ZMod 2))) (by norm_num)
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num))
    _ (by intro x hx; fin_cases hx <;>
          exact isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num))
    (by simp)

/-- The depth-one `L`-series is the `atL1` series. -/
example : atLr 2 (omegaSmall 2 (thetaOf (ZMod 2))) [(1, omegaSmall 2 (thetaOf (ZMod 2)))]
    = atL1 2 (omegaSmall 2 (thetaOf (ZMod 2))) 1 (omegaSmall 2 (thetaOf (ZMod 2))) :=
  atLr_singleton (q := 2) (ω := omegaSmall 2 (thetaOf (ZMod 2))) (by norm_num)
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)) 1
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num))

/-- The paper's depth-one `𝓛(s;Q)` is Chang's depth-one series over `F₃`. -/
example : atLrPaper 3 (omegaSmall 3 (thetaOf (ZMod 3))) [(2, omegaSmall 3 (thetaOf (ZMod 3)))]
    = atL1 3 (omegaSmall 3 (thetaOf (ZMod 3))) 2 (omegaSmall 3 (thetaOf (ZMod 3))) :=
  atLrPaper_singleton (q := 3) (ω := omegaSmall 3 (thetaOf (ZMod 3))) (by norm_num)
    (isSmall_omegaSmall 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num)) 2
    (isSmall_omegaSmall 3 (thetaOf (ZMod 3)) (v_thetaOf (ZMod 3)) (by norm_num))

/-- **The entry-wise trivialisation recursion** in the paper's convention: peeling off the last
tuple element.  Here `k = 1`, so the relation reads
`𝓛(L ++ [(s,Q)]) = Qω^s·𝓛(L)^{(1)} + 𝓛(L ++ [(s,Q)])^{(1)}` at cutoff `0`. -/
example :
    atLrcutPaper 2 (omegaSmall 2 (thetaOf (ZMod 2)))
        ([(1, omegaSmall 2 (thetaOf (ZMod 2))),
          (1, omegaSmall 2 (thetaOf (ZMod 2)))]) 0
      = (∑ i ∈ Finset.range 1, frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) (0 + i)
            (omegaSmall 2 (thetaOf (ZMod 2)) ^ 1 * omegaSmall 2 (thetaOf (ZMod 2)))
          * atLrcutPaper 2 (omegaSmall 2 (thetaOf (ZMod 2)))
              [(1, omegaSmall 2 (thetaOf (ZMod 2)))] (0 + i + 1))
        + atLrcutPaper 2 (omegaSmall 2 (thetaOf (ZMod 2)))
            ([(1, omegaSmall 2 (thetaOf (ZMod 2))),
              (1, omegaSmall 2 (thetaOf (ZMod 2)))]) 1 :=
  atLrPaper_fold (q := 2) (ω := omegaSmall 2 (thetaOf (ZMod 2))) (by norm_num)
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num))
    [(1, omegaSmall 2 (thetaOf (ZMod 2)))]
    (by intro x hx; fin_cases hx <;>
          exact isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num))
    1 (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)) 0 1

/-- The twist–shift identity for the cutoff depth-two series over `F₂`. -/
example (N k : ℕ) :
    frobTwist (R := RatFunc.CompletionAtInfty (ZMod 2)) (p := 2) k
        (atLrcut 2 (omegaSmall 2 (thetaOf (ZMod 2)))
          [(1, omegaSmall 2 (thetaOf (ZMod 2))), (1, omegaSmall 2 (thetaOf (ZMod 2)))] N)
      = atLrcut 2 (omegaSmall 2 (thetaOf (ZMod 2)))
          [(1, omegaSmall 2 (thetaOf (ZMod 2))), (1, omegaSmall 2 (thetaOf (ZMod 2)))] (N + k) :=
  frobTwist_atLrcut (q := 2) (ω := omegaSmall 2 (thetaOf (ZMod 2))) (by norm_num)
    (isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num))
    _ (by intro x hx; fin_cases hx <;>
          exact isSmall_omegaSmall 2 (thetaOf (ZMod 2)) (v_thetaOf (ZMod 2)) (by norm_num)) N k

/-- Associativity of the construction (the matrix-product structure), depth two, over `F₂`. -/
example (g : ℕ → PowerSeries (RatFunc.CompletionAtInfty (ZMod 2))) (N : ℕ) :
    atLrFold 2 (omegaSmall 2 (thetaOf (ZMod 2))) g
        ([(1, omegaSmall 2 (thetaOf (ZMod 2)))] ++ [(1, omegaSmall 2 (thetaOf (ZMod 2)))]) N
      = atLrFold 2 (omegaSmall 2 (thetaOf (ZMod 2)))
          (fun i => atLrFold 2 (omegaSmall 2 (thetaOf (ZMod 2))) g
            [(1, omegaSmall 2 (thetaOf (ZMod 2)))] i)
          [(1, omegaSmall 2 (thetaOf (ZMod 2)))] N :=
  atLrFold_append 2 (omegaSmall 2 (thetaOf (ZMod 2))) g
    [(1, omegaSmall 2 (thetaOf (ZMod 2)))] [(1, omegaSmall 2 (thetaOf (ZMod 2)))] N

end

end ZagierHoffmanPositiveChar
