import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Term-by-term differentiation of series, in the one-dimensional iterated derivative

If a family `g n : ℝ → F` consists of functions of class `C^∞` (indeed of class `C^ω`), and
the `k`-th iterated derivative of `g n` is bounded uniformly in the point by a summable
sequence `v k`, then the series `∑' n, g n` is `k` times differentiable and its `k`-th
iterated derivative is the series of the `k`-th iterated derivatives.

This is deduced from Mathlib's `iteratedFDeriv_tsum` (the analogous statement for the iterated
Fréchet derivative) using that for functions on `ℝ` the `k`-th iterated derivative is related to
the `k`-th iterated Fréchet derivative by the linear isometry equivalence
`ContinuousMultilinearMap.piFieldEquiv` (which has the same operator norm), and that a
continuous linear equivalence commutes with infinite sums.
-/

namespace Work.Diff.EXT

/-- The `k`-th iterated derivative of a term-by-term differentiable series is the series of the
`k`-th iterated derivatives. -/
theorem iteratedDeriv_tsum
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℕ → ℝ → F) (v : ℕ → ℕ → ℝ) (hg : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n))
    (hv : ∀ k, Summable (v k)) (hb : ∀ k n t, ‖iteratedDeriv k (g n) t‖ ≤ v k n) (k : ℕ) :
    iteratedDeriv k (fun t => ∑' n, g n t) = fun t => ∑' n, iteratedDeriv k (g n) t := by
  -- The hypothesis `hb` gives a summable uniform bound on the *iterated Fréchet* derivative as
  -- well, since `‖iteratedFDeriv ℝ j (g n) x‖ = ‖iteratedDeriv j (g n) x‖`.
  have hb' : ∀ (j : ℕ) (n : ℕ) (x : ℝ), ↑j ≤ (⊤ : ℕ∞) → ‖iteratedFDeriv ℝ j (g n) x‖ ≤ v j n := by
    intro j n x _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hb j n x
  -- Mathlib's term-by-term differentiation for the iterated Fréchet derivative.
  have H := iteratedFDeriv_tsum (𝕜 := ℝ) (E := ℝ) (α := ℕ) (F := F) (f := g) (v := v)
    (N := (⊤ : ℕ∞)) hg (fun j _ => hv j) hb' (k := k) le_top
  -- For functions on `ℝ`, the iterated derivative is the iterated Fréchet derivative evaluated
  -- through the isometry `piFieldEquiv`, whose inverse is evaluation at the constant vector `1`.
  have he : ∀ (φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ) F),
      (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm φ = φ (fun _ => 1) :=
    fun _ => rfl
  funext x
  have Hx : iteratedFDeriv ℝ k (fun y => ∑' n, g n y) x =
      ∑' n, iteratedFDeriv ℝ k (g n) x := congrFun H x
  calc iteratedDeriv k (fun t => ∑' n, g n t) x
      = (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm
          (iteratedFDeriv ℝ k (fun t => ∑' n, g n t) x) := by
        rw [he]; rfl
    _ = (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm
          (∑' n, iteratedFDeriv ℝ k (g n) x) := by rw [Hx]
    _ = ∑' n, (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm
          (iteratedFDeriv ℝ k (g n) x) :=
        ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) F).symm.toContinuousLinearEquiv).map_tsum
    _ = ∑' n, iteratedDeriv k (g n) x := by
        apply tsum_congr
        intro n
        rw [he]
        rfl

end Work.Diff.EXT
