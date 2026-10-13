/-
  WilG4c / `SlicedSurrogateDefs` — the *fibre* (sliced) surrogate of BNZ §5.4.

  BNZ feed Corollary 19 the tuple of the pure-`y` composites
  `(λ,x) ↦ F^{(β)}(λ, x, γ_{i,α}(λ,x))` (`β₁ = 0`), which lie in `[-1,1]` rather than in
  `(0,1)`; the surrogate `(∂^β + 2)/4` repairs that at the cost of the factor `4`, which is
  then cancelled by the shrunk chart `φ'(s) = φ(c + s/4)` (`StepHigherPlan.md` §2.3/§9).

  Unlike `Work.WilkG4c.surrogate`, the domain condition here is the **fibre** condition
  `ContDiffAt ℝ |β| (slice (f l) x) (γ l x)` (smoothness of the slice `y' ↦ f l (x, y')`), not
  the joint one; this is what makes the surrogate honest at degenerate parameters
  (`StepHigherPlan.md` §8).  The graph of the surrogate is `Ω`-bounded by composing the *fibre*
  derivative graph `AlDgListSlice (p+1) (n-1)` (`SlicedDerivDefs`) with the graph of `γ`; that
  membership is `Work.WilkG4c.surrogateSliceFamGraph_mem`.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedAlpha
import Submission.Work.WilG4c.StepHigherDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG5

/-- The *fibre* surrogate of the composite `(l,x) ↦ ∂_M (f l) (x, γ l x)`: it is
`(∂_M (slice (f l) x) (γ l x) + 2)/4` where the slice is `C^{|M|}` at `γ l x`, and the fallback
value `1/2` elsewhere (so that it is a *total* `Ω`-definable function). -/
noncomputable def surrogateSlice (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (M : List (Fin n)) (l : Fin p → ℝ) (x : ℝ) : ℝ :=
  if ContDiffAt ℝ M.length (slice (f l) x) (γ l x) then
    (iteratedFDeriv ℝ M.length (slice (f l) x) (γ l x)
      (fun j => Pi.single (M.get j) 1) + 2) / 4
  else 1 / 2

@[simp] theorem surrogateSlice_of_mem {p n : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)}
    {M : List (Fin n)} {l : Fin p → ℝ} {x : ℝ}
    (h : ContDiffAt ℝ M.length (slice (f l) x) (γ l x)) :
    surrogateSlice p n f γ M l x =
      (iteratedFDeriv ℝ M.length (slice (f l) x) (γ l x)
        (fun j => Pi.single (M.get j) 1) + 2) / 4 := by
  rw [surrogateSlice, if_pos h]

@[simp] theorem surrogateSlice_of_not_mem {p n : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)}
    {M : List (Fin n)} {l : Fin p → ℝ} {x : ℝ}
    (h : ¬ ContDiffAt ℝ M.length (slice (f l) x) (γ l x)) :
    surrogateSlice p n f γ M l x = 1 / 2 := by
  rw [surrogateSlice, if_neg h]

/-- The sliced surrogate takes values in `(0,1)` as soon as the fibre derivative is bounded by
`1` on the locus. -/
theorem surrogateSlice_mem_Ioo {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)} {M : List (Fin n)} {l : Fin p → ℝ} {x : ℝ}
    (hb : ContDiffAt ℝ M.length (slice (f l) x) (γ l x) →
      |iteratedFDeriv ℝ M.length (slice (f l) x) (γ l x)
        (fun j => Pi.single (M.get j) 1)| ≤ 1) :
    surrogateSlice p n f γ M l x ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [surrogateSlice]
  by_cases h : ContDiffAt ℝ M.length (slice (f l) x) (γ l x)
  · rw [if_pos h]
    have := hb h
    constructor <;> linarith [abs_le.mp this]
  · rw [if_neg h]; norm_num

end Work.WilkG4c
