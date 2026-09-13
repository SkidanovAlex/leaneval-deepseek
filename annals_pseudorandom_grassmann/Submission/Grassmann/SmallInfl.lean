import Mathlib
import Submission.Grassmann.HybridLaplacian
import Submission.Grassmann.LemLv
import Submission.Grassmann.TransposeBS
import Submission.Grassmann.InfluenceBound
import Submission.Commons.LinearAlgebra.finrank_ker_comp

/-!
# The order of a hybrid derivative versus the degree of a homogeneous function

A character `X` of rank `i` survives the hybrid Laplacian `L_{V₁,W₁}` (i.e. satisfies
`hybridPred Q ι X`) only if `i ≥ hybridOrder Q ι = dim V₁ + codim W₁`.  Consequently the
hybrid Laplacian *kills* every pure level-`i` function as soon as the order of the pair exceeds
`i`:

  `L_{V₁,W₁}[f^{= i}] = 0` for `hybridOrder Q ι > i`.

This is what allows the small-influence hypothesis `SmallInfl i ε (f^{= i})` (Proposition 5.6
is stated only for pairs of order `≤ i`) to be upgraded to `SmallInfl d ε (f^{= i})` for any
`d ≥ i`, which is the missing ingredient in the paper's derivation of `cor:atmostd`
(Theorem 1.5's Corollary 1.4) from the corollary of hypercontractivity.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- **A character kept by the hybrid Laplacian of `(Q,ι)` has rank at least the order of the
pair.**  Proof: `ker Q ≤ range X` and `ker (Q X) ≤ range ι`, whence
`(m - rank X) + dim ker Q = dim ker (Q X) ≤ dim range ι`. -/
theorem hybridOrder_le_rank_of_hybridPred {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : hybridPred Q ι X) : hybridOrder Q ι ≤ X.rank := by
  rw [hybridOrder]
  have hker_le : LinearMap.ker Q.mulVecLin ≤ LinearMap.range X.mulVecLin := hX.1
  -- `ker (Q ∘ X) = ker X + ker Q` (as far as dimensions go)
  have h1 : Module.finrank 𝔽₂ ↥(LinearMap.ker (Q.mulVecLin.comp X.mulVecLin)) =
      Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin) +
        Module.finrank 𝔽₂ ↥(LinearMap.ker Q.mulVecLin) := by
    rw [Commons.LinearAlgebra.finrank_ker_comp, inf_eq_left.mpr hker_le]
  -- `ker (Q ∘ X) ≤ range ι`
  have h2 : Module.finrank 𝔽₂ ↥(LinearMap.ker (Q.mulVecLin.comp X.mulVecLin)) ≤
      Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin) := by
    refine Submodule.finrank_mono ?_
    intro w hw
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply] at hw
    exact hX.2 w hw
  -- `dim ker X = m - rank X`
  have h3 : Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin) = m - X.rank := by
    have h := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
    have hrank : Module.finrank 𝔽₂ ↥(LinearMap.range X.mulVecLin) = X.rank := rfl
    rw [hrank, Module.finrank_fin_fun] at h
    omega
  have h4 := h2
  rw [h1, h3] at h4
  have h5 : X.rank ≤ m := X.rank_le_width
  have h6 : Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin) ≤ m := by
    have h := Submodule.finrank_le (LinearMap.range ι.mulVecLin)
    rwa [Module.finrank_fin_fun] at h
  omega

/-- **The hybrid Laplacian kills a pure level-`i` function when the order exceeds `i`.** -/
theorem lapMulN_hybridPred_nprojPure_eq_zero {m n : ℕ} {m' n' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂) (i : ℕ)
    (hi : i < hybridOrder Q ι) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    lapMulN (hybridPred Q ι) (nprojPure i f) = 0 := by
  refine eq_of_fhat_eq fun Y => ?_
  rw [fhat_lapMulN]
  rw [show fhat (0 : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) Y = 0 from fhat_zero Y]
  by_cases hY : hybridPred Q ι Y
  · rw [if_pos hY, fhat_nprojPure]
    have hge := hybridOrder_le_rank_of_hybridPred Q ι Y hY
    rw [if_neg (by omega : ¬ (Y.rank = i)), zero_mul, mul_zero]
  · rw [if_neg hY, zero_mul]

/-- **Small influences are inherited by larger orders for pure levels**: a pure level-`i`
function with `(i,ε)`-small generalised influences has `(d,ε)`-small generalised influences for
every `d ≥ i` (the influences at orders in `(i,d]` simply vanish). -/
theorem SmallInfl_of_le_order_nprojPure {m n : ℕ} {i d : ℕ} (hid : i ≤ d) {ε : ℝ}
    (hε : 0 ≤ ε) {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (h : SmallInfl i ε (nprojPure i f)) : SmallInfl d ε (nprojPure i f) := by
  intro m' n' Q ι T hQ
  by_cases hcase : hybridOrder Q ι ≤ i
  · exact h Q ι T hcase
  · have hzero : lapMulN (hybridPred Q ι) (nprojPure i f) = 0 :=
      lapMulN_hybridPred_nprojPure_eq_zero Q ι i (by omega) f
    rw [inflBS2, hzero]
    simp only [shift_zero, restr_zero, l2sq_zero]
    exact hε

end

end Submission.Grassmann
