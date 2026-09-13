import Mathlib
import Submission.Grassmann.InductiveStep
import Submission.Grassmann.LemLv

/-!
# Generalised influences and the order-one case of `prop:influences measure globalness`

The paper's generalised influence (`I_{V₁,W₁,T}[f] = ‖D_{V₁,W₁,T}[f]‖₂²`) and the statement that
restriction-globalness implies small influences (Proposition 5.6 of arXiv:2209.04243).

This file formalises

* `inflBS2 Q ι T f` — the normalised `L²` norm squared of the derivative `D_{V₁,W₁,T}[f]`;
* `SmallInfl d ε f` — the statement that all influences of order `≤ d` are at most `ε`;
* `sum_normSq_fcoeff` (Parseval for the *normalised* coefficients: `Σ_X ‖f̂ X‖² = ‖f‖₂²`) and
  `l2sq_nprojPure_le` (the normalised level projection is an `L²`-contraction);
* **`inflBS2_nprojPure_le_of_order_one`** — the order-one case of Proposition 5.6: for
  `(V₁, W₁) = (span v, W)` with `v ≠ 0` and `f` `(d,ε)`-restriction global,
  `I_{V₁,W₁,T}[f^{=d}] ≤ 100·2^{4d}·ε`.

The proof is a two-line combination of the three main theorems of the last three modules:
`lem:lv` (`nprojPure_restr_shift_TOp`) rewrites the influence of `f^{=d}` as the level-`(d-1)`
part of the restriction of `𝒯_{d,v}[f]`, `l2sq_nprojPure_le` discards the level projection,
and `l2sq_restr_shift_TOp_le` (the convexity step) bounds the result by `100·2^{4d}·ε`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## Parseval for the normalised coefficients -/

/-- **Parseval for the normalised Fourier coefficients**: `Σ_X ‖f̂(X)‖² = ‖f‖₂²`. -/
lemma sum_normSq_fcoeff {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖fcoeff f X‖ ^ 2 = l2sq f := by
  have hpoint : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂,
      ‖fcoeff f X‖ ^ 2 = ((2 : ℝ) ^ (m * n))⁻¹ ^ 2 * ‖fhat f X‖ ^ 2 := by
    intro X
    rw [fcoeff, norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
    ring
  rw [Finset.sum_congr rfl (fun X _ => hpoint X), ← Finset.mul_sum, fhat_parseval_normSq, l2sq, sq]
  rw [show ((2 : ℝ) ^ (m * n))⁻¹ * ((2 : ℝ) ^ (m * n))⁻¹ *
        ((2 : ℝ) ^ (m * n) * ∑ A : Matrix (Fin m) (Fin n) 𝔽₂, ‖f A‖ ^ 2) =
      (((2 : ℝ) ^ (m * n))⁻¹ * (2 : ℝ) ^ (m * n)) *
        (((2 : ℝ) ^ (m * n))⁻¹ * ∑ A : Matrix (Fin m) (Fin n) 𝔽₂, ‖f A‖ ^ 2) by ring,
    inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

/-- The normalised pure-level projection is an `L²`-contraction. -/
lemma l2sq_nprojPure_le {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (nprojPure d f) ≤ l2sq f := by
  rw [← sum_normSq_fcoeff (nprojPure d f), ← sum_normSq_fcoeff f]
  refine Finset.sum_le_sum fun X _ => ?_
  rw [fcoeff_nprojPure]
  by_cases hX : X.rank = d
  · rw [if_pos hX, one_mul]
  · rw [if_neg hX, zero_mul, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact sq_nonneg _

/-! ## Generalised influences -/

/-- The paper's generalised influence `I_{V₁,W₁,T}[f] = ‖D_{V₁,W₁,T}[f]‖₂²` of the pair
`(V₁,W₁) = (ker Q, range ι)` at the shift `T`, in normalised form. -/
def inflBS2 {m n : ℕ} {m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℝ :=
  l2sq (restr Q ι (shift T (lapMulN (hybridPred Q ι) f)))

/-- `f` has `(d,ε)`-small generalised influences. -/
def SmallInfl {m n : ℕ} (d : ℕ) (ε : ℝ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : Prop :=
  ∀ {m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (T : Matrix (Fin m) (Fin n) 𝔽₂), hybridOrder Q ι ≤ d → inflBS2 Q ι T f ≤ ε

/-- Under the hypotheses of `lem:lv` the hybrid Laplacian has order exactly one. -/
lemma hybridOrder_eq_one {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) {v : Fin n → 𝔽₂} (hv : v ≠ 0)
    (hker : LinearMap.ker Q.mulVecLin = Submodule.span 𝔽₂ {v})
    (hιtop : LinearMap.range ι.mulVecLin = ⊤) : hybridOrder Q ι = 1 := by
  have h1 : Module.finrank 𝔽₂ ↥(LinearMap.ker Q.mulVecLin) = 1 := by
    rw [hker]
    exact finrank_span_singleton hv
  have h2 : Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin) = m := by
    rw [hιtop, finrank_top, Module.finrank_pi]
    simp
  rw [hybridOrder, h1, h2, Nat.sub_self, add_zero]

/-- **The order-one case of Proposition 5.6** (arXiv:2209.04243): if `f` is `(d,ε)`-restriction
global then the influence of `f^{=d}` at an order-one pair `(V₁,W₁) = (span v, W)` is at most
`100·2^{4d}·ε`. -/
theorem inflBS2_nprojPure_le_of_order_one {m n m' n' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    {v : Fin n → 𝔽₂} (hv : v ≠ 0)
    (hker : LinearMap.ker Q.mulVecLin = Submodule.span 𝔽₂ {v})
    (hιtop : LinearMap.range ι.mulVecLin = ⊤)
    (d : ℕ) (hd : 1 ≤ d) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : GlobalBS d ε f) :
    inflBS2 Q ι T (nprojPure d f) ≤ 100 * (2:ℝ) ^ (4 * d) * ε := by
  rw [inflBS2, ← nprojPure_restr_shift_TOp Q ι hv hker hιtop d hd T f]
  refine le_trans (l2sq_nprojPure_le (d - 1) _) ?_
  exact l2sq_restr_shift_TOp_le Q ι v hv d T f hε h
    ((le_of_eq (hybridOrder_eq_one Q ι hv hker hιtop)).trans hd)

end

end Submission.Grassmann
