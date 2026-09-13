import Submission.Grassmann.ShiftAverage
import Submission.Grassmann.Concentration
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_pair_le_pow

/-!
# The pair-sum over subspaces `(V₁,W₁)` and the counting step of `cor:Corollary of hypercontractivity`

The hypercontractive inequality of arXiv:2209.04243 (`thm:Hypercontractivity in the Bilinear
scheme`, Theorem 1.5) bounds `‖f‖₄⁴` by `q^{100d²}` times the sum, over pairs of subspaces
`(V₁,W₁)` of order `dim V₁ + codim W₁ ≤ d`, of the averaged fourth power
`E_T ‖D_{V₁,W₁,T}[f]‖₂⁴` of the derivative.  Bounding each averaged fourth power by `ε` times
the averaged square (the small-influence hypothesis, `ShiftAverage.sum_sq_inflBS2_le_of_smallInfl`)
and using `E_T ‖D_{V₁,W₁,T}[f]‖₂² = ‖L_{V₁,W₁}[f]‖₂²` (`ShiftAverage.sum_inflBS2_eq`), the
right-hand side becomes `ε` times the *pair-sum of hybrid-Laplacian norms*

  `pairSum d f = Σ_{V₁ ≤ V} Σ_{W₁ ≤ W} [dim V₁ + codim W₁ ≤ d] · ‖L_{V₁,W₁}[f]‖₂²`,

which is what this file packages as `HypHyper`.

The paper's `cor:Corollary of hypercontractivity` then follows by a counting argument: expanding
`‖L_{V₁,W₁}[f]‖₂²` in the Fourier basis, the sum over pairs exchanges with the sum over
characters, and for a character `X` of rank `≤ d` the number of pairs `(V₁,W₁)` of order `≤ d`
with `V₁ ≤ Im X` and `ker X ≤ W₁` is at most `q^{10d²}` (the commons lemma
`Commons.LinearAlgebra.Submodule.card_submodule_pair_le_pow`).  This is `pairSum_le`.

* `hybridPredSub`/`Lsub` — the pair-indexed hybrid Laplacian, expressed by subspaces only;
* `hybridPred_eq_hybridPredSub` — the bridge to the matrix-based `hybridPred` of the paper's
  development (`V₁ = ker Q`, `W₁ = range ι`);
* `l2sq_Lsub_eq` — **Parseval for the pair Laplacian**:
  `‖L_{V₁,W₁}[f]‖₂² = Σ_{X : V₁ ≤ Im X, X⁻¹V₁ ≤ W₁} |f̂(X)|²`;
* `pairSum_le` — the counting bound `pairSum d f ≤ 2^{10d²} · ‖f‖₂²` for `DegLe d f`;
* `HypHyper` — Theorem 1.5 in the form used by the paper's corollary;
* `HypCor4_of_HypHyper` — the paper's `cor:Corollary of hypercontractivity`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## The pair-indexed hybrid Laplacian -/

/-- The Fourier-multiplier predicate of the hybrid Laplacian `L_{V₁,W₁}`, expressed purely in
terms of the two subspaces: keep the characters `u_X` with `Im X ⊇ V₁` and
`X⁻¹(V₁) ⊆ W₁`. -/
def hybridPredSub {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) : Prop :=
  V₁ ≤ LinearMap.range X.mulVecLin ∧ ∀ w : Fin m → 𝔽₂, X.mulVec w ∈ V₁ → w ∈ W₁

/-- The pair-indexed hybrid Laplacian `L_{V₁,W₁}`, as a Fourier multiplier on `L(V,W)`. -/
def Lsub {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ :=
  lapMulN (hybridPredSub V₁ W₁) f

/-- The predicate of the hybrid Laplacian only depends on the pair `(ker Q, range ι)`. -/
lemma hybridPred_eq_hybridPredSub {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) :
    hybridPred Q ι = hybridPredSub (LinearMap.ker Q.mulVecLin) (LinearMap.range ι.mulVecLin) :=
  rfl

/-- The matrix-based hybrid Laplacian is the pair Laplacian of `(ker Q, range ι)`. -/
lemma Lsub_ker_range {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Lsub (LinearMap.ker Q.mulVecLin) (LinearMap.range ι.mulVecLin) f =
      lapMulN (hybridPred Q ι) f := by
  rw [Lsub, hybridPred_eq_hybridPredSub]

/-! ## Parseval for the pair Laplacian -/

/-- **Parseval for the pair-indexed hybrid Laplacian**: the squared `L²` norm of `L_{V₁,W₁}[f]`
is the Fourier weight of `f` on the characters kept by the pair. -/
lemma l2sq_Lsub_eq {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (Lsub V₁ W₁ f) = ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
      if hybridPredSub V₁ W₁ X then ‖fcoeff f X‖ ^ 2 else 0 := by
  rw [← sum_normSq_fcoeff (Lsub V₁ W₁ f)]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Lsub, fcoeff_lapMulN]
  by_cases hX : hybridPredSub V₁ W₁ X
  · rw [if_pos hX, if_pos hX, one_mul]
  · rw [if_neg hX, if_neg hX, zero_mul, norm_zero]
    norm_num

/-! ## The pair sum -/

/-- The **pair sum** `Σ_{V₁,W₁ : dim V₁ + codim W₁ ≤ d} ‖L_{V₁,W₁}[f]‖₂²` appearing in the
paper's `cor:Corollary of hypercontractivity`. -/
def pairSum {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℝ :=
  ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
    if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d then l2sq (Lsub V₁ W₁ f) else 0

/-- For a fixed character `X`, the number of pairs of order `≤ d` keeping it. -/
def pairCount {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) : ℝ :=
  ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
    if hybridPredSub V₁ W₁ X ∧ Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
      then 1 else 0

/-- **The counting bound for a single character**: a character of rank at most `d` is kept by
at most `2^{10d²}` pairs of subspaces of order at most `d`. -/
lemma pairCount_le {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (hX : X.rank ≤ d) :
    pairCount d X ≤ (2 : ℝ) ^ (10 * d ^ 2) := by
  rw [pairCount]
  have hstrong : (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if hybridPredSub V₁ W₁ X ∧
            Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
          then (1 : ℝ) else 0))
      ≤ (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧
            Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
          then (1 : ℝ) else 0)) := by
    refine Finset.sum_le_sum fun V₁ _ => Finset.sum_le_sum fun W₁ _ => ?_
    by_cases h : hybridPredSub V₁ W₁ X ∧
        Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
    · obtain ⟨hpred, hord⟩ := h
      have hker : LinearMap.ker X.mulVecLin ≤ W₁ := by
        intro w hw
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
        exact hpred.2 w (by rw [hw]; exact V₁.zero_mem)
      rw [if_pos ⟨hpred, hord⟩, if_pos ⟨hpred.1, hker, hord⟩]
    · rw [if_neg h]; positivity
  refine hstrong.trans ?_
  have hprod : (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧
            Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
          then (1 : ℝ) else 0))
      = (∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if p.1 ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ p.2 ∧
            Module.finrank 𝔽₂ p.1 + (m - Module.finrank 𝔽₂ p.2) ≤ d
          then (1 : ℝ) else 0)) :=
    (Fintype.sum_prod_type (f := fun p : Submodule 𝔽₂ (Fin n → 𝔽₂) ×
        Submodule 𝔽₂ (Fin m → 𝔽₂) =>
        (if p.1 ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ p.2 ∧
            Module.finrank 𝔽₂ p.1 + (m - Module.finrank 𝔽₂ p.2) ≤ d
          then (1 : ℝ) else 0))).symm
  rw [hprod, Finset.sum_boole]
  have hcard : ((Finset.univ.filter (fun p : Submodule 𝔽₂ (Fin n → 𝔽₂) ×
      Submodule 𝔽₂ (Fin m → 𝔽₂) =>
      p.1 ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ p.2 ∧
        Module.finrank 𝔽₂ p.1 + (m - Module.finrank 𝔽₂ p.2) ≤ d)).card : ℝ)
      = (Nat.card {p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂) //
          p.1 ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ p.2 ∧
          Module.finrank 𝔽₂ p.1 + (m - Module.finrank 𝔽₂ p.2) ≤ d} : ℝ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  exact_mod_cast Commons.LinearAlgebra.Submodule.card_submodule_pair_le_pow n m d X hX

/-- **The pair sum in terms of the pair counts.** -/
lemma pairSum_eq {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    pairSum d f = ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖fcoeff f X‖ ^ 2 * pairCount d X := by
  simp only [pairSum, pairCount, l2sq_Lsub_eq]
  have hstep : ∀ (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)),
      (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
        then ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          (if hybridPredSub V₁ W₁ X then ‖fcoeff f X‖ ^ 2 else 0) else 0)
      = ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
            then (if hybridPredSub V₁ W₁ X then ‖fcoeff f X‖ ^ 2 else 0) else 0) := by
    intro V₁ W₁
    by_cases h : Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
    · rw [if_pos h]
      refine (Finset.sum_congr rfl fun X _ => by rw [if_pos h]).symm
    · rw [if_neg h]
      refine (Finset.sum_eq_zero fun X _ => by rw [if_neg h]).symm
  simp only [hstep]
  have hswap : (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
            then (if hybridPredSub V₁ W₁ X then ‖fcoeff f X‖ ^ 2 else 0) else 0))
      = ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
            then (if hybridPredSub V₁ W₁ X then ‖fcoeff f X‖ ^ 2 else 0) else 0) := by
    rw [← Fintype.sum_prod_type (f := fun p : Submodule 𝔽₂ (Fin n → 𝔽₂) ×
        Submodule 𝔽₂ (Fin m → 𝔽₂) =>
        ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          (if Module.finrank 𝔽₂ p.1 + (m - Module.finrank 𝔽₂ p.2) ≤ d
            then (if hybridPredSub p.1 p.2 X then ‖fcoeff f X‖ ^ 2 else 0) else 0))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun X _ => ?_
    exact Fintype.sum_prod_type (f := fun p : Submodule 𝔽₂ (Fin n → 𝔽₂) ×
      Submodule 𝔽₂ (Fin m → 𝔽₂) =>
      (if Module.finrank 𝔽₂ p.1 + (m - Module.finrank 𝔽₂ p.2) ≤ d
        then (if hybridPredSub p.1 p.2 X then ‖fcoeff f X‖ ^ 2 else 0) else 0))
  rw [hswap]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun V₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun W₁ _ => ?_
  by_cases h1 : Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
  · by_cases h2 : hybridPredSub V₁ W₁ X
    · rw [if_pos h1, if_pos h2, if_pos ⟨h2, h1⟩]; ring
    · rw [if_pos h1, if_neg h2, if_neg (fun hc => h2 hc.1)]; ring
  · rw [if_neg h1, if_neg (fun hc => h1 hc.2)]; ring

/-- **The counting step of `cor:Corollary of hypercontractivity`**: for a function of degree at
most `d`, the pair sum is at most `2^{10d²}` times its squared `L²` norm. -/
theorem pairSum_le {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) :
    pairSum d f ≤ (2 : ℝ) ^ (10 * d ^ 2) * l2sq f := by
  rw [pairSum_eq]
  have hterm : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂,
      ‖fcoeff f X‖ ^ 2 * pairCount d X ≤ ‖fcoeff f X‖ ^ 2 * (2 : ℝ) ^ (10 * d ^ 2) := by
    intro X
    by_cases hX : (fcoeff f X) = 0
    · rw [hX, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul, zero_mul]
    · have hrank : X.rank ≤ d := by
        by_contra h
        exact hX (by rw [fcoeff, hf X (by omega), mul_zero])
      exact mul_le_mul_of_nonneg_left (pairCount_le d X hrank) (by positivity)
  calc (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖fcoeff f X‖ ^ 2 * pairCount d X)
      ≤ ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          ‖fcoeff f X‖ ^ 2 * (2 : ℝ) ^ (10 * d ^ 2) := Finset.sum_le_sum fun X _ => hterm X
    _ = (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖fcoeff f X‖ ^ 2) * (2 : ℝ) ^ (10 * d ^ 2) := by
        rw [Finset.sum_mul]
    _ = l2sq f * (2 : ℝ) ^ (10 * d ^ 2) := by rw [sum_normSq_fcoeff]
    _ = (2 : ℝ) ^ (10 * d ^ 2) * l2sq f := by ring

end

end Submission.Grassmann
