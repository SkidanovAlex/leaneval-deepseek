import Submission.Grassmann.InductiveStep
import Submission.Grassmann.LemLv
import Submission.Grassmann.LemLvDual
import Submission.Grassmann.DerivativeComposition
import Submission.Grassmann.InfluenceBound

/-!
# Proposition 5.6 of arXiv:2209.04243: the inductive step, V-side

This file contains the first half of the induction proving that restriction-global functions
have small generalised influences (Proposition 5.6 of `An analogue of Bonami's Lemma for
functions on spaces of linear maps`).

The two ingredients are

* **`globalBS_restr_TOp`** — the *globalness transfer*: if `f` is `(d,ε)`-restriction global
  then `f' = (𝒯_{d,U}[f])_{(U,W)→0}` is `(d-1, O(q^{4d})ε)`-restriction global, where
  `U = span v ≤ ker Q₁`.  This is the analytic content of `lem:inductive step`.

* **`inflBS2_mul_reduction`** — the *reduction identity*: for a surjective `Q₁` with
  `ker Q₁ = span v`, the influence of `f^{=d}` at the pair `(Q₂Q₁, ι)` equals the influence of
  `(f')^{=d-1}` at the pair `(Q₂, ι)` (with zero shift), where `f'` is as above.

Together they let the induction on `d` proceed: an influence of order `d` at `(Q,ι)` is an
influence of order `d-1` at `(Q₂,ι)` of the smaller function `f'`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## Small technical lemmas -/

/-- Restricting by a composite is restricting twice. -/
lemma restr_mul_one {m n n₁ n₂ m' : ℕ} (Q₁ : Matrix (Fin n₁) (Fin n) 𝔽₂)
    (Q₂ : Matrix (Fin n₂) (Fin n₁) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    restr (Q₂ * Q₁) ι f = restr Q₂ ι (restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) f) := by
  rw [restr_restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) Q₂ ι f, Matrix.one_mul]

/-- The trivial shift. -/
lemma shift_zero_left {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    shift (0 : Matrix (Fin m) (Fin n) 𝔽₂) f = f := by
  funext A; simp [shift]

/-- The order of `Q` against the identity inclusion. -/
lemma hybridOrder_one {m n n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂) :
    hybridOrder Q (1 : Matrix (Fin m) (Fin m) 𝔽₂) =
      Module.finrank 𝔽₂ ↥(LinearMap.ker Q.mulVecLin) := by
  have htop : Module.finrank 𝔽₂
      ↥(LinearMap.range (1 : Matrix (Fin m) (Fin m) 𝔽₂).mulVecLin) = m := by
    rw [Matrix.mulVecLin_one, LinearMap.range_id, finrank_top, Module.finrank_pi]
    simp
  rw [hybridOrder, htop, Nat.sub_self, add_zero]

/-- **Additivity of the order under composition**, general inclusion. -/
lemma hybridOrder_mul {m n n₁ n₂ m₂ : ℕ} (Q₁ : Matrix (Fin n₁) (Fin n) 𝔽₂)
    (Q₂ : Matrix (Fin n₂) (Fin n₁) 𝔽₂) (ι : Matrix (Fin m) (Fin m₂) 𝔽₂)
    (hQ₁ : LinearMap.range Q₁.mulVecLin = ⊤) :
    hybridOrder (Q₂ * Q₁) ι =
      hybridOrder Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) + hybridOrder Q₂ ι := by
  have hker : Module.finrank 𝔽₂ ↥(LinearMap.ker (Q₂ * Q₁).mulVecLin) =
      Module.finrank 𝔽₂ ↥(LinearMap.ker Q₁.mulVecLin) +
        Module.finrank 𝔽₂ ↥(LinearMap.ker Q₂.mulVecLin) := by
    have hk : LinearMap.ker (Q₂ * Q₁).mulVecLin =
        Submodule.comap Q₁.mulVecLin (LinearMap.ker Q₂.mulVecLin) := by
      rw [Matrix.mulVecLin_mul, LinearMap.ker_comp]
    rw [hk, Commons.LinearAlgebra.finrank_comap_eq Q₁.mulVecLin (LinearMap.ker Q₂.mulVecLin)]
    have : LinearMap.ker Q₂.mulVecLin ⊓ LinearMap.range Q₁.mulVecLin =
        LinearMap.ker Q₂.mulVecLin := by
      rw [hQ₁, inf_top_eq]
    rw [this]
  have h1 : hybridOrder (Q₂ * Q₁) ι =
      Module.finrank 𝔽₂ ↥(LinearMap.ker (Q₂ * Q₁).mulVecLin) +
        (m - Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin)) := rfl
  have h2 : hybridOrder Q₂ ι =
      Module.finrank 𝔽₂ ↥(LinearMap.ker Q₂.mulVecLin) +
        (m - Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin)) := rfl
  rw [h1, h2, hybridOrder_one Q₁, hker]
  omega

/-! ## The globalness transfer (`lem:inductive step`, V-side) -/

/-- **`lem:inductive step` of arXiv:2209.04243, globalness part, V-side.**  If `f` is
`(d,ε)`-restriction global (`d ≥ 1`) and `ker Q₁ = span v` for a nonzero `v`, then the
function `(𝒯_{d,v}[f])_{(span v, W) → 0}` obtained by applying the order-one derivative
`D_{span v}` is `(d-1, 100·2^{4d}ε)`-restriction global. -/
theorem globalBS_restr_TOp {m n n'' d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    {ε : ℝ} (hε : 0 ≤ ε) (h : GlobalBS d ε f) (hd : 1 ≤ d)
    (Q₁ : Matrix (Fin n'') (Fin n) 𝔽₂) (v : Fin n → 𝔽₂) (hv : v ≠ 0)
    (hker : LinearMap.ker Q₁.mulVecLin = Submodule.span 𝔽₂ {v})
    (hrange : LinearMap.range Q₁.mulVecLin = ⊤)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) :
    GlobalBS (d - 1) (100 * (2:ℝ) ^ (4 * d) * ε)
      (restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) (shift T (TOp v d f))) := by
  intro m' n' Q₂ ι hord T''
  have h1 : restr Q₂ ι
        (shift T'' (restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) (shift T (TOp v d f)))) =
      restr (Q₂ * Q₁) ι (shift (T + T'' * Q₁) (TOp v d f)) := by
    rw [shift_restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) T'' (shift T (TOp v d f)),
      Matrix.one_mul, shift_shift, restr_restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) Q₂ ι,
      Matrix.one_mul]
  rw [h1]
  refine l2sq_restr_shift_TOp_le (Q₂ * Q₁) ι v hv d (T + T'' * Q₁) f hε h ?_
  rw [hybridOrder_mul Q₁ Q₂ ι hrange, hybridOrder_one Q₁, hker, finrank_span_singleton hv]
  omega

/-! ## The reduction identity (`lem:inductive step`, reduction part) -/

/-- **The order-`d` influence at `(Q₂Q₁, ι)` is the order-`(d-1)` influence of the smaller
function at `(Q₂, ι)`.**  This combines the composition identity
`restr_shift_lapMulN_mul` with `lem:lv` (`nprojPure_restr_shift_TOp`). -/
theorem inflBS2_mul_reduction {m n n' n'' m' : ℕ}
    (Q₁ : Matrix (Fin n'') (Fin n) 𝔽₂) (Q₂ : Matrix (Fin n') (Fin n'') 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) {v : Fin n → 𝔽₂} (hv : v ≠ 0)
    (hker : LinearMap.ker Q₁.mulVecLin = Submodule.span 𝔽₂ {v})
    (hrange : LinearMap.range Q₁.mulVecLin = ⊤)
    (d : ℕ) (hd : 1 ≤ d) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    inflBS2 (Q₂ * Q₁) ι T (nprojPure d g) =
      inflBS2 Q₂ ι 0 (nprojPure (d - 1)
        (restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) (shift T (TOp v d g)))) := by
  have htop : LinearMap.range (1 : Matrix (Fin m) (Fin m) 𝔽₂).mulVecLin = ⊤ := by
    rw [Matrix.mulVecLin_one, LinearMap.range_id]
  rw [inflBS2, restr_mul_one Q₁ Q₂ ι
    (shift T (lapMulN (hybridPred (Q₂ * Q₁) ι) (nprojPure d g)))]
  rw [restr_shift_lapMulN_mul Q₁ Q₂ ι hrange T (nprojPure d g)]
  rw [← nprojPure_restr_shift_TOp Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) hv hker htop d hd T g]
  rw [inflBS2, shift_zero_left]

end

end Submission.Grassmann