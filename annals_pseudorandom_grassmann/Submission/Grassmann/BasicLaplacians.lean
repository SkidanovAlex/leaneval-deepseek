import Submission.Grassmann.PairSum
import Submission.Grassmann.Convolution

/-!
# The basic (non-hybrid) Laplacians `L_{V₁}` and `L_{W₁}`

Besides the hybrid Laplacians `L_{V₁,W₁}` (`hybridPred`/`Lsub`), arXiv:2209.04243 §3.8 defines
the two "basic" Laplacians

  `L_{V₁}[f] = Σ_{X : Im X ⊇ V₁} f̂(X) u_X`,   `L_{W₁}[f] = Σ_{X : ker X ⊆ W₁} f̂(X) u_X`.

Their composition `L_{V₁} ∘ L_{W₁}` is what appears in the Fourier expansion of `f²` in §4
(`lem:hyp inductive step`), and the *hybrid* Laplacian is precisely the additional cut
`X⁻¹(V₁) ⊆ W₁` that makes the derivative reduce the degree:

  `L_{V₁,W₁} = L_{V₁}∘L_{W₁} · 1[X⁻¹(V₁) ⊆ W₁]`.

This file records the two basic Laplacians, their Fourier multipliers and the containment
`L_{V₁,W₁} ≤ L_{V₁}∘L_{W₁}`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- The basic `V`-Laplacian `L_{V₁}`: keep the characters `u_X` with `Im X ⊇ V₁`. -/
def Lup {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ :=
  lapMulN (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => V₁ ≤ LinearMap.range X.mulVecLin) f

/-- The basic `W`-Laplacian `L_{W₁}`: keep the characters `u_X` with `ker X ⊆ W₁`. -/
def Ldown {m n : ℕ} (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ :=
  lapMulN (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => LinearMap.ker X.mulVecLin ≤ W₁) f

/-- The Fourier coefficients of `L_{V₁}`. -/
lemma fcoeff_Lup {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (Lup V₁ f) X =
      (if V₁ ≤ LinearMap.range X.mulVecLin then 1 else 0) * fcoeff f X :=
  fcoeff_lapMulN _ f X

/-- The Fourier coefficients of `L_{W₁}`. -/
lemma fcoeff_Ldown {m n : ℕ} (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (Ldown W₁ f) X =
      (if LinearMap.ker X.mulVecLin ≤ W₁ then 1 else 0) * fcoeff f X :=
  fcoeff_lapMulN _ f X

/-- The Fourier coefficients of the composition `L_{V₁} ∘ L_{W₁}`. -/
lemma fcoeff_Lup_Ldown {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (Lup V₁ (Ldown W₁ f)) X =
      (if V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ then 1 else 0) *
        fcoeff f X := by
  rw [fcoeff_Lup, fcoeff_Ldown]
  by_cases h : V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁
  · rw [if_pos h, if_pos h.1, if_pos h.2]; ring
  · rw [if_neg h]
    by_cases h1 : V₁ ≤ LinearMap.range X.mulVecLin
    · rw [if_pos h1, if_neg (fun hc => h ⟨h1, hc⟩)]; ring
    · rw [if_neg h1]; ring

/-- The hybrid Laplacian is obtained from `L_{V₁} ∘ L_{W₁}` by the extra cut
`X⁻¹(V₁) ⊆ W₁`; in particular `hybridPredSub` implies the conditions of the composition. -/
lemma hybridPredSub_imp_Lup_Ldown {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (h : hybridPredSub V₁ W₁ X) :
    V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ :=
  ⟨h.1, fun w hw => h.2 w (by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    rw [hw]
    exact V₁.zero_mem)⟩

/-- **The Fourier coefficients of `(L_{V₁} ∘ L_{W₁}[f])²`**: the coefficient of `X` receives the
contribution of the pair `(Y, X + Y)` exactly when `V₁ ⊆ Im Y ∩ Im(X+Y)` and
`ker Y, ker(X+Y) ⊆ W₁` — the characterisation used in the F₂ analysis
(`|Σ_{(Y,Z) ∈ 𝓕₂(X)} f̂(Y)f̂(Z)|` is bounded by the coefficients of the composed Laplacian). -/
theorem fhat_sq_Lup_Ldown {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fhat (fun A => Lup V₁ (Ldown W₁ f) A * Lup V₁ (Ldown W₁ f) A) X =
      ((2 : ℂ) ^ (m * n))⁻¹ *
        ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
          ((if V₁ ≤ LinearMap.range Y.mulVecLin then (1 : ℂ) else 0) *
            ((if LinearMap.ker Y.mulVecLin ≤ W₁ then (1 : ℂ) else 0) * fhat f Y)) *
          ((if V₁ ≤ LinearMap.range (X + Y).mulVecLin then (1 : ℂ) else 0) *
            ((if LinearMap.ker (X + Y).mulVecLin ≤ W₁ then (1 : ℂ) else 0) *
              fhat f (X + Y))) := by
  rw [fhat_mul_fun]
  congr 1
  refine Finset.sum_congr rfl fun Y _ => ?_
  simp only [Lup, Ldown, fhat_lapMulN]

end

end Submission.Grassmann
