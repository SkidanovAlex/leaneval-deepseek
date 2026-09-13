import Mathlib
import Submission.Grassmann.Restriction
import Submission.Grassmann.Laplacian
import Submission.Grassmann.HybridLaplacian
import Submission.Grassmann.BilinearDegree
import Submission.Grassmann.LevelDecomp
import Submission.Grassmann.Dictator

/-!
# Restrictions, influences and the conditional hypercontractivity statement on `L(V,W)`

This file sets up the objects of Section 3/7 of arXiv:2209.04243 for the bilinear scheme
`L(V,W)` (encoded as `m × n` matrices over `𝔽₂`, so that functions live on
`Matrix (Fin m) (Fin n) 𝔽₂`):

* `l2sq f`, `l4q f` — the normalised `‖f‖₂²` and `‖f‖₄⁴`;
* `restrictBS Q ι T f = f_{(V₁,W₁) → T}` — the `d`-restriction of the paper, where
  `V₁ = ker Q` and `W₁ = range ι` (`(d,ε)`-restriction globalness);
* `inflBS Q ι T f` — the generalised influence `‖D_{V₁,W₁,T}[f]‖₄⁴`, where the derivative
  `D_{V₁,W₁,T}` is the restriction of the hybrid Laplacian `L_{V₁,W₁}` shifted by `T`;
* `GlobalBS d ε f` — `(d,ε)`-restriction globalness;
* `truncBS d f` — the degree-`d` truncation `f^{≤ d}`;
* `HypBSglob` — **Theorem 1.5 / Corollary 1.4** in the form "global functions satisfy a
  conditional hypercontractive inequality", stated as a `Prop` (the deep part of the paper).
-/

open Classical Finset BigOperators
open scoped Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- The normalised squared `L²` norm `‖f‖₂² = 2^{-mn} Σ_A ‖f A‖²`. -/
def l2sq (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℝ :=
  ((2 : ℝ) ^ (m * n))⁻¹ * ∑ A, ‖f A‖ ^ 2

/-- The normalised `‖f‖₄⁴ = 2^{-mn} Σ_A ‖f A‖⁴`. -/
def l4q (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℝ :=
  ((2 : ℝ) ^ (m * n))⁻¹ * ∑ A, ‖f A‖ ^ 4

lemma l2sq_nonneg (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : 0 ≤ l2sq f :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

lemma l4q_nonneg (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : 0 ≤ l4q f :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

/-- The `d`-restriction `f_{(V₁,W₁) → T}` of the paper, encoded with `V₁ = ker Q`,
`W₁ = range ι`: it is `A ↦ f(ι A Q + T)`. -/
def restrictBS {m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : Matrix (Fin m') (Fin n') 𝔽₂ → ℂ :=
  restr Q ι (shift T f)

lemma restrictBS_apply {m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (A : Matrix (Fin m') (Fin n') 𝔽₂) :
    restrictBS Q ι T f A = f (ι * A * Q + T) := rfl

/-- `(d, ε)`-**restriction globalness**: every `d`-restriction has squared `L²` norm `≤ ε`. -/
def GlobalBS (d : ℕ) (ε : ℝ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : Prop :=
  ∀ {m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂),
    hybridOrder Q ι ≤ d → ∀ T : Matrix (Fin m) (Fin n) 𝔽₂,
      l2sq (restr Q ι (shift T f)) ≤ ε

/-- The generalised influence `‖D_{V₁,W₁,T}[f]‖₄⁴` of the pair `(V₁,W₁) = (ker Q, range ι)`
and the shift `T`: the fourth power of the norm of the restricted, shifted derivative
`(Δ_T ∘ L_{V₁,W₁})` of `f`. -/
def inflBS {m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℝ :=
  l4q (restr Q ι (shift T (lapMulN (hybridPred Q ι) f)))

/-- The degree-`d` truncation `f^{≤ d}` of a function on `L(V,W)`: keep the characters of
rank at most `d`. -/
def truncBS (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin m) (Fin n) 𝔽₂ → ℂ :=
  lapMulN (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => X.rank ≤ d) f

lemma truncBS_degLe (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DegLe d (truncBS d f) := by
  intro X hX
  rw [truncBS, fhat_lapMulN]
  rw [if_neg (by omega), zero_mul]

/-- **`cor:atmostd` of arXiv:2209.04243** (the Bonami-type lemma for global *Boolean* functions
on `L(V,W)`): a Boolean `(d,ε)`-restriction global function satisfies
`‖f^{≤d}‖₄⁴ ≤ q^{Cd²} ε ‖f^{≤d}‖₂²`.

Note (compared with `HypCor4`) that the Boolean hypothesis is *essential*: for a general
complex-valued `f` the statement is false (take `f` a spike of height `h`; `GlobalBS d ε f`
only forces `‖f‖₂² ≤ ε`, so `‖f‖₄⁴/‖f‖₂² = h²` can exceed `q^{Cd²}ε`), and it is also essential
that `ε` is a free parameter: writing `ε = q^{-Cd²}` would collapse the right-hand side to
`‖f^{≤d}‖₂²`, which is already false for a constant spike of height in `(1, 2^{mn/2})`. -/
def HypBSglob : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ) (d : ℕ)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (ε : ℝ),
    0 ≤ ε → (∀ A, f A = 0 ∨ f A = 1) → GlobalBS d ε f →
      l4q (truncBS d f) ≤ (2 : ℝ) ^ (C * d ^ 2) * ε * l2sq (truncBS d f)

/-- **Theorem 1.6 of arXiv:2209.04243** (small-set expansion for the shortcode graph), stated as
a hypothesis: a restriction-global family `S` of linear maps has almost no `rank`-one neighbour
inside itself.  The probability is the ratio of the number of pairs `(A,B)` with `A ∈ S`,
`rank B = 1`, `A + B ∈ S` to `#S · #{B : rank B = 1}`.

The hypothesis `1 ≤ r` is necessary: for `r = 0` the hypothesis is `(1,1)`-globalness, which
holds for every indicator, while `S` = everything has ratio `1` (see `ROADMAP.md`). -/
def HypSSE : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (m n : ℕ) (r : ℕ), 1 ≤ r →
    ∀ S : Finset (Matrix (Fin m) (Fin n) 𝔽₂),
    GlobalBS (r + 1) ((2 : ℝ) ^ (-(C₀ * r ^ 2))) (fun A => if A ∈ S then 1 else 0) →
      (∑ A ∈ S, ∑ B : Matrix (Fin m) (Fin n) 𝔽₂,
          if B.rank = 1 then (if A + B ∈ S then (1 : ℝ) else 0) else 0) /
        ((S.card : ℝ) * (∑ B : Matrix (Fin m) (Fin n) 𝔽₂,
          if B.rank = 1 then (1 : ℝ) else 0)) < ((2 : ℝ) ^ r)⁻¹

end

end Submission.Grassmann
