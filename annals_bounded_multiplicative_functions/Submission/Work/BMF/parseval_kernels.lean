import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Kernel vocabulary for the short-interval Parseval bound (`parseval_short`)

This file sets up the objects used in the proof of `Work.BMF.parseval_short`, the
Matomäki–Radziwiłł (Annals 2016, Lemma `lem:shortintsumtoDirpols`) "Parseval bound"
for short interval sums of a bounded sequence, in the two-sided (complex-coefficient)
form required here.

We write

* `dirPoly a X t = ∑_{n ∈ [X,4X]} a n · n^{-(1+it)}`, the Dirichlet polynomial
  `A(1+it)` of the paper;
* `winKern h x t = ((x+h)^{1+it} - x^{1+it})/(h(1+it)) = h^{-1}∫_x^{x+h} u^{it}du`,
  the normalised window kernel, so that `Perron` gives
  `(1/h) ∑_{x≤n≤x+h} a n ≈ (1/2π)∫ A(1+it) winKern h x t dt`;
* `Theta δ t = ((1+δ)^{1+it}-1)/(δ(1+it)) = δ^{-1}∫_0^δ (1+u)^{it}du`, the
  "average" kernel, so that `winKern h x t = x^{it} Θ(h/x) t`;
* `Delta h₁ h₂ x t = Θ(h₁/x) t - Θ(h₂/x) t`, the difference kernel, whose smallness
  (the cancellation of the low-frequency main terms) is the content of the Parseval bound.
-/

namespace Work.BMF

open scoped BigOperators
open Polynomial Finset Real Complex

/-- The Dirichlet polynomial `A(1+it) = ∑_{n ∈ [X,4X]} a n · n^{-(1+it)}` on the line `Re s = 1`. -/
noncomputable def dirPoly (a : ℕ → ℂ) (X t : ℝ) : ℂ :=
  ∑ n ∈ natIcc X (4 * X), a n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))

/-- The normalised window kernel `h^{-1}∫_x^{x+h} u^{it} du
= ((x+h)^{1+it} - x^{1+it}) / (h (1+it))`. -/
noncomputable def winKern (h x t : ℝ) : ℂ :=
  (((x + h : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ))
      - ((x : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ))) / ((h : ℂ) * (1 + Complex.I * (t : ℂ)))

/-- The average kernel `Θ(δ,t) = ((1+δ)^{1+it}-1)/(δ(1+it)) = δ^{-1}∫_0^δ (1+u)^{it}du`. -/
noncomputable def Theta (δ t : ℝ) : ℂ :=
  (((1 + δ : ℝ) : ℂ) ^ (1 + Complex.I * (t : ℂ)) - 1)
    / ((δ : ℂ) * (1 + Complex.I * (t : ℂ)))

/-- The difference kernel `Δ(x,t) = Θ(h₁/x,t) - Θ(h₂/x,t)`. -/
noncomputable def Delta (h₁ h₂ x t : ℝ) : ℂ := Theta (h₁ / x) t - Theta (h₂ / x) t

end Work.BMF
