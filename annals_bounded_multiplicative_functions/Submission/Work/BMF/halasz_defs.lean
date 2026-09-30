import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the complex Halász theorem (`Work.BMF.halasz_complex`)

This file sets up the vocabulary used by the proof of

`|Σ_{n ≤ x} f n| ≤ C x ((1 + M) exp(-M) + 1/√T)`,  `M = min_{|t| ≤ 2T} 𝔻(f, n ↦ n^{it}; x)²`

for `f` multiplicative with `f 1 = 1` and `‖f n‖ ≤ 1`.

The route follows Ramaré's *effective* proof of Halász's theorem (Proposition `majm` of
"Moyennes effectives de fonctions multiplicatives complexes", arXiv:1709.01315), i.e. the
"Dirichlet series + Mellin–Plancherel + Gallagher" argument of Montgomery–Tenenbaum, specialised
to the case `r ≡ 1` (so `M(x;r) = ⌊x⌋`, `Z(x;r) = Σ_{p ≤ x} 1/p` and the trivial
Halberstam–Richert bound is replaced by `|g| ≤ 1`).
-/

namespace Work.BMF

open Finset Real Complex

/-- `vF f x s = Σ_{p ≤ x} f p * p^{-s}`: the "prime sum" appearing in the logarithm of the
truncated Euler product of `f`. -/
noncomputable def vF (f : ℕ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  ∑ p ∈ (⌊x⌋₊).primesLE, f p * (p : ℂ) ^ (-s)

/-- `Zrcp y = Σ_{p ≤ y} 1/p`. -/
noncomputable def Zrcp (y : ℝ) : ℝ := ∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / p

/-- `mHalSum f x t = Σ_{p ≤ x} (1 - Re (f p * p^{-it}))/p`. -/
noncomputable def mHalSum (f : ℕ → ℂ) (x t : ℝ) : ℝ :=
  ∑ p ∈ (⌊x⌋₊).primesLE, (1 - (f p * (p : ℂ) ^ (-(Complex.I * t))).re) / p

/-- `mHal f x T = min_{|t| ≤ T} Σ_{p ≤ x} (1 - Re (f p * p^{-it}))/p`
(the pretentious distance of `f` to `n^it`, minimised over the window `|t| ≤ T`). -/
noncomputable def mHal (f : ℕ → ℂ) (x T : ℝ) : ℝ :=
  ⨅ (t : {t : ℝ // |t| ≤ T}), mHalSum f x t.1

/-- `Wsup f x α T = sup_{|t| ≤ T} Re Σ_{p ≤ x} f p * p^{-1-α-it}`. -/
noncomputable def Wsup (f : ℕ → ℂ) (x α T : ℝ) : ℝ :=
  ⨆ (t : {t : ℝ // |t| ≤ T}), (vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re

/-- `Kf f x = Σ_{n ≤ x} f n * log n`. -/
noncomputable def Kf (f : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * (Real.log n : ℂ)

/-- `Mf f x = Σ_{n ≤ x} f n`. -/
noncomputable def Mf (f : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n

/-- The Dirichlet series with coefficients `f n * log n`, i.e. `-G'(s)` where `G = LSeries f`. -/
noncomputable def Kser (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (f n * (Real.log n : ℂ)) * (n : ℂ) ^ (-s)

end Work.BMF
