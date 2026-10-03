/-
# Kernel form of the halved averages and of the §6 model operators

This module fixes the *concrete* vocabulary in which the §6 model-operator approximation
(Proposition `mod-approx` of Krause--Mirek--Tao) and the §7 small-scale estimate are stated:

* `convOp κ u` — the linear convolution operator with kernel `κ` on `ℤ`; for
  `κ = iwKer ρ l Φ` this is the Ionescu--Wainger multiplier `T^l_Φ` in the form `iwConv`;
* `bilinOp K u v` — the **bilinear convolution operator** with kernel `K : ℤ → ℤ → ℂ`.  Every
  bilinear Fourier multiplier whose symbol is a bounded measure is of this form, and the two
  objects of §6 are:
  - `khalf m P`, the kernel of the halved average `Ã_m(u,v)(x) = m⁻¹ ∑_{m/2 < n ≤ m} u(x-n)v(x-P(n))`
    (finite support, so `bilinOp (khalf m P) u v = Ã_m(u,v)` *exactly*: `bilinOp_khalf`);
  - `kres q P`, the kernel of the arithmetic (residue) average
    `E_{z ∈ ℤ/q} u(x-z)v(x-P(z))`, which is the "form-1" factorisation of the twisted bilinear
    multiplier `B^{l₁,l₂,m_ℤ̂}_{m_*}` of §6;
* `kernComp K κ κ'` — the kernel of the composition of a bilinear operator with two linear
  convolution operators, i.e. the carrier of the §6 functional calculus
  `B_{M·(ψ₁⊗ψ₂)}(u,v) = B_M(T_{ψ₁}u, T_{ψ₂}v)`;
* `iwKer ρ l Φ`, `Tmult ρ l Φ` — the IW multiplier kernel and operator.

The point of the kernel formulation is that *all* the analytic inputs become `ℓ¹`-estimates on
kernels: by `eLpNorm_bilinOp_le` the `ℓ^p` operator norm of `bilinOp K` is bounded by the `ℓ¹(ℤ²)`
norm of `K`, so the §6 approximation `Ã_N ≈ B_{m_*m_ℤ̂}` and the §7 single-scale estimate are both
reduced to estimates on explicit kernels (no measure theory on the frequency torus is needed).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Split

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier

/-- The linear convolution operator with kernel `κ` on `ℤ`: `(κ * u)(x) = ∑'_j κ j * u (x - j)`. -/
noncomputable def convOp (κ : ℤ → ℂ) (u : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑' j : ℤ, κ j * u (x - j)

/-- The bilinear convolution operator with kernel `K : ℤ → ℤ → ℂ`:
`bilinOp K u v x = ∑'_a ∑'_b K a b * u (x - a) * v (x - b)`. -/
noncomputable def bilinOp (K : ℤ → ℤ → ℂ) (u v : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑' a : ℤ, ∑' b : ℤ, K a b * u (x - a) * v (x - b)

/-- The kernel of the halved average: `khalf m P a b = m⁻¹` when `m/2 < a ≤ m` and `b = P(a)`,
and `0` otherwise.  With it, `bilinOp (khalf m P) u v = Ã_m(u,v)`. -/
noncomputable def khalf (m : ℕ) (P : ℤ[X]) : ℤ → ℤ → ℂ :=
  fun a b => if (m / 2 : ℤ) < a ∧ a ≤ (m : ℤ) ∧ b = P.eval a then ((m : ℂ))⁻¹ else 0

/-- The kernel of the arithmetic (residue) average over `ℤ/q`:
`kres q P a b = q⁻¹` when `0 ≤ a < q` and `b = P(a)`, and `0` otherwise.  With it,
`bilinOp (kres q P) u v x = q⁻¹ ∑_{z < q} u (x - z) v (x - P(z))`. -/
noncomputable def kres (q : ℕ) (P : ℤ[X]) : ℤ → ℤ → ℂ :=
  fun a b => if 0 ≤ a ∧ a < (q : ℤ) ∧ b = P.eval a then ((q : ℂ))⁻¹ else 0

/-- The kernel of the Ionescu--Wainger multiplier `T^l_Φ = Π_{≤l,≤·}` with symbol
`iwSymbolSet (iwArithFreqs ρ l) Φ`: the Fourier coefficients of that symbol. -/
noncomputable def iwKer (ρ : ℝ) (l : ℕ) (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) : ℤ → ℂ :=
  iwKernel (iwSymbolSet (iwArithFreqs ρ l) Φ)

/-- The Ionescu--Wainger multiplier `T^l_Φ` as a convolution operator. -/
noncomputable def Tmult (ρ : ℝ) (l : ℕ) (Φ : Work.Analysis.IonescuWainger.Circle → ℂ)
    (u : ℤ → ℂ) : ℤ → ℂ :=
  convOp (iwKer ρ l Φ) u

/-- The kernel of the composition of a bilinear operator (kernel `K`) with two linear
convolution operators (kernels `κ`, `κ'`): the carrier of the §6 functional calculus
`B_{M·(ψ₁⊗ψ₂)}(u,v) = B_M(T_{ψ₁}u, T_{ψ₂}v)`. -/
noncomputable def kernComp (K : ℤ → ℤ → ℂ) (κ κ' : ℤ → ℂ) : ℤ → ℤ → ℂ :=
  fun a b => ∑' a' : ℤ, ∑' b' : ℤ, K (a - a') (b - b') * κ a' * κ' b'

/-- The `ℓ¹(ℤ²)` mass of a bilinear kernel. -/
noncomputable def kernMass (K : ℤ → ℤ → ℂ) : ℝ≥0∞ :=
  ∑' p : ℤ × ℤ, ‖K p.1 p.2‖ₑ

/-- The arithmetic frequency set of the *exact-height* projection `Π_{l,≤·} = Π_{≤l,≤·} - Π_{≤l-1,≤·}`:
`A_l \ A_{l-1}` (with `A_0` itself for `l = 0`). -/
noncomputable def diffFreqs (ρ : ℝ) (l : ℕ) : Finset Work.Analysis.IonescuWainger.Circle :=
  if l = 0 then iwArithFreqs ρ 0 else iwArithFreqs ρ l \ iwArithFreqs ρ (l - 1)

/-- **The multiplier family of the §5 pieces**, linear in its symbol: applied to the *fixed*
function `u = f`, the exact-height multiplier with symbol `φ`,
`Tm ρ l φ u = iwConv (A_l \ A_{l-1}) (periodize φ) u`.
This is the family to which the Rademacher--Menshov reduction
(`Work.Analysis.Paraproduct.SmallScale.smallScale_variational_le_Vr`) is applied: the tuple of
pieces is `k ↦ Tm ρ l (pieceSym s N_k) f`, and the randomised combination is
`Tm ρ l (∑_k ε_k (pieceSym s N_{k+1} - pieceSym s N_k)) f` because `Tm` is linear in the symbol. -/
noncomputable def Tm (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (u : ℤ → ℂ) : ℤ → ℂ :=
  iwConv (diffFreqs ρ l) (periodize φ) u

/-- The symbol of the piece `Fpiece (kmtPj ρ) 0 l s N`: the annulus bump at height `s - logN N`
for `s ≠ 0`, and the single bump at height `- logN N` for `s = 0` (the "low" piece). -/
noncomputable def pieceSymF (s N : ℕ) : ℝ → ℂ :=
  fun ξ => if s = 0 then etaCut Work.KMTContract.kmtEta (-(Work.Analysis.EndVar.logN N)) ξ
    else etaCut Work.KMTContract.kmtEta (-(Work.Analysis.EndVar.logN N) + (s : ℤ)) ξ
      - etaCut Work.KMTContract.kmtEta (-(Work.Analysis.EndVar.logN N) + (s : ℤ) - 1) ξ

/-- The symbol of the piece `Gpiece (kmtPj ρ) d 0 l s N`: the annulus bump at height
`d (s - logN N)` for `s ≠ 0`, and the single bump at height `- d logN N` for `s = 0`. -/
noncomputable def pieceSymG (d : ℤ) (s N : ℕ) : ℝ → ℂ :=
  fun ξ => if s = 0 then etaCut Work.KMTContract.kmtEta (-(d * Work.Analysis.EndVar.logN N)) ξ
    else etaCut Work.KMTContract.kmtEta (d * (-(Work.Analysis.EndVar.logN N) + (s : ℤ))) ξ
      - etaCut Work.KMTContract.kmtEta (d * (-(Work.Analysis.EndVar.logN N) + (s : ℤ) - 1)) ξ

end

end Work.KMTAreas.A7
