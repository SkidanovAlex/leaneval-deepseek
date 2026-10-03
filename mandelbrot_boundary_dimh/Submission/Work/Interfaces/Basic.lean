import Mathlib
import ChallengeDeps

/-!
# mandelbrot_boundary_dimh — lead interfaces (parabolic-independent layer)

Written by the lead. Definitions and `Prop`s only. Every area proves ONE of the `...Statement`
props below (possibly assuming others as hypotheses); `Submission/Work/Wiring.lean` composes them
into `dimH (frontier Mandelbrot) = 2`.

Route (Shishikura 1998, specialised to the cusp c = 1/4, see NOTES_LEAD_blueprint.md):
* `DynStatement`  (parabolic core = Theorem 2 for `x ↦ e^{2πiα} x + x²`): for α = 1/(a₁ − 1/(a₂+β))
  the polynomial `Tc (cOfAlpha α)` carries a conformal IFS (`HypIFS`) with log N / log K ≥ 2 − ε.
* `ParamStatement`: real α ∈ (0,1) gives a point `cOfAlpha α` of the main-cardioid boundary, in ∂M.
* `DimStatement`: dimension of a conformal IFS limit set ≥ log N / log K (mass distribution + Koebe).
* `MotionStatement`: the IFS of `Tc c₀` moves holomorphically for c near c₀, Lipschitz in c,
  bi-Hölder with exponent → 1 (replaces λ-lemma + QC + Mori).
* `TransferStatement`: c₀ ∈ ∂M with an IFS ⇒ dimH ∂M ≥ a · log N / log K for every a < 1
  (Montel + max-modulus/Rouché + Hölder; replaces MSS Lemma III.2 and Shishikura Lemma 3.2).
* `MsetStatement`: basic facts about M (closed, ⊆ closedBall 0 2, escape, dimH ∂M ≤ 2).
-/

open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Topology

noncomputable section

namespace MandelDim

/-! ## Basic facts about the Mandelbrot set -/

/-- MSET area. -/
def MsetStatement : Prop :=
  IsClosed Mandelbrot ∧ Mandelbrot ⊆ closedBall (0 : ℂ) 2 ∧
  (∀ c ∈ Mandelbrot, ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ 2) ∧
  (∀ c ∉ Mandelbrot, Tendsto (fun n : ℕ => ‖(Tc c)^[n] 0‖) atTop atTop) ∧
  dimH (frontier Mandelbrot) ≤ 2

/-! ## Conformal iterated function systems -/

/-- Composition along a word: `ifsComp τ [i₁, …, iₖ] = τ i₁ ∘ ⋯ ∘ τ iₖ` (`[]` gives `id`). -/
def ifsComp {N : ℕ} (τ : Fin N → ℂ → ℂ) : List (Fin N) → ℂ → ℂ
  | [] => id
  | i :: l => τ i ∘ ifsComp τ l

/-- A univalent conformal IFS on the disc `ball p r`: `N` holomorphic injective branches mapping
`ball p r` into `ball p (r/2)`, with pairwise disjoint images, and derivative modulus at least
`K⁻¹` on `ball p (r/2)` (i.e. the expanding inverse maps have derivative at most `K` there). -/
def IsConformalIFS (N : ℕ) (τ : Fin N → ℂ → ℂ) (p : ℂ) (r K : ℝ) : Prop :=
  0 < r ∧ 1 < K ∧
  (∀ i, DifferentiableOn ℂ (τ i) (ball p r)) ∧
  (∀ i, InjOn (τ i) (ball p r)) ∧
  (∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) ∧
  (Pairwise fun i j => Disjoint (τ i '' ball p r) (τ j '' ball p r)) ∧
  (∀ i, ∀ z ∈ ball p (r / 2), K⁻¹ ≤ ‖deriv (τ i) z‖)

/-- The coding map: `codingPt τ p ω = lim_k (τ (ω 0) ∘ ⋯ ∘ τ (ω (k-1))) p`. -/
def codingPt {N : ℕ} (τ : Fin N → ℂ → ℂ) (p : ℂ) (ω : ℕ → Fin N) : ℂ :=
  limUnder atTop (fun k : ℕ => ifsComp τ ((List.range k).map ω) p)

/-- The cylinder of infinite words beginning with the finite word `l`. -/
def cylinder {N : ℕ} (l : List (Fin N)) : Set (ℕ → Fin N) :=
  {ω | ∀ k (h : k < l.length), ω k = l.get ⟨k, h⟩}

/-- The IFS consists of inverse branches of iterates of `Tc c`. -/
def IsDynIFS (c : ℂ) {N : ℕ} (τ : Fin N → ℂ → ℂ) (n : Fin N → ℕ) (p : ℂ) (r : ℝ) : Prop :=
  ∀ i, 1 ≤ n i ∧ ∀ z ∈ ball p r, (Tc c)^[n i] (τ i z) = z

/-- `Tc c` has a conformal IFS of inverse branches with `N` branches and expansion ≤ `K`. -/
def HypIFS (c : ℂ) (N : ℕ) (K : ℝ) : Prop :=
  ∃ (τ : Fin N → ℂ → ℂ) (n : Fin N → ℕ) (p : ℂ) (r : ℝ),
    IsConformalIFS N τ p r K ∧ IsDynIFS c τ n p r

/-- DIM area: dimension lower bound for every cylinder piece of the limit set. -/
def DimStatement : Prop :=
  ∀ (N : ℕ) (τ : Fin N → ℂ → ℂ) (p : ℂ) (r K : ℝ), 2 ≤ N → IsConformalIFS N τ p r K →
    ∀ l : List (Fin N),
      ENNReal.ofReal (Real.log N / Real.log K) ≤ dimH (codingPt τ p '' cylinder l)

/-- MOTION area: holomorphic motion of the coding map of a dynamical IFS of `Tc c₀`, for `c`
near `c₀`: holomorphic and Lipschitz in `c`, injective, equivariant, with bounded forward orbits,
uniformly contracting in the code (words sharing `k` letters are `C θ^k`-close), and `a`-Hölder
between any two parameters of the disc (for a given `a < 1`). -/
def MotionStatement : Prop :=
  ∀ (c₀ : ℂ) (N : ℕ) (τ : Fin N → ℂ → ℂ) (n : Fin N → ℕ) (p : ℂ) (r K : ℝ),
    2 ≤ N → IsConformalIFS N τ p r K → IsDynIFS c₀ τ n p r →
    ∀ a : ℝ, a < 1 → ∃ ρ : ℝ, 0 < ρ ∧ ∃ π : ℂ → (ℕ → Fin N) → ℂ,
      (∀ ω, π c₀ ω = codingPt τ p ω) ∧
      (∀ ω, DifferentiableOn ℂ (fun c => π c ω) (ball c₀ ρ)) ∧
      (∀ c ∈ ball c₀ ρ, Function.Injective (π c)) ∧
      (∀ c ∈ ball c₀ ρ, ∀ ω, (Tc c)^[n (ω 0)] (π c ω) = π c (fun k => ω (k + 1))) ∧
      (∃ B : ℝ, ∀ c ∈ ball c₀ ρ, ∀ ω, ∀ j : ℕ, ‖(Tc c)^[j] (π c ω)‖ ≤ B) ∧
      (∃ C θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ c ∈ ball c₀ ρ, ∀ k : ℕ, ∀ ω ω' : ℕ → Fin N,
        (∀ j < k, ω j = ω' j) → ‖π c ω - π c ω'‖ ≤ C * θ ^ k) ∧
      (∃ L : ℝ, ∀ c ∈ ball c₀ ρ, ∀ c' ∈ ball c₀ ρ, ∀ ω, ‖π c ω - π c' ω‖ ≤ L * ‖c - c'‖) ∧
      (∃ C : ℝ, ∀ c ∈ ball c₀ ρ, ∀ c' ∈ ball c₀ ρ, ∀ ω ω',
        ‖π c ω - π c ω'‖ ≤ C * ‖π c' ω - π c' ω'‖ ^ a)

/-- TRANSFER area: from a dynamical IFS at a boundary parameter to the dimension of `∂M`. -/
def TransferStatement : Prop :=
  ∀ c₀ ∈ frontier Mandelbrot, ∀ (N : ℕ) (K : ℝ), 2 ≤ N → HypIFS c₀ N K →
    ∀ a : ℝ, 0 < a → a < 1 →
      ENNReal.ofReal (a * (Real.log N / Real.log K)) ≤ dimH (frontier Mandelbrot)

/-! ## Parameters near the cusp -/

/-- The parameter whose fixed point `e^{2πiα}/2` has multiplier `e^{2πiα}`:
`Tc (cOfAlpha α)` is affinely conjugate (by `z = x + e^{2πiα}/2`) to `x ↦ e^{2πiα} x + x²`. -/
def cOfAlpha (α : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * α) / 2 - Complex.exp (4 * Real.pi * Complex.I * α) / 4

/-- PARAM area: the main-cardioid boundary (real rotation number in (0,1)) lies in `∂M`. -/
def ParamStatement : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → cOfAlpha α ∈ frontier Mandelbrot

/-- The secondary-bifurcation rotation number `1 / (a₁ - 1 / (a₂ + β))` of Shishikura's Theorem 2. -/
def alphaOf (a₁ a₂ : ℕ) (β : ℂ) : ℂ := 1 / ((a₁ : ℂ) - 1 / ((a₂ : ℂ) + β))

/-- DYN (the parabolic core, Shishikura's Theorem 2 at the cusp, case p/q = 0/1). -/
def DynStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ b : ℝ, 0 < b → ∃ N₁ N₂ : ℕ, ∀ a₁ a₂ : ℕ, N₁ ≤ a₁ → N₂ ≤ a₂ →
    ∀ β : ℂ, 0 ≤ β.re → β.re < 1 → |β.im| ≤ b →
      ∃ (N : ℕ) (K : ℝ), 2 ≤ N ∧ 1 < K ∧ 2 - ε ≤ Real.log N / Real.log K ∧
        HypIFS (cOfAlpha (alphaOf a₁ a₂ β)) N K

end MandelDim
