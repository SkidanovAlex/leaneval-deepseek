import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.H2nd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.K2ndDefs` — the `c`-number dictionary data of FS `eq:HLambdaSecond`

FS `thm:Kafz` (the `c`-number substitution) replaces an *anti-normal* monomial
`a₀^p (a₀†)^q (lift B)` on the algebraic core `FockCore (cfock (Excited m))` by
the integral against the coherent-state measure of its symbol `z^p z̄^q B`.
`Work.BoseB4.Kafz_lattice` turns this into a statement about a *mode-lattice*
operator `W` once one knows

    `split (W x) = (∑ᵢ a₀^{pᵢ}(a₀†)^{qᵢ}(lift Bᵢ)) (split x)`   for every `x`.

This module supplies the right-hand side for FS's box Hamiltonian
`Work.BoseB4.H2nd` — i.e. the *complex-spectator* operators that the concrete
mode-lattice words of `eq:HLambdaSecond` correspond to under `Work.BoseB4.split`,
together with their condensation into the nine anti-normal slots

    `(p,q) ∈ {(0,0),(1,1),(2,2),(2,0),(0,2),(2,1),(1,0),(1,2),(0,1)}`.

Everything is stated over `cfock (Excited m)`, the complex Fock core of the
excited modes, so the result feeds straight into `Work.BoseB4.Kafz_sum` /
`Work.BoseB4.Kafz_lattice`.

## Conventions

* `annX m k` is the abstract excited-mode annihilation at the lattice mode
  `k : Fin m`; it is `0` at the condensate mode `k = 0`, so a sum over *all* of
  `Fin m` may be used in place of a sum over `exc m = univ.erase 0`.
* `CX k = creX m k ∘ annX m k` is the (condensate-free) number operator of the
  mode `k`.
* the `K…` families are the images of the corresponding words of
  `Work.BoseB4.H2nd` under the dictionary `a_k ↔ annX m k`, `a_k† ↔ creX m k`,
  `a₀ ↔ a0`, `a₀† ↔ a0d`, with the condensate words already reordered into
  anti-normal form `a₀^p (a₀†)^q`.  The reordering coefficients are the Wick
  coefficients of `Work.BoseB4.a0dpow_comp_lift_comp_a0pow`: e.g.
  `(a₀†)²a₀² = monoOp 2 2 1 − 4 (monoOp 1 1 1) + 2 (monoOp 0 0 1)` and
  `(a₀†)a₀ = monoOp 1 1 1 − monoOp 0 0 1`.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

variable {m : ℕ} [NeZero m]

/-! ## The excited-mode operators on the complex Fock core -/

/-- The excited-mode **annihilation at the lattice mode `k`**, `0` for the
condensate mode `k = 0`. -/
noncomputable def annX (m : ℕ) [NeZero m] (k : Fin m) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  if h : k = 0 then 0 else annC (Excited m) ⟨k, h⟩

/-- The excited-mode **creation at the lattice mode `k`**, `0` for the
condensate mode `k = 0`. -/
noncomputable def creX (m : ℕ) [NeZero m] (k : Fin m) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  if h : k = 0 then 0 else creC (Excited m) ⟨k, h⟩

/-- The **number operator of the lattice mode `k`** on the excited modes,
`CX k = creX k ∘ annX k`. -/
noncomputable def CX (k : Fin m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (creX m k).comp (annX m k)

/-! ## The scalar data of `eq:HLambdaSecond` -/

/-- `ℓ⁻³` of FS's box side. -/
noncomputable def i3 (D : H2ndData m) : ℝ := D.ell ^ (-(3 : ℝ))

/-- FS's contact coefficient `½ℓ⁻³(ĝ(0) + ĝ_ω(0))`. -/
noncomputable def cHC (D : H2ndData m) : ℝ := (1 / 2) * i3 D * (D.g0 + D.gomega0)

/-- FS's chemical-potential coefficient `−μĝ(0)` of the `a₀†a₀` term. -/
noncomputable def cMu (D : H2ndData m) : ℝ := -(D.mu * D.g0)

/-- FS's gap coefficient `b/(2ℓ²)`. -/
noncomputable def gGap (D : H2ndData m) : ℝ := D.b / (2 * D.ell ^ 2)

/-- FS's high-momentum gap coefficient `ε_T b/(2d²ℓ²)`. -/
noncomputable def gGapH (D : H2ndData m) : ℝ := D.eT * D.b / (2 * D.d ^ 2 * D.ell ^ 2)

/-! ## The contributions of `eq:HLambdaSecond`, term by term

Each `K…` family is the image under the mode dictionary of one word of
`Work.BoseB4.H2nd`.  The names record the condenser word the term carries. -/

/-- Image of the kinetic row `Σ_k τ(k) a_k†a_k` (`a₀`-free). -/
noncomputable def Kkin (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((D.tau k : ℝ) : ℂ) • CX k

/-- Image of the gap row `(b/2ℓ²) n₊`. -/
noncomputable def Kgap (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((gGap D : ℝ) : ℂ) • CX k

/-- Image of the high-momentum gap row `ε_T(b/2d²ℓ²) n₊^H`. -/
noncomputable def KgapH (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ (exc m).filter (fun k => k ∈ D.PHset), ((gGapH D : ℝ) : ℂ) • CX k

/-- Image of the `a₀`-free part of `Σ_k (Ŵ₁(k)+Ŵ₁ω(k)) a₀†a_k†a_k a₀`, i.e. the
`(a₀†)a₀ = monoOp 1 1 1 − monoOp 0 0 1` slot with the *positive* coefficient. -/
noncomputable def KHW1 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, (((D.W1 k + D.W1omega k) : ℝ) : ℂ) • CX k

/-- Image of the `monoOp 0 0 1` part of `Σ_k (Ŵ₁(k)+Ŵ₁ω(k)) a₀†a_k†a_k a₀`, with
the *negative* coefficient. -/
noncomputable def KHW2 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((-(D.W1 k + D.W1omega k) : ℝ) : ℂ) • CX k

/-- Image of the `(a₀†)²a₀²` part of the contact term. -/
noncomputable def KHC2 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ((cHC D : ℝ) : ℂ) • 1

/-- Image of the `a₀†a₀` part of the contact term. -/
noncomputable def KHC1 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ((-(4 * cHC D) : ℝ) : ℂ) • 1

/-- Image of the `(a₀†)⁰a₀⁰` part of the contact term. -/
noncomputable def KHC0 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ((2 * cHC D : ℝ) : ℂ) • 1

/-- Image of the `a₀†a₀` part of the `−μĝ(0)a₀†a₀` term. -/
noncomputable def Kmu1 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ((cMu D : ℝ) : ℂ) • 1

/-- Image of the `(a₀†)⁰a₀⁰` part of the `−μĝ(0)a₀†a₀` term. -/
noncomputable def Kmu0 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ((-(cMu D) : ℝ) : ℂ) • 1

/-- Image of the `a₀†a₀†a_k a_{−k}` half of the Bogoliubov pair term. -/
noncomputable def Kbog1 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, (((1 / 2) * D.W1 k : ℝ) : ℂ) • (annX m k).comp (annX m (-k))

/-- Image of the `a_k†a_{−k}†a₀a₀` half of the Bogoliubov pair term. -/
noncomputable def Kbog2 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, (((1 / 2) * D.W1 k : ℝ) : ℂ) • (creX m k).comp (creX m (-k))

/-- Image of the `ℓ⁻³(a₀†)a₀² a_k†` part of the `χ̂_Λ` term. -/
noncomputable def KchiA (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((i3 D * D.W10 * D.chiHat k : ℝ) : ℂ) • creX m k

/-- Image of the `−(2ℓ⁻³+μ)a₀ a_k†` part of the `χ̂_Λ` term. -/
noncomputable def KchiB (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((-((2 * i3 D + D.mu) * D.W10 * D.chiHat k) : ℝ) : ℂ) • creX m k

/-- Image of the `ℓ⁻³(a₀†)²a₀ a_k` part of the `χ̂_Λ` term. -/
noncomputable def KchiC (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((i3 D * D.W10 * D.chiHat k : ℝ) : ℂ) • annX m k

/-- Image of the `−(ℓ⁻³+μ)a₀† a_k` part of the `χ̂_Λ` term. -/
noncomputable def KchiD (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((-((i3 D + D.mu) * D.W10 * D.chiHat k) : ℝ) : ℂ) • annX m k

/-- `(2,1)` part of the `ℓ⁻³a₀†a₀Ŵ₁ω(0)χ̂_Λ` term. -/
noncomputable def KchiOmA (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((i3 D * D.W1omega0 * D.chiHat k : ℝ) : ℂ) • creX m k

/-- `(1,0)` part of the `ℓ⁻³a₀†a₀Ŵ₁ω(0)χ̂_Λ` term. -/
noncomputable def KchiOmB (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((-(2 * i3 D * D.W1omega0 * D.chiHat k) : ℝ) : ℂ) • creX m k

/-- `(1,2)` part of the `ℓ⁻³a₀†a₀Ŵ₁ω(0)χ̂_Λ` term. -/
noncomputable def KchiOmC (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((i3 D * D.W1omega0 * D.chiHat k : ℝ) : ℂ) • annX m k

/-- `(0,1)` part of the `ℓ⁻³a₀†a₀Ŵ₁ω(0)χ̂_Λ` term. -/
noncomputable def KchiOmD (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((-(i3 D * D.W1omega0 * D.chiHat k) : ℝ) : ℂ) • annX m k

/-- `(1,1)` part of the `((ℓ⁻³a₀†a₀−μ)Ŵ₁(0))ℓ⁻³∫a_k†a_k` term. -/
noncomputable def KnnA (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((i3 D * D.W10 * i3 D : ℝ) : ℂ) • CX k

/-- `(0,0)` part of the `((ℓ⁻³a₀†a₀−μ)Ŵ₁(0))ℓ⁻³∫a_k†a_k` term. -/
noncomputable def KnnB (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((-((i3 D + D.mu) * D.W10 * i3 D) : ℝ) : ℂ) • CX k

/-- `(1,1)` part of the `(ℓ⁻³a₀†a₀Ŵ₁ω(0))ℓ⁻³∫a_k†a_k` term. -/
noncomputable def KnnC (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((i3 D * D.W1omega0 * i3 D : ℝ) : ℂ) • CX k

/-- `(0,0)` part of the `(ℓ⁻³a₀†a₀Ŵ₁ω(0))ℓ⁻³∫a_k†a_k` term. -/
noncomputable def KnnD (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ exc m, ((-(i3 D * D.W1omega0 * i3 D) : ℝ) : ℂ) • CX k

/-! ## The nine anti-normal slots -/

/-- The `(0,0)` slot: all `a₀`-free contributions. -/
noncomputable def K00 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  Kkin D + Kgap D + KgapH D + KHW2 D + KHC0 D + Kmu0 D + KnnB D + KnnD D

/-- The `(1,1)` slot `a₀†a₀`. -/
noncomputable def K11 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  KHW1 D + KHC1 D + Kmu1 D + KnnA D + KnnC D

/-- The `(2,2)` slot `a₀²(a₀†)²`. -/
noncomputable def K22 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  KHC2 D

/-- The `(2,0)` slot `a₀² a_k†a_{−k}†`. -/
noncomputable def K20 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  Kbog2 D

/-- The `(0,2)` slot `(a₀†)² a_k a_{−k}`. -/
noncomputable def K02 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  Kbog1 D

/-- The `(2,1)` slot `a₀²a₀† a_k†`. -/
noncomputable def K21 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  KchiA D + KchiOmA D

/-- The `(1,0)` slot `a₀ a_k†`. -/
noncomputable def K10 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  KchiB D + KchiOmB D

/-- The `(1,2)` slot `a₀(a₀†)² a_k`. -/
noncomputable def K12 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  KchiC D + KchiOmC D

/-- The `(0,1)` slot `a₀† a_k`. -/
noncomputable def K01 (D : H2ndData m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  KchiD D + KchiOmD D

/-- The exponent pairs of the nine slots, in the order of `Kvec`. -/
def Kexp : Fin 9 → ℕ × ℕ :=
  ![(0, 0), (1, 1), (2, 2), (2, 0), (0, 2), (2, 1), (1, 0), (1, 2), (0, 1)]

/-- The annihilation exponent of slot `i`. -/
def Kpvec (i : Fin 9) : ℕ := (Kexp i).1

/-- The creation exponent of slot `i`. -/
def Kqvec (i : Fin 9) : ℕ := (Kexp i).2

/-- The spectator operator of slot `i`, in the order `Kexp`. -/
noncomputable def Kvec (D : H2ndData m) :
    Fin 9 → cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ![K00 D, K11 D, K22 D, K20 D, K02 D, K21 D, K10 D, K12 D, K01 D]

/-- **The complex-spectator operator of FS `eq:HLambdaSecond`**: the anti-normal
sum `Σᵢ a₀^{pᵢ}(a₀†)^{qᵢ}(lift Bᵢ)` that a mode-lattice word of
`Work.BoseB4.H2nd` corresponds to under `Work.BoseB4.split`. -/
noncomputable def K2ndC (D : H2ndData m) :
    FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) :=
  ∑ i : Fin 9, monoOp (Kpvec i) (Kqvec i) (Kvec D i)

/-- **The anti-Wick symbol `𝓚(z)` of `eq:HLambdaSecond`**: the operator obtained
from `K2ndC` by the substitution `a₀ ↦ z`, `a₀† ↦ z̄` (FS `eq:subst-z`). -/
noncomputable def K2ndSym (D : H2ndData m) (z : ℂ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ i : Fin 9, symbol (Kpvec i) (Kqvec i) (Kvec D i) z

end Work.BoseB4
