/-
# The model operators of the large-scale estimate (Krause--Mirek--Tao §6--§8)

This module fixes the vocabulary of the large-scale part (`VarpLossLarge`, the regime
`N > splitCut ρ L`) of Theorem `varp` at the exponents `(p₁,p₂) ≠ (2,2)`, following §6--§8 of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022.

## The objects

For a fixed Ionescu--Wainger parameter `ρ`, the paper replaces the concrete column
`Ã_N(F_N f, G_N g)` of `varpCol` (§6, "approximation by model operators") by the *twisted
bilinear Fourier multiplier*

  `B^{l₁,l₂,m_Ẑ}_m(h,k)(x) = ∑_{j₁,j₂} K(j₁,j₂) h(x-j₁) k(x-j₂)`,

with the kernel `K` of the bilinear multiplier whose symbol on `𝕋²` is

  `σ(ξ₁,ξ₂) = ∑_{α₁ ∈ (ℚ/ℤ)_{≤l₁}} ∑_{α₂ ∈ (ℚ/ℤ)_{≤l₂}} m_Ẑ(α₁,α₂) m(ξ₁-α₁, ξ₂-α₂)`,

where `m_Ẑ(α₁,α₂) = E_{n ∈ ℤ/qℤ} e(α₁ n + α₂ P(n))` is the arithmetic symbol.  Here we only need
the case in which `m = m₁ ⊗ m₂` is a *product* symbol (the integration-by-parts identity
`integ-ident` and the functional calculus `bn-ident` of §6 reduce the general case to the product
`m_* = η_{≤-2u} ⊗ η_{≤-2du}` and the modulated bumps `φ_{N,t} ⊗ φ̃_{N,t}`), so that

  `K(j₁,j₂) = (∑_{α₁,α₂} m_Ẑ(α₁,α₂) e(-j₁α₁ - j₂α₂)) · 𝓕⁻m₁(j₁) · 𝓕⁻m₂(j₂)`.

The *model tuple* of §6/§8 is then

  `n ↦ ∫_{1/2}^1 B^{l₁,l₂,m_Ẑ}_{m_*}(T^{l₁}_{φ_{N,t}} F, T^{l₂}_{φ̃_{N,t}} G) dt`,
  `N = ⌊a n⌋`, `F = Π_{≤l₁,≤0} f`, `G = Π_{≤l₂,≤0} g`

(the bottom scale of the contract's pieces being `u = 0`), and the large-scale analysis proves
that this tuple is *acceptable*, i.e. bounded by `⟨L⟩^{O(1)} 2^{O(ρL)} ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`
with `L = max (max l₁ l₂) (max k₁ k₂)`.

## The regime restriction

The functional calculus `B^{...}_{m(φ₁⊗φ₂)} = B^{...}_m(T^{l₁}_{φ₁}·, T^{l₂}_{φ₂}·)` requires the
symbol `m_*` to be identically `1` on the support of `φ_{N,t} ⊗ φ̃_{N,t}`, i.e.
`2^{k} / N ≤ 2^{-2u}` for the continuous scales `k = k₁,k₂`.  We therefore restrict the model
tuple to the *main regime* `k + 2u ≤ Log N` (`u = scaleCount 1 ρ L`), where this holds; the
complementary *exceptional regime* contains only `O_{ρ,L,C₀}(1)` admissible scales `N`, and is
estimated by the elementary single-scale Hölder bound `eLpNorm_AhalfR_le_of_pieces` below.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Split
import Submission.Work.KMTAreas.A7.ProjBound

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract
open Work.Analysis.EndVar

/-! ## The continuous exponential `e(x) = exp (2πi x)` -/

/-- `e(x) = exp (2 π i x)`, the standard character of `ℝ`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-! ## The linear Ionescu--Wainger multiplier `T^{≤l}_φ` -/

/-- **The linear Ionescu--Wainger multiplier `T^{≤l}_φ`.**  It is the convolution on `ℤ` with the
Fourier coefficients of the symbol `ξ ↦ ∑_{α ∈ (ℚ/ℤ)_{≤l}} (periodize φ)(ξ - α)`, written in the
form `iwConv` so that it makes sense for every `f : ℤ → ℂ`. -/
noncomputable def Tle (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (f : ℤ → ℂ) : ℤ → ℂ :=
  iwConv (iwArithFreqs ρ l) (periodize φ) f

theorem Tle_apply (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (f : ℤ → ℂ) (n : ℤ) :
    Tle ρ l φ f n =
      ∑' j : ℤ, iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize φ)) j * f (n - j) := rfl

/-- `Tle` agrees with the concrete IW projection `kmtProj` for the cutoff symbol. -/
theorem Tle_etaCut (ρ : ℝ) (l : ℕ) (k : ℤ) :
    Tle ρ l (etaCut Work.KMTContract.kmtEta k) = kmtProj ρ l k := rfl

@[simp] theorem Tle_zero_right (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) :
    Tle ρ l φ (0 : ℤ → ℂ) = 0 := by
  funext n
  simp [Tle, iwConv]

/-! ## The bumps `φ_N`, `φ̃_N` and their modulations -/

/-- The paper's bump `φ_N` at the continuous scale `k₁` (bottom scale `u = 0`):
`φ_N(ξ) = η(2^{Log N - k₁}ξ) - η(2^{Log N-k₁+1}ξ)` for `k₁ ≥ 1`, and `φ_N(ξ) = η(2^{Log N}ξ)`
at the bottom scale `k₁ = 0`. -/
noncomputable def varphiN (N : ℕ) (k₁ : ℕ) : ℝ → ℂ :=
  if k₁ = 0 then fun ξ => Work.KMTContract.kmtEta (((2 : ℝ) ^ (logN N : ℝ)) * ξ)
  else fun ξ =>
      Work.KMTContract.kmtEta (((2 : ℝ) ^ ((logN N : ℝ) - (k₁ : ℝ))) * ξ)
      - Work.KMTContract.kmtEta (((2 : ℝ) ^ ((logN N : ℝ) - (k₁ : ℝ) + 1)) * ξ)

/-- The paper's bump `φ̃_N` at the continuous scale `k₂` (bottom scale `u = 0`), with the
`d`-fold rescaled frequencies `2^{d(Log N - k₂)}`. -/
noncomputable def varphitildeN (d : ℕ) (N : ℕ) (k₂ : ℕ) : ℝ → ℂ :=
  if k₂ = 0 then fun ξ => Work.KMTContract.kmtEta (((2 : ℝ) ^ ((d : ℝ) * (logN N : ℝ))) * ξ)
  else fun ξ =>
      Work.KMTContract.kmtEta (((2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k₂ : ℝ)))) * ξ)
      - Work.KMTContract.kmtEta (((2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k₂ : ℝ) + 1))) * ξ)

/-- The modulated bump `φ_{N,t}(ξ) = φ_N(ξ) e(N t ξ)`. -/
noncomputable def varphiNt (N : ℕ) (k₁ : ℕ) (t : ℝ) : ℝ → ℂ :=
  fun ξ => varphiN N k₁ ξ * ee ((N : ℝ) * t * ξ)

/-- The real evaluation of an integer polynomial. -/
noncomputable def PevalR (P : ℤ[X]) (x : ℝ) : ℝ := (P.map (Int.castRingHom ℝ)).eval x

/-- The modulated bump `φ̃_{N,t}(ξ) = φ̃_N(ξ) e(P(Nt) ξ)`. -/
noncomputable def varphitildeNt (P : ℤ[X]) (d : ℕ) (N : ℕ) (k₂ : ℕ) (t : ℝ) : ℝ → ℂ :=
  fun ξ => varphitildeN d N k₂ ξ * ee (PevalR P ((N : ℝ) * t) * ξ)

/-- The symbol `m_* = η_{≤-2u}` of §6 (the first tensor factor); at `u = 0` this is `η` itself. -/
noncomputable def mStarF (u : ℕ) : ℝ → ℂ := etaCut Work.KMTContract.kmtEta (-(2 * (u : ℤ)))

/-- The symbol `η_{≤-2du}` of §6 (the second tensor factor). -/
noncomputable def mStargF (d u : ℕ) : ℝ → ℂ :=
  etaCut Work.KMTContract.kmtEta (-((d : ℤ) * 2 * (u : ℤ)))

/-! ## The arithmetic symbol `m_Ẑ` and the twisted bilinear multiplier -/

/-- **The arithmetic symbol** `m_Ẑ(α₁,α₂) = E_{n ∈ ℤ/qℤ} e(α₁ n + α₂ P(n))`, for a modulus `q`
that kills `α₁` and `α₂` (the sum is over `q` consecutive integers, hence is the average over
`ℤ/qℤ`). -/
noncomputable def mZ (P : ℤ[X]) (q : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ℂ :=
  (q : ℂ)⁻¹ * ∑ n ∈ Finset.range q,
    fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂

/-- The modulus `Q_L = lcm P_{≤L}`, a common denominator of all arithmetic frequencies of height
`≤ 2^L`. -/
noncomputable def arithQ (ρ : ℝ) (L : ℕ) : ℕ := max 1 ((iwP ρ L).lcm id)

theorem arithQ_pos (ρ : ℝ) (L : ℕ) : 0 < arithQ ρ L := lt_of_lt_of_le one_pos (le_max_left _ _)

/-- The kernel of the twisted bilinear multiplier in the arithmetic frequencies: the double
Fourier coefficient `∑_{α₁,α₂} m_Ẑ(α₁,α₂) e(-j₁α₁-j₂α₂)` of `m_{l₁,l₂,Ẑ}`. -/
noncomputable def arithKernel (ρ : ℝ) (P : ℤ[X]) (q : ℕ) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) : ℂ :=
  ∑ α₁ ∈ iwArithFreqs ρ l₁, ∑ α₂ ∈ iwArithFreqs ρ l₂,
    mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂

/-- The (inverse) Fourier transform at an integer frequency of a one-variable symbol:
`cw m j = ∫ m(θ) e(-jθ) dθ`. -/
noncomputable def cw (m : ℝ → ℂ) (j : ℤ) : ℂ := ∫ θ : ℝ, m θ * ee (-(j : ℝ) * θ)

/-! ## The exact-height objects of §6

The paper's §6 model operator uses the **exact-height** multipliers
`T^l_φ = T_{Proj(φ ⊗ 1_{(ℚ/ℤ)_l})}` (with `(ℚ/ℤ)_l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}` the *exact*
Iw height level), not the height-`≤ l` multipliers `T^{≤l}_φ`.  The §5 pieces of the contract are
built from the exact-height projections (`piExact l m = Π_{≤l,≤m} - Π_{≤l-1,≤m} = T^l_{η_{≤m}}`),
so the model tuple that approximates them must use the exact-height objects as well:
The definitions below are the exact-height versions of
`Tle`, `arithKernel` and `Btwist`; `modelTuple` uses them, so that `modelTuple` is the paper's
§6 model operator `B^{l₁,l₂,m_Ẑ}_{m_*}(T^{l₁}_{φ_{N,t}}f, T^{l₂}_{φ̃_{N,t}}g)` with the
*exact-height* multipliers `T^{l}` and arithmetic frequencies. -/

/-- **The exact-height Ionescu--Wainger multiplier `T^{l}_φ`** on `ℤ`: convolution with the
Fourier coefficients of the symbol `∑_{α ∈ (ℚ/ℤ)_l} (periodize φ)(· - α)`, where
`(ℚ/ℤ)_l = iwArithFreqsNew ρ l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}` is the exact height-`2^l` level. -/
noncomputable def Tex (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (f : ℤ → ℂ) : ℤ → ℂ :=
  iwConv (iwArithFreqsNew ρ l) (periodize φ) f

noncomputable def arithKernelExact (ρ : ℝ) (P : ℤ[X]) (q : ℕ) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) : ℂ :=
  ∑ α₁ ∈ iwArithFreqsNew ρ l₁, ∑ α₂ ∈ iwArithFreqsNew ρ l₂,
    mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂

/-- **The twisted bilinear multiplier `B^{l₁,l₂,m_Ẑ}_{m₁⊗m₂}`** at exact arithmetic heights,
in the kernel form `∑_{j₁,j₂} K(j₁,j₂) h(x-j₁)k(x-j₂)`. -/
noncomputable def BtwistExact (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j₁ : ℤ, ∑' j₂ : ℤ,
    arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂
      * h (x - j₁) * k (x - j₂)

/-- **The twisted bilinear multiplier `B^{l₁,l₂,m_Ẑ}_{m₁⊗m₂}`** with a *product* symbol
`m₁ ⊗ m₂`, in the kernel form `∑_{j₁,j₂} K(j₁,j₂) h(x-j₁) k(x-j₂)`. -/
noncomputable def Btwist (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j₁ : ℤ, ∑' j₂ : ℤ,
    arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂
      * h (x - j₁) * k (x - j₂)

/-! ## The main regime of the large-scale estimate -/

/-- The auxiliary scale `u = ⌊C₂ 2^{2ρL}⌋` of the scale split (with `C₂ = 1`). -/
noncomputable def uScale (ρ : ℝ) (L : ℕ) : ℕ := scaleCount 1 ρ L

/-- **The main regime of the large-scale analysis.**  The continuous frequency window attached to
the scale `k` at the physical scale `N` is `ℝ_{≤ -Log N + k}` (of width `2^k/N`); the symbol `m_*`
of §6 has band `ℝ_{≤-2u}`.  The functional calculus requires the window to sit inside the band,
i.e. `k + 2u ≤ Log N`. -/
def mainRegime (ρ : ℝ) (k₁ k₂ : ℕ) (N : ℕ) : Prop :=
  k₁ + 2 * uScale ρ (max k₁ k₂) ≤ (logN N).toNat ∧
    k₂ + 2 * uScale ρ (max k₁ k₂) ≤ (logN N).toNat

/-- The main regime is decidable. -/
instance (ρ : ℝ) (k₁ k₂ N : ℕ) : Decidable (mainRegime ρ k₁ k₂ N) := by
  unfold mainRegime; infer_instance

/-! ## The model tuple -/

/-- **The model tuple of §6/§8.**  On the admissible scales of the main regime it is
`n ↦ ∫_{1/2}^1 B^{l₁,l₂,m_Ẑ}_{m_*}(T^{l₁}_{φ_{N,t}}f, T^{l₂}_{φ̃_{N,t}}g) dt`, and it vanishes off
the index set, off the large scales and off the main regime.

(The paper writes the arguments of the model operator as `T^{l₁}_{φ_{N,t}}F`,
`T^{l₂}_{φ̃_{N,t}}G` with `F = Π_{≤l₁,≤-u}f`, `G = Π_{≤l₂,≤-du}g`; by the functional calculus
`T^{l}_{φ}T^{l}_{ψ} = T^{l}_{φψ}` these agree with `T^{l₁}_{φ_{N,t}}f`, `T^{l₂}_{φ̃_{N,t}}g`
because `φ_{N,t}` is supported at frequency scale `2^{k}/N ≤ 2^{-2u}` and `η_{≤-2u} = 1` there.
Writing the tuple in terms of `f, g` directly is essential: the projection `Π_{≤l,≤0}` is *not*
bounded on `ℓ^p`, since `periodize kmtEta ≥ 1` pointwise, so `Π_{≤l,≤0}` has norm at least
`|(ℚ/ℤ)_{≤l}| ≥ 2^l`.) -/
noncomputable def modelTuple (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
        ∧ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
        ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n)) then
      ∫ t in (1/2 : ℝ)..1,
        BtwistExact ρ P l₁ l₂
          (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
          (Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x
    else 0

/-- **The main part of the concrete column family**: `varpCol` restricted to the index set, to
the large scales `N > splitCut ρ L` and to the main regime. -/
noncomputable def mainPartTuple (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
        ∧ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
        ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n)) then
      varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x
    else 0


/-- The scale `L = max (max l₁ l₂) (max k₁ k₂)` of the loss, as a real number. -/
noncomputable def lmaxR (l₁ l₂ k₁ k₂ : ℕ) : ℝ := (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ)

/-- The loss weight `⟨L⟩^c · 2^{cρL}` of the estimates at the exponents `(p₁,p₂) ≠ (2,2)`. -/
noncomputable def lossWeight (c ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : ℝ :=
  (1 + lmaxR l₁ l₂ k₁ k₂) ^ c * (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂)


/-- **The concrete column family of `VarpLossLarge`**: the §5 columns `varpCol`, restricted to the
large scales `N > splitCut ρ L`. -/
noncomputable def colTuple (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) then
      varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x
    else 0

/-- **The exceptional part** of the column family: the contribution of the scales which are
admissible and large but *not* in the main regime (i.e. `varpCol - mainPartTuple`).  For a fixed
quadruple `(l₁,l₂,k₁,k₂)` this family is supported on the finitely many lacunary scales with
`Log N ≤ 16 C₀ ^ 2 + 16`. -/
noncomputable def exceptionalPart (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x

theorem colTuple_eq (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x =
      if splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) then
        varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x
      else 0 := rfl

/-- The pointwise splitting of the column family into the model tuple, the model-approximation
error and the exceptional part. -/
theorem colTuple_eq_sum (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ =
      fun n x => modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
        + ((mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
  funext n x
  simp only [exceptionalPart, Pi.add_apply, Pi.sub_apply]
  ring



/-- **The weight of the single-scale model approximation** (`mod-approx` of §6): the paper's
Proposition gives the error `2^{O(max(2^{ρl}, s))} N^{-1}`, and since `s ≤ L` and `2^{ρl} ≤ 2^{ρL}`
this is `≤ modWeight A ρ L · N^{-1}` for a suitable `A ≥ 0` (`L = lmaxR l₁ l₂ k₁ k₂`).

Note that `A` is *not* required to be independent of `ρ`: the paper's implied constant depends on
the IW hierarchy (through `C₃` and `mag-lem`(ii)(iii)), hence on `ρ`.  This is harmless because
in the assembly the whole factor `modWeight A ρ L` is multiplied by the lacunary sum
`∑_n N_n^{-1} ≲ 2^{-2^{L/C₀}}` and the product `2^{A(2^{ρL}+L)} · 2^{-2^{L/C₀}}` is bounded by a
constant depending only on `ρ` (absorbed into `K(Λ)`), so that the *final* exponent may be taken
independent of `ρ`. -/
noncomputable def modWeight (A ρ L : ℝ) : ℝ :=
  (2 : ℝ) ^ (A * ((2 : ℝ) ^ (ρ * L) + L))

theorem modWeight_nonneg (A ρ L : ℝ) : 0 ≤ modWeight A ρ L := Real.rpow_nonneg (by norm_num) _

/-! ## The repaired model: the separation of the exact-height fibres

The model symbol of §6 is `m_* = η_{≤-2u} ⊗ η_{≤-2du}`, where the paper takes
`u = ⌊C₂ 2^{2ρl}⌋` with `C₂` a *free* constant (`C₂` is allowed to be large, see the paper's
\eqref{u-def} and the discussion around `bn-ident`), and `l = max(l₁,l₂)`.

The workspace normalises `C₂ = 1` (`uScale ρ L = scaleCount 1 ρ L = ⌊2^{2ρL}⌋`).  That is *not*
enough: the functional calculus `func-calc-3` / `bn-ident` requires `m_*` to be identically `1`
on the window of the bump `φ_{N,t}`, whose continuous frequencies carry the *arithmetic* index
`α ∈ diffFreqs ρ lᵢ`; when the plateau `2^{-2u}` of `m_*` is wider than the separation of the
exact-height fibres, the composed model operator acquires *cross-fibre* terms which the concrete
column does not have.  With `C₂ = 1` this happens as soon as `max(l₁,l₂)` is large compared with
`L = max (max l₁ l₂) (max k₁ k₂)`; the refutation of `Work.KMTAreas.A7.HiMassBound` (and of the
single-scale content of `ModelApproxHi`) is recorded in
`NOTES_A7_HiMassBoundHolds_VERDICT.md`, and the repair below is the one prescribed there (§3).

Distinct fractions `a/q ≠ a'/q'` with `q,q' ≤ 2^l` are at distance `≥ 2^{-2l}`
(`nonAliasing`/`mag-lem`(iii) of the paper), so the plateau must satisfy `2^{-2u} ≲ 2^{-2l}`, i.e.
`u ≳ l`; hence the extra term `max l₁ l₂ + 3` in `uRep`, on top of the paper's `⌊C₂2^{2ρl}⌋`.
-/

/-- **The band parameter `u` of the §6 model symbol**, repaired so that the plateau `2^{-2u}` of
`m_*` is *below* the separation of the exact-height fibres `diffFreqs ρ (max l₁ l₂)`. -/
noncomputable def uRep (ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : ℕ :=
  max (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) (max l₁ l₂ + 3)

/-- **The band condition of the §6 model**: the frequency window `ℝ_{≤ -Log N + k}` of the bump
`φ_{N,t}` (of width `2^{k}/N`) must lie inside the plateau of `m_*` (of width `2^{-2u}`), i.e.
`k + 1 + 2u ≤ Log N` for the two continuous scales. -/
def bandCond (ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (N : ℕ) : Prop :=
  k₁ + 1 + 2 * uRep ρ l₁ l₂ k₁ k₂ ≤ (logN N).toNat ∧
    k₂ + 1 + 2 * uRep ρ l₁ l₂ k₁ k₂ ≤ (logN N).toNat

instance bandCondDecidable (ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (N : ℕ) :
    Decidable (bandCond ρ l₁ l₂ k₁ k₂ N) := by
  unfold bandCond; infer_instance

/-- **The repaired model tuple of §6/§8**: the same object as `modelTuple`, but with the model
symbol's band `uRep` (so that the functional calculus `bn-ident` holds) and with the band
condition `bandCond` added to its guard (off the band the model is `0`, and the (finitely many,
`ρ`- and `C₀`-bounded) off-band scales are absorbed by the constant `K(Λ)` of the estimates).

See the module docstring above and `NOTES_A7_HiMassBoundHolds_VERDICT.md` §3. -/
noncomputable def modelTupleRep (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
        ∧ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
        ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n))
        ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
      ∫ t in (1/2 : ℝ)..1,
        BtwistExact ρ P l₁ l₂
          (mStarF (uRep ρ l₁ l₂ k₁ k₂))
          (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
          (Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
          (Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x
    else 0

/-- The pointwise splitting of the column family with the *repaired* model. -/
theorem colTuple_eq_sum_rep (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ =
      fun n x => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
        + ((mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
  funext n x
  simp only [exceptionalPart, Pi.add_apply, Pi.sub_apply]
  ring
end

end Work.KMTAreas.A7
