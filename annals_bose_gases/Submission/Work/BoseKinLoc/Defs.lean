import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.LocPotential
import Submission.Symmetry
import Submission.Work.BSKinetic.FamilyBound_of_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseKinLoc.Defs` — Node C: the DECOUPLED localised box word
(FS `thm:CompareBoxEnergy`, `eq:Def_HB`, `eq:DefT`)

This chapter is Node C of the audit (`BOSE_AUDIT_LEAD.md` §4, node C):
`CompareBoxEnergy` at the **decoupled** parameters — the chemical potential `μ`
is a free real, the localisation scale `ℓ` is a free positive real
(`ℓ = ℓ(μ)` in the application), the particle number `n` is **free**, and the
kinetic parameters `d, s, ε_T, b` are FS's `ℒ`-independent small parameters.

## Why decoupled (the audit's root cause)

Every refuted earlier version of the kinetic localisation quantified over
*all* `L ≥ 1` and *all* `N` with `μ := N/L³` and the box side tied to `L`.  FS's
box theorem instead lives at **one scale**: `μ` fixed, box side
`ℓ = K_ℓ (μa)^{-1/2}`, particle number free, `μℓ³ ≫ 1`, with
`ρa³`-dependent parameters.  The statements of this chapter therefore carry
`(ℓ, μ, d, s, ε_T, b)` as free parameters with no relation to any particle
number or any large volume `L`.  (`ℓ → ∞` is *allowed*: the support condition
`R ≤ ℓ·r₀` is a lower bound on the localisation scale, not an upper bound on
the volume — this is the "support-radius test" of the audit.)

## Contents of this module

All of FS `eq:DefT`'s four kinetic pieces as one-body quadratic forms on
`ψ : ℝ³ → ℝ`, at the moving box `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³`:

| name | FS | object |
|---|---|---|
| `neuWord` | `eq:DefT` first term | `½ε_T(dℓ)⁻² (−Δ^N_u)(−Δ^N_u+(dℓ)⁻²)⁻¹` on `Q_uψ` |
| `gapWord` | `eq:DefT` second term | `bℓ⁻²Q_u` |
| `momWord` | `eq:DefT` third term | `bε_T(dℓ)⁻²Q_u 1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)Q_u` |
| `mainWord` | `eq:T'u` | `Q_uχ_u{(1−ε_T)[√−Δ−½(sℓ)⁻¹]₊²+ε_T[√−Δ−½(dsℓ)⁻¹]₊²}χ_uQ_u` |

together with

* `fsT` — their sum (= FS's `𝒯_u`, a one-body quadratic form);
* `slotForm`/`kinForm`/`potWordU`/`boxForm` — FS `eq:Def_HB`: the `N`-body localised
  box Hamiltonian `H_{Λ,u}(μ)_N = Σᵢ𝒯_u^{(i)} − μΣᵢ∫w_{1,u}(xᵢ,y)dy + Σ_{i<j}w_u(xᵢ,xⱼ)`
  as a quadratic form (the one-body kinetic pieces are spectral, hence the slot lifting);
* `SymCSBox n ℓ` (symmetric smooth box states) and `EΛ` — FS's
  `E_Λ(μ) = inf Spec H_Λ(μ)` as the infimum of the box words over the free
  particle number `n` and over symmetric states;
* `ombox`, `coverU` — the one-particle box `Ω = [0,L]³` and the set of
  translation parameters `u` whose box meets `Ω` (`|coverU| = (L+ℓ)³/ℓ³`,
  the audit's `((L+ℓ)/ℓ)³`).

## Conventions

* `Λ(u)` is `bsBox ℓ u` (`Work.BSKinetic`), definitionally `Work.UBBInputs9.bigBox`;
  the window `χ_u` is `Submission.BoseGases.chiU` (= `Work.BSKinetic.bsWin`),
  supported **exactly** in `Λ(u)` (`chi` is supported in `[−1/2,1/2]³`), so all
  the operators below are supported in `Λ(u)^N` — this is what makes the
  sector decomposition of `Sector.lean` exact rather than approximate.
* `Q_u ψ = ψ − (box mean of ψ)` is `Work.BSKinetic.bsQ` (FS's `Q_u`, whose
  indicator `θ_u` is redundant inside `Λ(u)`).
* the `u`-family `{Λ(u)}_{u∈ℝ³}` is an exact partition of unity both for the
  bump window (`∫_u χ_u(x)² du = 1`, `integral_chiScale_sub_smul_sq`) and for
  the indicator (`∫_u 1_{Λ(u)}(x) du = 1`) — the multiplicity is **one**, so
  no volume factor is lost in the kinetic localisation.
* the box word is stated for a **pair of potentials `(v, g)`**: `v` the
  interaction and `g := v(1−ω)` the one-body kernel of `−μ∫w_{1,u}`; the
  identity `∫g = 8πa v` (`ScatChosen`) is *not* used in this module.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

/-- The Euclidean three-space of the chapter (used throughout the statements). -/
scoped[Work] notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseKinLoc

open Submission.BoseGases
open Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false

open _root_.BoseGases

/-! ## 1. The moving box, its window and the box-mean-free projection -/

/-- FS's large box `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` (the corpus's `bigBox`/`bsBox`). -/
def lamBox (ℓ : ℝ) (u : ℝ³) : Set ℝ³ := bsBox ℓ u

/-- FS's window `χ_u(x) = χ(x/ℓ − u)`. -/
def winU (ℓ : ℝ) (u x : ℝ³) : ℝ := bsWin ℓ u x

/-- The indicator `θ_u = 1_{Λ(u)}` of FS's `eq:Theta`. -/
def indU (ℓ : ℝ) (u : ℝ³) : ℝ³ → ℝ := (lamBox ℓ u).indicator fun _ => (1 : ℝ)

/-- FS's box mean `Q_u`'s companion `m_u(ψ) = |Λ(u)|⁻¹∫_{Λ(u)}ψ`. -/
def meanU (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ := bsMean ℓ u ψ

/-- FS's mean-free projection `Q_uψ = θ_u(ψ − m_u)`, written without the redundant indicator. -/
def Qfree (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ³ → ℝ := bsQ ℓ u ψ

/-- The spectral cut-off momentum of FS `eq:DefT`'s third term:
`1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)` is the indicator of `‖p‖ > (d²ℓ)⁻¹`. -/
def momProj (ℓ d : ℝ) (p : ℝ³) : ℝ := if (d ^ 2 * ℓ)⁻¹ < ‖p‖ then 1 else 0

/-! ## 2. The four kinetic pieces of FS `eq:DefT` (one-body quadratic forms)

All four are functionals of a one-body state `ψ : ℝ³ → ℝ` and a translation
parameter `u : ℝ³`; they are the diagonal matrix elements of FS's operators. -/

/-- The Neumann-resolvent fraction `(−Δ^N_u)(−Δ^N_u+a²)⁻¹` as a quadratic form on the
box `Λ(u)`, defined by the Dirichlet principle / resolvent variational formula

    `⟨ϕ, A(A+a²)⁻¹ϕ⟩ = inf_g  [ ‖ϕ‖²_{Λ} − 2a²⟨ϕ,g⟩_{Λ} + a²(‖∇g‖²_{Λ} + a²‖g‖²_{Λ}) ]`

(the infimum over globally smooth compactly supported trials `g`; the minimiser
is `(A+a²)⁻¹ϕ`).  This is BS Lemma 3.7 / FS `eq:DefT`'s first term. -/
def neuFrac (ℓ : ℝ) (a2 : ℝ) (u : ℝ³) (ϕ : ℝ³ → ℝ) : ℝ :=
  sInf { c : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      c = (∫ z in lamBox ℓ u, (ϕ z) ^ 2)
          - 2 * a2 * (∫ z in lamBox ℓ u, ϕ z * g z)
          + a2 * ((∑ k : Fin 3, ∫ z in lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2)
                  + a2 * (∫ z in lamBox ℓ u, (g z) ^ 2)) }

/-- FS `eq:DefT`, first term: `½ε_T(dℓ)⁻²(−Δ^N_u)(−Δ^N_u+(dℓ)⁻²)⁻¹` applied to `Q_uψ`. -/
def neuWord (ℓ d εT : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
  (1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ) * neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) u (Qfree ℓ u ψ)

/-- The *bare* mean-free mass in the box: `⟨Q_uψ, Q_uψ⟩ = ∫_{Λ(u)}(ψ − m_u)²`.
(FS `eq:Quav`: `∫_u Q_u du = 1 − θ̂(ℓp)²` in Fourier.) -/
def gapBare (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
  ∫ z in lamBox ℓ u, (Qfree ℓ u ψ z) ^ 2

/-- FS `eq:DefT`, second term (the large-box Neumann gap): `bℓ⁻²Q_u`. -/
def gapWord (ℓ b : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
  b * ℓ ^ (-2 : ℤ) * gapBare ℓ u ψ

/-- The *bare* large-momentum form `⟨θ_uQ_uψ, 1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)θ_uQ_uψ⟩` in the
corpus's momentum convention. -/
def momForm (ℓ d : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : ℝ³, momProj ℓ d p *
      ‖kinFT (fun z : ℝ³ => ((indU ℓ u z : ℝ) : ℂ) * ((Qfree ℓ u ψ z : ℝ) : ℂ)) p‖ ^ 2

/-- FS `eq:DefT`, third term (large momenta):
`bε_T(dℓ)⁻²Q_u 1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)Q_u`, in the corpus's momentum convention. -/
def momWord (ℓ d εT b : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
  b * εT * (d * ℓ) ^ (-2 : ℤ) * momForm ℓ d u ψ

/-- FS `eq:T'u` (through `eq:DefT`'s fourth term): the two-cutoff windowed kinetic word
`Q_uχ_u{(1−ε_T)[√−Δ−½(sℓ)⁻¹]₊² + ε_T[√−Δ−½(dsℓ)⁻¹]₊²}χ_uQ_u`, written with the
corpus's `bsOneBody` (whose coefficient `F` is the radial momentum symbol). -/
def mainWord (ℓ d s εT : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
  (1 - εT) * bsOneBody ℓ (fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ
    + εT * bsOneBody ℓ (fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ

/-- **FS `eq:DefT`**: the localised kinetic operator `𝒯_u` as a one-body quadratic form. -/
def fsT (ℓ d s εT b : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
  neuWord ℓ d εT u ψ + gapWord ℓ b u ψ + momWord ℓ d εT b u ψ + mainWord ℓ d s εT u ψ

/-! ## 3. The `N`-body localised box form (FS `eq:Def_HB`)

FS `eq:Def_HB` is a **quadratic form** (its one-body kinetic pieces are spectral,
not multiplicative), so the `N`-body object is defined slot by slot.  For a one-body
form `q` and an `N`-body state `Φ`, the `i`-th slot contribution is

    `slotForm N q ℓ u i Φ := ℓ⁻³ ∫_{x} 1_{Λ(u)}(xᵢ)·q(fibre N i Φ x) d x`,

which by the fibre structure (`q(fibre N i Φ x)` does **not** depend on `xᵢ`) is exactly
`∫_{x_{≠i}} q(fibre N i Φ x) d x_{≠i} = ⟨Φ, AᵢΦ⟩` for the self-adjoint `A` with form `q`
(the normalised slot-`i` integral produces the peeling). -/

/-- The slot-`i` fibre of an `N`-body state: `z ↦ Φ(x with xᵢ = z)`. -/
def fibre (N : ℕ) (i : Fin N) (Φ : X N → ℝ) (x : X N) : ℝ³ → ℝ :=
  fun z => Φ (Function.update x i z)

/-- The `i`-th slot lifting of a one-body form `q`: `⟨Φ, AᵢΦ⟩` for the self-adjoint `A`
with form `q` (see the section comment). -/
def slotForm (N : ℕ) (q : (ℝ³ → ℝ) → ℝ) (ℓ : ℝ) (u : ℝ³) (i : Fin N) (Φ : X N → ℝ) : ℝ :=
  ℓ ^ (-3 : ℤ) * ∫ x : X N, indU ℓ u (x i) * q (fibre N i Φ x)

/-- The kinetic part of FS `eq:Def_HB`: `Σᵢ𝒯_u^{(i)}`. -/
def kinForm (N : ℕ) (ℓ d s εT b : ℝ) (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, slotForm N (fsT ℓ d s εT b u) ℓ u i Φ

/-- The **multiplicative** part of FS `eq:Def_HB` as a function of the configuration:
`−μΣᵢ∫_y w_{1,u}(xᵢ,y)dy + Σ_{i<j}w_u(xᵢ,xⱼ)`.  This is the part to which
`LocPotential`'s pointwise identities apply. -/
def potWordU (N : ℕ) (v g : ℝ³ → ℝ) (ℓ μ : ℝ) (u : ℝ³) (x : X N) : ℝ :=
  -μ * (∑ i : Fin N, ∫ y : ℝ³, wLoc ℓ g u (x i) y)
    + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, wLoc ℓ v u (x ij.1.1) (x ij.1.2)

/-- **FS `eq:Def_HB`** — the localised box Hamiltonian `H_{Λ,u}(μ)_N` as a quadratic form. -/
def boxForm (N : ℕ) (v g : ℝ³ → ℝ) (ℓ μ d s εT b : ℝ) (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  kinForm N ℓ d s εT b u Φ
    + ∫ x : X N, (Φ x) ^ 2 * potWordU N v g ℓ μ u x

/-- The **box-restricted** kinetic part: the same slot forms with the configuration integral
restricted to the box `abox N ℓ`.  FS's box Hamiltonian lives on `L²(Λ^n)`, so its form sees only
the box. -/
def kinFormB (N : ℕ) (ℓ d s εT b : ℝ) (Φ : X N → ℝ) : ℝ :=
  ℓ ^ (-3 : ℤ) * ∑ i : Fin N,
    ∫ x in abox N ℓ, indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Φ x)

/-- The **box-restricted** box form: this is FS's `H_Λ(μ)` as a form on `L²(Λ^n)`, i.e. the
object whose infimum is `E_Λ(μ)`.  For states supported in `abox n ℓ` it agrees with the
whole-space `boxForm` (which is the object used for the operator-level comparison, where the state
lives in a larger box). -/
def boxFormB (N : ℕ) (v g : ℝ³ → ℝ) (ℓ μ d s εT b : ℝ) (Φ : X N → ℝ) : ℝ :=
  kinFormB N ℓ d s εT b Φ
    + ∫ x in abox N ℓ, (Φ x) ^ 2 * potWordU N v g ℓ μ 0 x

/-- The **chemical-potential part** of the box-restricted form: `−μΣᵢ∫_y w_{1}(xᵢ,y)dy`. -/
def chemPartB (N : ℕ) (g : ℝ³ → ℝ) (ℓ μ : ℝ) (Φ : X N → ℝ) : ℝ :=
  ∫ x in abox N ℓ, (Φ x) ^ 2 * (-μ * ∑ i : Fin N, ∫ y : ℝ³, wLoc ℓ g 0 (x i) y)

/-- The **pair-interaction part** of the box-restricted form: `Σ_{i<j}w(xᵢ,xⱼ)`. -/
def pairPartB (N : ℕ) (v : ℝ³ → ℝ) (ℓ : ℝ) (Φ : X N → ℝ) : ℝ :=
  ∫ x in abox N ℓ, (Φ x) ^ 2 *
    (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, wLoc ℓ v 0 (x ij.1.1) (x ij.1.2))

/-- `boxFormB` splits into its kinetic, chemical and pair parts. -/
def boxFormB_eq_parts (N : ℕ) (v g : ℝ³ → ℝ) (ℓ μ d s εT b : ℝ) (Φ : X N → ℝ) : Prop :=
  boxFormB N v g ℓ μ d s εT b Φ
    = kinFormB N ℓ d s εT b Φ + chemPartB N g ℓ μ Φ + pairPartB N v ℓ Φ

/-! ## 4. The box energy `E_Λ(μ)` (FS `eq:Def_HB2`, free particle number) -/

/-- Symmetric smooth states supported in the centred box `abox n ℓ`: the trial class
of FS's box energy `E_Λ(μ)`.  (`ℓ` is free; `n` is free.) -/
structure SymCSBox (n : ℕ) (ℓ : ℝ) where
  /-- the underlying function -/
  toFun : X n → ℝ
  /-- global smoothness (so that all box integrals and directional derivatives are defined) -/
  contDiff : ContDiff ℝ ∞ toFun
  /-- supported in the centred box `abox n ℓ` -/
  tsupport_subset : tsupport toFun ⊆ abox n ℓ
  /-- bosonic symmetry -/
  symm : PermInvariant n toFun
  /-- nonzero -/
  nezero : toFun ≠ 0

instance (n : ℕ) (ℓ : ℝ) : CoeFun (SymCSBox n ℓ) (fun _ => X n → ℝ) where
  coe Φ := Φ.toFun

/-- The `L²`-norm square of a box state, over the centred box. -/
def sqNormB (n : ℕ) (ℓ : ℝ) (Φ : X n → ℝ) : ℝ := ∫ x in abox n ℓ, (Φ x) ^ 2

/-- **Smooth symmetric box states with no support condition.**  FS's box energy is the infimum
over `L²(Λ)` with no boundary condition on the state, and both `boxForm … 0 ·` and `sqNormB` see
only the *restriction* of the state to `abox n ℓ`; the sector decomposition of the localisation
(C3) produces fibres that are smooth on the box but do not extend to a smooth function compactly
supported *inside* it, so this is the class in which `EΛ` must be taken.  (`SymCSBox` is kept for
the corpus idiom and for the `Word/*` API; `SymCSBox.toBoxState` embeds.) -/
structure BoxState (n : ℕ) (ℓ : ℝ) where
  /-- the underlying function -/
  toFun : X n → ℝ
  /-- global smoothness -/
  contDiff : ContDiff ℝ ∞ toFun
  /-- bosonic symmetry -/
  symm : PermInvariant n toFun
  /-- nonzero -/
  nezero : toFun ≠ 0

instance (n : ℕ) (ℓ : ℝ) : CoeFun (BoxState n ℓ) (fun _ => X n → ℝ) where
  coe Φ := Φ.toFun

/-- The support-restricted class embeds in the relaxed class. -/
def SymCSBox.toBoxState {n : ℕ} {ℓ : ℝ} (Φ : SymCSBox n ℓ) : BoxState n ℓ :=
  { toFun := Φ.toFun, contDiff := Φ.contDiff, symm := Φ.symm, nezero := Φ.nezero }

/-- **FS's box energy `E_Λ(μ) = inf Spec H_Λ(μ)`**, as the infimum of the *box-restricted* box
form `boxFormB` quotients over the **free** particle number `n` and smooth symmetric box states
(the relaxed class `BoxState`, i.e. no support condition — see its docstring).  Both the numerator
(`boxFormB`) and the denominator (`sqNormB`) see only the box restriction, which is what makes the
quotient the genuine box Rayleigh quotient (this is the repair of the `Sector/fibre_bound`
refutation: with the whole-space `boxForm` in the numerator, states vanishing on the box but
non-zero on the "mixed" region make the quotient unbounded below). -/
def EΛ (v g : ℝ³ → ℝ) (ℓ μ d s εT b : ℝ) : ℝ :=
  ⨅ n : ℕ, ⨅ Φ : BoxState n ℓ, boxFormB n v g ℓ μ d s εT b Φ / sqNormB n ℓ Φ

/-- Per-sector box energy (`n` fixed); `EΛ` is its infimum over `n`. -/
def EΛn (n : ℕ) (v g : ℝ³ → ℝ) (ℓ μ d s εT b : ℝ) : ℝ :=
  ⨅ Φ : BoxState n ℓ, boxFormB n v g ℓ μ d s εT b Φ / sqNormB n ℓ Φ

/-! ## 4b. The momentum symbols of the residuals

`fhat` is the `p`-convention Fourier transform of a real test function; the symbols
`raSym` (BS `eq:Neumannineq`), `gapSym` (BS `eq:Quav` / Taylor), `errSym` (the `Cs`
error term of BS `lm:kinloc`) and the Fourier forms built on them are the language in
which the four residuals of `KinLocal.lean` are stated. -/

/-- The `p`-convention Fourier transform of a real one-body state. -/
def fhat (ψ : ℝ³ → ℝ) (p : ℝ³) : ℂ := kinFT (fun z : ℝ³ => (ψ z : ℂ)) p

/-- BS `eq:Neumannineq` symbol: `p²/(p²+(dℓ)⁻²)`. -/
def raSym (ℓ d : ℝ) (p : ℝ³) : ℝ := ‖p‖ ^ 2 / (‖p‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ))

/-- BS `eq:Neumannineq` right-hand side as a quadratic form:
`⟨ψ, (−Δ)(−Δ+(dℓ)⁻²)⁻¹ψ⟩`. -/
def raFrac (ℓ d : ℝ) (ψ : ℝ³ → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, raSym ℓ d p * ‖fhat ψ p‖ ^ 2

/-- BS `eq:Quav`/Taylor symbol for `∫_uQ_udu`: `β⁻¹ℓ²p²/(ℓ²p²+β)`. -/
def gapSym (ℓ β : ℝ) (p : ℝ³) : ℝ :=
  β⁻¹ * ((ℓ ^ 2 * ‖p‖ ^ 2) / (ℓ ^ 2 * ‖p‖ ^ 2 + β))

/-- The `∫_uQ_udu` bound as a quadratic form. -/
def gapFrac (ℓ β : ℝ) (ψ : ℝ³ → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, gapSym ℓ β p * ‖fhat ψ p‖ ^ 2

/-- The `Cs` error symbol of BS `lm:kinloc`: `p²/(p²+β)`. -/
def errSym (β : ℝ) (p : ℝ³) : ℝ := ‖p‖ ^ 2 / (‖p‖ ^ 2 + β)

/-! ## 5. The volume of the localisation region

`Ω = [0,L]³` is the canonical one-particle box; the translation parameters whose
box `Λ(u)` meets `Ω` form `coverU ℓ L`, of volume `(L+ℓ)³/ℓ³` — the audit's
`((L+ℓ)/ℓ)³`. -/

/-- The one-particle box `Ω = [0,L]³`. -/
def ombox (L : ℝ) : Set ℝ³ := {x : ℝ³ | ∀ k : Fin 3, x k ∈ Set.Icc 0 L}

/-- The set of translation parameters `u` whose box `Λ(u)` meets `Ω = [0,L]³`. -/
def coverU (ℓ L : ℝ) : Set ℝ³ := {u : ℝ³ | ∃ x ∈ ombox L, x - ℓ • u ∈ acube ℓ}

/-! ## 6. The parameter regime (FS `eq:BSlidingassp`, and the two tests) -/

/-- FS `eq:BSlidingassp`: the positive parameters `ε_T, d, s, b` are bounded by a
universal constant `c₀`; `ℓ > 0` is free.  This is the regime in which FS
`lem:LocKinEn` holds; `d ≤ 1` is recorded because the two cut-offs are ordered
`½(dsℓ)⁻¹ ≥ ½(sℓ)⁻¹` exactly when `d ≤ 1`. -/
def KinRegime (c₀ ℓ d s εT b : ℝ) : Prop :=
  0 < ℓ ∧ 0 < d ∧ d ≤ c₀ ∧ d ≤ 1 ∧ 0 < s ∧ s ≤ c₀ ∧
    0 < εT ∧ εT ≤ c₀ ∧ 0 < b ∧ b ≤ c₀

/-! ## 7. Basic API -/

lemma fsT_eq_sum (ℓ d s εT b : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    fsT ℓ d s εT b u ψ =
      neuWord ℓ d εT u ψ + gapWord ℓ b u ψ + momWord ℓ d εT b u ψ
        + mainWord ℓ d s εT u ψ := rfl

lemma kinForm_eq (N : ℕ) (ℓ d s εT b : ℝ) (u : ℝ³) (Φ : X N → ℝ) :
    kinForm N ℓ d s εT b u Φ = ∑ i : Fin N, slotForm N (fsT ℓ d s εT b u) ℓ u i Φ := rfl

/-- The bare gap form is nonnegative. -/
lemma gapBare_nonneg (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : 0 ≤ gapBare ℓ u ψ :=
  integral_nonneg fun z => sq_nonneg _

/-- The gap word is nonnegative (`Q_u` is a projection, `b, ℓ > 0`). -/
lemma gapWord_nonneg {ℓ b : ℝ} (hb : 0 ≤ b) (hℓ : 0 ≤ ℓ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    0 ≤ gapWord ℓ b u ψ := by
  unfold gapWord
  have h1 : 0 ≤ b * ℓ ^ (-2 : ℤ) := mul_nonneg hb (zpow_nonneg hℓ _)
  have h2 : 0 ≤ gapBare ℓ u ψ := gapBare_nonneg ℓ u ψ
  exact mul_nonneg h1 h2

/-- The momentum word is nonnegative. -/
lemma momForm_nonneg {ℓ d : ℝ} (u : ℝ³) (ψ : ℝ³ → ℝ) : 0 ≤ momForm ℓ d u ψ := by
  unfold momForm
  refine mul_nonneg (by positivity) (integral_nonneg fun p => ?_)
  exact mul_nonneg (by unfold momProj; split <;> norm_num) (sq_nonneg _)

/-- The momentum word is nonnegative. -/
lemma momWord_nonneg {ℓ d εT b : ℝ} (hb : 0 ≤ b) (hε : 0 ≤ εT) (hdℓ : 0 ≤ d * ℓ)
    (u : ℝ³) (ψ : ℝ³ → ℝ) : 0 ≤ momWord ℓ d εT b u ψ := by
  unfold momWord
  have hcoef : 0 ≤ b * εT * (d * ℓ) ^ (-2 : ℤ) :=
    mul_nonneg (mul_nonneg hb hε) (zpow_nonneg hdℓ _)
  exact mul_nonneg hcoef (momForm_nonneg u ψ)

/-- The main (cut-off) kinetic word is nonnegative when `0 ≤ ε_T ≤ 1`. -/
lemma mainWord_nonneg {ℓ d s εT : ℝ} (hε : 0 ≤ εT) (hε1 : εT ≤ 1) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    0 ≤ mainWord ℓ d s εT u ψ := by
  have h1 : 0 ≤ bsOneBody ℓ (fsKinCoeff ((2 * (s * ℓ))⁻¹)) u ψ :=
    bsOneBody_nonneg (fun r => fsKinCoeff_nonneg _ r) u ψ
  have h2 : 0 ≤ bsOneBody ℓ (fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u ψ :=
    bsOneBody_nonneg (fun r => fsKinCoeff_nonneg _ r) u ψ
  unfold mainWord
  linarith [mul_nonneg (sub_nonneg.mpr hε1) h1, mul_nonneg hε h2]

end Work.BoseKinLoc
