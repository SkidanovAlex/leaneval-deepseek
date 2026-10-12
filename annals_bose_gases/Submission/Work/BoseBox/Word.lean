import ChallengeDeps
import Submission.Work.BoseBox.Basic
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.Word` — the localised box word (`eq:Def_HB`), `E_Λ`, the box theorem, `HBoxG`

This module fixes the objects of FS `thm:LHY-Box` at **decoupled** parameters: the
chemical potential `μ` is a free real variable, the box side is FS's healing-length
side `ℓ = K_ℓ(μa)^{-1/2}`, and the particle number `n` is free.  Nothing here
quantifies over `L ≥ 1` together with `N` (the defect the audit records for the
previous route).

## The word (`eq:DefT`, `eq:Def_HB`)

FS's localised Hamiltonian in the box `Λ(u)` is

    (H_{Λ,u}(μ))_N = Σᵢ 𝒯_u^{(i)} − μ Σᵢ ∫w_{1,u}(xᵢ,y)dy + Σ_{i<j} w_u(xᵢ,xⱼ),

with `𝒯_u` of `eq:DefT`:

    𝒯_u = ½ε_T(dℓ)⁻²(−Δ_u^𝒩)/(−Δ_u^𝒩+(dℓ)⁻²) + bℓ⁻²Q_u
          + bε_T(dℓ)⁻²Q_u1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)Q_u + 𝒯'_u,
    𝒯'_u = Q_uχ_u{(1−ε_T)[√−Δ−(2sℓ)⁻¹]₊² + ε_T[√−Δ−(2dsℓ)⁻¹]₊²}χ_uQ_u.

`tKinWord` is this word in the corpus's vocabulary:

* `tBdiagForm` (`Work.SmallBoxTBWord`) on the box `Λ(u)` (side `ℓ`) for the two spectral halves — the symbol
  `tauSymb ℓ d s ε_T r = (1−ε_T)[r−(2sℓ)⁻¹]₊² + ε_T[r−(2dsℓ)⁻¹]₊²` is FS's, and
  `tBdiagForm` is linear in the symbol, so `𝒯'_u` is one invocation;
* `cnPlusBox` (the corpus's `Q_{B(u)}`-excited count) for the Neumann resolvent
  `(−Δ^𝒩_u)/(−Δ^𝒩_u+(dℓ)⁻²) ≤ 1` and for FS's `bℓ⁻²Q_u` gap;
* `tBdiagForm` with the indicator symbol `highSymb` for the high-momentum term.

The potential part is the corpus's `qLHSword` at FS's *localised* kernels
`w_u(x,y) = χ_u(x)W(x−y)χ_u(y)` (`Submission.BoseGases.wLoc`), so the whole word
is first-quantised and needs no Fock space: `boxWordU` is the `n`-particle
expectation.  Its `u`-integral is FS `lem:LocPotential`
(`Submission.BoseGases.locPotential_pair_sum` / `locPotential_onebody_sum`,
proved).

## The statements

* `EBox` — FS `E_Λ(μ) = inf spec H_Λ(μ)`, as the infimum over `n` and over the
  corpus's trial states `CSBox n ℓ` of the word/norm² quotient;
* `LHYBox` — FS `thm:LHY-Box` (`eq:EnergyBoxRes1`): the per-state bound
  `ℓ³Λ(a v) C η₀ μ ≤ boxWordU …` with the SHARP `128/(15√π)` inside `Lambda`,
  for every `μ` with `μa³` small, every `n` and every state;
* `HBoxG` — the audit's single remaining target: the finite-volume
  LHY-Background at Dirichlet volume, eventually in `L`;
* `PerStateBox` — the per-`(L,N,state)` canonical form of the same bound, i.e.
  the "input to `HBoxG`" that the `C`+`B` route delivers (`G`-reduction);
* `CompareBox` — the `C`-node shape (`thm:CompareBoxEnergy` at the decoupled
  side `ℓ`): the canonical shifted energy of a big-box state dominates the
  localised box energy up to the number of interior boxes.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBox


open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.SmallBoxTBWord
open Work.SmallBoxSliding

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The box side `ℓ = K_ℓ(μa)^{-1/2}` -/

/-- FS `eq:def_ell`: the box side `ℓ = K_ℓ(μa)^{-1/2}` (the healing length times
`K_ℓ`).  This is the *only* place where the box side is tied to the parameters;
the particle number is free. -/
noncomputable def boxSide (P : FSParams) (μ a : ℝ) : ℝ := P.Kl * (μ * a) ^ (-(1 / 2 : ℝ))

lemma boxSide_pos {P : FSParams} {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hKl : 0 < P.Kl) :
    0 < boxSide P μ a :=
  mul_pos hKl (Real.rpow_pos_of_pos (mul_pos hμ ha) _)

/-- **The healing-length identity** `μℓ³ = K_ℓ³(μa)^{-1/2}/a`: the reason FS's
box is "large" (`μℓ³ ≫ 1`) at the decoupled parameters. -/
lemma mu_ell_cube (P : FSParams) (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    μ * boxSide P μ a ^ 3 = P.Kl ^ 3 * (μ * a) ^ (-(1 / 2 : ℝ)) / a := by
  have hμa : 0 < μ * a := mul_pos hμ ha
  have h3 : (μ * a) ^ (-(3 / 2 : ℝ)) = (μ * a) ^ (-(1 / 2 : ℝ)) * (μ * a)⁻¹ := by
    rw [show (-(3 / 2 : ℝ)) = (-(1 / 2 : ℝ)) + (-1) by norm_num, Real.rpow_add hμa,
      Real.rpow_neg_one]
  have hpp : ((μ * a) ^ (-(1 / 2 : ℝ))) ^ 3 = (μ * a) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμa.le]
    norm_num
  dsimp [boxSide]
  rw [mul_pow, hpp, h3, eq_div_iff (ne_of_gt ha)]
  field_simp

/-- `μℓ³` at FS's choice of parameters: `(μa³)^{-166/323}`, the `N = 1`
constant-state test quantity of the audit (it tends to `∞`, so `μℓ³ ≥ 2` for
small diluteness). -/
lemma mu_ell_cube_fsParams {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    μ * boxSide (fsParams (μ * a ^ 3)) μ a ^ 3 = (μ * a ^ 3) ^ (-(166 / 323 : ℝ)) := by
  have hμa : 0 < μ * a := mul_pos hμ ha
  have hμa3 : 0 < μ * a ^ 3 := by positivity
  have ha0 : a ≠ 0 := ne_of_gt ha
  rw [mu_ell_cube (fsParams (μ * a ^ 3)) μ a hμ ha]
  have hKl : (fsParams (μ * a ^ 3)).Kl ^ 3 = (μ * a ^ 3) ^ (-(9 / 646 : ℝ)) := by
    dsimp [fsParams, fsXp]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμa3.le]
    norm_num
  have hμa' : μ * a = μ * a ^ 3 / a ^ 2 := by field_simp
  have hsec : (μ * a) ^ (-(1 / 2 : ℝ)) / a = (μ * a ^ 3) ^ (-(1 / 2 : ℝ)) := by
    rw [hμa']
    rw [Real.div_rpow (by positivity : (0:ℝ) ≤ μ * a ^ 3) (by positivity : (0:ℝ) ≤ a ^ 2)]
    have h1 : (a ^ 2 : ℝ) ^ (-(1 / 2 : ℝ)) = a⁻¹ := by
      rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
      have h2 : (((2 : ℕ) : ℝ) * (-(1 / 2 : ℝ))) = -1 := by norm_num
      rw [h2, Real.rpow_neg_one]
    rw [h1, div_div]
    field_simp
  rw [hKl]
  rw [show (μ * a ^ 3) ^ (-(9 / 646 : ℝ)) * (μ * a) ^ (-(1 / 2 : ℝ)) / a
      = (μ * a ^ 3) ^ (-(9 / 646 : ℝ)) * ((μ * a) ^ (-(1 / 2 : ℝ)) / a) by ring]
  rw [hsec, ← Real.rpow_add hμa3]
  norm_num

/-! ## 2. The FS kinetic word `𝒯_u` (`eq:DefT`, `eq:T'u`)

The word lives on FS's box `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` with the window
`χ_u(x) = χ(x/ℓ − u)` (`eq:Def_chi`), i.e. on the *healing-length* box of side
`ℓ`; the small boxes of side `ℓd` (App. `SmallBoxes`) appear only inside the
a-priori bounds (`B1`), not in the box word. -/

/-- FS's box `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` (`eq:Def_HB`'s `Λ` translated by `u`). -/
def bigBox (ℓ : ℝ) (u : ℝ³) : Set ℝ³ := {x : ℝ³ | x - ℓ • u ∈ acube ℓ}

/-- FS's box window `χ_u(x) = χ(x/ℓ − u)`. -/
noncomputable def chiBig (ℓ : ℝ) (u : ℝ³) (x : ℝ³) : ℝ := chiScale ℓ (x - ℓ • u)

/-- FS `def:tau`: the symbol of the main (large-box) kinetic term,
`τ(k) = (1−ε_T)[|k|−(2sℓ)⁻¹]₊² + ε_T[|k|−(2dsℓ)⁻¹]₊²`. -/
noncomputable def tauSymb (ℓ d s eT r : ℝ) : ℝ :=
  (1 - eT) * fsKinCoeff ((2 * s * ℓ)⁻¹) r + eT * fsKinCoeff ((2 * d * s * ℓ)⁻¹) r

/-- The symbol of FS's high-momentum gap term
`bε_T(dℓ)⁻²Q_u1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)Q_u`. -/
noncomputable def highSymb (ℓ d eT b r : ℝ) : ℝ :=
  if ((d ^ 2 * ℓ)⁻¹ : ℝ) < r then b * eT * (d * ℓ) ^ (-(2 : ℝ)) else 0

/-- **FS `eq:DefT`/`eq:T'u`**: the localised kinetic word `𝒯_u` at scale `ℓ` and
parameters `(d, s, ε_T, b)`, as the `N`-body quadratic form `Σᵢ(𝒯_u)^{(i)}`.

It is the parallel development's `Work.BoseKinLoc.kinForm`, whose four pieces
(`neuWord`, `gapWord`, `momWord`, `mainWord`) are FS's displayed terms.  In
particular the first term is FS's genuine large-box Neumann-resolvent fraction
`(−Δ^𝒩_u)(−Δ^𝒩_u+(dℓ)⁻²)⁻¹` (`Work.BoseKinLoc.neuFrac`), **not** the small-box
constant `½ε_T(1+π⁻²)⁻¹(dℓ)⁻²`: on the lowest Neumann mode of `Λ(u)` the fraction
is `π²d²/(1+π²d²)`, which is `d⁻²`-times *smaller* than that constant, so the
constant is not an upper bound of FS's word and the localisation inequality
`∫_u𝒯_u du ≤ −Δ` (FS `lem:LocKinEn`) fails for it — this was machine-checked
when the chapter carried the constant (see `CNodeDefs.lean`'s history note). -/
noncomputable def tKinWord (n : ℕ) (ℓ d s eT b : ℝ) (u : ℝ³) (Φ : X n → ℝ) : ℝ :=
  Work.BoseKinLoc.kinForm n ℓ d s eT b u Φ

/-- **FS `eq:Def_HB` at scale `ℓ`**: the localised box word
`(H_{Λ,u}(μ))_n = Σᵢ𝒯_u + (−μΣᵢ∫w_{1,u} + Σ_{i<j}w_u)`, i.e. `tKinWord` plus the
corpus's localised FS potential word `qLHSwordB`.

The `u = 0` instance is the box Hamiltonian `H_Λ(μ)` of FS `eq:Def_HB2`, whose
infimum over states is `EBox`. -/
noncomputable def boxWordU (n : ℕ) (ℓ μ d s eT b : ℝ) (v : ℝ³ → ℝ)
    (h : ScatSol v) (u : ℝ³) (Φ : X n → ℝ) : ℝ :=
  tKinWord n ℓ d s eT b u Φ
    + qLHSword (N := n) ℓ μ (Submission.BoseGases.wLoc ℓ v u)
        (Submission.BoseGases.wLoc ℓ (g0 v h) u) Φ

/-- **FS `E_Λ(μ) = inf spec H_Λ(μ)`** at scale `ℓ(μ) = K_ℓ(μa)^{-1/2}`: the
infimum of the box word over the particle number `n` and the corpus trial states
`CSBox n ℓ` (smooth, nonzero, positive centred-box norm).  The particle number is
free — this is the object the box theorem bounds. -/
noncomputable def EBox (P : FSParams) (μ a : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) : ℝ :=
  ⨅ n : ℕ, ⨅ Φ : CSBox n (boxSide P μ a),
    boxWordU n (boxSide P μ a) μ P.d P.s P.eT P.b v h 0 (Φ : X n → ℝ) /
      (∫ x in abox n (boxSide P μ a), ((Φ : X n → ℝ) x) ^ 2)

/-! ## 3. The box theorem (`thm:LHY-Box`) at FS's parameters -/

/-- The parameter block at diluteness `μa³`: FS's `fsParams` fed with the
diluteness of the pair `(μ, a)`.  This is the *only* way the parameters depend on
the chemical potential, and it is the bridge that keeps `μ`, `ℓ` and the
particle number decoupled. -/
noncomputable def paramsAt (μ a : ℝ) : FSParams := fsParams (μ * a ^ 3)

/-- FS's box side at the diluteness-correct parameters: `ℓ = K_ℓ(μa)^{-1/2}`
with `K_ℓ` from `fsParams (μa³)`. -/
noncomputable def sideAt (μ a : ℝ) : ℝ := boxSide (paramsAt μ a) μ a

/-- `E_Λ(μ)` at the parameters `fsParams (μa³)` (the abbreviation the box theorem
and the comparison statement use). -/
noncomputable def EBoxAt (μ a : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) : ℝ :=
  EBox (paramsAt μ a) μ a v h

/-- **FS `thm:LHY-Box`** (`eq:EnergyBoxRes1`) at FS's parameter choice:

there is `ε₀ > 0` such that whenever the diluteness `μa³` is at most `ε₀` (and
the parameter conditions `ParamsOK (fsParams (μa³)) (μa³)` hold — automatic for
small `μa³`, `paramsOK_fsParams`), **every** `n`-particle state `Φ` in the box of
side `ℓ = K_ℓ(μa)^{-1/2}` satisfies

    ℓ³·Λ(a v) C η₀ μ·‖Φ‖² ≤ ⟨Φ, H_Λ(μ)Φ⟩

with `Λ A K η₀ ρ = −4πρ²A(1 − (128/(15√π))√(ρA³) + K(ρA³)^{1/2+η₀})` the SHARP
two-term value and `H_Λ(μ)` the localised box word `boxWordU · 0`.  This is the
mountain of FS §5–11 (`B0`–`B8` decompose it); the particle number `n` is free,
`μ` is fixed, and the box side is tied to `μ`, so the `N = 1` constant-state test
passes (`μℓ³ ≥ 2`). -/
def LHYBox (v : ℝ³ → ℝ) (h : ScatSol v) (η₀ C : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, 0 < μ → μ * (a v) ^ 3 ≤ ε₀ → ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) →
      ∀ n : ℕ, ∀ Φ : CSBox n (sideAt μ (a v)),
        sideAt μ (a v) ^ 3 * Lambda (a v) C η₀ μ *
            (∫ x in abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2)
          ≤ boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
              (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ : X n → ℝ)

/-- **The per-state canonical form of the box bound** — the "input to `HBoxG`"
that the `C` + `B` route delivers (`audit §4 G`): for small `ρ` and all large `L`,
every state of the box `(N,L)` with `N ≤ 2ρL³` has shifted energy at least
`L³·gcTwoTerm(a v) C (1/2+η₀) ρ`, where the shift is the FS chemical-potential
term `8πaρN`. -/
def PerStateBox (v : ℝ³ → ℝ) (η₀ C : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ * (a v) ^ 3 ≤ ε₀ →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ N : ℕ,
        (N : ℝ) ≤ 2 * ρ * L ^ 3 → ∀ Ψ : CInfty0Box N L,
          L ^ 3 * gcTwoTerm (a v) C (1 / 2 + η₀) ρ
            ≤ Rayl N L v Ψ - 8 * π * (a v) * ρ * (N : ℝ)

/-- **The `C`-node shape** (FS `thm:CompareBoxEnergy` at the decoupled side `ℓ`,
`audit §4 C`): for a big-box state `Ψ` of the box `(N,L)`, the canonical shifted
energy at chemical potential `μ` dominates the number of sliding boxes times the
localised box energy (truncated at `0`, which is what the FS proof of
`CompareBoxEnergy` uses for the sign of `E_Λ`).

The factor is `((L + ℓ)/ℓ)³` — the audit's statement verbatim.  FS's localisation
region is the set of `u` with `Λ(u) ∩ Ω ≠ ∅`, whose volume is `(L+ℓ)³/ℓ³`
(FS read `H_Ω(μ) ≥ ∫_{ℓ⁻¹(Ω+B(0,ℓ/2))}(H_{Λ,u}(μ))_N du ≥ ℓ⁻³|Ω+B|E_Λ(μ)`), and
the *boundary loss* `((L+ℓ)/L)³ → 1` is absorbed by the `C`+`B` assembly
`perStateBox_of_LHYBox_compareBox` into the error constant (its `∃L₀` is
`ρ`-dependent, exactly as FS's thermodynamic limit requires).  The smaller factor
`(L/ℓ)³` would be a *stronger* statement than the localisation argument delivers.

The `u`-averaging (`lem:LocKinEn` + `lem:LocPotential`), the sector decomposition
(`C3`) and the support-radius condition `R ≤ ℓ·r₀` are all inside this statement;
it is *not* the content of this chapter, it is the interface that consumes
`LHYBox`.  (The radius condition is automatic for small `μ`, where
`ℓ = K_ℓ(μa)^{-1/2} → ∞`.) -/
def CompareBox (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, ∀ Ψ : CInfty0Box N L,
    ((L + sideAt μ (a v)) / sideAt μ (a v)) ^ 3 * min 0 (EBoxAt μ (a v) v h)
      ≤ Rayl N L v Ψ - 8 * π * (a v) * μ * (N : ℝ)

/-- **`HBoxG`** (the audit's single remaining target, §4 G): the finite-volume
Dirichlet LHY-Background, eventually in `L`, at the FS chemical potential
`μ = 8πaρ` and truncation `ρmax = 2ρ`.  This is exactly the hypothesis `hboxg`
of the closed interface `GCBoxBound.hpres_of_gcTwoTerm`. -/
def HBoxG (v : ℝ³ → ℝ) (η₀ Cw : ℝ) : Prop :=
  ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ ≤ gcDensity v (8 * π * (a v) * ρ) (2 * ρ) L

end Work.BoseBox
