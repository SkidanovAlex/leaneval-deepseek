import ChallengeDeps
import Submission.Work.BoseBox.Nodes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.CNodeDefs` — the `C`-node vocabulary (`thm:CompareBoxEnergy`)

The `C` node of the audit (`BOSE_AUDIT_LEAD.md` §4 C) compares the canonical box
energy of FS `thm:CompareBoxEnergy` with the localised box energy.  This module
fixes the *vocabulary* of that comparison (the audit's `SymBox N L`, `Λ(u)`, the
region of localisation parameters, and the two terms into which the corpus
quotient `Rayl` splits), so that the node's statements can be written in this
chapter's own names.

* `ombox L` — the corner box `[0,L]³`;
* `coverU ℓ L` — the set of `u` with `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` meeting `ombox L`
  (FS's localisation region `ℓ⁻¹(Ω+B(0,ℓ/2))`, of volume `(L+ℓ)³/ℓ³`);
* `kinGradC N L Ψ` — the Dirichlet *gradient* word over the corner box,
  `ΣᵢΣ_k∫_{Ωᴺ}(∂_{ik}Ψ)²` (the integration-by-parts form of the kinetic energy);
* `potIntC N L v Ψ` — the interaction term `(1/2)Σ_{p∈pairSet N}∫_{Ωᴺ}Ψ²v(x_{p.1}−x_{p.2})`
  (the ordered-pair form used by the corpus's localised word `qLHSword`, with the
  `1/2` matching FS's `Σ_{i<j}`);
* the ambient-box words `tKinAmb`/`potAmb`/`boxAmb` (`eq:DefT`, `eq:Def_HB` on the
  sliding box `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³`, with the ambient `x`-integration over the
  corner box `box N L`), and the named inputs of the node `CKinAmb` (`lem:LocKinEn`),
  `CFibreAmb` (the sector/fibre bound), plus the two technical side conditions
  `CWordIntegrable` (the `u`-integrands are integrable on `coverU`) and
  `BoxWordBddBelow` (the box-word family is bounded below, so that `EBoxAt` is a
  genuine infimum).

The identity `Rayl N L v Ψ · ∫Ψ² = kinGradC + potIntC` is the bridge the node
consumes; it is delegated (`BoseBox/rayl_decomp`) and recorded as a statement
ledger in `rayl_decomp.lean`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology

namespace Work.BoseBox


open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.SmallBoxTBWord

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The corner box `[0,L]³ ⊂ ℝ³` (the big box `Ω` of the comparison statement). -/
def ombox (L : ℝ) : Set ℝ³ := {x : ℝ³ | ∀ k : Fin 3, x k ∈ Set.Icc 0 L}

/-- **FS's localisation region**: the set of translation parameters `u` whose box
`Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` meets `Ω = ombox L`.  Its volume is `(L+ℓ)³/ℓ³`
(FS's `ℓ⁻¹(Ω+B(0,ℓ/2))`), which is the origin of the `((L+ℓ)/ℓ)³` factor of
`CompareBox`. -/
def coverU (ℓ L : ℝ) : Set ℝ³ := {u : ℝ³ | ∃ x ∈ ombox L, x - ℓ • u ∈ acube ℓ}

/-- **The Dirichlet gradient word** over the corner box: `ΣᵢΣ_k∫_{Ωᴺ}(∂_{ik}Ψ)²`,
the integration-by-parts form of the kinetic energy of `Ψ`. -/
noncomputable def kinGradC (N : ℕ) (L : ℝ) (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin 3,
    ∫ x in box N L, (fderiv ℝ Ψ x (kcDir N i k)) ^ 2

/-- **The corner-box version of FS's projected spectral form**: `tBdiagFormInd` with the
`x`-integration over the *corner* box `box N L` (the ambient box of `Rayl`, `CInfty0Box`
and `potAmb`), so that the whole `C`-node chain lives in one convention. -/
noncomputable def tBdiagFormIndC (N : ℕ) (L : ℝ) (A : Set ℝ³) (volA : ℝ) (χ : ℝ³ → ℝ)
    (F : ℝ → ℝ) (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : ℝ³, F ‖p‖ *
      ((L ^ 3)⁻¹ * ∫ x in box N L,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)

/-- The corner-box excited count `Σᵢ∫_{box N L}(Q_{B,i}Ψ)²` (the indicator-corrected
`Work.UBBInputs8.cnPlusBoxInd` with the corner ambient box). -/
noncomputable def cnPlusBoxIndC (N : ℕ) (L : ℝ) (A : Set ℝ³) (volA : ℝ) (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in box N L, (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2

/-- **The gradient word over the *centred* box** `abox N L`.  This is the ambient box
over which the corpus's centred `tBdiagForm` integrates (the convention of
`Work.UBBInputs8.tBdiagFormInd`); it is *not* the right-hand side of the `C` node,
whose states live in the corner box `box N L` and whose gradient word is
`kinGradC` — a state of `box N L` need not be supported in `abox N L`
(`cornerState_tsupport_not_subset_abox`), and moving the state by the translation
`c = (L/2,…,L/2)` transports the *right-hand side* only
(`kinGradAbox_translate_eq_kinGradC`).  The definition is kept because that
translation bridge is stated with it. -/
noncomputable def kinGradAbox (N : ℕ) (L : ℝ) (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin 3,
    ∫ x in abox N L, (fderiv ℝ Ψ x (kcDir N i k)) ^ 2

/-- **The interaction term** of the corpus box word, in the ordered-pair form of
`qLHSword`: `(1/2)Σ_{p∈pairSet N}∫_{Ωᴺ}Ψ²·v(x_{p.1}−x_{p.2})` (`= ∫Ψ²Σ_{i<j}v` for
even `v`). -/
noncomputable def potIntC (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Ψ : X N → ℝ) : ℝ :=
  (1 / 2) * ∫ x in box N L,
    (Ψ x) ^ 2 * (∑ p ∈ pairSet N, v (x p.1 - x p.2))

/-- The box norm² of a state. -/
noncomputable def boxSqC (N : ℕ) (L : ℝ) (Ψ : X N → ℝ) : ℝ :=
  ∫ x in box N L, (Ψ x) ^ 2

/-! ## The localised words at an ambient box `Ω = [0,L]³`

`tKinWord`/`boxWordU` of `Word.lean` live on FS's *anchored* box of side `ℓ`
(`u = 0`), which is what `thm:LHY-Box` needs.  The comparison statement
`CompareBox` needs the same words on the *sliding* box `Λ(u)` inside the big box
`Ω`, so the ambient box `L` becomes an explicit parameter (the only change: the
`x`-integration runs over `Ωᴺ` instead of the centred box). -/

/-- **FS `eq:DefT` at the ambient box**: the localised kinetic word `𝒯_u` of the
sliding box `Λ(u)`, as a quadratic form on states of the big box.

It is `Work.BoseBox.tKinWord` (`Word.lean`), i.e. the parallel development's
`Work.BoseKinLoc.kinForm` — the `N`-body lift `Σᵢ(𝒯_u)^{(i)}` of FS's word with
the **genuine** large-box Neumann-resolvent fraction.  The ambient box parameter
`L` is *not used*: the whole-space slot lifting of `Work.BoseKinLoc` already
localises through the indicator `θ_u` inside `fsT`, and for a state supported in
the corner box `box N L` it agrees with the box-restricted form; keeping `L` in
the signature is what lets the `C`-node statements carry the state's box
explicitly. -/
noncomputable def tKinAmb (N : ℕ) (L ℓ d s eT b : ℝ) (u : ℝ³) (Ψ : X N → ℝ) : ℝ :=
  tKinWord N ℓ d s eT b u Ψ

/-- **FS `eq:Def_HB`'s potential part at the ambient box**: the chemical-potential
term `−μΣᵢ∫_{Λ(u)}w_{1,u}(xᵢ,y)dy` plus the sliding pair term `Σ_{i<j}w_u(xᵢ,xⱼ)`,
with the *sliding* fibre integral over `Λ(u)`. -/
noncomputable def potAmb (N : ℕ) (L ℓ μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v)
    (u : ℝ³) (Ψ : X N → ℝ) : ℝ :=
  ∫ x in box N L, (Ψ x) ^ 2 *
    (- μ * (∑ i : Fin N, ∫ y in bigBox ℓ u, wLoc ℓ (g0 v h) u (x i) y)
      + (1 / 2) * (∑ p ∈ pairSet N, wLoc ℓ v u (x p.1) (x p.2)))

/-- **FS `eq:Def_HB` at the ambient box**: `tKinAmb + potAmb`, the localised box
form `⟨Ψ, (H_{Λ,u}(μ))_N Ψ⟩` for a state `Ψ` of the big box. -/
noncomputable def boxAmb (N : ℕ) (L ℓ μ d s eT b : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v)
    (u : ℝ³) (Ψ : X N → ℝ) : ℝ :=
  tKinAmb N L ℓ d s eT b u Ψ + potAmb N L ℓ μ v h u Ψ

/-! ## The named inputs of the `C` node

`CompareBox` is implied by the two inequalities below together with the
identity `rayl_decomp` (`Rayl·‖Ψ‖² = kinGradC + potIntC`), FS `lem:LocPotential`
(the `u`-average of `potAmb` is `potIntC` up to the chemical term — the corpus's
`locPotential_*` and `locPotentialWord_integral_u`) and the volume
`|coverU ℓ L| = (L+ℓ)³/ℓ³` (whence the factor `((L+ℓ)/ℓ)³`).

* `CKinAmb` is FS `lem:LocKinEn` (`∫_u𝒯_u du ≤ −Δ`) read at the *ambient* box and
  restricted to the localisation region `coverU` (the localisation region is
  exactly where the `u`-integrand is supported; the restriction loses nothing).
  The statement lives in the **corner** convention shared by the whole node:
  the states are `Ψ : X N → ℝ` with `tsupport Ψ ⊆ box N L`, the ambient box is
  the corner box `box N L` (via the corner variants `tBdiagFormIndC` /
  `cnPlusBoxIndC`), and the right-hand side is the matching corner-box gradient
  word `kinGradC` (`rayl_decomp`'s ambient convention).  A *centred*-box
  rendering is not instantiable on `CInfty0Box` states
  (`cornerState_tsupport_not_subset_abox`) and translation does not transport
  the word (`kinGradAbox_translate_eq_kinGradC` fixes only the right-hand side).

  The integrability hypothesis is `IntegrableOn … (coverU ℓ L)`, *not* global
  `Integrable`: a prover showed that the corpus's `cnPlusBox`/`boxQ` carry **no
  FS indicator** `θ_u`, so for `Λ(u)` far from the ambient box one has `Q_uΨ = Ψ`
  and the word is bounded below by the positive constant
  `(ε_T/2(1+π⁻²)⁻¹(dℓ)⁻² + bℓ⁻²)·N‖Ψ‖²` outside a bounded set — a non-integrable
  tail (machine-checked: `kinLocAmbient.lean`, `tKinAmb_ge_of_far`).  The
  global-`Integrable` rendering was therefore *vacuous*.  FS's own `Q_u` includes
  the indicator, so the corpus's sliding words differ from FS's off the box (and
  a faithful `C1` wants indicator-corrected words, or the `coverU` restriction
  used here).  The *sharp* measurability/integrability of the `u`-integrand —
  a genuine side condition of any Lean rendering of `∫_u 𝒯_u du`, since the
  `u`-dependence sits inside the `p`-integral of `tBdiagFormIndC` — is the
  separate node `CWordIntegrable` below.

  The regime constant `c₀` carries `1/16 ≤ c₀`, i.e. it accommodates FS's
  **fixed** `b = bValue = 1/16` (`eq:DefT`'s `bℓ⁻²Q_u` gap term): FS apply
  BS Lemma 3.7 at `b = 1/16`, so their universal constant exceeds it, and the
  node must be instantiable at `b = (paramsAt μ (a v)).b = 1/16`.

  It is the analytic heart of the node (Bratteli–Solovej Lemma 3.7 / Thm 3.10 +
  FS's two-region symbol estimates);
* `CFibreAmb` is the *sector/fibre* bound: for each `u`, the localised box form
  dominates the box energy `E_Λ(μ)` times the norm² — FS's "`(H_{Λ,u}(μ))_N` is
  unitarily equivalent to `(H_Λ(μ))_N`, hence `≥ E_Λ(μ)`", pushed through the
  decomposition of a big-box state over the subsets of particles inside `Λ(u)`.

**Caveat (found in the parallel development `Work.BoseKinLoc`)**: `EBoxAt` is an
`⨅` over the free particle number and the trial states, and a Mathlib `sInf` of an
unbounded-below family is the junk value `0`; the guard `BoxWordBddBelow` below
supplies the bounded-belowness of the box-word family (exactly what
`Work.BoseKinLoc.Sector.fibre_bound_v2` carries as a `BddBelow` field). -/
def CKinAmb : Prop :=
  ∃ c₀ : ℝ, 1 / 16 ≤ c₀ ∧
    ∀ (N : ℕ) (L ℓ d s eT b : ℝ), 0 < L → 0 < ℓ →
      0 < d → d ≤ c₀ → d ≤ 1 → 0 < s → s ≤ c₀ → 0 < eT → eT ≤ c₀ → 0 < b → b ≤ c₀ →
      ∀ Ψ : X N → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ box N L →
        IntegrableOn (fun u : ℝ³ => tKinAmb N L ℓ d s eT b u Ψ) (coverU ℓ L) →
          (∫ u in coverU ℓ L, tKinAmb N L ℓ d s eT b u Ψ) ≤ kinGradC N L Ψ

/-- **`C3` — the fibre bound** at FS's parameters: for every localisation
parameter `u` in the region and every state `Ψ` of the big box, the localised box
form dominates the box energy times the norm².

The hypothesis `∃ c, ∀ n Φ, c ≤ boxWordU … / norm²` (a *uniform* lower bound for the
box-word family at the scale `ℓ(μ)`) is **required**: `EBoxAt = ⨅ n, ⨅ Φ, …` is an
`⨅` whose Mathlib value is the junk `0` when the family is unbounded below, and
`min 0` does not guard against that (`EBox_le_zero` gives `E_Λ ≤ 0` regardless, so
`min 0 E_Λ = E_Λ` always).  This is the finding of the parallel development
(`Work.BoseKinLoc.Sector.not_boxForm_ge_boxEnergy`, `fibre_bound_v2`'s `BddBelow`
fields). -/
def CFibreAmb (v : ℝ³ → ℝ) (h : ScatSol v) : Prop :=
  ∀ (μ : ℝ), 0 < μ → ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) →
    (∃ c : ℝ, ∀ (n : ℕ) (Φ : CSBox n (sideAt μ (a v))),
        c ≤ boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
              (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ : X n → ℝ)
            / norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)) →
    ∀ (N : ℕ) (L : ℝ), 1 ≤ L →
      ∀ Ψ : X N → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ box N L →
        ∀ u ∈ coverU (sideAt μ (a v)) L,
          min 0 (EBoxAt μ (a v) v h) * boxSqC N L Ψ
            ≤ boxAmb N L (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
                (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h u Ψ

/-! ## The two technical side conditions of the `C` node

Both are *eventual in `μ`* statements at FS's parameters, and both are
faithfulness (not mathematics) side conditions of the Lean rendering: the first
says that the two localised words are integrable functions of the translation
parameter `u` (so that the `u`-averages of the node are ordinary Bochner
integrals), the second that the box-word family is bounded below (so that
`EBoxAt = ⨅ n ⨅ Φ …` is a genuine infimum and not the junk value `0`). -/

/-- **`C0` — integrability of the localised words as functions of `u`.**  At FS's
parameters and for small `μ`, for every `N`, every `L ≥ 1` and every smooth
`Ψ` supported in the corner box `box N L`, both the localised kinetic word
`tKinAmb` and the localised potential word `potAmb` are integrable on the
localisation region `coverU (sideAt μ (a v)) L`.

This is a *measurability/finiteness* statement, not an inequality: the words
integrate over `p` (spectral form) and over `x` (ambient box), and their
`u`-dependence enters through the sliding box `Λ(u) = bigBox ℓ u` and its window
`chiBig ℓ u`; `coverU` is a bounded region (of volume `((L+ℓ)/ℓ)³`), so
integrability is a bound on the word over a bounded set of `u`.  It is the
side condition under which the `u`-averages of `CKinAmb` and of `potAmb_integral`
can be added — `∫_u (tKinAmb + potAmb) = ∫_u tKinAmb + ∫_u potAmb`. -/
def CWordIntegrable (v : ℝ³ → ℝ) (h : ScatSol v) : Prop :=
  ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ (N : ℕ) (L : ℝ), 1 ≤ L →
    ∀ Ψ : X N → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ box N L →
      (IntegrableOn (fun u : ℝ³ =>
          tKinAmb N L (sideAt μ (a v)) (paramsAt μ (a v)).d (paramsAt μ (a v)).s
            (paramsAt μ (a v)).eT (paramsAt μ (a v)).b u Ψ)
        (coverU (sideAt μ (a v)) L))
      ∧ (IntegrableOn (fun u : ℝ³ => potAmb N L (sideAt μ (a v)) μ v h u Ψ)
        (coverU (sideAt μ (a v)) L))

/-- **`C3b` — the box-word family is bounded below.**  At FS's parameters and for
small `μ`, the quotients `boxWordU n ℓ(μ) … Φ / ‖Φ‖²` of the box words are
uniformly bounded below over the free particle number `n` and the trial states
`Φ : CSBox n (sideAt μ (a v))`.

This is what makes `EBoxAt = ⨅ n, ⨅ Φ, …` a genuine infimum: an `⨅` of an
unbounded-below family is the junk value `0` in Mathlib, and `min 0` does not
repair that (`EBox_le_zero` gives `E_Λ ≤ 0` regardless).  It is the guard that
`CFibreAmb` carries as an explicit hypothesis and that the `C`-node assembly
consumes. -/
def BoxWordBddBelow (v : ℝ³ → ℝ) (h : ScatSol v) : Prop :=
  ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∃ c : ℝ,
    ∀ (n : ℕ) (Φ : CSBox n (sideAt μ (a v))),
      c ≤ boxWordU n (sideAt μ (a v)) μ (paramsAt μ (a v)).d (paramsAt μ (a v)).s
            (paramsAt μ (a v)).eT (paramsAt μ (a v)).b v h 0 (Φ : X n → ℝ)
          / norm2N n (sideAt μ (a v)) (Φ : X n → ℝ)

end Work.BoseBox
