import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.paramsAt_facts
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.Defs` — the a-priori chapter (FS §5 + Appendix `SmallBoxes`)

Subproject `Work.BoseFixB1` (node D5 of `BOSE_BOXNODES_LEAD.md` §4): the
**a-priori bounds** `NodeB1B` of FS `thm:aprioribounds`, on the box-restricted
symmetric states of the frozen vocabulary `Work.BoseBoxFix`
(`wordB`/`normB`/`IsLowB`/`Adm` over `Work.BoseKinLoc.BoxState`), at FS's
parameters `paramsAt μ (a v)`, `sideAt μ (a v)`.

Everything here is **`sorry`-free**.  The chapter's mathematical content lives
in the *interface propositions* of §4 and the lemmas about them, each of which
is dispatched as a separate lemma request (see `Design.md` for the ledger and
the FS mapping).

## The two interface propositions

FS `thm:aprioriHLambda` says that a low state satisfies
`⟨H_Λ(μ)⟩ ≥ −4πμ²aℓ³(1+C K_B³(μa³)^{1/2}) + (b/2ℓ²)⟨n₊⟩ + R_Ψ`, with `R_Ψ ≥ 0`
the `u`-integral remainder of the second localisation.  We record this as

* `AprioriHLambdaIneq` — the per-state inequality above, in the frozen
  vocabulary (`wordB` on the right, `cnPlus` and the state-level `RPsiB` on the
  left), homogeneous in the state (no normalisation hypothesis);

and the Cauchy–Schwarz/Jensen passage from `R_Ψ` to the particle window as

* `WindowBridge` — `|n − μℓ³| ≤ √(8πaℓ³)·√(R_Ψ/(c₁‖Φ‖²))`.

`Bridge.nodeB1B_of_pieces` derives `NodeB1B` from these two (`+ 0 < a v`), and
*is the whole point of the chapter*: `NodeB1B`'s two windows are then exactly
`nWindow` and `nPlusWindow` at FS's parameters.

## Why the state-level `R_Ψ`

FS's `R_Ψ = ⟨Ψ, (∫_{I₋} F(n(u)/|B(u)|)∬w_{1,B(u)} du)Ψ⟩` is a *quadratic form*
on `L²(Λ^n)`; `n(u) = Σᵢ1_{B(u)}(xᵢ)` is a multiplication operator, so the
expectation is the configuration integral of `|Ψ|²` times `F(n(u)(x)/|B(u)|)`.
`RPsiB` below is that expression written out, with the corpus's smooth
small-box cutoff `chiSmallB` in place of the indicator (the corpus convention of
`Work.SmallBoxSliding`, whose `R_Psi` is the same object at the density level).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Admission, and the elementary facts about FS's parameters

`Adm v ε₀ μ` is `0 < μ ∧ μ(a v)³ ≤ ε₀ ∧ ParamsOK (paramsAt μ (a v)) (μ(a v)³)`.
The elementary consequences of `ParamsOK` (`paramsAt_facts`) are what every
statement of this chapter uses. -/

/-- The chemical potential of an admissible point is positive. -/
lemma adm_mu_pos {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) : 0 < μ := h.1

/-- The diluteness of an admissible point. -/
lemma adm_dilute {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) : μ * (a v) ^ 3 ≤ ε₀ := h.2.1

/-- The FS parameter conditions of an admissible point. -/
lemma adm_paramsOK {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) :
    ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) := h.2.2

/-- `Adm` is monotone in the smallness threshold. -/
lemma Adm.mono {v : ℝ³ → ℝ} {ε₀ ε₀' μ : ℝ} (h : Adm v ε₀' μ) (hle : ε₀' ≤ ε₀) :
    Adm v ε₀ μ :=
  ⟨h.1, le_trans h.2.1 hle, h.2.2⟩

/-- `paramsAt μ a` **is** `fsParams (μa³)`. -/
lemma paramsAt_eq_fsParams (μ a : ℝ) : paramsAt μ a = fsParams (μ * a ^ 3) := rfl

/-- The box side **is** `K_ℓ (μa)^{-1/2}`. -/
lemma sideAt_eq (μ a : ℝ) :
    sideAt μ a = (paramsAt μ a).Kl * (μ * a) ^ (-(1 / 2 : ℝ)) := rfl

/-- The scattering length is positive at an admissible point (forced by FS
`sec:params`: `con:sKell` and `con:KellKLd` cannot hold with `a ≤ 0`). -/
lemma adm_a_pos {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) : 0 < a v :=
  (paramsAt_facts h.1 h.2.2).1

/-- The diluteness is at most one at an admissible point. -/
lemma adm_dilute_le_one {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) (hε : ε₀ ≤ 1) :
    μ * (a v) ^ 3 ≤ 1 := le_trans h.2.1 hε

/-- FS's small dimensionless parameters are positive at an admissible point. -/
lemma adm_d_pos {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) : 0 < (paramsAt μ (a v)).d :=
  (paramsAt_facts h.1 h.2.2).2.1

/-- FS's `s` is positive at an admissible point. -/
lemma adm_s_pos {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) : 0 < (paramsAt μ (a v)).s :=
  (paramsAt_facts h.1 h.2.2).2.2.1

/-- FS's `ε_T` lies in `[0,1]` at an admissible point. -/
lemma adm_eT_bounds {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) :
    0 ≤ (paramsAt μ (a v)).eT ∧ (paramsAt μ (a v)).eT ≤ 1 :=
  ⟨(paramsAt_facts h.1 h.2.2).2.2.2.1, (paramsAt_facts h.1 h.2.2).2.2.2.2.1⟩

/-- FS's `b` is nonnegative at an admissible point. -/
lemma adm_b_nonneg {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) : 0 ≤ (paramsAt μ (a v)).b :=
  (paramsAt_facts h.1 h.2.2).2.2.2.2.2.1

/-- `K_ℓ` is positive at an admissible point. -/
lemma adm_Kl_pos {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) : 0 < (paramsAt μ (a v)).Kl :=
  (paramsAt_facts h.1 h.2.2).2.2.2.2.2.2

/-- The box side is positive at an admissible point. -/
lemma adm_ell_pos {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) : 0 < sideAt μ (a v) := by
  rw [sideAt_eq]
  exact mul_pos (adm_Kl_pos h)
    (Real.rpow_pos_of_pos (mul_pos (adm_mu_pos h) (adm_a_pos h)) _)

/-- FS's gap coefficient `b` is `bValue = 1/16 > 0` (it is a *fixed* universal
constant, not a parameter dependent on `μ`). -/
lemma paramsAt_b_eq (μ a : ℝ) : (paramsAt μ a).b = bValue := rfl

/-- `b > 0` at every parameter point. -/
lemma paramsAt_b_pos (μ a : ℝ) : 0 < (paramsAt μ a).b := by
  rw [paramsAt_b_eq]; norm_num [bValue]

/-- `K_B > 0`. -/
lemma paramsAt_KB_pos {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) : 0 < (paramsAt μ (a v)).KB := by
  rw [paramsAt_eq_fsParams]
  exact fsXp_pos (t := μ * (a v) ^ 3) (c := -(6 : ℝ))
    (mul_pos h.1 (pow_pos (adm_a_pos h) 3))

/-- `1 ≤ K_B` at an admissible point (i.e. for `μa³ ≤ 1`). -/
lemma one_le_KB {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (ht : μ * a ^ 3 ≤ 1) :
    1 ≤ (paramsAt μ a).KB := by
  rw [paramsAt_eq_fsParams]
  have ht0 : 0 < μ * a ^ 3 := mul_pos hμ (pow_pos ha 3)
  have h := fsXp_le_fsXp (t := μ * a ^ 3) (a := (0 : ℝ)) (b := -(6 : ℝ)) ht0 ht
    (by norm_num)
  simpa [fsParams, fsXp] using h

/-- `1 ≤ K_ℓ` at an admissible point.  This is the only place where the
*sign* of `K_ℓ`'s exponent is used. -/
lemma one_le_Kl {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (ht : μ * a ^ 3 ≤ 1) :
    1 ≤ (paramsAt μ a).Kl := by
  rw [paramsAt_eq_fsParams]
  have ht0 : 0 < μ * a ^ 3 := mul_pos hμ (pow_pos ha 3)
  have h := fsXp_le_fsXp (t := μ * a ^ 3) (a := (0 : ℝ)) (b := -(3 / 2 : ℝ)) ht0 ht
    (by norm_num)
  simpa [fsParams, fsXp] using h

/-! ## 1. The two windows, in FS's own shape

`nWindow`/`nPlusWindow` (`Work.BoseBox.Nodes`) are *defined* as FS's
`eq:apriorinn+` right-hand sides; the two lemmas below record the
`sideAt`-form used by the chapter. -/

/-- FS `eq:apriorinn+`, first window, at `ℓ = sideAt μ (a v)`:
`μ ℓ³ K_B^{3/2} K_ℓ (μa³)^{1/4}`. -/
lemma nWindow_eq (μ a : ℝ) :
    nWindow (paramsAt μ a) μ a
      = μ * sideAt μ a ^ 3 * (paramsAt μ a).KB ^ (3 / 2 : ℝ) * (paramsAt μ a).Kl
          * (μ * a ^ 3) ^ (1 / 4 : ℝ) := rfl

/-- FS `eq:apriorinn+`, second window, at `ℓ = sideAt μ (a v)`:
`μ ℓ³ K_B³ K_ℓ² (μa³)^{1/2}`. -/
lemma nPlusWindow_eq (μ a : ℝ) :
    nPlusWindow (paramsAt μ a) μ a
      = μ * sideAt μ a ^ 3 * (paramsAt μ a).KB ^ 3 * (paramsAt μ a).Kl ^ 2
          * (μ * a ^ 3) ^ (1 / 2 : ℝ) := rfl

/-- `μ · a · ℓ² = K_ℓ²` at FS's box side: the *only* identity used to convert
between FS's `K_ℓ`-bookkeeping and the physical scales `μ, a, ℓ`. -/
lemma mu_mul_a_mul_ell_sq (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    μ * a * sideAt μ a ^ 2 = (paramsAt μ a).Kl ^ 2 := by
  rw [sideAt_eq]
  have hμa : 0 < μ * a := mul_pos hμ ha
  have h1 : ((μ * a) ^ (-(1 / 2 : ℝ))) ^ 2 = (μ * a)⁻¹ := by
    rw [sq, ← Real.rpow_add hμa, ← Real.rpow_neg_one]
    norm_num
  rw [mul_pow, h1]
  field_simp

/-- `ℓ³ > 0` at an admissible point. -/
lemma ell_cube_pos {v : ℝ³ → ℝ} {ε₀ μ : ℝ} (h : Adm v ε₀ μ) :
    0 < sideAt μ (a v) ^ 3 := pow_pos (adm_ell_pos h) 3

/-- FS's threshold `Θ` at the box side: `ℓ³ Θ (a v) J μ = −4πμ²(a v)ℓ³(1−J√(μa³))`. -/
lemma ell_cube_theta {v : ℝ³ → ℝ} {J μ : ℝ} (hav : 0 < a v) :
    sideAt μ (a v) ^ 3 * Theta (a v) J μ
      = -(4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
            * (1 - J * Real.sqrt (μ * (a v) ^ 3))) := by
  rw [Theta, Real.sqrt_eq_rpow]
  ring

/-- `‖Φ‖² ≥ 0` — `normB` is the integral of a square. -/
lemma normB_nonneg {v : ℝ³ → ℝ} {μ : ℝ} {n : ℕ} (Φ : X n → ℝ) :
    0 ≤ normB v μ n Φ :=
  integral_nonneg fun x => sq_nonneg _

/-- `IsLowB` unfolded into the threshold form used in the proofs. -/
lemma isLowB_iff {v : ℝ³ → ℝ} {h : ScatSol v} {J μ : ℝ} {n : ℕ} {Φ : X n → ℝ}
    (hav : 0 < a v) :
    IsLowB v h J μ n Φ ↔
      wordB v h μ n Φ
        ≤ -(4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
              * (1 - J * Real.sqrt (μ * (a v) ^ 3))) * normB v μ n Φ := by
  rw [IsLowB, ell_cube_theta (J := J) (μ := μ) hav]

/-! ## 2. The state-level remainder `R_Ψ` of the second localisation

FS localise further into the boxes `B(u) = Λ ∩ ((ℓd)•u + [−ℓd/2,ℓd/2]³)` and
split off the nonnegative remainder

`R_Ψ = ⟨Ψ, ∫_{I₋} F(n(u)/|B(u)|) ∬w_{1,B(u)} du Ψ⟩`,  `F(t) = c(t−μ)²/(1+tμ⁻¹)`.

`RPsiB` below is the configuration-level integral of that quadratic form, with
the corpus's smooth small-box cutoff `chiSmallB` (`Work.SmallBoxSliding`). -/

/-- The per-configuration small-box particle count `Σᵢ χ_{B(u)}(xᵢ)²`
(the smooth surrogate for FS's `n(u) = Σᵢ1_{B(u)}(xᵢ)`). -/
def nCountB (M : ℕ) (ℓ d : ℝ) (u : ℝ³) {n : ℕ} (x : X n) : ℝ :=
  ∑ i : Fin n, (chiSmallB M ℓ d u (x i)) ^ 2

/-- FS's per-box mass `∬w_{1,B(u)}` as a function of `u` alone. -/
def w1MassB {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (ℓ d : ℝ) (u : ℝ³) : ℝ :=
  ∫ x : ℝ³, ∫ y : ℝ³, wSmall1Pair h M ℓ d u x y

/-- **FS's `R_Ψ`** at the state level, in the corpus's smooth-cutoff
convention: the configuration integral of `|Φ|²` against
`F(n(u)/|B(u)|)∬w_{1,B(u)}`, integrated over the `m(u) = 1` set `I₋`.

**The `|B(u)|` of the smooth model is the `χ_B²`-mass `chiMass M ℓ d u`, not the
nominal volume `(ℓd)³`.**  The count `nCountB u x = Σᵢχ_{B(u)}(xᵢ)²` is the
smooth surrogate of FS's sharp count `Σᵢ1_{B(u)}(xᵢ)`, and the normalisation
that makes FS's `U`-argument work (`∫_Λ U = 1`, hence
`P_ΛUP_Λ = ℓ⁻³P_Λ` and `Σᵢ(P_ΛUP_Λ)ᵢ = (n − n₊)ℓ⁻³`) is the *Λ-mass* of the
cut-off: with `U(z) = C⁻¹∫_{I₋}(∬w_{1,B(u)})/|B(u)|·χ_B(z)²du` one has
`∫_Λ U = C⁻¹∫_{I₋}∬w_{1,B(u)}du = 1` for `|B(u)| := ∫χ_B² = chiMass M ℓ d u`,
whereas using the nominal volume `(ℓd)³` leaves a non-constant weight
(`chiMass/(ℓd)³` has *u*-mean `1` but `w_{1,B}`-weighted mean `∫χ⁴/∫χ² > 1`),
which breaks the identity and the window. -/
def RPsiB {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (c μ : ℝ) (ℓ d : ℝ)
    {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  ∫ u in interiorSet ℓ d μ, w1MassB h M ℓ d u *
    (∫ x in abox n ℓ, (Φ x) ^ 2 * psiWeight c μ (nCountB M ℓ d u x / chiMass M ℓ d u))

/-- The chapter's `R_Ψ` at FS's small-box parameters: `M` and `d` from the
parameter block, `c = 1` (the convexity constant of `psiWeight` is absorbed
into the multiplicative constants). -/
abbrev RPsi (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  RPsiB h (paramsAt μ (a v)).M 1 μ (sideAt μ (a v)) (paramsAt μ (a v)).d Φ

/-! ## 3. The two interface propositions

Both are *per-state, at FS's parameters*, on the frozen vocabulary.  They are
the two halves of FS §5 + Appendix `SmallBoxes` that the chapter must supply. -/

/-- **FS `eq:aprioriRn+`** — the two a-priori bounds of FS's
`thm:aprioriHLambda` (the Appendix `SmallBoxes` output).

There are a universal constant `C ≥ 1` and a smallness threshold `ε₀ > 0` such
that whenever `μ` is admissible (`0 < μ`, `μ(a v)³ ≤ ε₀`, FS's parameter
conditions) and `J ≤ K_B³`, *every* low box state (`IsLowB`, FS
`eq:aprioriPsi`) satisfies the two bounds

* `0 ≤ R_Ψ` and `R_Ψ ≤ C μ²(a v)ℓ³ K_B³ (μ(a v)³)^{1/2}‖Φ‖²`,
* `(b/2ℓ²)⟨n₊⟩ ≤ C μ²(a v)ℓ³ K_B³ (μ(a v)³)^{1/2}‖Φ‖²`,

`R_Ψ` being FS's `u`-integral remainder (`RPsiB`), `⟨n₊⟩` the corpus `cnPlus ℓ`
and `b = bValue` FS's gap coefficient.  These are exactly FS's
`eq:aprioriRn+` (note `μ(a v)ℓ² = K_ℓ²`, so both right-hand sides are also
`C μℓ³K_B³K_ℓ²(μa³)^{1/2}`), with a free universal constant — all constants in
this chapter are free (see the design note).

The bounds are homogeneous in `Φ`, so no normalisation hypothesis is needed.
This is the *output* of the Appendix: the sliding localisation
(FS `eq:aprioriPsi` ⟹ `eq:appsliding`), the per-small-box bound
(FS `thm:smallbox`), the group decomposition and the `u`-bookkeeping. -/
def AprioriHLambdaIneq (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ C ε₀ : ℝ, 1 ≤ C ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      IsLowB v h J μ n Φ →
        0 ≤ RPsi v h μ Φ ∧
        RPsi v h μ Φ ≤ C * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
              * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
              * normB v μ n Φ ∧
        ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
              * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ C * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
              * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
              * normB v μ n Φ

/-- **FS `thm:aprioriHLambda`, step 4: the particle window.**

There is a universal `C` and a smallness threshold `ε₀` such that for every
admissible `μ` with `J ≤ K_B³`, every particle number `n` and every *low* box
state (`IsLowB`, FS `eq:aprioriPsi`),

`|n − μℓ³| ≤ C · nWindow (paramsAt μ (a v)) μ (a v)`,

i.e. `|n/ℓ³ − μ| ≤ C μ K_B^{3/2}K_ℓ(μa³)^{1/4}` — FS `eq:apriorinn+`'s first
inequality (with a free universal constant).

This is FS's *separate* step 4 in the proof of `thm:aprioriHLambda`: the `R_Ψ`
bound of `AprioriHLambdaIneq` gives, through the convexity of `F` (Jensen) and
one Cauchy–Schwarz,
`|C⁻¹∫_{I₋}(n(u)/|B(u)|)∬w_{1,B(u)}du − μ| ≤ √(R_Ψ/(C c₁))` with
`C = ∫_{I₋}∬w_{1,B(u)} ≥ 8π(a v)ℓ³(1−o(1))` (FS `eq:appw1sliding`); the
state-count bridge `ΣᵢU(xᵢ) ↔ n/ℓ³` (FS's `U`, `P_ΛUP_Λ = ℓ⁻³`,
`U ≤ Cℓ⁻³`, FS `eq:aprioriU`) with the `ε`-split at
`ε = K_B^{3/2}K_ℓ(μa³)^{1/4}` turns that into the window — the `n₊`-part of
the split being *exactly* the `cnPlus` bound of `AprioriHLambdaIneq`.

The hypothesis `0 < normB v μ n Φ` is **not** redundant: `Work.BoseKinLoc.BoxState`
carries no support condition, and a state vanishing on the configuration box
(`normB = 0`, hence `wordB = 0` and `IsLowB` trivially) would otherwise satisfy
`IsLowB` at *every* particle number, making the window false
(`Work.BoseFixB1.not_windowBridge_holds`).  The frozen `NodeB1B` carries the same
hypothesis, so the consumer `nodeB1B_of_pieces` supplies it.

`windowBridge_of_apriori` records the intended dependency
(`AprioriHLambdaIneq v h J → WindowBridge v h J`). -/
def WindowBridge (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      0 < normB v μ n Φ → IsLowB v h J μ n Φ →
        |(n : ℝ) - μ * sideAt μ (a v) ^ 3|
          ≤ C * nWindow (paramsAt μ (a v)) μ (a v)


/-! ## 4. FS's second localisation: the small-box family `B(u)` at FS parameters

FS `eq:BSsliding2` (Bratteli–Solovej Thm 3.10) localises the large-box
Hamiltonian `H_Λ(μ)` over the small boxes
`B(u) = Λ ∩ ((ℓd)•u + [−ℓd/2,ℓd/2]³)`: the *per-box* word of
`Work.SmallBoxTBWord` (`tBwordB`, `qLHSwordB` at the corpus cut-off `chiB`), with
the box side `dℓ`, the gap coefficient `ε_T` and the spectral cut-off
`(dsℓ)⁻¹` — exactly FS `eq:appTB` / `eq:HBU`.

The two definitions below instantiate those objects at FS's parameters
(`d`, `s`, `ε_T` from `paramsAt μ (a v)`, box side `ℓ = sideAt μ (a v)`), so
that `SlidingB` can be stated in the frozen vocabulary (`wordB`, `cnPlus`). -/

/-- The small-box side `dℓ` at FS's parameters. -/
def sbSide (μ : ℝ) (a : ℝ) : ℝ := (paramsAt μ a).d * sideAt μ a

/-- FS's spectral cut-off `(dsℓ)⁻¹` of the small-box kinetic `eq:appTB`. -/
def sbCut (μ : ℝ) (a : ℝ) : ℝ := ((paramsAt μ a).d * (paramsAt μ a).s * sideAt μ a)⁻¹

/-- **FS `eq:appTB`**: the small-box kinetic word `𝒯_{B(u)}` at FS's parameters
(the gap coefficient `ε_T` and the cut-off `(dsℓ)⁻¹`), with **FS's own box
projection** `Q_{B(u)} = 1_{B(u)} − P_{B(u)}`.

The box indicator matters: FS's `B(u) = Λ(0) ∩ ((ℓd)•u + [−ℓd/2,ℓd/2]³)` is
*empty* for `u` far away, and FS's `H_{B(u)}(μ)` is then the zero operator.  The
corpus's indicator-free `Work.SmallBoxTBWord.tBwordB` instead has `Q_B = 1` on
the far set, so its gap term is a positive constant there and the `u`-integrand
is *not* integrable (Mathlib returns the junk value `0`), which refutes any
sliding inequality stated with it (`Work.UBBInputs8.A.not_integrable_tBwordB_const`,
`Work.UBBInputs7.Finding`).  `sbKin` therefore uses the FS-faithful repair
`Work.UBBInputs8.tBwordBInd`, whose integrand vanishes identically outside the
box (`Work.UBBInputs8.A.tBwordBInd_const_zero`). -/
def sbKin {v : ℝ³ → ℝ} (μ : ℝ) (M : ℕ) (u : ℝ³) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  Work.UBBInputs8.tBwordBInd n (sideAt μ (a v)) (paramsAt μ (a v)).d
    (paramsAt μ (a v)).eT (sbCut μ (a v)) u Φ

/-- The small-box **potential** word of FS `eq:HBU` at FS's parameters: the
corpus `qLHSwordB` at the localised kernels `w_{B(u)}`, `w_{1,B(u)}`. -/
def sbPot {v : ℝ³ → ℝ} (h : ScatSol v) (μ : ℝ) {n : ℕ} (u : ℝ³)
    (Φ : X n → ℝ) : ℝ :=
  qLHSwordB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ u Φ

/-- The per-`u` small-box energy word `H_{B(u)}(μ)` (FS `eq:HBU`). -/
def sbWord {v : ℝ³ → ℝ} (h : ScatSol v) (μ : ℝ) {n : ℕ} (u : ℝ³)
    (Φ : X n → ℝ) : ℝ :=
  sbKin (v := v) μ (paramsAt μ (a v)).M u Φ + sbPot h μ u Φ

/-- **FS `eq:BSsliding2`** (Bratteli–Solovej Thm 3.10) at FS's parameters, in
the frozen vocabulary: the large-box form `boxFormB` dominates the large-box
kinetic gap plus the `u`-integral of the small-box forms `H_{B(u)}(μ)`.

`wordB` is FS's `H_Λ(μ)` (`Work.BoseKinLoc.boxFormB` at `u = 0`), `cnPlus ℓ` is
FS's `⟨n₊⟩ = Σᵢ⟨Q_{Λ,i}⟩` for the large box `Λ = acube ℓ`, and the integrand
`sbWord` is FS's small-box word (`eq:appTB` + `eq:HBU`) at the small boxes
`B(u)` of side `dℓ = sbSide`, with the localised kernels of `lem:LocPotential`.
The multiplicative constant `C ≥ 1` in front of the integral is free (all
constants of this chapter are free; `C = 1` is FS's claim).

The *state* is unrestricted: this is the operator inequality (both sides are
quadratic forms), which is why the constant-state test (`n = 1`, `Φ ≡ 1`, both
sides `= −4πμ²aℓ³`) is consistent. -/
def SlidingB (v : ℝ³ → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 1 ≤ C ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
          * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        + (1 / C) * ∫ u : ℝ³, sbWord h μ u (Φ : X n → ℝ)
      ≤ wordB v h μ n Φ


/-- **FS `thm:smallbox` integrated over the small boxes** — the per-box half of
`thm:aprioriHLambda`.

There are `ε₀ > 0` and `C ≥ 0` such that for admissible `μ` with `J ≤ K_B³` and
every low box state,

`0 ≤ R_Ψ` and
`R_Ψ ≤ ∫_{ℝ³} H_{B(u)}(μ)(Φ) du + 4πμ²(a v)ℓ³(1 + C K_B³(μa³)^{1/2})‖Φ‖²`,

the integrand being FS's small-box word `sbWord` (kinetic `eq:appTB` plus
potential `eq:HBU` at the localised kernels).

The proof is FS's: on the good set `G = {‖(ℓd)•u‖_∞ ≤ ½ℓ(1+d) − μ^{-1/3}}`
every small box has shortest side `λ₁(u) ≥ μ^{-1/3}`, so `thm:smallbox` applies
box by box; integrating `∬w_{1,B(u)} ≈ 8π(a v)|B(u)|` against `F(n(u)/|B(u)|)`
over `I₋` produces `R_Ψ`, the total mass `∫_{I₋}∬w_{1,B(u)}du ≈ 8π(a v)ℓ³`
(FS `eq:appw1sliding`) produces the background `4πμ²aℓ³`, and the discarded
sets `Gᶜ` and the `μ ↦ 4μ` band `G ∖ I₋` are paid for by the `χ_B`-mass law
(FS `eq:badset`); both losses (`Cμ²a(μa³)^{M/3}ℓ³` and `Cμad^{-3}`) are
`≤ Cμ²aℓ³K_B³(μa³)^{1/2}` at FS's parameters for `μa³` small, and the
`u`-integral is split as `∫_{ℝ³} = ∫_G + ∫_{Gᶜ}` (the integrability side
condition). -/
def SmallBoxCollected (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      IsLowB v h J μ n Φ →
        0 ≤ RPsi v h μ Φ ∧
        RPsi v h μ Φ
          ≤ (∫ u : ℝ³, sbWord h μ u (Φ : X n → ℝ))
            + 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
                * (1 + C * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n Φ

end Work.BoseFixB1
