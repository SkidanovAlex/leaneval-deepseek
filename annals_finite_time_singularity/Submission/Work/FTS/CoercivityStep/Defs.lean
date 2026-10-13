/-
# `Work.FTS.CoercivityStep` — the `ℋ^k` coercivity induction of Elgindi's §5–§6,
# re-audited and repaired

This directory owns **Node N2** of `FTS_AUDIT_LEAD.md` §4: the coercivity chapter that
produces `∃ IP, IsH4IP α IP` with `c|g|²_{ℋ^k} ≤ IP(𝓛_Γ^T g, g)`, together with the
`𝓗³`/`∂_τ` instance used for the fake-time equation (tex 1575–1577).

## Why a separate directory

`Submission/Work/Coercivity/` is an already-delivered directory (54K lines, everything
proved except the induction step `HkIPStep_isHkIP`).  Its own `NOTES.md` records three
*machine-checked* findings that force a redesign of the specification before the paper's
induction step (tex 661–707) can be formalised.  The present directory restates the
targets in the redesigned vocabulary, keeps the delivered Coercivity material as its
base case, and proves the step.  The findings, and the design they force:

1. **Honesty.**  `Spaces.HkSq` is a *Bochner* integral, so it is Lean's junk value `0`
   whenever its integrand is not integrable.  Every clause relating `HkSq` to `IP` has to
   be restricted to a class on which the integrand is honest.

2. **Linearity is not free.**  `deriv` is totalised and `HkMem` does not imply
   `AEStronglyMeasurable`, so an *unrestricted* additivity clause for `IP` is
   **false**: `Work.Coercivity.not_IsHkIP_H1IP` exhibits a two-valued non-measurable
   counterexample, and `Work.Coercivity.H1IP_add_fails_of_twoValued` even refutes the
   `HkMem`-restricted form.  The linearity clauses must be taken on the class

     `HkReg α k f  :=  SmoothNbhd f ∧ HkMem α k f`

   (smooth on a neighbourhood of the closed quadrant, honest `ℋ^k` integrand).  This is
   exactly what the paper assumes implicitly.

3. **The step still needs one more clause.**  The paper's splitting
   `D_θ 𝓛_Γ^T f = 𝓛_Γ^T(D_θ f) + E₁` is paired with `D_θ f`, and `E₁` is not a smooth
   function of the paper's class, so no clause of the delivered `IsHkIP` certifies that
   the pairing `IP E₁ (D_θ f)` splits.  Two repairs are used here: the **regularity
   package** `StepReg α n` ("the projector is smoothing", the paper's implicit statement
   that `𝓛_Γ^T(D_θ f)` and `E₁` are again of the class `HkReg α n`), and the
   **Cauchy–Schwarz clause** `cs`, so that `IP E₁ (D_θ f)` is bounded by honest `ℋ^n`
   norms.  With these, the paper's induction goes through verbatim.

4. **Constant bookkeeping.**  The paper writes "we choose `c_{1,k}` so that
   `c_{1,k} C̄_k = (1/2)c_{k-1}²`".  Running that arithmetic through gives a genuine
   requirement: the level-`n` coercivity constant `cc` must dominate the level-`n`
   Cauchy–Schwarz constant `CC` times the square root of the commutator constant,
   `CC√κ ≤ cc/2`.  This is *scale invariant* (rescaling `IP` scales `cc` and `CC` alike),
   so it is not an artefact of a normalisation choice; it is named in `StepInputs` and
   carried honestly through `HkIPStep_isHkIP_fts`.

## Naming

Every target restated from `Work/Coercivity` carries the suffix `_fts`; the
correspondence is listed in `Submission/Work/FTS/CoercivityStep/NOTES.md`.

## Conventions

Functions of the self-similar variables are curried, `f : ℝ → ℝ → ℝ`, applied as
`f z θ`, and all integrals are over `Iz × Iθ = [0,∞) × [0,π/2]` with the measure
`dz dθ` (the paper's Warning in §Notation: **not** `z dz dθ`).  Everything is in
namespace `Work.FTS.CoercivityStep`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep

set_option autoImplicit false

/-! ## The domain and the regularity class -/

/-- The open quadrant `(0,∞) × (0,π/2)` of the self-similar variables.  It is co-null in
`Iz × Iθ`, so it is the correct set on which to impose *pointwise* congruence of the
pairing (`wip`-integrals only see the values a.e.). -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-- **The linearity class of the `ℋ^k` inner product.**  `f` is smooth on a neighbourhood
of the closed quadrant and its `ℋ^k`-integrand is honest (`HkMem`).

This is the class on which all *constructive* clauses of `IsHkIPCore_fts` are stated.  It
is forced by `Work.Coercivity.not_IsHkIP_H1IP`: an unrestricted additivity clause is
false, because `deriv` is totalised and `HkMem` does not imply a.e. strong measurability.
The class is closed under `+`, `-`, scalar multiples, `D_z` and `D_θ`. -/
def HkReg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  Work.Spaces.SmoothNbhd f ∧ Work.Spaces.HkMem α k f

/-! ## The specification of an inner product on `ℋ^k`

The paper's §"Higher order derivatives and the inner product on `ℋ^k`" (tex 661–707)
constructs, by induction on `k`, an inner product `(·,·)_{ℋ^k}` together with two
properties: comparability with `|·|_{ℋ^k}` and coercivity of `𝓛_Γ^T`.  The specification
below is that construction's interface, corrected by findings 2 and 3 above.  It is split
into a *core* (the constructive clauses, which are inherited by the inductive step) and
the coercivity clause (which is what the step has to produce). -/

/-- **The constructive part of an admissible inner product on `ℋ^k`.**

* clauses 1–6 are the bilinear/symmetric/positive/congruence part, stated on the class
  `HkReg α k` (see `HkReg` for why the restriction is forced);
* clause 7 is the Cauchy–Schwarz bound, needed by the induction step to pair the
  commutator defect `E₁` with `D_θ f`;
* clauses 8–9 are the paper's upper and lower comparability with `|·|_{ℋ^k}`, stated on
  the admissible class `HkAdm α k` (`Work.Coercivity.HkAdm`), which carries the
  smoothness, the `HkMem` certificates and the `L₁₂`-zero-mode conditions that make the
  paper's projector honest. -/
structure IsHkIPCore_fts (α : ℝ) (k : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) : Prop where
  /-- Additivity in the first argument. -/
  add_fst : ∀ f₁ f₂ g : ℝ → ℝ → ℝ, HkReg α k f₁ → HkReg α k f₂ → HkReg α k g →
    HkReg α k (f₁ + f₂) → IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
  /-- `ℝ`-homogeneity in the first argument. -/
  smul_fst : ∀ (c : ℝ) (f g : ℝ → ℝ → ℝ), HkReg α k f → HkReg α k g →
    IP (fun z θ => c * f z θ) g = c * IP f g
  /-- Additivity in the second argument. -/
  add_snd : ∀ f g₁ g₂ : ℝ → ℝ → ℝ, HkReg α k f → HkReg α k g₁ → HkReg α k g₂ →
    HkReg α k (g₁ + g₂) → IP f (g₁ + g₂) = IP f g₁ + IP f g₂
  /-- `ℝ`-homogeneity in the second argument. -/
  smul_snd : ∀ (c : ℝ) (f g : ℝ → ℝ → ℝ), HkReg α k f → HkReg α k g →
    IP f (fun z θ => c * g z θ) = c * IP f g
  /-- Symmetry (the paper's `(·,·)_{ℋ^k}` is an inner product). -/
  symm : ∀ f g : ℝ → ℝ → ℝ, IP f g = IP g f
  /-- The pairing only depends on its first argument through the values on the open
  quadrant `Qd`, which is co-null in the domain of integration. -/
  congr_qd : ∀ f f' g : ℝ → ℝ → ℝ, HkReg α k f → HkReg α k f' → HkReg α k g →
    (∀ z θ : ℝ, (z, θ) ∈ Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- Nonnegativity of the diagonal. -/
  nonneg : ∀ h : ℝ → ℝ → ℝ, 0 ≤ IP h h
  /-- Cauchy–Schwarz for the pairing against the honest `ℋ^k` norm. -/
  cs : ∃ C : ℝ, 0 < C ∧ ∀ f g : ℝ → ℝ → ℝ, HkReg α k f → HkReg α k g →
    |IP f g| ≤ C * Work.Spaces.HkNorm α k f * Work.Spaces.HkNorm α k g
  /-- Lower comparability: the pairing dominates the `ℋ^k` norm squared. -/
  le_self : ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α k f →
    Work.Spaces.HkSq α k f ≤ IP f f
  /-- Upper comparability with a constant depending on `k` only. -/
  upper : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α k f →
    IP f f ≤ C * Work.Spaces.HkSq α k f

/-- **An admissible inner product on `ℋ^k`** (the paper's `(·,·)_{ℋ^k}`): the
constructive clauses `IsHkIPCore_fts` together with the paper's Proposition
`prop:HkCoercivity`, i.e. coercivity of `𝓛_Γ^T` on the admissible class. -/
structure IsHkIP_fts (α : ℝ) (k : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) : Prop where
  core : IsHkIPCore_fts α k IP
  /-- **Coercivity of `𝓛_Γ^T`** (the paper's Proposition `prop:HkCoercivity`). -/
  coercive : ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α k f →
    c * Work.Spaces.HkSq α k f ≤ IP (Work.Coercivity.LGammaT α f) f

/-- **An admissible inner product on `ℋ^k` together with a *named* coercivity
constant.**  This is the form in which the paper's induction is stated: at each level one
must know the coercivity constant explicitly, because the next step's constant
bookkeeping compares it with the Cauchy–Schwarz constant of the level. -/
structure IsHkIPc_fts (α : ℝ) (k : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) (c : ℝ) : Prop where
  hc : 0 < c
  prop : IsHkIP_fts α k IP
  coercive : ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α k f →
    c * Work.Spaces.HkSq α k f ≤ IP (Work.Coercivity.LGammaT α f) f

/-- **The `ℋ⁴` interface consumed by the a-priori estimate of §Modulation**, restated.

`Work.Construction.IsH4IP` requires its Cauchy–Schwarz, additivity and homogeneity clauses
for *arbitrary* functions; by finding 2 above those clauses are false for the concrete
inner product, so this is the honest version: the same field names, with the constructive
clauses restricted to `HkReg α 4`.  A caller that discharges the a-priori estimate only
ever applies these clauses to the concrete functions `N₀, N, N_*`, which lie in `HkReg α 4`
under the a-priori hypotheses, so the restriction is harmless in use. -/
structure IsH4IP_fts (α : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) : Prop where
  /-- An admissible inner product on `ℋ⁴`. -/
  hIP : IsHkIP_fts α 4 IP

/-! ## The paper's induction step

`HkIPStep` is `Work.Coercivity.HkIPStep`, the paper's recursion (tex 686)
`(f,g)_{ℋ^k} = (f,g)_{ℋ^{k-1}} + c₁(D_θf,D_θg)_{ℋ^{k-1}} + c₂(D_zf,D_zg)_{ℋ^{k-1}}`.
Its coercivity chain needs two inputs beyond `IsHkIP_fts`: the regularity of the four
participants (`StepReg`) and the two commutator norm bounds (`CommutBounds`), together
with the constant balance named in `StepInputs`. -/

/-- The `D_θ` commutator defect `E₁ = D_θ𝓛_Γ^T f − 𝓛_Γ^T(D_θ f)` of the paper (tex 693). -/
def E₁ (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Spaces.Dth (Work.Coercivity.LGammaT α f) - Work.Coercivity.LGammaT α (Work.Spaces.Dth f)

/-- The `D_z` commutator defect `E₂ = D_z𝓛_Γ^T f − 𝓛_Γ^T(D_z f)` of the paper (tex 700). -/
def E₂ (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Spaces.Dz (Work.Coercivity.LGammaT α f) - Work.Coercivity.LGammaT α (Work.Spaces.Dz f)

/-- **The regularity package of the induction step.**  For every `f ∈ HkAdm α (n+1)` (so
`f` is smooth, its `HkMem` certificates and `L₁₂`-zero-modes hold up to order `n+1`), the
four functions occurring in the paper's splitting

  `D_θ𝓛_Γ^T f = 𝓛_Γ^T(D_θ f) + E₁`,  `D_z𝓛_Γ^T f = 𝓛_Γ^T(D_z f) + E₂`

lie again in the class `HkReg α n`, and so do the two left-hand sides.  This is the
paper's implicit regularity of `𝓛_Γ^T` (tex 690: "`L₁₂` is actually smoothing in `θ` so
that `L₁₂(D_θ f)` and `L₁₂(f)` actually have the same regularity") made into a named
obligation about `𝓛_Γ^T` alone; it carries no coercivity content. -/
def StepReg (α : ℝ) (n : ℕ) : Prop :=
  ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α (n + 1) f →
    HkReg α n (Work.Coercivity.LGammaT α (Work.Spaces.Dth f)) ∧
    HkReg α n (E₁ α f) ∧
    HkReg α n (Work.Coercivity.LGammaT α (Work.Spaces.Dz f)) ∧
    HkReg α n (E₂ α f) ∧
    HkReg α n (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) ∧
    HkReg α n (Work.Spaces.Dz (Work.Coercivity.LGammaT α f))

/-- **The two commutator estimates of the paper** (tex 690–700) with a *named* constant:
`|E₁|_{ℋ^n} ≤ κ|f|_{ℋ^n}` and `|E₂|_{ℋ^n} ≤ κ(|f| + |D_θf|)_{ℋ^n}` for every
`f ∈ HkAdm α (n+1)`.

In the workspace the `D_θ` estimate is **proved** (`Work.Coercivity.CommutTheta_holds`);
the `D_z` estimate is stated (`Work.Coercivity.CommutZ`) and, in the delivered repository,
proved in `Work.Coercivity.CommutZ_holds`.  Both give this predicate with some constant. -/
def CommutBounds (α : ℝ) (n : ℕ) (κ : ℝ) : Prop :=
  0 < κ ∧
    (∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α (n + 1) f →
      Work.Spaces.HkSq α n (E₁ α f) ≤ κ * Work.Spaces.HkSq α n f) ∧
    (∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α (n + 1) f →
      Work.Spaces.HkSq α n (E₂ α f)
        ≤ κ * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)))

/-- **The complete input package of one level of the induction.**  At level `n` one must
know: the inner product with its *named* coercivity constant `cc` and Cauchy–Schwarz
constant `CC`; the regularity package `StepReg α n`; the commutator bounds with a named
constant `κ`; and the **balance** `CC√κ ≤ cc/2`, which is what makes the next step's
constant bookkeeping close.

The balance is not bookkeeping that can be dodged: for any admissible `IP`,
`cc/CC ≤ ‖𝓛_Γ^T‖_{ℋ^n→ℋ^n}` (apply coercivity and Cauchy–Schwarz to the pair
`(𝓛_Γ^T f, f)`), and `cc/CC` is invariant under rescaling `IP`.  It is the hidden
hypothesis of the paper's "choose `c_{1,k}` so that `c_{1,k}C̄_k = (1/2)c_{k-1}²`". -/
def StepInputs (α : ℝ) (n : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ)
    (cc CC κ : ℝ) : Prop :=
  0 < cc ∧ 0 < CC ∧ IsHkIPc_fts α n IP cc ∧
    (∀ f g : ℝ → ℝ → ℝ, HkReg α n f → HkReg α n g →
      |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g) ∧
    StepReg α n ∧ CommutBounds α n κ ∧ CC * Real.sqrt κ ≤ cc / 2

/-! ## Elementary API -/

theorem Qd_subset_dom : Qd ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
  intro p hp
  simp only [Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Work.Spaces.Iz, Work.Spaces.Iθ,
    Set.mem_Ici, Set.mem_Icc] at hp ⊢
  exact ⟨le_of_lt hp.1, hp.2.1.le, hp.2.2.le⟩

theorem IsHkIP_fts.cs {α : ℝ} {k : ℕ}
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (h : IsHkIP_fts α k IP) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : ℝ → ℝ → ℝ, HkReg α k f → HkReg α k g →
      |IP f g| ≤ C * Work.Spaces.HkNorm α k f * Work.Spaces.HkNorm α k g := h.core.cs

theorem IsHkIP_fts.le_self {α : ℝ} {k : ℕ}
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (h : IsHkIP_fts α k IP) {f : ℝ → ℝ → ℝ}
    (hf : Work.Coercivity.HkAdm α k f) : Work.Spaces.HkSq α k f ≤ IP f f :=
  h.core.le_self f hf

theorem IsHkIP_fts.upper {α : ℝ} {k : ℕ}
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (h : IsHkIP_fts α k IP) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α k f →
      IP f f ≤ C * Work.Spaces.HkSq α k f := h.core.upper

theorem IsHkIP_fts.nonneg {α : ℝ} {k : ℕ}
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} (h : IsHkIP_fts α k IP)
    (u : ℝ → ℝ → ℝ) : 0 ≤ IP u u := h.core.nonneg u

theorem IsH4IP_fts.coercive (α : ℝ) {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsH4IP_fts α IP) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α 4 f →
      c * Work.Spaces.HkSq α 4 f ≤ IP (Work.Coercivity.LGammaT α f) f :=
  h.hIP.coercive

theorem IsH4IP_fts.le_self (α : ℝ) {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsH4IP_fts α IP) {f : ℝ → ℝ → ℝ} (hf : Work.Coercivity.HkAdm α 4 f) :
    Work.Spaces.HkSq α 4 f ≤ IP f f :=
  h.hIP.le_self hf

theorem IsH4IP_fts.upper (α : ℝ) {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsH4IP_fts α IP) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α 4 f →
      IP f f ≤ C * Work.Spaces.HkSq α 4 f :=
  h.hIP.upper

theorem IsH4IP_fts.cs (α : ℝ) {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsH4IP_fts α IP) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : ℝ → ℝ → ℝ, HkReg α 4 f → HkReg α 4 g →
      |IP f g| ≤ C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g :=
  h.hIP.cs

end Work.FTS.CoercivityStep
