import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.UBBInputs9.A.tBwordBInd_nonneg
import Submission.Work.UBBInputs9.A.tsupport_chiB_subset_dlBox
import Submission.Work.UBBInputs9.B.chiBigAux
import Submission.Work.UBBInputs9.B.chiSup_sq_ge
import Submission.Work.UBBInputs9.B.integral_fderiv_chiBPhi_sq_eq
import Submission.Work.UBBInputs9.B.pd_aux.boxMean_term_le
import Submission.Work.UBBInputs9.B.pd_aux.integrable_kinIntPrj
import Submission.Work.UBBInputs9.B.pd_aux.integral_kinInt_pdMu_eq
import Submission.Work.UBBInputs9.B.pd_aux.proj_prod_lower
import Submission.Work.UBBInputs9.B.tBwordKinBig_eq_T0Form
import Submission.Work.UBBInputs9.C.fderiv_chiB_apply
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BSKinetic.Defs` — the operator-level sliding kinetic localisation

This chapter attacks the residual `hloc` of the a-priori chain
(`Work.UBBInputs9.Defs.KineticLocalisationWSm`, `Work.AprioriWire`), i.e. FS Fournais–Solovej
*The energy of dilute Bose gases* `lem:LocKinEn` and the Bratteli–Solovej Thm 3.10
(`eq:BSsliding2`).  The roadmap was fixed by `Work.UBBInputs9/README.md` §4–5 and consists of the
two named forms

    `Work.UBBInputs9.BSslidingKin N ℓ d b ε c Φ`
      :  `(b/2ℓ²)·cnPlus ℓ Φ + ∫_u 𝒯_{B(u)}(Φ) du  ≤  𝒯_Λ(Φ)`   (`= tBwordKinBig`),
    `Work.UBBInputs9.LocKinEnWord N ℓ c Φ`
      :  `∫_u 𝒯'_{Λ(u)}(Φ) du  ≤  kinWord N ℓ Φ`.

## What this chapter does

Everything in the corpus is a *word*: an explicit multiple integral.  The BS/FS localisation is an
*operator* inequality, and its two load-bearing ingredients are

* (BS Lemma 3.7 / `(44)`) the exact `u`-integral of the *projected* moving-box family
  `∫_u Q_u 𝒦(√−Δ) Q_u du`, computed by BS Lemma 3.3 for the indicator family; and
* (FS's `lem:LocKinEn` proof) the symbol bound `H(p) ≤ Cb·min{|p|², d⁻²}`.

This file sets up the vocabulary in which those two statements can be *stated* on top of the
corpus's word calculus: the **big-box family** (`bsBox`, `bsWin`), the **box mean-free projection
of the moving box** (`bsMean`, `bsQ`), the **one-body big-box kinetic form** `bsOneBody`, its
`u`-integral `bsFamilyForm`, and the two Dirichlet words `dSpace` (full space) and `kinWord`
(the corpus's box-restricted word).  It then fixes the *targets* and the *named residuals*.

## The convention

The big-box family of FS `lem:LocKinEn` is `Λ(u) = ℓu + acube ℓ`, with window
`χ_u(x) = χ(x/ℓ − u) = chiScale ℓ (x − ℓu)`; it is an **exact** `L²`-partition,
`∫_u χ_u(x)² du = 1` (`Work.UBBInputs9.B.integral_chiScale_sub_smul_sq`), for the corpus bump
`chi` (`chi_L2 : ∫ χ² = 1`).  The corpus's `Work.UBBInputs9.chiBig`/`bigBox` are *definitionally*
`bsWin`/`bsBox` (both are `chiScale ℓ (x − ℓ•u)` / `x − ℓ•u ∈ acube ℓ`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.UBBInputs9

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## 1. The moving box and its window -/

/-- **The big box `Λ(u) = ℓu + acube ℓ`** of FS `lem:LocKinEn` (definitionally
`Work.UBBInputs9.bigBox`). -/
def bsBox (ℓ : ℝ) (u : ℝ³) : Set ℝ³ := {x : ℝ³ | x - ℓ • u ∈ acube ℓ}

/-- **The big-box window `χ_u(x) = χ(x/ℓ − u)`** (definitionally `Work.UBBInputs9.chiBig` and
`Submission.BoseGases.chiU`). -/
def bsWin (ℓ : ℝ) (u x : ℝ³) : ℝ := chiScale ℓ (x - ℓ • u)

/-- The window of the *anchored* box, `χ_{u=0} = χ(x/ℓ)`. -/
def bsWin0 (ℓ : ℝ) (x : ℝ³) : ℝ := chiScale ℓ x

lemma bsBox_eq_bigBox (ℓ : ℝ) (u : ℝ³) : bsBox ℓ u = Work.UBBInputs9.bigBox ℓ u := rfl

lemma bsWin_eq_chiBig (ℓ : ℝ) (u : ℝ³) : bsWin ℓ u = Work.UBBInputs9.chiBig ℓ u := rfl

lemma bsWin_eq_chiU {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u x : ℝ³) : bsWin ℓ u x = chiU ℓ u x := by
  rw [bsWin, chiU, chiScale, smul_sub, smul_smul, inv_mul_cancel₀ hℓ, one_smul]

/-! ## 2. The moving-box mean-free projection `Q_{Λ(u)}` -/

/-- **The box mean `|Λ(u)|⁻¹ ∫_{Λ(u)} ψ`** of a one-body state over the *moving* box, written on
the unit cube: `(ℓ³)⁻¹ ∫_{acube ℓ} ψ(ℓu + z) dz`.  (The box `Λ(u)` is `ℓu + acube ℓ` and has
volume `ℓ³`.) -/
def bsMean (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
  (ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, ψ (ℓ • u + z)

/-- **The mean-free part of `ψ` in the moving box**: `Q_{Λ(u)}ψ = ψ − |Λ(u)|⁻¹∫_{Λ(u)}ψ`, as a
function of the position `x`.  (This is FS's `Q_u` for the big-box family; the corpus's
`Work.SmallBoxTBWord.boxQ` is the *small*-box analogue.) -/
def bsQ (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ³ → ℝ := fun x => ψ x - bsMean ℓ u ψ

/-- The *anchored* box mean `Q_{Λ}`, i.e. `bsMean` at `u = 0`; the corpus's `aQ`. -/
def bsQ0 (ℓ : ℝ) (ψ : ℝ³ → ℝ) : ℝ³ → ℝ := bsQ ℓ 0 ψ

/-! ## 3. The one-body kinetic forms -/

/-- **The one-body big-box kinetic form** `⟨Q_{Λ(u)}ψ, χ_u F(√−Δ) χ_u Q_{Λ(u)}ψ⟩` written in
the corpus's `p`-convention Fourier form:
`(2π)⁻³ ∫_p F(‖p‖)·‖kinFT (χ_u · Q_{Λ(u)}ψ)‖²`.  For `F = fsKinCoeff c = [·−c]₊²` this is the
spectral half of FS `eq:DefT`'s `𝒯'_u`; for `F = (·)²` it is the Dirichlet form
`∫|∇(χ_u·Q_{Λ(u)}ψ)|²` (`bosegases`-style Plancherel, cf.
`Work.SmallBoxTBWord.tBdiagForm_sq_eq_dirichlet`). -/
def bsOneBody (ℓ : ℝ) (F : ℝ → ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : ℝ³, F ‖p‖ * ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) p‖ ^ 2

/-- The `u`-integral of the one-body big-box kinetic form — the left side of FS `lem:LocKinEn`
at the moving-box family. -/
def bsFamilyForm (ℓ : ℝ) (F : ℝ → ℝ) (ψ : ℝ³ → ℝ) : ℝ :=
  ∫ u : ℝ³, bsOneBody ℓ F u ψ

/-- **The full-space one-body Dirichlet word** `∫_{ℝ³}Σ_k(∂_kψ)²`.  This is the `−Δ` of FS's
`lem:LocKinEn` at the one-body level, and the honest right-hand side of the family inequality:
the corpus's `kinWord` integrates the *same* thing but only over the box `abox`, whereas the
family form sees `ψ` on the whole space (the boxes `Λ(u)` sweep `ℝ³`). -/
def dSpace (ψ : ℝ³ → ℝ) : ℝ :=
  ∑ k : Fin 3, ∫ x : ℝ³, (fderiv ℝ ψ x (kcStdBasis k)) ^ 2

/-- The box-restricted Dirichlet word `∫_{acube ℓ}Σ_k(∂_kψ)²` — `kinWord` at `N = 1`. -/
def dBox (ℓ : ℝ) (ψ : ℝ³ → ℝ) : ℝ :=
  ∑ k : Fin 3, ∫ x in acube ℓ, (fderiv ℝ ψ x (kcStdBasis k)) ^ 2

/-! ## 4. The `N`-body family form and the two named targets

`Work.UBBInputs9.tBwordKinBigU N ℓ c u Φ = tBwordKinInd ℓ (Λ(u)) (ℓ³) (χ_u) c Φ` is the corpus's
word for `𝒯'_{Λ(u)}`; the `N`-body family form is its `u`-integral. -/

/-- **The `N`-body family form** `∫_u 𝒯'_{Λ(u)}(Φ) du`: the corpus's `tBwordKinBigU` integrated
over the moving box. -/
def familyBigKin (N : ℕ) (ℓ c : ℝ) (Φ : X N → ℝ) : ℝ :=
  ∫ u : ℝ³, tBwordKinBigU N ℓ c u Φ

/-- **The anchored big-box kinetic word** (FS `eq:DefT`'s main kinetic term at `u = 0`), i.e.
`Work.UBBInputs9.tBwordKinBig`. -/
def anchoredBigKin (N : ℕ) (ℓ c : ℝ) (Φ : X N → ℝ) : ℝ := tBwordKinBig N ℓ c Φ

/-! ## 5. The named residuals of this chapter

The two residuals are *one-body* statements about the moving-box family, from which the corpus's
`N`-body forms follow fibre by fibre (§`Reduce`).  Both are the exact place where BS Lemma 3.3 /
FS's symbol bound enter; they are *not* word identities (see `Refute` for the machine-checked
reason for the cutoff). -/

/-- **Residual (Loc-ℝ): the uncut family is dominated by the full-space Dirichlet word.**
For every smooth compactly supported one-body `ψ`,

    `∫_u ⟨Q_{Λ(u)}ψ, χ_u F(√−Δ) χ_u Q_{Λ(u)}ψ⟩ du ≤ ∫_{ℝ³}Σ_k(∂_kψ)²`.

For `F = (·)²` this is the projected version of the exact big-box telescoping
(`Work.UBBInputs9.B.integral_dirichlet_chiBig_eq` shows the *unprojected* version has the positive
excess `(Σ_k∫(∂_kχ)²)/ℓ³·∫ψ²`); the projection is what must pay for it.  For
`F = fsKinCoeff c` with `c ≥ C/ℓ` the cutoff kills the boundary layer.  This is BS's Lemma 3.3
content (`∫_u Q_u𝒦(√−Δ)Q_u du ≤ 𝒦(√−Δ)` for the bump family). -/
def FamilyBound (ℓ c : ℝ) : Prop :=
  ∀ ψ : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) ψ → HasCompactSupport ψ →
    bsFamilyForm ℓ (fsKinCoeff c) ψ ≤ dSpace ψ

/-- **The uncut (`c = 0`) family bound.**  This is *strictly stronger* than `FamilyBound ℓ c` for
`c ≥ 0` (`FamilyBound_of_le`), i.e. `FamilyBound ℓ 0` is the hardest member of the family.  It is
**not** claimed here: `familyForm_zero_eq` (proved in this chapter) computes the exact excess

    `bsFamilyForm ℓ (·)² ψ − dSpace ψ`
      `= (mean term) + (boundary term)`,
    (mean term) `= Σ_k ∫_u (bsMean ℓ u ψ)·∫_x (bsWin ℓ u x)²·∂_k²ψ`,
    (boundary term) `= Σ_k ∫_u ∫_x (bsQ ℓ u ψ x)²·(∂_k bsWin ℓ u x)² ≥ 0`,

so at `c = 0` the projection alone does *not* remove the window excess — the boundary term is what
the cutoff `[‖p‖−c]₊²` must kill, which is exactly FS's own remark (``we need the third term to
control errors'').  The honest residual is therefore `FamilyBound ℓ c` at FS's cutoff
`c = ½(sℓ)⁻¹` (which is `≥ C/ℓ` under `eq:BSlidingassp`), not at `c = 0`. -/
def FamilyBound0 (ℓ : ℝ) : Prop := FamilyBound ℓ 0

/-! ## 6. Slot fibres and the box-supported state class -/

/-- The slot-`i` fibre of an `N`-body state at the configuration `x`:
`z ↦ Φ(x_{i←z})`. -/
def fibN {N : ℕ} (i : Fin N) (Φ : X N → ℝ) (x : X N) : ℝ³ → ℝ :=
  fun z => Φ (Function.update x i z)

/-- The slot-`0` identification `X 1 → (ℝ³ → ℝ)`: the one-particle state as a function of its
position. -/
def slotFun1 (Φ : X 1 → ℝ) : ℝ³ → ℝ := fun z => Φ (fun _ => z)

/-- **Box-supported states**: `Φ` vanishes off the centred box `abox N ℓ`.  This is the state class
FS's `lem:LocKinEn` lives on (their Hilbert space is `L²` of the box), and the class on which the
corpus's `LocKinEnWord` is stated correctly (`Refute` shows it fails on the unrestricted class). -/
def SuppInBox (N : ℕ) (ℓ : ℝ) (Φ : X N → ℝ) : Prop :=
  ∀ x : X N, (∃ i : Fin N, x i ∉ acube ℓ) → Φ x = 0

/-- **The box-supported form of FS `lem:LocKinEn`**: the `u`-integral of the big-box family's main
kinetic term is dominated by the box-restricted Dirichlet word, *for states supported in the
box*.  `Reduce.locKinEnWordBox_of_familyBound` derives it from the one-body statement
`FamilyBound`, fibre by fibre. -/
def LocKinEnWordBox (N : ℕ) (ℓ c : ℝ) : Prop :=
  ∀ Φ : X N → ℝ, ContDiff ℝ (⊤ : ENat) Φ → SuppInBox N ℓ Φ →
    familyBigKin N ℓ c Φ ≤ kinWord N ℓ Φ

/-! ## 7. The unprojected family (the machine-checked reason for the projection) -/

/-- The **unprojected** one-body big-box family form `∫_u ⟨ψ, χ_u F(√−Δ) χ_u ψ⟩ du`, i.e.
`bsOneBody` with `Q_{Λ(u)}` replaced by the identity.  This is the form whose `u`-integral was
computed exactly in `Work.UBBInputs9.B.integral_dirichlet_chiBig_eq`; the *difference* to
`bsOneBody` is the whole content of BS's Lemma 3.3. -/
def bsOneBodyUnproj (ℓ : ℝ) (F : ℝ → ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : ℝ³, F ‖p‖ * ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2

/-- The `u`-integral of the unprojected family form. -/
def bsFamilyFormUnproj (ℓ : ℝ) (F : ℝ → ℝ) (ψ : ℝ³ → ℝ) : ℝ :=
  ∫ u : ℝ³, bsOneBodyUnproj ℓ F u ψ

/-! ## 8. The witness state of the refutation -/

/-- **The far-bump witness**: the corpus bump `chi`, scaled to width `δ` and centred at `3ℓ e₀`,
seen as a one-particle state.  For `δ` small it vanishes identically on (a neighbourhood of) the
analysis box `abox 1 ℓ`, so `kinWord 1 ℓ (farBump ℓ δ) = 0`, while the moving-box family
`Λ(u) = ℓu + acube ℓ` sweeps its support and contributes a strictly positive kinetic.  This is the
state that refutes the corpus's `LocKinEnWord` (`Refute`). -/
noncomputable def farBump (ℓ δ : ℝ) : X 1 → ℝ :=
  fun x => chi ((δ⁻¹) • (x 0 - (3 * ℓ) • kcStdBasis 0))

/-! ## 9. The residuals of the consumer chain to `hloc`

`Work.UBBInputs9.KineticLocalisationWSm d b` (the field `hloc` of
`Work.AprioriWire.Defs.AprioriClauses8W`) is

    `∀ N ℓ ε c Φ, ContDiff Φ → (b/2ℓ²)·cnPlus ℓ Φ + ∫_u 𝒯_{B(u)}(Φ) ≤ kinWordW N ℓ Φ`.

The two sources named for it by `Work.UBBInputs9/README.md` §4–5 and
`Work.AprioriWire/README.md` §3.4 are `BSslidingKin` (Bratteli–Solovej Thm 3.10 — the small-box
family against the *anchored big-box* kinetic `tBwordKinBig`) and `LocKinEnWord` (FS
`lem:LocKinEn` — the big-box family against the plain Dirichlet word).  Neither is a consequence
of the corpus's word calculus, and the corpus chain from them to `hloc` needs one further
comparison, which is *not* the corpus's `kinWordW_le_sup` (that one goes the other way).  The
three objects below name exactly what is needed. -/

/-- The kinetic content of Bratteli–Solovej Thm 3.10 / FS `eq:BSsliding2`, quantified: the small
box word (with FS's gap term) plus the global excited count `(b/2ℓ²)cnPlus` is dominated by the
*anchored* big-box kinetic word `tBwordKinBig`. -/
def BSslidingKinAll (d b : ℝ) : Prop :=
  ∀ (N : ℕ) (ℓ ε c : ℝ) (Φ : X N → ℝ), Work.UBBInputs9.BSslidingKin N ℓ d b ε c Φ

/-- **The missing link between the BS budget and the `χ`-weighted word of the consumer.**  FS's
budget for the localised kinetic is the *windowed* anchored word `𝒯_{u=0}` — `tBwordKinBig` for
its `𝒯'` part — while `hloc` is stated at the `χ`-weighted plain word `kinWordW`.  The passage
from `tBwordKinBig` to `kinWordW` is the Dirichlet identity
`∫(∂(χφ))² = ∫χ²(∂φ)² − ∫χχ''φ²`, so it *fails* whenever `∫χχ''φ² < 0` on the `χ`-plateau —
this is the same defect as `Work.SmallBoxA0.kinPWord_exceeds_kinWord` and
`Work.UBBInputs9.B.exists_kinWord_lt_kinWordW`.  The corpus's `B.kinWordW_le_sup` goes the opposite
way (`kinWordW ≤ chiSup²·kinWord`), so it does **not** supply this step. -/
def BigBoxKin_le_kinWordW : Prop :=
  ∀ (N : ℕ) (ℓ c : ℝ) (Φ : X N → ℝ), ContDiff ℝ (⊤ : ENat) Φ →
    Work.UBBInputs9.tBwordKinBig N ℓ c Φ ≤ Work.UBBInputs9.kinWordW N ℓ Φ

/-! ## 10. The per-slot (one-body) reduction of the `N`-body words

Every word of the chapter is a sum over slots of a *one-body* quantity of the slot fibre
(`tBamp` is independent of the slot-`i` coordinate, `aP` is too), so the `N`-body inequalities
reduce to their `N = 1` instances.  The two definitions below name the slot fibre as an
`X 1`-state, so that the `N = 1` words apply verbatim. -/

/-- **The slot-`i` fibre of an `(n+1)`-particle state, as a one-particle state.**  `kcInsN n i`
inserts the position into slot `i`; the other slots are frozen at `r`. -/
def slotState1 {n : ℕ} (i : Fin (n + 1)) (Φ : X (n + 1) → ℝ) (r : X n) : X 1 → ℝ :=
  fun x => Φ (kcInsN n i (x 0, r))

/-- The **one-particle small-box word** `𝒯_{B(u)}` (`Work.UBBInputs8.tBwordBInd` at `N = 1`). -/
def smallBoxWord1 (ℓ d ε c : ℝ) (u : ℝ³) (φ : X 1 → ℝ) : ℝ :=
  Work.UBBInputs8.tBwordBInd 1 ℓ d ε c u φ

/-- The **one-particle anchored big-box kinetic word** (`Work.UBBInputs9.tBwordKinBig` at
`N = 1`). -/
def bigBoxWord1 (ℓ c : ℝ) (φ : X 1 → ℝ) : ℝ :=
  Work.UBBInputs9.tBwordKinBig 1 ℓ c φ

/-- **The one-particle left-hand side of `BSslidingKin`**: the kinetic gap `(b/2ℓ²)cnPlus` plus
the `u`-integral of the small-box word `𝒯_{B(u)}`.  `Work.UBBInputs9.BSslidingKin 1 ℓ d b ε c φ`
is by definition `oneBodySmallKin ℓ d b ε c φ ≤ bigBoxWord1 ℓ c φ`. -/
def oneBodySmallKin (ℓ d b ε c : ℝ) (φ : X 1 → ℝ) : ℝ :=
  (b / (2 * ℓ ^ 2)) * cnPlus ℓ φ +
    (∫ u : ℝ³, Work.UBBInputs8.tBwordBInd 1 ℓ d ε c u φ)

/-- **The one-body small-box localisation** — the `N = 1` content of `BSslidingKin`.  This is the
statement BS actually prove: their Lemma 3.3 (with Lemma 3.7/`(44)`) gives, at `N = 1`,
`(b/2ℓ²)⟨Q_Λ⟩ + ∫_u⟨𝒯_{B(u)}⟩ du ≤ ⟨𝒯'_{u=0}⟩`.  By
`bsSlidingKin_succ_of_oneBody` this one-body statement implies the `N`-body `BSslidingKin` on
box-supported states, so it is the exact residual to attack. -/
def OneBodySmallBoxBound (ℓ d b ε c : ℝ) : Prop :=
  ∀ φ : X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
    oneBodySmallKin ℓ d b ε c φ ≤ bigBoxWord1 ℓ c φ

end Work.BSKinetic
