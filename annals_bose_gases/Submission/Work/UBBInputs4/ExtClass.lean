import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.UBBInputs2.Chain
import Submission.Work.UBBInputs2.dlBackground_lt_lambda
import Submission.Work.UBBInputs2.integrable_qLHSBIntegrand
import Submission.Work.UBBInputs3.MatLoc.Main
import Submission.Work.UBBInputs3.MatLoc.profG_num
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs4.ExtClass` — the trial-class extension (round 4, `CNeu`)

## The finding this file answers

Round 3's `README.md` §2 records (and `Work.UBBInputs3.NPlusGrading` exhibits) the
**state-class obstruction**: FS's localised state

    Ψ̃ = ‖φ̃‖⁻¹ Σᵢ φ̃ᵢ ‖1_{n₊=i}Ψ‖⁻¹ 1_{n₊=i}Ψ

of `lem:LocMatrices` is **not** in the corpus trial class `CInfty0Box N L`:

* the `1_{n₊=i}` are polynomials in the mean projections `Pᵢ` (`aP`), and `PᵢΨ` is
  *constant in the `i`-th coordinate*, hence does not vanish outside the box — while
  `CInfty0Box` demands `tsupport ⊆ interior (box N L)`;
* consequently the recombined state is supported on all of `ℝ^{3N}`, and the delivered
  chain's normalisation `boxSq N L Ψ = ∫_{box N L} Ψ²` is *not* the FS normalisation
  `∫_Λ Ψ²` of the box `Λ` on which the projections `Pᵢ, Qᵢ` are defined.

FS themselves never leave their box: their states are elements of `ℱ_s(L²(Λ))`, `Λ` the
*centred* box, and their `H_Λ(μ)` is the **Neumann** Hamiltonian on `Λ`. So the faithful
formalisation of §7's steps (2)–(4) is *not* the Dirichlet class `CInfty0Box` but the
**Neumann class** — which the corpus already has, `Submission.Neumann.CNeu N L`
(globally smooth functions on the configuration space, no support condition), together
with its energy `eNeu`, the embedding `embNeu : CInfty0Box N L → CNeu N L` and the
identity `quotient_eq_emb` (the Dirichlet quotient of `Ψ` is the Neumann quotient of
`embNeu Ψ`).

## What this file delivers (the trial-class extension)

* `RaylNeu N L v Φ` — the **Neumann Rayleigh quotient** of `Φ : CNeu N L`, i.e. the
  quadratic form of FS's `H = Σ −Δᵢ^𝒩 + Σ_{i<j} v(xᵢ−xⱼ)` on the extended class
  (the *gradient* form `kinNeu`, so no boundary term: the Neumann form domain `H¹`);
* `boxSqNeu N L Φ = ∫_{box N L} Φ²` (the round-2/3 normalisation) and
  `aboxSq N L Φ = ∫_{abox N L} Φ²` — the **covariant window normalisation** matching the
  cube `acube L` on which the projections `Pᵢ, Qᵢ` of `cnPlus` are defined.  The reason
  `aboxSq` (not `boxSqNeu`) is the correct slot: `cnPlus` is *literally* the quadratic
  form of the operator `n₊ = ΣᵢQᵢ` in `L²(abox N L)`, see
  `Work.UBBInputs4.cnPlus_eq_qform_nPlus`;
* `LowStateNeu v N L J Φ` — FS `eq:aprioriPsi` on the extended class;
* `WindowNeu W N L Φ := cnPlus L Φ ≤ W N L · aboxSq N L Φ` — the **covariant** `n₊`-window
  (`W` has the dimension of an excited-particle number, and both sides are of degree 2 in
  `Φ`, so the predicate is scale-invariant — this is the round-1 finding (B) prevented);
* `neuScale Φ c hc` — the scaling witness, so that covariance is *statable*.

The bridges back to the delivered `CInfty0Box` consumers live in
`Work.UBBInputs4.RaylNeuEmb` / `Work.UBBInputs4.BoxSqEmb`
(`RaylNeu N L v (embNeu hL Ψ) = Rayl N L v Ψ`, `aboxSq ≤ boxSqNeu`), and the *whole*
Route-H chain is re-run at this class in `Work.UBBInputs4.Arith` /
`Work.UBBInputs4.Residuals` / `Work.UBBInputs4.Chain`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs
open Work.UBBInputs2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The covariant quantities on the extended class -/

/-- **The extended-class (Neumann) Rayleigh quotient**: the quadratic form of FS's box
Hamiltonian `H_Λ(ρ) = Σᵢ −Δᵢ^𝒩 + Σ_{i<j} v(xᵢ − xⱼ)` on the extended state class
`CNeu N L`, normalised by the **box** `L²`-norm.  The kinetic part is the gradient form
`kinNeu` (the Neumann form domain), not the operator expression `Σ Ψ·(−ΔᵢΨ)` — for a state
that does not vanish at the boundary these differ by a boundary term, and only the
gradient form is the quadratic form of the Neumann Laplacian. -/
noncomputable def RaylNeu (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Φ : CNeu N L) : ℝ :=
  (kinNeu N L Φ + intNeu N L v Φ) / (∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2)

/-- The **box** `L²`-norm square of an extended state (the denominator of `RaylNeu`); for
`embNeu hL Ψ` it is `boxSq N L Ψ`.  This is the round-2/3 normalisation slot. -/
noncomputable def boxSqNeu (N : ℕ) (L : ℝ) (Φ : CNeu N L) : ℝ :=
  ∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2

/-- **The covariant window normalisation**: the `L²`-mass of the state on the *centred*
box `abox N L`, the box over which the mean projections `Pᵢ` and hence the excited count
`n₊ = ΣᵢQᵢ` are defined (`cnPlus` integrates the `Qᵢ` over `abox N L`).  For a state in
`L²(abox N L)` (FS's `ℱ_s(L²(Λ))`) this is the normalisation in which FS state
`eq:apriorinn+`. -/
noncomputable def aboxSq (N : ℕ) (L : ℝ) (Φ : CNeu N L) : ℝ :=
  ∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2

/-- **FS `eq:aprioriPsi` on the extended class**: the state's shifted `H_Λ(ρ)`-expectation
(`ρ := dens N L`) is at most the a-priori threshold, exactly as in round 2's `LowStateH`
but with the Neumann quotient. -/
def LowStateNeu (v : ℝ³ → ℝ) (N : ℕ) (L J : ℝ) (Φ : CNeu N L) : Prop :=
  RaylNeu N L v Φ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3
    ≤ Theta (a v) J (dens N L) * L ^ 3

/-- **The covariant `n₊`-window on the extended class** (FS `eq:apriorinn+`, second
conjunct, in its covariant form): the excited count of `Φ`, measured in `abox N L`, is at
most `W N L` times the state's mass there.  Both sides are of degree `2` in `Φ`, so the
predicate is invariant under `Φ ↦ cΦ` — the covariance that round 1 found missing in the
bare `cnPlus ≤ W N L`. -/
def WindowNeu (W : ℕ → ℝ → ℝ) (N : ℕ) (L : ℝ) (Φ : CNeu N L) : Prop :=
  cnPlus L (Φ : X N → ℝ) ≤ W N L * aboxSq N L Φ

/-! ## 2. The scaling witness (covariance is *statable*) -/

/-- Scaling an extended state by a nonzero constant — the witness that `RaylNeu` and
`WindowNeu` are scale-covariant (`RaylNeu_scale`, `WindowNeu_scale`). -/
noncomputable def neuScale {N : ℕ} {L : ℝ} (Φ : CNeu N L) (c : ℝ) (hc : c ≠ 0) :
    CNeu N L where
  toFun := fun x => c * (Φ : X N → ℝ) x
  contDiff := (contDiff_const (c := c)).mul Φ.contDiff
  nezero := by
    intro h
    apply Φ.nezero
    funext x
    have hx : c * (Φ : X N → ℝ) x = 0 := congrFun h x
    exact (mul_eq_zero.mp hx).resolve_left hc
  sq_pos := by
    have h : (∫ x in box N L, (c * (Φ : X N → ℝ) x) ^ 2)
        = c ^ 2 * (∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [h]
    exact mul_pos (sq_pos_of_ne_zero hc) Φ.sq_pos

@[simp] theorem neuScale_coe {N : ℕ} {L : ℝ} (Φ : CNeu N L) (c : ℝ) (hc : c ≠ 0) :
    ((neuScale Φ c hc : CNeu N L) : X N → ℝ) = fun x => c * (Φ : X N → ℝ) x := rfl

/-! ## 3. Elementary facts -/

/-- `RaylNeu` unfolds to the quotient of the extended Hamiltonian's quadratic form. -/
theorem RaylNeu_def {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (Φ : CNeu N L) :
    RaylNeu N L v Φ
      = (kinNeu N L Φ + intNeu N L v Φ) / (∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2) := rfl

/-- `boxSqNeu` is the box `L²`-norm square. -/
theorem boxSqNeu_def {N : ℕ} {L : ℝ} (Φ : CNeu N L) :
    boxSqNeu N L Φ = ∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2 := rfl

/-- `aboxSq` is the centred-box `L²`-norm square. -/
theorem aboxSq_def {N : ℕ} {L : ℝ} (Φ : CNeu N L) :
    aboxSq N L Φ = ∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2 := rfl

/-- The box `L²`-norm square of an extended state is positive (the structure field). -/
theorem boxSqNeu_pos {N : ℕ} {L : ℝ} (Φ : CNeu N L) : 0 < boxSqNeu N L Φ := Φ.sq_pos

/-- The covariant window normalisation is nonnegative. -/
theorem aboxSq_nonneg {N : ℕ} {L : ℝ} (Φ : CNeu N L) : 0 ≤ aboxSq N L Φ := by
  rw [aboxSq_def]
  exact integral_nonneg fun x => sq_nonneg _

/-- **The extended Rayleigh quotient is nonnegative** for `v ≥ 0` (the kinetic and
interaction terms of the Neumann form are nonnegative). -/
theorem RaylNeu_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hv : 0 ≤ v) (Φ : CNeu N L) :
    0 ≤ RaylNeu N L v Φ := by
  rw [RaylNeu_def]
  have hnum : 0 ≤ kinNeu N L Φ + intNeu N L v Φ :=
    add_nonneg (kinNeu_nonneg Φ) (intNeu_nonneg hv Φ)
  exact div_nonneg hnum (le_of_lt Φ.sq_pos)

end Work.UBBInputs4
