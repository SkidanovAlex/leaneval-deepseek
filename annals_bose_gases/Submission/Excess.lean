import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import ChallengeDeps
import Submission.GCPressure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Ingredient 1 — the vanishing canonical excess (T = 0 equivalence of ensembles).

For a density `0 < ρ < ρmax` and a box of side `L`, write `N(L) := ⌊ρL³⌋` and

    gcCanonSet v ρmax ρ L := { gcDensity(μ,ρmax,L) + μ·N(L)/L³ | μ ≥ 0 }

the grand-canonical affine values evaluated at the *canonical* particle density
`N(L)/L³`.  The canonical density `diag v ρ L = E(N(L),L)/L³` dominates every
element of this set (canonical ≥ grand-canonical, `boxEnergy_ge_gcBox_add`),
so the canonical excess

    gcExcess v ρmax ρ L := diag v ρ L − sSup (gcCanonSet v ρmax ρ L)   ≥ 0

measures how far the canonical ground state sits above the best grand-canonical
lower bound.

INGREDIENT 1 (the research-level input of the thermodynamic-limit upper side):
for `0 < ρ < ρmax`, `gcExcess v ρmax ρ L = o(1)` as `L → ∞`.  Together with the
limsup-sup exchange (Control (i), `ConcaveUniform`) this yields
`diagLimsup v ρ ≤ gcSup v ρmax ρ` (`gcSup_upper`), hence `x̲ = x̄ = S` and the
closure of Layer 2.

This module states Ingredient 1 precisely (as the target) and records the
elementary supporting facts: the value domination, boundedness of the set, and
nonnegativity of the excess.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The grand-canonical affine values at density `ρ` for a box of side `L`:
`gcDensity(μ,ρmax,L) + μ·⌊ρL³⌋/L³`, `μ ≥ 0`. -/
def gcCanonSet (v : ℝ³ → ℝ) (ρmax : ℝ) (ρ : ℝ) (L : ℝ) : Set ℝ :=
  {y : ℝ | ∃ μ : ℝ, 0 ≤ μ ∧ y = gcDensity v μ ρmax L +
    μ * ((Nat.floor (ρ * L ^ 3) : ℝ) / L ^ 3)}

/-- The canonical excess of a box of side `L` at nominal density `ρ`. -/
noncomputable def gcExcess (v : ℝ³ → ℝ) (ρmax : ℝ) (ρ : ℝ) (L : ℝ) : ℝ :=
  diag v ρ L - sSup (gcCanonSet v ρmax ρ L)

/-! ## Elementary supporting facts -/

/-- The canonical density dominates every grand-canonical affine value. -/
lemma gcDensity_add_mu_rho_L_le_diag {v : ℝ³ → ℝ} {ρ ρmax μ L : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ ρmax) (hμ : 0 ≤ μ) :
    gcDensity v μ ρmax L + μ * ((Nat.floor (ρ * L ^ 3) : ℝ) / L ^ 3) ≤ diag v ρ L := by
  let N : ℕ := Nat.floor (ρ * L ^ 3)
  have hx0 : 0 ≤ ρ * L ^ 3 := mul_nonneg hρ0 (pow_nonneg hL.le 3)
  have hNad : gcAdmissible ρmax L N := by
    dsimp [gcAdmissible, N]
    have hfl : (Nat.floor (ρ * L ^ 3) : ℝ) ≤ ρ * L ^ 3 := Nat.floor_le hx0
    have hle : ρ * L ^ 3 ≤ ρmax * L ^ 3 := mul_le_mul_of_nonneg_right hρm (pow_nonneg hL.le 3)
    exact le_trans hfl hle
  have hge := boxEnergy_ge_gcBox_add (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hL hv hNad
  have hd := div_le_div_of_nonneg_right hge (pow_nonneg hL.le 3)
  -- (gcBox + μN)/L³ ≤ E(N)/L³: split the left side:
  have hEq : gcDensity v μ ρmax L + μ * ((N : ℝ) / L ^ 3) = (gcBox v μ ρmax L + μ * (N : ℝ)) / L ^ 3 := by
    dsimp [gcDensity]
    ring
  rwa [hEq]

/-- `gcCanonSet` is nonempty (`μ = 0`). -/
lemma gcCanonSet_nonempty (v : ℝ³ → ℝ) (ρmax ρ L : ℝ) : (gcCanonSet v ρmax ρ L).Nonempty := by
  refine ⟨gcDensity v 0 ρmax L, 0, le_rfl, ?_⟩
  simp

/-- `gcCanonSet` is bounded above by the canonical density. -/
lemma gcCanonSet_bddAbove {v : ℝ³ → ℝ} {ρ ρmax L : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ ρmax) :
    BddAbove (gcCanonSet v ρmax ρ L) := by
  refine ⟨diag v ρ L, ?_⟩
  intro y hy
  rcases hy with ⟨μ, hμ, rfl⟩
  exact gcDensity_add_mu_rho_L_le_diag (v := v) (ρ := ρ) (ρmax := ρmax) (μ := μ) (L := L)
    hv hρmax hL hρ0 hρm hμ

/-- The canonical excess is nonnegative. -/
lemma gcExcess_nonneg {v : ℝ³ → ℝ} {ρ ρmax L : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ ρmax) :
    0 ≤ gcExcess v ρmax ρ L := by
  dsimp [gcExcess]
  have hle : sSup (gcCanonSet v ρmax ρ L) ≤ diag v ρ L := by
    apply csSup_le (gcCanonSet_nonempty v ρmax ρ L)
    intro y hy
    rcases hy with ⟨μ, hμ, rfl⟩
    exact gcDensity_add_mu_rho_L_le_diag (v := v) (ρ := ρ) (ρmax := ρmax) (μ := μ) (L := L)
      hv hρmax hL hρ0 hρm hμ
  linarith

/-! ## Value form and csSup plumbing -/

/-- The grand-canonical affine value at `μ ≥ 0` evaluated at the canonical
density of a box of side `L`. -/
noncomputable def gcCanonValue (v : ℝ³ → ℝ) (ρmax : ℝ) (ρ : ℝ) (μ : ℝ) (L : ℝ) : ℝ :=
  gcDensity v μ ρmax L + μ * ((Nat.floor (ρ * L ^ 3) : ℝ) / L ^ 3)

/-- `gcCanonSet` consists exactly of the values of `gcCanonValue`. -/
lemma gcCanonSet_eq_range {v : ℝ³ → ℝ} {ρmax ρ L : ℝ} :
    gcCanonSet v ρmax ρ L = {y : ℝ | ∃ μ : ℝ, 0 ≤ μ ∧ y = gcCanonValue v ρmax ρ μ L} := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨μ, hμ, hy⟩
    exact ⟨μ, hμ, by simpa [gcCanonValue] using hy⟩
  · intro hy
    rcases hy with ⟨μ, hμ, hy⟩
    exact ⟨μ, hμ, by simpa [gcCanonValue] using hy⟩

/-- A single witnessing value bounds the supremum below:
`(∃ μ ≥ 0, value(μ) ≥ a) ⟹ sSup ≥ a`. -/
lemma gcCanon_sup_ge_of_value_ge {v : ℝ³ → ℝ} {ρ ρmax L a : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ ρmax)
    (hw : ∃ μ : ℝ, 0 ≤ μ ∧ a ≤ gcCanonValue v ρmax ρ μ L) :
    a ≤ sSup (gcCanonSet v ρmax ρ L) := by
  rcases hw with ⟨μ, hμ, hle⟩
  rw [gcCanonSet_eq_range]
  apply le_csSup_of_le (gcCanonSet_bddAbove (v := v) (ρ := ρ) (ρmax := ρmax) (L := L)
    hv hρmax hL hρ0 hρm)
  · exact ⟨μ, hμ, rfl⟩
  · simpa [gcCanonValue] using hle

/-- Supremum approximation from below: if `sSup ≥ a`, then for every `η > 0`
there is a value at least `a − η`. -/
lemma gcCanon_value_ge_of_sup_ge {v : ℝ³ → ℝ} {ρ ρmax L a : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ ρmax)
    (hsup : a ≤ sSup (gcCanonSet v ρmax ρ L)) {η : ℝ} (hη : 0 < η) :
    ∃ μ : ℝ, 0 ≤ μ ∧ a - η ≤ gcCanonValue v ρmax ρ μ L := by
  by_contra hnot
  -- all values < a − η: then a − η is an upper bound of the set
  have hall : ∀ μ : ℝ, 0 ≤ μ → gcCanonValue v ρmax ρ μ L < a - η := by
    intro μ hμ
    by_contra hge
    -- value ≥ a − η: contradiction with hnot
    have hle : a - η ≤ gcCanonValue v ρmax ρ μ L := le_of_not_gt hge
    exact hnot ⟨μ, hμ, hle⟩
  have hb : ∀ y : ℝ, y ∈ gcCanonSet v ρmax ρ L → y ≤ a - η := by
    intro y hy
    rcases hy with ⟨μ, hμ, rfl⟩
    have hlt := hall μ hμ
    simpa [gcCanonValue] using hlt.le
  have hs : sSup (gcCanonSet v ρmax ρ L) ≤ a - η := by
    apply csSup_le (gcCanonSet_nonempty v ρmax ρ L)
    exact hb
  linarith

/-- Algebraic form: the excess is at most `ε` iff the supremum reaches
`diag − ε`. -/
lemma gcExcess_le_iff {v : ℝ³ → ℝ} {ρ ρmax L ε : ℝ} :
    gcExcess v ρmax ρ L ≤ ε ↔ diag v ρ L - ε ≤ sSup (gcCanonSet v ρmax ρ L) := by
  dsimp [gcExcess]
  constructor <;> intro h <;> linarith

/-! ## Ingredient 1 — decomposed into a value-level subclaim plus plumbing -/

/-
Decomposition of the vanishing excess:

  gcExcess_witness_aux   (the analytic subclaim, single open obligation):
      ∀ε>0 ∀ᶠL ∃μ ≥ 0:  E(⌊ρL³⌋,L) − gcBox(μ,L) − μ⌊ρL³⌋ ≤ ε·L³
      i.e. the canonical ground state at density ρ is asymptotically within
      ε·L³ of μ-optimality for some chemical potential μ ≥ 0.
      (equivalence-of-ensembles / asymptotic discrete-convexity content;
       genuine research input, NOT derivable from the corpus)
  ── gcExcess_witness_of_aux (proved below: divide by L³) ──▶
  gcExcess_witness       :  ∀ε>0 ∀ᶠL ∃μ ≥ 0:  diag ρ L − ε ≤ value(μ,L)
  ── gcExcess_vanishes_of_witness (proved earlier) ──▶
  gcExcess_vanishes      :  ∀ε>0 ∀ᶠL: gcExcess ≤ ε.
-/

/-- The witness form of the vanishing excess: eventually the canonical box
density is within `ε` of some grand-canonical affine value. -/
def gcExcess_witness (v : ℝ³ → ℝ) (ρmax : ℝ) (ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop, ∃ μ : ℝ, 0 ≤ μ ∧
    diag v ρ L - ε ≤ gcCanonValue v ρmax ρ μ L

/-- Witness form implies the vanishing excess (csSup plumbing). -/
lemma gcExcess_vanishes_of_witness {v : ℝ³ → ℝ} {ρ ρmax : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hρ0 : 0 ≤ ρ) (hρm : ρ < ρmax)
    (hw : gcExcess_witness v ρmax ρ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop, gcExcess v ρmax ρ L ≤ ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [hw (ε / 2) hε2, eventually_ge_atTop (1 : ℝ)] with L hwL hL1
  have hLpos : 0 < L := by linarith
  rcases hwL with ⟨μ, hμ, hle⟩
  have hsup : diag v ρ L - ε / 2 ≤ sSup (gcCanonSet v ρmax ρ L) :=
    gcCanon_sup_ge_of_value_ge (v := v) (ρ := ρ) (ρmax := ρmax) (L := L)
      hv hρmax hLpos hρ0 (le_of_lt hρm) ⟨μ, hμ, hle⟩
  have hleε : diag v ρ L - ε ≤ sSup (gcCanonSet v ρmax ρ L) := by nlinarith
  exact (gcExcess_le_iff (v := v) (ρ := ρ) (ρmax := ρmax) (L := L) (ε := ε)).2 hleε

/-- The canonical gap at a chemical potential `μ ≥ 0` (nonnegative by the
canonical ≥ grand-canonical bound): `E(N,L) − gcBox(μ,L) − μN`, `N = ⌊ρL³⌋`. -/
noncomputable def gcCanonGap (v : ℝ³ → ℝ) (ρmax : ℝ) (ρ : ℝ) (μ : ℝ) (L : ℝ) : ℝ :=
  boxEnergy (Nat.floor (ρ * L ^ 3)) L v - gcBox v μ ρmax L - μ * (Nat.floor (ρ * L ^ 3) : ℝ)

/-- The canonical gap is nonnegative (for admissible `N`, i.e. `ρ ≤ ρmax`). -/
lemma gcCanonGap_nonneg {v : ℝ³ → ℝ} {ρ ρmax μ L : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hL : 0 < L) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ ρmax) (hμ : 0 ≤ μ) :
    0 ≤ gcCanonGap v ρmax ρ μ L := by
  let N : ℕ := Nat.floor (ρ * L ^ 3)
  have hx0 : 0 ≤ ρ * L ^ 3 := mul_nonneg hρ0 (pow_nonneg hL.le 3)
  have hNad : gcAdmissible ρmax L N := by
    dsimp [gcAdmissible, N]
    have hfl : (Nat.floor (ρ * L ^ 3) : ℝ) ≤ ρ * L ^ 3 := Nat.floor_le hx0
    have hle : ρ * L ^ 3 ≤ ρmax * L ^ 3 := mul_le_mul_of_nonneg_right hρm (pow_nonneg hL.le 3)
    exact le_trans hfl hle
  have hge := boxEnergy_ge_gcBox_add (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hL hv hNad
  dsimp [gcCanonGap, N]
  nlinarith

/-- The value-level analytic subclaim (Ingredient 1's core): the canonical gap
is eventually `≤ ε·L³` for some `μ ≥ 0`. -/
def gcExcess_witness_aux (v : ℝ³ → ℝ) (ρmax : ℝ) (ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop, ∃ μ : ℝ, 0 ≤ μ ∧
    gcCanonGap v ρmax ρ μ L ≤ ε * L ^ 3

/-- The value-level subclaim implies the witness form (divide by `L³`). -/
lemma gcExcess_witness_of_aux {v : ℝ³ → ℝ} {ρ ρmax : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hρ : 0 ≤ ρ) (hρm : ρ ≤ ρmax) (haux : gcExcess_witness_aux v ρmax ρ) :
    gcExcess_witness v ρmax ρ := by
  intro ε hε
  filter_upwards [haux ε hε, eventually_ge_atTop (1 : ℝ)] with L hL haL1
  have hLpos : 0 < L := by linarith
  rcases hL with ⟨μ, hμ, hgap⟩
  refine ⟨μ, hμ, ?_⟩
  -- gap/L³ ≤ ε ⟹ diag − ε ≤ value(μ)
  have hd := div_le_div_of_nonneg_right hgap (pow_nonneg hLpos.le 3)
  have hL3 : L ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hLpos)
  -- gcCanonGap/L³ = diag − value(μ,L):
  have hEq : gcCanonGap v ρmax ρ μ L / L ^ 3 =
      diag v ρ L - gcCanonValue v ρmax ρ μ L := by
    dsimp [gcCanonGap, gcCanonValue, gcDensity, diag]
    have h : (boxEnergy (Nat.floor (ρ * L ^ 3)) L v - gcBox v μ ρmax L - μ * (Nat.floor (ρ * L ^ 3) : ℝ)) / L ^ 3 =
        boxEnergy (Nat.floor (ρ * L ^ 3)) L v / L ^ 3 - gcBox v μ ρmax L / L ^ 3 - μ * ((Nat.floor (ρ * L ^ 3) : ℝ) / L ^ 3) := by
      field_simp [hL3]
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have hr : (ε * L ^ 3) / L ^ 3 = ε := by field_simp [hL3]
  have hd' : diag v ρ L - gcCanonValue v ρmax ρ μ L ≤ ε := by
    rwa [hEq, hr] at hd
  nlinarith

/-- The value-level subclaim implies the vanishing excess (composition). -/
lemma gcExcess_vanishes_of_witness_aux {v : ℝ³ → ℝ} {ρ ρmax : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hρ : 0 < ρ) (hρm : ρ < ρmax) (haux : gcExcess_witness_aux v ρmax ρ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop, gcExcess v ρmax ρ L ≤ ε := by
  have hw := gcExcess_witness_of_aux (v := v) (ρmax := ρmax) (ρ := ρ) hv hρmax hρ.le (le_of_lt hρm) haux
  exact gcExcess_vanishes_of_witness (v := v) (ρmax := ρmax) (ρ := ρ) hv hρmax hρ.le hρm hw

