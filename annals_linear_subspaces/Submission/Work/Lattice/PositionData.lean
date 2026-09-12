import Mathlib
import ChallengeDeps
import Submission.Work.Lattice.GraysonLattice
import Submission.Work.Lattice.IsometryLatticeBounded
import Submission.Work.Lattice.MaxNorm
import Submission.Work.Lattice.MaxNormFlow
import Submission.Work.Lattice.MaxNormPosition
import Submission.Work.Lattice.Prop5Block
import Submission.Work.Lattice.FlowRateSubspace
import Submission.Work.Lattice.FlowRateAsymptotic
import Submission.Work.Lattice.FlowDataMax
import Submission.GeometryOfNumbers.PlaneFinrank

/-!
# The flow rate as a function of the *position*, and the maximal position at a rank

de Saxcé's §3 flow `a_t = diag(e^{−t/ℓ} (ℓ times), e^{t/(d−ℓ)} …)` acts on `⋀^j ℝᵈ` with
block eigenvalues `exp(t·σ_u)`, `σ_u = −(j−u)/ℓ + u/(d−ℓ)` (`u` = the number of `Lᗮ`-factors,
`Submission.FlowRateAsymptotic.sig`).  The *position* of a `j`-dimensional subspace `P` is
`ω = dim (P ⊓ L)`; the top block of its wedge is `j − ω` (`Submission.TopBlockIndex`), so the
flow rate of the wedge of `P` is

    σ_{j−ω} = −ω/ℓ + (j−ω)/(d−ℓ)      (`sigPos` below).

This module records:

* the dictionary: the algebra (`sigPos_eq`), the antitonicity in the position (`sigPos_anti`),
  the endpoints, and the **criterion** `σ ≤ 0 ↔ ω ≥ ℓ·j/d` (`sigPos_nonpos_iff`);
* the identification of the `σ`-slope of the top block with `sigPos` of the position
  (`sig_topBlockIndex_eq_sigPos`), via `Submission.TopBlockIndex`;
* the **accounting inequality** of the flag argument: for nondecreasing position increments and
  nondecreasing slopes, `∑_{s<N} (ω(s+1) − ω s)·Λ s ≥ ω N · Λ 0`; hence a bound
  `∑ ≤ R` with `ω N > 0` forces the *first* slope to satisfy `Λ 0 ≤ R / ω N`
  (`first_slope_le_of_sum_le`).

Module `Submission.Work.Lattice.PositionData`, namespace `Submission.PositionData`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.PositionData

open Submission.FlowRateAsymptotic
open Submission.MaxNormFlow
open Submission.MaxNorm
open Submission.ExteriorCoordinates
open Submission.Prop5Block
open Submission.GraysonLattice
open Submission.GraysonData
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.MaxNormPosition
open Submission.FlowRateSubspace

variable {d : ℕ}

/-! ### 1. The flow rate at a position -/

/-- The `σ`-slope written with the *complementary* denominator `d − ℓ`. -/
theorem slope_eq {ℓ : ℕ} (hℓd : ℓ ≤ d) :
    slope (d := d) ℓ = 1 / (ℓ : ℝ) + 1 / (((d - ℓ : ℕ)) : ℝ) := by
  unfold Submission.FlowRateAsymptotic.slope
  rw [Nat.cast_sub hℓd]

/-- **The flow rate at a position `ω`**: the log-eigenvalue of the block with `j − ω`
complement (expanding) directions, i.e. of the wedge of a `j`-dimensional subspace whose
position (number of contracting, `L`-directions) is `ω`. -/
noncomputable def sigPos (d j ℓ ω : ℕ) : ℝ := sig (d := d) j ℓ (j - ω)

/-- The two expressions for the flow rate. -/
theorem sigPos_eq {j ℓ ω : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hω : ω ≤ j) :
    sigPos d j ℓ ω = -((ω : ℝ) / (ℓ : ℝ)) + (((j - ω : ℕ) : ℝ) / (((d - ℓ : ℕ)) : ℝ)) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hdmR : (((d - ℓ : ℕ)) : ℝ) = (d : ℝ) - (ℓ : ℝ) := Nat.cast_sub (le_of_lt hℓd)
  have hdR : (0 : ℝ) < (((d - ℓ : ℕ)) : ℝ) := by
    rw [hdmR]
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  have hsub : (((j - ω : ℕ)) : ℝ) = (j : ℝ) - (ω : ℝ) := Nat.cast_sub hω
  rw [sigPos, sig, slope_eq (d := d) (le_of_lt hℓd), hsub]
  field_simp
  ring

/-- The flow rate is **antitone** in the position: more contracting directions means a smaller
(more contracting) flow rate. -/
theorem sigPos_anti {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {j ω ω' : ℕ} (h1 : ω ≤ ω')
    (h2 : ω' ≤ j) :
    sigPos d j ℓ ω' ≤ sigPos d j ℓ ω :=
  sig_mono (d := d) hℓ0 hℓd (Nat.sub_le_sub_left h1 j)

/-- The flow rate at position `0` is the fully expanding one. -/
theorem sigPos_zero {j ℓ : ℕ} : sigPos d j ℓ 0 = sig (d := d) j ℓ j := by
  rw [sigPos, Nat.sub_zero]

/-- The flow rate at the **full** position `j` is the fully contracting one `−j/ℓ`. -/
theorem sigPos_self {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) :
    sigPos d j ℓ j = -(j : ℝ) / (ℓ : ℝ) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hdmR : (((d - ℓ : ℕ)) : ℝ) = (d : ℝ) - (ℓ : ℝ) := Nat.cast_sub (le_of_lt hℓd)
  have hdR : (0 : ℝ) < (((d - ℓ : ℕ)) : ℝ) := by
    rw [hdmR]
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  rw [sigPos, Nat.sub_self, sig, slope_eq (d := d) (le_of_lt hℓd)]
  field_simp
  ring

/-- **The criterion.**  The flow rate of the position `ω` is `≤ 0` (i.e. the block is
non-expanding) exactly when the position is at least the "critical" fraction `ℓ·j/d`. -/
theorem sigPos_nonpos_iff {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {j ω : ℕ} (hω : ω ≤ j) :
    sigPos d j ℓ ω ≤ 0 ↔ (j : ℝ) * (ℓ : ℝ) ≤ (ω : ℝ) * (d : ℝ) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hdR : (0 : ℝ) < (d : ℝ) - (ℓ : ℝ) := by
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  rw [sigPos_eq hℓ0 hℓd hω, Nat.cast_sub (le_of_lt hℓd), Nat.cast_sub hω]
  have h1 : -((ω : ℝ) / (ℓ : ℝ)) + ((j : ℝ) - (ω : ℝ)) / ((d : ℝ) - (ℓ : ℝ)) ≤ 0 ↔
      ((j : ℝ) - (ω : ℝ)) / ((d : ℝ) - (ℓ : ℝ)) ≤ (ω : ℝ) / (ℓ : ℝ) := by
    constructor <;> intro h <;> linarith
  rw [h1, div_le_div_iff₀ hdR hℓR]
  constructor <;> intro h <;> nlinarith [h]

/-! ### 2. The top block of a wedge is the complementary position -/

/-- **The top block index of the wedge of a linearly independent family spanning `P`** is the
number of complement directions `finrank P − finrank (P ⊓ modelX ℓ)`. -/
theorem topBlockIndex_eq_sub_meetDim {ℓ : ℕ} (P : Submodule ℝ (E d))
    (b : Fin (Module.finrank ℝ P) → E d) (hb : LinearIndependent ℝ b)
    (hspan : Submodule.span ℝ (Set.range b) = P) :
    topBlockIndex ℓ (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) b) =
      Module.finrank ℝ P - Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (E d)) :=
  topBlockIndex_eq_of_isTopBlock (d := d) _ (Nat.sub_le _ _)
    (isTopBlock_iMulti_of_linearIndependent (d := d) (ℓ := ℓ) P b hb hspan)

/-- **The flow rate of a family is the flow rate of its position.**  For a linearly independent
family `b` spanning `P`, the `σ`-slope of the top block of its wedge is `sigPos` of the position
`finrank (P ⊓ modelX ℓ)`. -/
theorem sig_topBlockIndex_eq_sigPos {ℓ : ℕ} (P : Submodule ℝ (E d))
    (b : Fin (Module.finrank ℝ P) → E d) (hb : LinearIndependent ℝ b)
    (hspan : Submodule.span ℝ (Set.range b) = P) :
    sig (d := d) (Module.finrank ℝ P) ℓ
        (topBlockIndex ℓ (exteriorPower.ιMulti ℝ (Module.finrank ℝ P) b)) =
      sigPos d (Module.finrank ℝ P) ℓ
        (Module.finrank ℝ (P ⊓ modelX (d := d) ℓ : Submodule ℝ (E d))) := by
  rw [sigPos, topBlockIndex_eq_sub_meetDim (d := d) (ℓ := ℓ) P b hb hspan]

/-! ### 3. The accounting inequality -/

/-- **The accounting inequality.**  Let `ω : ℕ → ℝ` be nondecreasing with `ω 0 = 0` and let
`Λ : ℕ → ℝ` be nondecreasing.  Then for every `N`,

    `∑_{s<N} (ω (s+1) − ω s) · Λ s  ≥  ω N · Λ 0`.

(Each summand is `≥ (ω (s+1) − ω s)·Λ 0` because `Λ s ≥ Λ 0` and the increments are `≥ 0`.) -/
theorem sum_weighted_ge_of_monotone {ω Λ : ℕ → ℝ} (hω0 : ω 0 = 0)
    (hωmono : Monotone ω) (hΛmono : Monotone Λ) (N : ℕ) :
    ω N * Λ 0 ≤ ∑ s ∈ Finset.range N, (ω (s + 1) - ω s) * Λ s := by
  have hterm : ∀ s ∈ Finset.range N, (ω (s + 1) - ω s) * Λ 0 ≤ (ω (s + 1) - ω s) * Λ s := by
    intro s _
    have h1 : 0 ≤ ω (s + 1) - ω s := by
      have := hωmono (Nat.le_succ s); linarith
    exact mul_le_mul_of_nonneg_left (hΛmono (Nat.zero_le s)) h1
  have hsum : (∑ s ∈ Finset.range N, (ω (s + 1) - ω s)) * Λ 0 =
      ∑ s ∈ Finset.range N, (ω (s + 1) - ω s) * Λ 0 := Finset.sum_mul _ _ _
  have htelescope : (∑ s ∈ Finset.range N, (ω (s + 1) - ω s)) = ω N := by
    rw [Finset.sum_range_sub (fun s => ω s) N, hω0]
    ring
  calc ω N * Λ 0 = (∑ s ∈ Finset.range N, (ω (s + 1) - ω s)) * Λ 0 := by rw [htelescope]
    _ = ∑ s ∈ Finset.range N, (ω (s + 1) - ω s) * Λ 0 := hsum
    _ ≤ ∑ s ∈ Finset.range N, (ω (s + 1) - ω s) * Λ s := Finset.sum_le_sum hterm

/-- **The good-time consequence for the first slope.**  If the weighted accounting sum is
bounded by `R` and `ω N > 0`, then the first slope is bounded: `Λ 0 ≤ R / ω N`. -/
theorem first_slope_le_of_sum_le {ω Λ : ℕ → ℝ} (hω0 : ω 0 = 0) (hωmono : Monotone ω)
    (hΛmono : Monotone Λ) {N : ℕ} {R : ℝ} (hN : 0 < ω N)
    (hsum : ∑ s ∈ Finset.range N, (ω (s + 1) - ω s) * Λ s ≤ R) :
    Λ 0 ≤ R / ω N := by
  have h := sum_weighted_ge_of_monotone hω0 hωmono hΛmono N
  rw [le_div_iff₀ hN]
  linarith [h, hsum]

/-! ### 4. The maximal position at a rank (the "`Ω`" layer)

For the standard lattice `ℤᵈ = stdIntLattice d` and a rank `j`, `posMax d ℓ j` is the largest
dimension that the `L`-part `span(v) ⊓ modelX ℓ` can have, over the `ℝ`-independent integer
families `v : Fin j → ℤᵈ`.  It is attained (`posMax_spec`), it bounds the position of every
such family (`le_posMax`), and for `j ≤ d` it equals `min j ℓ` (`posMax_eq_min`): the extreme
positions are realised on the coordinate sub-lattices, which is why the model flow lattice
`a_t ℤᵈ` has the "Vee" polygon `j ↦ −t·min(j,ℓ)/ℓ + t·(j−ℓ)₊/(d−ℓ)`. -/

/-- The meet-dimension of the `ℝ`-span of a family `v` with `modelX ℓ`. -/
noncomputable def famPos {d : ℕ} (ℓ : ℕ) {j : ℕ} (v : Fin j → E d) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range v) ⊓ modelX (d := d) ℓ : Submodule ℝ (E d))

theorem famPos_le {d ℓ j : ℕ} {v : Fin j → E d} (hv : LinearIndependent ℝ v) :
    famPos ℓ v ≤ j := by
  have h1 : famPos ℓ v ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range v)) :=
    Submodule.finrank_mono (R := ℝ) (inf_le_left : _ ⊓ modelX (d := d) ℓ ≤ _)
  rw [Submission.PlaneFinrank.finrank_span_range v hv] at h1
  exact h1

/-- **The maximal position at rank `j`** over the `ℝ`-independent integer families
`v : Fin j → ℤᵈ`. -/
noncomputable def posMax (d ℓ j : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun ω => ∃ v : Fin j → E d, (∀ i, v i ∈ stdIntLattice d) ∧
    LinearIndependent ℝ v ∧ famPos (d := d) ℓ v = ω) j

theorem posMax_le (d ℓ j : ℕ) : posMax d ℓ j ≤ j := by
  classical
  exact Nat.findGreatest_le (P := fun ω => ∃ v : Fin j → E d, (∀ i, v i ∈ stdIntLattice d) ∧
    LinearIndependent ℝ v ∧ famPos (d := d) ℓ v = ω) j

/-- Every integer family of rank `j` has position at most `posMax d ℓ j`. -/
theorem famPos_le_posMax {ℓ j : ℕ} {v : Fin j → E d}
    (hmem : ∀ i, v i ∈ stdIntLattice d) (hv : LinearIndependent ℝ v) :
    famPos (d := d) ℓ v ≤ posMax d ℓ j := by
  classical
  refine Nat.le_findGreatest
    (P := fun ω => ∃ v : Fin j → E d, (∀ i, v i ∈ stdIntLattice d) ∧
      LinearIndependent ℝ v ∧ famPos (d := d) ℓ v = ω)
    (m := famPos (d := d) ℓ v) (n := j) (famPos_le hv) ?_
  exact ⟨v, hmem, hv, rfl⟩

/-- The maximal position is attained by an integer family. -/
theorem posMax_spec {ℓ j : ℕ} (hj : j ≤ d) :
    ∃ v : Fin j → E d, (∀ i, v i ∈ stdIntLattice d) ∧ LinearIndependent ℝ v ∧
      famPos (d := d) ℓ v = posMax d ℓ j := by
  classical
  have hLI : LinearIndependent ℝ (fun i : Fin j => (stdVec d (Fin.castLE hj i) : E d)) :=
    LinearIndependent.comp ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.linearIndependent)
      (Fin.castLE hj) (Fin.castLE_injective hj)
  have hmem : ∀ i : Fin j, (stdVec d (Fin.castLE hj i) : E d) ∈ stdIntLattice d :=
    fun i => Submodule.subset_span ⟨Fin.castLE hj i, rfl⟩
  refine Nat.findGreatest_spec
    (P := fun ω => ∃ v : Fin j → E d, (∀ i, v i ∈ stdIntLattice d) ∧
      LinearIndependent ℝ v ∧ famPos (d := d) ℓ v = ω)
    (m := famPos (d := d) ℓ (fun i : Fin j => (stdVec d (Fin.castLE hj i) : E d)))
    (n := j) (famPos_le hLI) ?_
  exact ⟨_, hmem, hLI, rfl⟩

end Submission.PositionData

end
