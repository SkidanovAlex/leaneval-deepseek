import Mathlib
import Submission.Work.Lattice.FlagMemberMinima
import Submission.Work.Lattice.QuotientMinima
import Submission.Commons.Lattice.SuccessiveMinima.covering_radius

/-!
# Lattice points near prescribed directions in a flag member (Prop 5, step B)

The first construction step of Prop 5 of de Saxcé (§3): for a flag member `V` (a nonzero
tight saturated subgroup of a full-rank lattice `Λ`) and a **unit vector** `u` in the real
span of `V`, and any radius `M ≥ 0`, there is a lattice point `v ∈ V` with

    `‖v − M·u‖ ≤ j·(C·λ_j(Λ) + ε)`,   `‖v‖ ∈ [M − j(Cλ_j(Λ)+ε), M + j(Cλ_j(Λ)+ε)]`

(`j = subDim V`).  This is the paper's "we may approach `uᵢ` by vectors in `a_t s_x V_{j_s}(ℤ)`
of norm in `[10Cλ, 12Cλ]`": the covering-radius engine
`Commons...exists_latticePoint_near_direction` on the transport lattice
(`FamilySpanMinkowski.familySpanLattice`), whose `m`-th successive minimum is bounded by
`C·λ_j(Λ)` through the flag-member minima bound (`FlagMemberMinima`).

All declarations are Mathlib + Submission + Commons.
-/

noncomputable section
open Set Module Real
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.FlagAnnulus

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.JoinSubmodularity
open Submission.IntrinsicIndex
open Submission.PhiSlack
open Submission.PhiPolygon
open Submission.PhiPolygonCompare
open Submission.Prop42Upper
open Submission.QuotientMinima
open Submission.FlagMemberMinima
open Submission.FamilySpanMinkowski
open Submission.UniformBddBelow
open Submission.LatticePolygon
open Commons.Lattice.SuccessiveMinima

/-- **Lattice points near a prescribed direction in a flag member.**  For a full-rank
`Λ ≤ ℝᵈ`, `A ≥ 0`, a nonzero tight saturated `V ≤ Λ`, a unit vector `u ∈ realSpan V`,
`M ≥ 0` and `ε > 0`, there is `v ∈ V` with the announced annulus bounds (with the
flag-member constant `C` of `FlagMemberMinima.successiveMinimum_le_of_tight_subgroup`). -/
theorem exists_flagMember_near_direction {d : ℕ} (Λ V : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : 0 ≤ A) (hVΛ : V ≤ Λ) (hV0 : V ≠ ⊥)
    (hVtight : phi A V = phiPolygon Λ A (subDim V))
    {u : E d} (hu : u ∈ realSpan V) (hu1 : ‖u‖ = 1) {M : ℝ} (hM : 0 ≤ M) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ v : E d, v ∈ V ∧
      ‖v - M • u‖ ≤ (subDim V : ℝ) *
        (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
          Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
          successiveMinimum (E := E d) Λ (subDim V) + ε) ∧
      ‖v‖ ≤ M + (subDim V : ℝ) *
        (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
          Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
          successiveMinimum (E := E d) Λ (subDim V) + ε) ∧
      M - (subDim V : ℝ) *
        (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
          Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
          successiveMinimum (E := E d) Λ (subDim V) + ε) ≤ ‖v‖ := by
  classical
  obtain ⟨cV, hliR, _hzli, _hmemΛ, hVspan⟩ :=
    exists_basis_family_int_of_le_lattice Λ hΛfin V hVΛ hV0
  have hj0 : 0 < subDim V := Nat.pos_of_ne_zero fun h => hV0 ((subDim_eq_zero_iff_bot V).mp h)
  have hjd : subDim V ≤ d := subDim_le_ambient V
  -- the transport lattice in Vf cV
  let L : Submodule ℤ (Vf cV) := familySpanLattice cV hliR
  haveI : DiscreteTopology L := by dsimp [L]; infer_instance
  haveI : IsZLattice ℝ L := by dsimp [L]; infer_instance
  have hLfin : Module.finrank ℤ L = subDim V := by
    dsimp [L]
    exact finrank_familySpanLattice hj0 cV hliR
  -- the direction, as a vector of the transport space
  have hRealV : realSpan V = Vf cV := by
    have h1 := congrArg (fun W : Submodule ℤ (E d) => realSpan W) hVspan
    rw [realSpan_spanFamily cV] at h1
    exact h1
  have huVf : u ∈ Vf cV := by rw [← hRealV]; exact hu
  let u' : Vf cV := ⟨u, huVf⟩
  have hu'1 : ‖u'‖ = 1 := by simpa [u'] using hu1
  obtain ⟨v', hv1, hv2, hv3⟩ :=
    exists_latticePoint_near_direction L (subDim V) hLfin u' hε hM hu'1
  -- the ambient vector, introduced as an opaque local
  set w : E d := (((v' : L) : Vf cV) : E d) with hw
  have hwmem : w ∈ V := by
    rw [hVspan]
    rw [hw]
    exact (familySpanLattice_carrier cV hliR ((v' : L) : Vf cV)).mp (v' : L).2
  have hwnorm : ‖w‖ = ‖(v' : L)‖ := by
    rw [hw]
    rfl
  have hwdiff : ‖w - M • u‖ = ‖(v' : L) - M • u'‖ := by
    rw [hw]
    have hMu : (((M : ℝ) • u' : Vf cV) : E d) = M • u := by
      simp [u']
    rw [← hMu]
    rfl
  have heq : successiveMinimum (E := Vf cV) L (subDim V) =
      successiveMinimum (E := E d) V (subDim V) := by
    dsimp only [L]
    rw [← successiveMinimum_familySpanLattice_eq cV hliR (i := subDim V)]
    exact congrArg (fun W : Submodule ℤ (E d) =>
      successiveMinimum (E := E d) W (subDim V)) hVspan.symm
  have hflag := successiveMinimum_le_of_tight_subgroup Λ V hΛfin hA hVΛ hV0 hVtight
    (i := subDim V) (by omega) le_rfl
  have hmono : successiveMinimum (E := E d) V (subDim V) ≤
      ((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
        Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
        successiveMinimum (E := E d) Λ (subDim V) := by
    simpa [mul_assoc] using hflag
  have hmul : (subDim V : ℝ) * (successiveMinimum (E := Vf cV) L (subDim V) + ε) ≤
      (subDim V : ℝ) *
        (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
          Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
          successiveMinimum (E := E d) Λ (subDim V) + ε) := by
    have h1 : (subDim V : ℝ) * (successiveMinimum (E := Vf cV) L (subDim V) + ε) ≤
        (subDim V : ℝ) * (successiveMinimum (E := E d) V (subDim V) + ε) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (subDim V))
      rw [heq]
    have h2 : (subDim V : ℝ) * (successiveMinimum (E := E d) V (subDim V) + ε) ≤
        (subDim V : ℝ) *
          (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
            Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
            successiveMinimum (E := E d) Λ (subDim V) + ε) :=
      mul_le_mul_of_nonneg_left (by linarith [hmono]) (Nat.cast_nonneg (subDim V))
    exact le_trans h1 h2
  refine ⟨w, hwmem, ?_, ?_, ?_⟩
  · rw [hwdiff]
    exact le_trans hv1 hmul
  · rw [hwnorm]
    have hb : M + (subDim V : ℝ) * (successiveMinimum (E := Vf cV) L (subDim V) + ε) ≤
        M + (subDim V : ℝ) *
          (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
            Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
            successiveMinimum (E := E d) Λ (subDim V) + ε) := by
      linarith [hmul]
    exact le_trans hv2 hb
  · rw [hwnorm]
    exact le_trans (sub_le_sub_left hmul M) hv3

end Submission.FlagAnnulus
