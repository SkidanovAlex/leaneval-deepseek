import Mathlib
import Submission.Work.Extraction.Supply
import Submission.Work.Lattice.PolygonUniformBound

/-!
# The supply count of a flag member is at most `ℓ`

The §3 extraction (de Saxcé, Prop. 5) accumulates, at the flag member with first active block `u`,
an orthonormal supply family of size `subDim V − u` whose `π₊`-mass is at least the uniform
constant `cStar d`.  Since the block-`0` component of the wedge is the wedge of the `L`-parts
(`blockElem_zero_eq_map_modelProj`), a positive `π₊`-mass forces the `L`-parts `π_L a_k` to be
linearly independent — and they all lie in the `ℓ`-dimensional space `L`:

    **`subDim V − u ≤ ℓ`**.

Consequently the capacity sequence of the §3 extraction can be taken to be at most `ℓ`, and the
accounting (`MaxPhiAccounting.phi_accounting_of_capacity_le`) applies with
`ω :=` the running maximum of the supply counts.

Module `Submission.Work.Extraction.SupplyBound`, namespace `Submission.SupplyBound`.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.SupplyBound

open Submission.ExteriorCoordinates
open Submission.WedgeBlocks
open Submission.WedgeBlockZero
open Submission.WedgeGeneralE1
open Submission.PlaneFinrank
open Submission.Supply
open Submission.GraysonLattice
open Submission.LatticePolygon
open Submission.ActiveBlock
open Submission.FlowDataMax

variable {d : ℕ}

/-- **The supply count of a flag member is at most `ℓ`.** -/
theorem supplyCount_le {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ)
    {V : Submodule ℤ (RD d)} (hV1 : 1 ≤ subDim V)
    {w : Fin (subDim V) → RD d} (hwli : LinearIndependent ℝ w)
    {u : ℕ} (hact : IsFirstActiveBlock (d := d) ℓ (subDim_le_ambient V) t
      (exteriorPower.ιMulti ℝ (subDim V) w) u)
    (hspan : Submodule.span ℝ (Set.range (fun i => eFlow (d := d) ℓ t (w i))) = realSpan V) :
    subDim V - u ≤ ℓ := by
  obtain ⟨a, haON, _haspan, hmass⟩ :=
    exists_supply (d := d) hℓ0 hℓd t hV1 hwli hact hspan
  have hpos : 0 < cStar d := cStar_pos d
  have hkey : blockElem (d := d) (k := subDim V - u) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ (subDim V - u) a) 0 =
      exteriorPower.ιMulti ℝ (subDim V - u) (fun k => modelProj (d := d) ℓ (a k)) := by
    rw [blockElem_zero_eq_map_modelProj (d := d) (k := subDim V - u) ℓ
      (exteriorPower.ιMulti ℝ (subDim V - u) a), exteriorPower.map_apply_ιMulti]
    rfl
  have hne : exteriorPower.ιMulti ℝ (subDim V - u) (fun k => modelProj (d := d) ℓ (a k)) ≠ 0 := by
    intro h0
    rw [hkey, h0, norm_zero] at hmass
    linarith
  have hli : LinearIndependent ℝ (fun k => modelProj (d := d) ℓ (a k)) :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero _ hne
  have hfr : Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun k => modelProj (d := d) ℓ (a k)))) = subDim V - u :=
    finrank_span_range _ hli
  have hle : Submodule.span ℝ (Set.range (fun k => modelProj (d := d) ℓ (a k))) ≤
      modelX (d := d) ℓ := by
    rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    exact projMap_mem (modelX (d := d) ℓ) (a k)
  have hmono := Submodule.finrank_mono hle
  rw [hfr, finrank_modelX (d := d) ℓ (le_of_lt hℓd)] at hmono
  exact hmono

end Submission.SupplyBound

end
