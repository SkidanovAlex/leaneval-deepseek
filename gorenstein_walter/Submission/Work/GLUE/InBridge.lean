/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GLUE area (fundmath3-gorenstein_walter)
-/
import Submission.Work.GLUE.Bridge
import Submission.Work.GLUE.PiCoreApi
import Submission.OddOrder.GroupTheory.SubgroupInAmbient

set_option autoImplicit false

open scoped MatrixGroups
open Subgroup

/-!
# GLUE: the `…In K` conventions against the library's `…InG` constructions

The contract file uses `XIn K = (X K).map K.subtype` to speak about subgroups of a subgroup
`K` inside the ambient group `G`.  The odd-order library uses the same idea under the names
`OddOrder.GroupTheory.opiCoreInG π K`, `OddOrder.GroupTheory.derivedInG K`.  This file records
the bridges, so that results phrased with the library's ambient constructions transfer to the
contract's vocabulary (and conversely).
-/

namespace Work.GW2

variable {G : Type*} [Group G]

/-! ### The `…In`-versions lie in their defining subgroup -/

theorem pCoreIn_le (p : ℕ) (K : Subgroup G) : pCoreIn p K ≤ K := Subgroup.map_subtype_le _

theorem oddCoreIn_le (K : Subgroup G) : oddCoreIn K ≤ K := Subgroup.map_subtype_le _

theorem fittingIn_le (K : Subgroup G) : fittingIn K ≤ K := Subgroup.map_subtype_le _

theorem fittingPiIn_le (π : Set ℕ) (K : Subgroup G) : fittingPiIn π K ≤ K :=
  Subgroup.map_subtype_le _

theorem layerIn_le (K : Subgroup G) : layerIn K ≤ K := Subgroup.map_subtype_le _

theorem fstarIn_le (K : Subgroup G) : fstarIn K ≤ K := Subgroup.map_subtype_le _

theorem twoResidualIn_le (K : Subgroup G) : twoResidualIn K ≤ K := Subgroup.map_subtype_le _

/-! ### Bridges to the library's ambient constructions -/

/-- `O_p(K)`, viewed inside `G`. -/
theorem pCoreIn_eq (p : ℕ) [Fact p.Prime] (K : Subgroup G) [Finite G] :
    pCoreIn p K = (OddOrder.Isaacs.Ch01.opCore p ↥K).map K.subtype := by
  rw [pCoreIn, pCore_eq_opCore]

/-- `F(K)`, viewed inside `G`. -/
theorem fittingIn_eq (K : Subgroup G) [Finite G] :
    fittingIn K = (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := by
  rw [fittingIn, fitting_eq_isaacsFitting]

/-- `O(K) = O_{2'}(K)`, viewed inside `G`, is the library's `opiCoreInG`. -/
theorem oddCoreIn_eq_opiCoreInG (K : Subgroup G) [Finite G] :
    oddCoreIn K = OddOrder.GroupTheory.opiCoreInG {q : ℕ | q ≠ 2} K := by
  rw [oddCoreIn, OddOrder.GroupTheory.opiCoreInG, oddCore_eq_oPiCore]

/-- `F_π(K) = O_π(F(K))`, viewed inside `G`. -/
theorem fittingPiIn_eq (π : Set ℕ) (K : Subgroup G) [Finite G] :
    fittingPiIn π K
      = ((OddOrder.Isaacs.Ch03.oPiCore π ↥(fitting ↥K)).map (fitting ↥K).subtype).map
          K.subtype := by
  rw [fittingPiIn, fittingPi_eq_oPiCore]

end Work.GW2
