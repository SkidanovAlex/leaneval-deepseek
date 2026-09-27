import Mathlib
import Submission.Work.Drive.CappingSpace
import Submission.Work.Drive.cappingSpace_homeomorph_prod
import Submission.Work.Drive.CappingDefs
import Submission.Work.Drive.exists_embedded_configuration_strip

/-!
# Stage 2: the rotation action and the model `ω`-chain

`Submission/Work/Drive/CHAIN_LEVEL_PLAN.md` §2 asks, for the chain route to `Work.Drive.ParityCore`,
for the *relative `3`-chain* `V_u` representing the class `ω_{P_u}` of the capped configuration strip,
with prescribed ends (`ω` is `1` at the axis end, `0` at the far end), and for the *rotation action*
of `S¹` on the capped manifold `Y` (the paper's clause "the counts are invariant under rotation").

This file fixes the interface those two objects consume, on top of the proved Stage-1 model
(`Work.Drive.CappingSpace`, `Work.Drive.cappingSpace_homeomorph_prod`, `Work.Drive.CappingDefs`):

* `Work.Drive.rotLens`, `Work.Drive.rotCapping` — the rotation (adding `v` to the `S¹` /
  doubled-direction coordinate) acting on the slice `LensSpace` and on the capping space
  `CappingSpace`, obtained by descending the proved compatible maps `Work.Drive.rotLensSum`,
  `Work.Drive.rotSum` along the boundary identifications `Work.Drive.lensRel_rot`,
  `Work.Drive.cappingRel_rot`.  Their basic `rfl`-level computation rules `rotLens_mk`,
  `rotCapping_mk` are proved here; the action laws and continuity are delegated (see below);
* `Work.Drive.omegaChain` — the **model** `ω`-chain.  In the model `Y = (0,∞) × LensSpace`
  (`Work.Drive.cappingSpace_homeomorph_prod`) a standard plane is a level `P_t = {t} × LensSpace`, and
  `ω_{P_t}` — the class which is `1` below `P_t` and `0` above it — is represented by the part of `Y`
  below the level `t`.  `Work.Drive.omegaChain_mem_iff` is the *model computation* recorded in
  `CHAIN_ROUTE_NOTES.md` ("`P_a ≺ P_b ⟺ a < b`, `⟨ω_{P_b}, essential loop of P_a⟩ = 1` iff the loop
  lies below `b`"): the radial coordinate plays the role of the paper's `λ = log r`, and the level
  `s` lies in the chain of level `t` exactly when `s < t`.

What is still missing for a *general* strip (recorded in `Submission/Work/Drive/OMEGA_CHAIN_STATUS.md`):
the capped plane `P_u = u·M ∪ cap_u` — for which `Work.Drive.exists_embedded_configuration_strip` (the
strip) and `Work.Drive.exists_disk_filling_of_meridian_class` (the cap disk) are already proved — and
then the relative `3`-chain of that plane. -/

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open scoped Topology

/-! ## The rotation action on the slice and on the capping space -/

/-- **The rotation of the slice `LensSpace`.**  `rotLens v` adds `v` to the doubled-direction
coordinate; it is `rotLensSum v` descended to the quotient along the boundary identification. -/
def rotLens (v : UnitAddCircle) : LensSpace → LensSpace :=
  Quotient.lift (fun p => Quotient.mk'' (rotLensSum v p))
    (fun _ _ h => Quotient.sound (lensRel_rot v h))

/-- **The rotation of the capping space `CappingSpace`.**  Descended from `rotSum` along
`cappingRel`. -/
def rotCapping (v : UnitAddCircle) : CappingSpace → CappingSpace :=
  Quotient.lift (fun p => Quotient.mk'' (rotSum v p))
    (fun _ _ h => Quotient.sound (cappingRel_rot v h))

@[simp] lemma rotLens_mk (v : UnitAddCircle) (p : CapTorus ⊕ ConfTorus) :
    rotLens v (Quotient.mk'' p) = Quotient.mk'' (rotLensSum v p) := rfl

@[simp] lemma rotCapping_mk (v : UnitAddCircle) (p : ConfigPiece ⊕ CapPiece) :
    rotCapping v (Quotient.mk'' p) = Quotient.mk'' (rotSum v p) := rfl

/-- **The model homeomorphism intertwines the two rotations.**  `Φ` sends the rotation of the
capping space to the rotation of the slice, the radial coordinate being untouched; conversely for the
inverse `Ψ`.  This is what lets a rotation-invariant count be evaluated in the model
`(0,∞) × LensSpace`. -/
theorem Phi_rot_equivariant (v : UnitAddCircle) :
    (∀ x : CappingSpace, Φ (rotCapping v x) = ((Φ x).1, rotLens v (Φ x).2)) ∧
    (∀ y : Set.Ioi (0 : ℝ) × LensSpace,
      Ψ ((y.1, rotLens v y.2)) = rotCapping v (Ψ y)) := by
  constructor
  · intro x
    induction x using Quotient.inductionOn with
    | h a => cases a <;> rfl
  · intro y
    obtain ⟨r, q⟩ := y
    induction q using Quotient.inductionOn with
    | h a => cases a <;> rfl

/-! ## The model `ω`-chain

In the model `Y = (0,∞) × LensSpace` a standard plane is the level set `{t} × LensSpace`; the class
`ω_{P_t}` (which is `1` below `P_t` and `0` above it, the axis end being the `r → 0` end) is
represented by the chain of the points below the level `t`. -/

/-- **The model `ω`-chain at the level `t`**: the part of the model `(0,∞) × LensSpace` below the
standard plane `{t} × LensSpace`, i.e. the relative `3`-chain running off to the axis end
(`r → 0`, where `ω = 1`). -/
def omegaChain (t : Set.Ioi (0 : ℝ)) : Set (Set.Ioi (0 : ℝ) × LensSpace) :=
  {p | (p.1 : ℝ) < t}

/-- **The model computation.**  A point of the level `s` lies in the `ω`-chain at level `t` exactly
when `s < t`; hence the essential loop of the plane `P_s` is paired with `ω_{P_t}` (`= 1`) exactly
when the loop lies below `t`, i.e. `P_s ≺ P_t ⟺ s < t` — the order is the left-to-right order of the
model's radial coordinate. -/
theorem omegaChain_mem_iff (s t : Set.Ioi (0 : ℝ)) (x : LensSpace) :
    ((s, x) : Set.Ioi (0 : ℝ) × LensSpace) ∈ omegaChain t ↔ (s : ℝ) < t :=
  Iff.rfl

/-- The model `ω`-chain is invariant under the rotation action: the rotation only moves the slice
coordinate, and the chain is a condition on the radial coordinate alone. -/
theorem omegaChain_rot_mem_iff (v : UnitAddCircle) (t : Set.Ioi (0 : ℝ))
    (p : Set.Ioi (0 : ℝ) × LensSpace) :
    ((p.1, rotLens v p.2) : Set.Ioi (0 : ℝ) × LensSpace) ∈ omegaChain t ↔ p ∈ omegaChain t :=
  Iff.rfl

end Work.Drive
