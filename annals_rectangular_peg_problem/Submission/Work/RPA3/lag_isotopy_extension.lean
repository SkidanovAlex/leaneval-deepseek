import Mathlib
import Submission.Work.RPA3.Defs
import Submission.Work.RPA3.A3Defs
import Submission.Work.RPA3.exists_reparam
import Submission.Work.RPA3.flux_primitive
import Submission.Work.RPA3.tubularData_exists
import Submission.Work.RPA3.exists_tubular_H
import Submission.Work.RPA3.follow_family

namespace Work.RPA3

/-- A3: a compactly supported, τ_π-symmetric Lagrangian isotopy of the zero section which equals the
zero section outside a compact set is induced by a compactly supported Hamiltonian flow: there is a
compactly supported, 2π-periodic Hamiltonian whose global flow carries the zero section into the
image of the family at τ = 1.  Proof: extend the family to all τ (exists_reparam, which preserves the
slices at τ = 0 and τ = 1 and makes the geometric hypotheses hold for every τ), build the flux
primitive (flux_primitive), the tubular data (tubularData_exists), the compactly supported extension
of the primitive to a Hamiltonian (exists_tubular_H) and follow the family with the flow of that
Hamiltonian (follow_family, the correctly stated form of the follow-the-family step: the Hamiltonian
produced by exists_tubular_H is C⁴, and C⁴ smoothness of `H` is needed so that `fderiv ℝ` is the
honest differential along the family -- see `_ce_exists_flow_following`); package the resulting
Hamiltonian as a CptPerHam and transfer the conclusion back along the slice equality at τ = 1. -/
theorem lag_isotopy_extension (L : Work.RPA3.LagFamily) :
    ∃ Hh : Work.RPA3.CptPerHam, ∃ Φ : ℝ → Work.RPA3.PS → Work.RPA3.PS, Work.RPA3.IsFlow Hh.H Φ ∧
      ∀ z ∈ Work.RPA3.Zsec, ∃ x t, Φ 1 z = L.ℓ 1 (x, t) := by
  -- Reparametrise so that the geometric hypotheses hold for every `τ ∈ ℝ`,
  -- keeping the slices at `τ = 0` and `τ = 1` unchanged.
  obtain ⟨L', hL'1, _hL'0⟩ := exists_reparam L
  -- The flux primitive of the family (stated for the plain `LagFamily`; `LagFamilyAll` is the same
  -- family, so the structure literal transfers the data).
  obtain ⟨h, hsm, hper, hvan, hdx, hdt⟩ := flux_primitive L'.toLagFamily
  have F : FluxPrimitive L' := ⟨h, hsm, hper, hvan, hdx, hdt⟩
  -- The tubular data.
  obtain ⟨T⟩ := tubularData_exists L'
  -- The compactly supported Hamiltonian extending the flux primitive; it is `C⁴`.
  obtain ⟨H, hHsm, hHper, hHsupp, hHlip, hHbdd, hHgen⟩ := exists_tubular_H L' F T
  obtain ⟨R, hR⟩ := hHsupp
  -- Follow the family with the flow of `H` (using the `C⁴` smoothness of `H`).
  obtain ⟨Φ, hΦflow, hΦ⟩ := follow_family L' H hHsm hHlip hHbdd hHgen
  refine ⟨⟨H, hHsm, hHper, R, hR⟩, Φ, hΦflow, ?_⟩
  intro z hz
  obtain ⟨x, t, hxt⟩ := hΦ z hz
  exact ⟨x, t, hxt.trans (hL'1 x t)⟩

end Work.RPA3
