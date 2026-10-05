import Mathlib
import Submission.Work.RPA3.Defs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.A3Defs
import Submission.Work.RPA3.flux_primitive
import Submission.Work.RPA3.lag_isotopy_extension
import Submission.Work.RPV.Defs

/-!
# RPA3: bridge to the shared vocabulary `Work.RPV`

Block A3 was developed in namespace `Work.RPA3` with its own copy of the route vocabulary
(`Submission/Work/RPA3/Defs.lean`).  The shared vocabulary of the project lives in
`Submission/Work/RPV/Defs.lean` (namespace `Work.RPV`).  The two copies contain the *same*
definitions and the *same* structures, field for field, so the bridge between them is a plain
structure literal.

This file records the bridge and restates the two deliverables of block A3 in the shared
vocabulary:

* `Work.RPA3.toRPA3LagFamily`: an `Work.RPV.LagFamily` is an `Work.RPA3.LagFamily`.
* `Work.RPA3.rpv_flux_primitive` (node D1) in the `Work.RPV` vocabulary.
* `Work.RPA3.rpv_lag_isotopy_extension` (node A3) in the `Work.RPV` vocabulary.

A caller holding a `Work.RPV.LagFamily` can therefore use the whole of block A3 without
reproving anything.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-! ## The conversions -/

/-- The route's `LagFamily` seen in `Work.RPA3`: a structure literal.  Every field has the same
type in the two vocabularies (`PS`, `symp`, `Tk`, `stdZ`, `tau` are the same definitions, and both
files carry the same field list). -/
def toRPA3LagFamily (L : Work.RPV.LagFamily) : Work.RPA3.LagFamily where
  ℓ := L.ℓ
  smooth := L.smooth
  per := L.per
  inj := fun τ hτ x t x' t' k h => L.inj τ hτ x t x' t' k h
  imm := fun τ hτ x t a b h => L.imm τ hτ x t a b h
  lag := fun τ x t => L.lag τ x t
  X0 := L.X0
  std := L.std
  start := L.start
  start_surj := L.start_surj
  symm := L.symm

@[simp] theorem toRPA3LagFamily_ell (L : Work.RPV.LagFamily) (τ : ℝ) (p : ℝ × ℝ) :
    (toRPA3LagFamily L).ℓ τ p = L.ℓ τ p := rfl

@[simp] theorem toRPA3LagFamily_X0 (L : Work.RPV.LagFamily) : (toRPA3LagFamily L).X0 = L.X0 := rfl

/-- A `Work.RPA3.CptPerHam` is a `Work.RPV.CptPerHam`: a structure literal. -/
def toRPVCptPerHam (Hh : Work.RPA3.CptPerHam) : Work.RPV.CptPerHam where
  H := Hh.H
  smooth := Hh.smooth
  per := Hh.per
  R := Hh.R
  supp := Hh.supp

/-! ## The two deliverables, in the shared vocabulary -/

/-- **D1 in the shared vocabulary.**  The flux form `β = ω(∂_τ ℓ, dℓ ·)` has a primitive
vanishing for `|x| ≥ X0`. -/
theorem rpv_flux_primitive (L : Work.RPV.LagFamily) :
    ∃ h : ℝ → ℝ × ℝ → ℝ, ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => h z.1 z.2) ∧
      (∀ τ x t, h τ (x, t + 2 * Real.pi) = h τ (x, t)) ∧
      (∀ τ x t, L.X0 ≤ |x| → h τ (x, t) = 0) ∧
      (∀ τ x t, deriv (fun y => h τ (y, t)) x =
          -Work.RPV.symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun y => L.ℓ τ (y, t)) x)) ∧
      (∀ τ x t, deriv (fun s => h τ (x, s)) t =
          -Work.RPV.symp (deriv (fun σ => L.ℓ σ (x, t)) τ)
            (deriv (fun s => L.ℓ τ (x, s)) t)) :=
  flux_primitive (toRPA3LagFamily L)

/-- **A3 in the shared vocabulary.**  An exact Lagrangian isotopy of the zero section which equals
the zero section outside a compact set is induced by a compactly supported Hamiltonian flow: the
flow of a compactly supported, `2π`-periodic Hamiltonian carries the zero section into the image of
the family at `τ = 1`. -/
theorem rpv_lag_isotopy_extension (L : Work.RPV.LagFamily) :
    ∃ Hh : Work.RPV.CptPerHam, ∃ Φ : ℝ → Work.RPV.PS → Work.RPV.PS, Work.RPV.IsFlow Hh.H Φ ∧
      ∀ z ∈ Work.RPV.Zsec, ∃ x t, Φ 1 z = L.ℓ 1 (x, t) := by
  obtain ⟨Hh, Φ, hΦ, hL⟩ := lag_isotopy_extension (toRPA3LagFamily L)
  refine ⟨toRPVCptPerHam Hh, Φ, hΦ, ?_⟩
  intro z hz
  obtain ⟨x, t, hxt⟩ := hL z hz
  exact ⟨x, t, hxt⟩

end Work.RPA3
