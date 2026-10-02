/-
# TripodCert — transfer of the tripod along the quasiconformal deformation

Area `Submission/Work/TripodCert/`.  The certificate produced by this area lives at the **seed**
parameter `c_b` (the root of the period-5 component, the box `Work.SeedCertRay.Xb`), while the
consumer `Work.ELAssembly.AssemblyInputs` needs the tripod at the **final** parameter `c₀`
(FQC's transported `c₂(t*)`).  The bridge is `Work.FQC.transfer_rays`, exactly as in
`Work.ELAssembly.hzero_of_transfer`: a homeomorphism `θ` of the plane carrying the escaping set of
`T_c` onto that of `T_{c₂}` and preserving the external angle maps the dynamic ray of `T_c` at
angle `ϑ` onto the dynamic ray of `T_{c₂}` at the same angle, hence the landing point `y` of the
three tripod rays to the landing point `θ y` of the same three rays.

Nothing about the conjugacy is used beyond ray preservation, so no dynamical identity is needed.
-/
import Mathlib
import Submission.Work.TripodCert.Basic
import Submission.Work.FQC.transfer_rays
import Submission.Work.ELTop.landsN_iff_landsAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.TripodCert

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays (IsDynBottcher Escaping)

/-- The three tripod angles, as a set of reals (the form in which the transfer statement is
phrased). -/
def tripodAngles : Set ℝ := {22 / 63, 25 / 63, 37 / 63}

@[simp] theorem mem_tripodAngles {ϑ : ℝ} :
    ϑ ∈ tripodAngles ↔ ϑ = 22 / 63 ∨ ϑ = 25 / 63 ∨ ϑ = 37 / 63 := by
  simp [tripodAngles, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- **(T2) Transfer of the tripod across the deformation.**  If the three tripod rays of `T_c`
land at a common point `y`, then the three tripod rays of `T_{c₂}` land at the common point
`θ y`, for any homeomorphism `θ` of the plane that preserves the escaping set and the external
angle (the FQC deformation datum). -/
noncomputable def tripod_of_transfer {c c₂ : ℂ} {φ ψ : ℂ → ℂ} (θ : ℂ ≃ₜ ℂ)
    (hb : IsDynBottcher c φ) (hb₂ : IsDynBottcher c₂ (φ ∘ (θ.symm : ℂ → ℂ)))
    (hesc : ∀ z : ℂ, Escaping c₂ (θ z) ↔ Escaping c z)
    (hN₂ : Work.EL.DynB c₂ ψ) (hψ : IsDynBottcher c₂ ψ) {y : ℂ}
    (h : ∀ ϑ ∈ tripodAngles, Work.Landing.landsAt c ϑ y) : Work.EL.Tripod hN₂ where
  y := θ y
  lands₁ := (Work.ELTop.landsN_iff_landsAt hN₂ hψ (22 / 63) (θ y)).mpr
    (((Work.FQC.transfer_rays θ hb hb₂ hesc (22 / 63)).2 y).mp
      (h (22 / 63) (by simp [tripodAngles])))
  lands₂ := (Work.ELTop.landsN_iff_landsAt hN₂ hψ (25 / 63) (θ y)).mpr
    (((Work.FQC.transfer_rays θ hb hb₂ hesc (25 / 63)).2 y).mp
      (h (25 / 63) (by simp [tripodAngles])))
  lands₃ := (Work.ELTop.landsN_iff_landsAt hN₂ hψ (37 / 63) (θ y)).mpr
    (((Work.FQC.transfer_rays θ hb hb₂ hesc (37 / 63)).2 y).mp
      (h (37 / 63) (by simp [tripodAngles])))
  lands₁' := (Work.ELTop.landsN_iff_landsAt hN₂ hψ (22 / 63 + 1) (θ y)).mpr
    (landsAt_add_one_iff.mpr (((Work.FQC.transfer_rays θ hb hb₂ hesc (22 / 63)).2 y).mp
      (h (22 / 63) (by simp [tripodAngles]))))

/-- **(T2) Transfer of the tripod across the deformation, from a tripod at `c`.**  The tripod
data at `c` (in `Work.EL`'s vocabulary) is converted to the landing statements by
`Work.ELTop.landsN_iff_landsAt` and then transported. -/
noncomputable def tripod_of_transfer_tripod {c c₂ : ℂ} {φ ψ : ℂ → ℂ} (θ : ℂ ≃ₜ ℂ)
    (hb : IsDynBottcher c φ) (hb₂ : IsDynBottcher c₂ (φ ∘ (θ.symm : ℂ → ℂ)))
    (hesc : ∀ z : ℂ, Escaping c₂ (θ z) ↔ Escaping c z)
    (hN : Work.EL.DynB c φ) (hN₂ : Work.EL.DynB c₂ ψ) (hψ : IsDynBottcher c₂ ψ)
    (T : Work.EL.Tripod hN) : Work.EL.Tripod hN₂ :=
  tripod_of_transfer θ hb hb₂ hesc hN₂ hψ (y := T.y) fun ϑ hϑ => by
    rcases mem_tripodAngles.mp hϑ with h | h | h
    · rw [h]; exact (Work.ELTop.landsN_iff_landsAt hN hb (22 / 63) T.y).mp T.lands₁
    · rw [h]; exact (Work.ELTop.landsN_iff_landsAt hN hb (25 / 63) T.y).mp T.lands₂
    · rw [h]; exact (Work.ELTop.landsN_iff_landsAt hN hb (37 / 63) T.y).mp T.lands₃

end Work.TripodCert
