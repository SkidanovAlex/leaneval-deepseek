/-
# SeedExist — the antipodal (central) symmetry of the ray structure

The dynamical Böttcher coordinate of `T_c(z) = z̄² + c` is **odd** on the escaping set
(`Work.Landing.Rays.isDynBottcher_odd`), because `T_c` is an even function.  Consequently the
two rays at the angles `θ` and `θ + 1/2` are reflections of each other in the origin:

`rayPt (θ + 1/2) t = - rayPt θ t`, `paramRay (θ+1/2) = - paramRay θ`
and the antipodal pair lands at the antipode of the landing point.

This is the input W2 of `NOTES_LEAD_mandelbar_seed.md` §3.3 (the design writes it as
`T_c (-z) = -z` for the pair curve and the component bookkeeping of W2(iv) and W4).
-/
import Submission.Work.SeedExist.Setup
import Submission.Work.Landing.Rays.preimage_mem_dynRay
import Submission.Work.ELPull.pb1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

noncomputable section

namespace Work.SeedExist

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- `z ∈ K c ↔ -z ∈ K c`: the filled Julia set is invariant under the central symmetry
(`T_c` is an even function). -/
theorem mem_K_neg_iff {c z : ℂ} : -z ∈ Work.EL.K c ↔ z ∈ Work.EL.K c := by
  have key : ∀ u : ℂ, Work.ParamRays.BoundedOrbit c u → Work.ParamRays.BoundedOrbit c (-u) := by
    rintro u ⟨M, hM⟩
    refine ⟨max M ‖u‖, fun n => ?_⟩
    cases n with
    | zero => simpa using le_max_right M ‖u‖
    | succ n =>
      rw [Work.Landing.Rays.orbit_neg c u n]
      exact le_trans (hM (n + 1)) (le_max_left M ‖u‖)
  constructor
  · intro h
    simpa [Work.EL.K, Work.ParamRays.filledJulia] using key (-z) h
  · intro h
    simpa [Work.EL.K, Work.ParamRays.filledJulia] using key z h

/-- `rayDirection (θ + 1/2) = - rayDirection θ`. -/
theorem rayDirection_add_half (θ : ℝ) :
    Work.Landing.rayDirection (θ + 1 / 2) = - Work.Landing.rayDirection θ := by
  have h1 : (↑(2 * Real.pi * (θ + 1 / 2)) : ℂ) * Complex.I
      = (↑(2 * Real.pi * θ) : ℂ) * Complex.I + (↑Real.pi * Complex.I) := by
    push_cast; ring
  rw [Work.Landing.rayDirection, Work.Landing.rayDirection, h1, Complex.exp_add,
    Complex.exp_pi_mul_I]
  ring

/-- `rayPoint (θ + 1/2) t = - rayPoint θ t`: the ray point of the antipodal angle is the
antipode. -/
theorem rayPoint_add_half (θ t : ℝ) :
    Work.Top.NakaneData.rayPoint (θ + 1 / 2) t = -Work.Top.NakaneData.rayPoint θ t := by
  rw [Work.ELTop.rayPoint_eq_mul_rayDirection, Work.ELTop.rayPoint_eq_mul_rayDirection,
    rayDirection_add_half]
  ring

/-- **The two rays at antipodal angles are reflections of each other**: at every level `t`,
`rayPt (θ + 1/2) t = - rayPt θ t`. -/
theorem rayPt_add_half {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) (θ t : ℝ) :
    hN.rayPt (θ + 1 / 2) t = - hN.rayPt θ t := by
  by_cases ht : 1 < t
  · have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
      Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN
    have hzK : hN.rayPt θ t ∉ Work.EL.K c := hN.rayPt_notMem ht
    have hnegK : -hN.rayPt θ t ∉ Work.EL.K c := fun h => hzK ((mem_K_neg_iff).mp h)
    have hzE : Work.ParamRays.Escaping c (hN.rayPt θ t) :=
      (Work.ParamRays.escaping_iff_not_bounded c _).mpr
        (by simpa [Work.EL.K, Work.ParamRays.filledJulia] using hzK)
    have hodd : Work.EL.dynPhi c (Work.ParamRays.dynPhiOf c) (-hN.rayPt θ t) =
        - Work.EL.dynPhi c (Work.ParamRays.dynPhiOf c) (hN.rayPt θ t) := by
      rw [Work.EL.dynPhi_of_notMem hnegK, Work.EL.dynPhi_of_notMem hzK]
      exact Work.Landing.Rays.isDynBottcher_odd hφ hzE
    refine hN.injOn_Phi (hN.rayPt_notMem ht) hnegK ?_
    rw [hN.Phi_rayPt ht, hodd, hN.Phi_rayPt ht, rayPoint_add_half]
  · rw [Work.Top.NakaneData.rayPt, Work.Top.NakaneData.rayPt, dif_neg ht, dif_neg ht, neg_zero]

/-- **The antipodal landing**: if the ray at angle `θ` lands at `y`, then the ray at angle
`θ + 1/2` lands at `-y`. -/
theorem landsN_add_half {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    {θ : ℝ} {y : ℂ} (h : Work.EL.LandsN hN θ y) :
    Work.EL.LandsN hN (θ + 1 / 2) (-y) := by
  have h2 : Filter.Tendsto (fun t : ℝ => - hN.rayPt θ t)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (-y)) := h.neg
  exact h2.congr' (Eventually.of_forall fun t => (rayPt_add_half hN θ t).symm)

/-- **The antipodal ray**: `paramRay (θ + 1/2)` is the reflection in the origin of
`paramRay θ`. -/
theorem paramRay_add_half {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) (θ : ℝ) :
    hN.paramRay (θ + 1 / 2) = (fun z : ℂ => -z) '' hN.paramRay θ := by
  have hodd : ∀ u : ℂ, u ∉ Work.EL.K c →
      Work.EL.dynPhi c (Work.ParamRays.dynPhiOf c) (-u) =
        - Work.EL.dynPhi c (Work.ParamRays.dynPhiOf c) u := by
    intro u hu
    have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
      Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN
    have hnegK : -u ∉ Work.EL.K c := fun h => hu ((mem_K_neg_iff).mp h)
    have huE : Work.ParamRays.Escaping c u :=
      (Work.ParamRays.escaping_iff_not_bounded c u).mpr
        (by simpa [Work.EL.K, Work.ParamRays.filledJulia] using hu)
    rw [Work.EL.dynPhi_of_notMem hnegK, Work.EL.dynPhi_of_notMem hu]
    exact Work.Landing.Rays.isDynBottcher_odd hφ huE
  ext z
  constructor
  · intro hz
    obtain ⟨hzK, t, ht, hzt⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hz
    have hnegK : -z ∉ Work.EL.K c := fun h => hzK ((mem_K_neg_iff).mp h)
    refine ⟨-z, ?_, by simp⟩
    refine (Work.Top.NakaneData.mem_paramRay_iff hN).mpr ⟨hnegK, t, ht, ?_⟩
    rw [hodd z hzK, hzt, rayPoint_add_half]
    ring
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hwK, t, ht, hwt⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hw
    have hnegK : -w ∉ Work.EL.K c := fun h => hwK ((mem_K_neg_iff).mp h)
    refine (Work.Top.NakaneData.mem_paramRay_iff hN).mpr ⟨hnegK, t, ht, ?_⟩
    rw [hodd w hwK, hwt, rayPoint_add_half]

end Work.SeedExist

end
