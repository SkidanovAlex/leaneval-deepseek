/-
# ELRig — side preservation at `z₁` from the cylinder lift data (`Z1Nest.SP`)

`NOTES_LEAD_mandelbar_residuals.md` §3.3: the ELNest field `NestData.band`
("the repelling petal is the band side of the `α`-pair") is **false** — it contradicts
`Ψ_ends` + `Pa ⊆ pairSide` + the disjointness of the two sides as soon as `Pa` is nonempty.
The correct replacement, which is what the nest arguments actually consume, is the *side
preservation* of §3.2 (d): near the parabolic point `z₁` the second return map
`F c = (T_c)^{10}` preserves the side of the `α`-pair.

This file proves it from the cylinder lift data alone:

* the flower gives `cover` (a punctured neighbourhood of `z₁` is `Pa ∪ Ψ(H_R)`) and
  `mapsTo_Pa`, so it suffices to treat the two cases `z ∈ Pa` and `z = Ψ w` with `w` in a
  far-left half plane;
* for `z = Ψ w` the statement is the shift invariance of the labelling
  `{u | Ψ u ∈ pairSide P}`, i.e. `Ψ w ∈ pairSide P ↔ Ψ (w + 1) ∈ pairSide P`.  Since
  `Ψ (w + 1) = F c (Ψ w)`, this is exactly the side preservation for the preimage `w`; it is
  the "even parity" half of the crossing-parity argument of §3.2 (b)–(d) and is proved in
  `Submission/Work/ELRig/sidePreserve_core.lean` (`Work.ELRig.sidePreserve_core`).
-/
import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.Flower
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.sidePreserve_core
import Submission.Work.ELTop.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

/-- **Side preservation at the parabolic point `z₁`** (`NOTES_LEAD_mandelbar_residuals.md` §3.2
(d), the ELNest field `Z1Nest.SP`).  Near `z₁`, off the pair curve, the second return map
`F c = (T_c)^{10}` maps each of the two sides of the `α`-pair to itself.

The proof splits a small punctured ball around `z₁` by the flower's `cover` into the petal `Pa`
(where both `z` and `F c z` are in `Pa`, hence in the far side) and the image of a far-left half
plane under the repelling coordinate `Ψ`, where the claim is the shift invariance
`Ψ w ∈ pairSide P ↔ Ψ (w + 1) ∈ pairSide P` of the side labelling (`sidePreserve_core`), together
with the defining functional equation `Ψ (w + 1) = F c (Ψ w)`. -/
theorem sidePreserve_of_rayCylLift {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    (P : Work.EL.CoPair d.hN) (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2)
    (hPy : P.y = d.z₁) (hside : Work.EL.PairSides d.hN P)
    (hPa_far : fl.Pa ⊆ Work.EL.pairSide P) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, z ∈ Metric.ball d.z₁ ρ → z ∉ Work.EL.pairCurve P →
      (z ∈ Work.EL.pairSide P ↔ Work.EL.F c z ∈ Work.EL.pairSide P) := by
  -- the reference level of the core lemma, and the level at which the flower's `cover` is used
  set R : ℝ := L.R + 1 with hRdef
  -- the flower's covering property of a punctured neighbourhood of `z₁` at the level `R + 1`
  obtain ⟨ρ, hρpos, hcover⟩ := fl.cover (R + 1)
  refine ⟨ρ, hρpos, ?_⟩
  intro z hz hzc
  rw [Metric.mem_ball] at hz
  -- `z ≠ z₁`, since `z₁` is the landing point of the pair curve
  have hzP : d.z₁ ∈ Work.EL.pairCurve P :=
    (Work.EL.mem_pairCurve_iff P d.z₁).mpr (Or.inr (Or.inl hPy.symm))
  have hzne : z ≠ d.z₁ := fun h => hzc (h ▸ hzP)
  have hzpos : 0 < ‖z - d.z₁‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr hzne
  have hzlt : ‖z - d.z₁‖ < ρ := by rwa [dist_eq_norm] at hz
  rcases hcover z hzpos hzlt with hPa_mem | ⟨w, hwR, hwz⟩
  · -- the petal: `F c` maps `Pa` into `Pa`, hence into the far side
    have h1 : z ∈ Work.EL.pairSide P := hPa_far hPa_mem
    have h2 : Work.EL.F c z ∈ Work.EL.pairSide P := hPa_far (fl.mapsTo_Pa hPa_mem)
    exact ⟨fun _ => h2, fun _ => h1⟩
  · -- the repelling half plane: use the shift invariance of the side labelling
    have hwR' : w.re < -R - 1 := by
      have : w.re < -(R + 1) := hwR
      linarith
    have hcore := sidePreserve_core d fl L P hPa hPb hPy hside hPa_far R le_rfl w hwR'
    rw [← hwz, ← fl.Ψ_shift w]
    exact hcore

end Work.ELRig
