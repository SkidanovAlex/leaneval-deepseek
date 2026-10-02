/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2 — item `G`: the angle set `A` is invariant under `g = (T_c)^[5]`

`NOTES_LEAD_mandelbar_seed.md` §4.2, item `G`, *invariance half*: if a ray of angle `θ` lands at
`z₁`, then so does the ray of angle `T^5 θ` (because `T_c^5` sends the ray at angle `θ` to the ray
at angle `T^5 θ` and fixes `z₁`).  The *injectivity* half of `G` (`T^i` is injective on the angles
landing at `T^i z₁`) is not needed by the assembly of `TwoRays.lean`: the finite certificate
`Cert.lean` supplies the distinctness of the angles at each level.  It is recorded here in the
weak form actually used, `landsN_image_of_injective`.
-/
import Submission.Work.SeedSimple2.Cert

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Function
open scoped Topology

noncomputable section

namespace Work.SeedSimple2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

theorem T_mem_Ico (θ : ℝ) : Work.EL.T θ ∈ Set.Ico 0 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- `T` is the angle map of `T_c` on the ray points. -/
theorem rayPt_T_iterate {c : ℂ} (d : Work.EL.RootParabolic c) (n : ℕ) {θ t : ℝ} (ht : 1 < t) :
    (Tantibar c)^[n] (Work.EL.rayPt d.hN θ t)
      = Work.EL.rayPt d.hN ((Work.EL.T^[n]) θ) (t ^ (2 ^ n)) :=
  Work.ELRig.rayPt_iterate_antibar d.hN d.bottcher ht n

/-- **Landing is natural under the iterates of `T_c`**: if the ray of angle `θ` lands at `z`,
then the ray of angle `T^[n] θ` lands at `(T_c)^[n] z`.  This is the `n`-fold iterate of
`Work.ELTop.landsN_map`. -/
theorem landsN_T_iterate {c : ℂ} (d : Work.EL.RootParabolic c) (n : ℕ) {θ : ℝ} {z : ℂ}
    (h : Work.EL.LandsN d.hN θ z) :
    Work.EL.LandsN d.hN ((Work.EL.T^[n]) θ) ((Tantibar c)^[n] z) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact Work.ELTop.landsN_map d.hN d.bottcher ih

/-- **Item `G` (invariance half)**: the angle set `A` of `z₁` is invariant under `g = T^5`. -/
theorem gAngle_mem_LandAngles {c : ℂ} (d : Work.EL.RootParabolic c) {θ : ℝ}
    (hθ : θ ∈ LandAngles d.hN d.z₁) : GAngle θ ∈ LandAngles d.hN d.z₁ := by
  obtain ⟨hθIco, hland⟩ := hθ
  refine ⟨?_, ?_⟩
  · exact (T_mem_Ico _)
  · have h := landsN_T_iterate d 5 hland
    rwa [d.per_half] at h

/-- The ray at angle `θ` lands at most at one point. -/
theorem landsN_unique {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {θ : ℝ} {y y' : ℂ}
    (h : Work.EL.LandsN hN θ y) (h' : Work.EL.LandsN hN θ y') : y = y' :=
  tendsto_nhds_unique h h'

end Work.SeedSimple2

end
