import Mathlib
import Submission.Work.FlowerGlue.RefCoord
import Submission.Work.FlowerGlue.cyl_rigid
import Submission.Work.FlowerGlue.RefExt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue

open Work.EL (RootParabolic F)

/-- See `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §1.2 for the design: extend `E.φa` to `R.P` by pulling back along `F` (injective there by `φa_inj` + `R.shift` + `R.inj`), get an entire injective 1-equivariant comparison map by periodicity, apply `Work.FlowerGlue.cyl_rigid`. -/
theorem ecalle_eq_ref_add_const {c : ℂ} {d : Work.EL.RootParabolic c}
    (R : Work.FlowerGlue.RefCoord d) (E : Work.FQC.EcalleData d) :
    ∃ s : ℂ, ∀ z ∈ R.P, ∀ n : ℕ, (Work.EL.F c)^[n] z ∈ E.Pa →
      E.φa ((Work.EL.F c)^[n] z) = R.φ z + n + s := by
  obtain ⟨s, hs⟩ := exists_const R E
  refine ⟨s, fun z hz n hn => ?_⟩
  have h1 : phiTilde R E z = E.φa ((F c)^[n] z) - n := phiTilde_eq_of_mem_Pa R E hz n hn
  have h2 : phiTilde R E z = R.φ z + s := hs z hz
  rw [h2] at h1
  have h3 : E.φa ((F c)^[n] z) = R.φ z + s + n := by rw [h1]; ring
  rw [h3]; ring

end Work.FlowerGlue
