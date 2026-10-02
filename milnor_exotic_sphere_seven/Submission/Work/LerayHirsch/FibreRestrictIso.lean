import Mathlib
import Submission.Work.LerayHirsch.FibreRestrict
import Submission.Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_indexAt
import Submission.Work.LerayHirsch.TautLine
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.pontryaginClass_comap
import Submission.Work.Agree.PlumbDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The class of the fibre coordinate on a fibre of `P(E)`

This module contains the first inputs of the identification of the restriction of the tautological
line bundle `ℓ` of `P(E)` (`Submission/Work/LerayHirsch/TautLine.lean`) to a fibre
`ProjFibre Z b` with the tautological line bundle of the fibre
(`Submission/Work/LerayHirsch/FibreRestrict.lean`):

* `Work.LerayHirsch.projClassFibre_mkProj` — on a point of the fibre presented as the class of a
  punctured point `p`, the identification `projClassFibre Z b : ProjFibre Z b → ℂP^{m-1}` sends it
  to the class of the fibre coordinate of `p` (the `ProjFibre`-version of
  `Work.LerayHirsch.projClass_mkProj`);
* `Work.LerayHirsch.projClassFibre_mkProj'` — the same in the `Projectivization.mk` form;
* `Work.LerayHirsch.fibreCoord_ne_zero_of_mkProj_eq` — the non-vanishing of a fibre coordinate is
  independent of the chosen lift.

The gluing-data identification is completed by the chart and transition computations in
`Submission/Work/LerayHirsch/FibreRestrict.lean`:

* `Work.LerayHirsch.mem_bundleComap_tautLine_fibreIncl` / `Work.LerayHirsch.fibreIncl_chart` — the
  `(Z.indexAt b, k)`-chart of the restriction of `ℓ` is the set of points whose `k`-th fibre
  coordinate does not vanish;
* `Work.LerayHirsch.tautCoeffLift_fibreIncl` — the transition functions of the restriction of `ℓ`
  are the ratios of the fibre coordinates;
* `Work.LerayHirsch.mem_tautLineP_baseSet` / `Work.LerayHirsch.tautLineP_coordChange_eq_ratio` — the
  same two statements for the tautological bundle `Work.LerayHirsch.tautLineP m` of `ℂP^{m-1}`.

So the restriction of `ℓ` to a fibre and the tautological bundle of the fibre have the *same*
charts and the *same* transition functions — the complete gluing-data content of
"`π_fibre^*ℓ ≅ ℓ(ℂP^{m-1})`".  What remains is to package this as a
`Work.Thom.BundleIso`; see §5 of `Submission/Work/LerayHirsch/README.md` for the precise statement
and the two available routes.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- The non-vanishing of a fibre coordinate does not depend on the chosen lift of a point of the
projectivisation. -/
theorem fibreCoord_ne_zero_of_mkProj_eq {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι}
    {k : Fin m} {p q : ↥(zeroComplement (realification Z))} (h : mkProj Z q = mkProj Z p)
    (hp : (show EuclideanSpace ℂ (Fin m) from p.1.2) k ≠ 0) :
    (show EuclideanSpace ℂ (Fin m) from q.1.2) k ≠ 0 := by
  obtain ⟨c, hc⟩ := (mkProj_eq_iff Z).mp h
  have h2 : (show EuclideanSpace ℂ (Fin m) from q.1.2)
      = (c : ℂ) • (show EuclideanSpace ℂ (Fin m) from p.1.2) := by
    have hcongr := congrArg
      (fun r : ↥(zeroComplement (realification Z)) => (show EuclideanSpace ℂ (Fin m) from r.1.2))
      hc
    rw [smulPunct_snd] at hcongr
    exact hcongr.symm
  have hc0 : (c : ℂ) ≠ 0 := by
    rintro h0
    have hq : (show EuclideanSpace ℂ (Fin m) from q.1.2) = 0 := by rw [h2, h0, zero_smul]
    exact (mem_zeroComplement q.1).mp q.2 hq
  have h3 : (show EuclideanSpace ℂ (Fin m) from q.1.2) k
      = (c : ℂ) * (show EuclideanSpace ℂ (Fin m) from p.1.2) k := by
    rw [h2]; rfl
  rw [h3]
  exact mul_ne_zero hc0 hp

/-- **The class of the fibre coordinate of a lifted point**: on the fibre of `π` over `b`, the
identification `projClassFibre Z b` sends the class of a punctured point `p` to the class of its
fibre coordinate. -/
theorem projClassFibre_mkProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (p : ↥(zeroComplement (realification Z)))
    (hp : projMap Z (mkProj Z p) = b) :
    projClassFibre Z b ⟨mkProj Z p, hp⟩
      = mkP m ⟨(show EuclideanSpace ℂ (Fin m) from p.1.2), (mem_zeroComplement p.1).mp p.2⟩ := by
  rw [projClassFibre_apply, projClass_mkProj]
  rfl

/-- **The class of a point of the fibre is the class of a lift's fibre coordinate**, in the form
`projClass Z (mkProj Z p) = mkP m ...` of `Work.LerayHirsch.projClass_mkProj`, read on the fibre:
`projClassFibre Z b ⟨mkProj Z p, _⟩` is the class of the fibre coordinate of `p`. -/
theorem projClassFibre_mkProj' (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (p : ↥(zeroComplement (realification Z))) (hp : p.1.proj = b) :
    projClassFibre Z b ⟨mkProj Z p, by rw [projMap_mkProj]; exact hp⟩
      = Projectivization.mk ℂ (show EuclideanSpace ℂ (Fin m) from p.1.2)
          ((mem_zeroComplement p.1).mp p.2) := by
  rw [projClassFibre_apply, projClass_mkProj]

end

end Work.LerayHirsch
