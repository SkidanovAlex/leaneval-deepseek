import Submission.Work.Milnor.MkCharted
import Submission.Work.Milnor.Model8
import Submission.Work.Morse.contMDiff_push_iff
import Submission.Work.Milnor.CongruenceInterface

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The endgame: no smooth identification of `Mk (-2)` with `S⁷`

This file isolates the **single remaining gap** of the project, and the hypothesis bridge that feeds
it.

* `cappingDiffeo_of_diffeo` — a `ℝ⁷`-diffeomorphism `Mk (-2) ≃ₘ S⁷` is a *capping diffeomorphism*
  `Work.Milnor.IsCappingDiffeo`, i.e. the same function is also smooth for the product atlas
  `(𝓡 4).prod (𝓡 3)` with which `Mk (-2)` was built.  The two atlases differ by pushing forward
  along the linear isometry `mkModelIso`, so this is `Work.Morse.contMDiff_push_iff`.
* `no_cappingDiffeo` — **the remaining theorem**: there is no capping diffeomorphism, i.e.
  `Mk (-2)` is an exotic `7`-sphere.  Its proof is the endgame described in
  `Submission/NOTES.md` §14.7–§14.10: from `F` one forms the closed `8`-manifold
  `X = cappedSpace (cappedDatum F hF)`, where

  - `Work.Cohomology.capped_cupSquare_generates` / `capped_cupSquare_is_pm_generator` give that the
    middle self-intersection number is `m = ±1` (Poincaré duality in the middle degree),
  - `Submission/Work/CharacteristicClasses/` is to supply `p₁(X) = ±6·x`,
  - `Submission/Work/SignatureBordism/` is to supply the dimension-`8` Hirzebruch congruence
    `p₁(X)² ≡ 4 σ(X) (mod 7)`,

  and then `Work.Milnor.endgame_congruence_route'` (with `Work.Milnor.six_sq_not_dvd`) gives a
  contradiction.  This file records the statement so that the assembly in `Submission.lean` is a
  single reference to it.
-/

open scoped Manifold ContDiff Topology

set_option maxHeartbeats 1600000

namespace Work.Milnor

noncomputable section

section Assembly

attribute [local instance] Work.Milnor.mkChartedSpace Work.Milnor.mk_isManifold

/-- The identity map is a diffeomorphism from `Mk (-2)` with the product atlas to `Mk (-2)` with the
pushed-forward `ℝ⁷` atlas (and conversely). -/
private def idDiffeomorph :
    Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯ Submission.Milnor.Mk (-2) where
  toEquiv := Equiv.refl _
  contMDiff_toFun :=
    (Work.Morse.contMDiff_push_iff (E := EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3))
      (E' := EuclideanSpace ℝ (Fin 7))
      (H := ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 3)))
      (I := (𝓡 4).prod (𝓡 3))
      (M := Submission.Milnor.Mk (-2))
      (E'' := EuclideanSpace ℝ (Fin 7))
      (H' := EuclideanSpace ℝ (Fin 7))
      (I' := 𝓡 7)
      (N := Submission.Milnor.Mk (-2))
      (L := Work.Milnor.mkModelIso)
      (f := ⇑(Equiv.refl (Submission.Milnor.Mk (-2))))).mp contMDiff_id
  contMDiff_invFun :=
    (Work.Morse.contMDiff_push_iff (E := EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3))
      (E' := EuclideanSpace ℝ (Fin 7))
      (H := ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 3)))
      (I := (𝓡 4).prod (𝓡 3))
      (M := Submission.Milnor.Mk (-2))
      (I' := (𝓡 4).prod (𝓡 3))
      (N := Submission.Milnor.Mk (-2))
      (L := Work.Milnor.mkModelIso)
      (f := ⇑(Equiv.refl (Submission.Milnor.Mk (-2))))).mpr contMDiff_id

/-- A `ℝ⁷`-diffeomorphism of `Mk (-2)` onto `S⁷` is a capping diffeomorphism. -/
theorem cappingDiffeo_of_diffeo
    (e : Submission.Milnor.Mk (-2) ≃ₘ⟮𝓡 7, 𝓡 7⟯ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1)) :
    IsCappingDiffeo ⇑e :=
  ⟨idDiffeomorph.trans e, rfl⟩

end Assembly

/-- **The remaining gap.**  There is no smooth identification of the sphere bundle `Mk (-2)` (the
unit sphere bundle of Milnor's rank-`4` bundle over `S⁴` with Euler number `1`) with `S⁷`.  This is
the exoticness of `Mk (-2)`, and it is exactly what `Submission.lean` still needs. -/
theorem no_cappingDiffeo (F : Submission.Milnor.Mk (-2) →
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1)) (hF : IsCappingDiffeo F) : False :=
  no_cappingDiffeo_of_cappedCongruence cappedCongruence F hF

end

end Work.Milnor
