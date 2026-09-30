/-
# The area `Final/`: everything in one import

`import Submission.Work.Final.All` brings in the whole final wiring of the challenge theorem:

* `Work.Final.FinalInputs` — **the remaining inputs**, in one class: the assembled space `M̂`
  (`Work.Space.RTData`), the smoothness of its Levi-Civita connection, the parametric curvature
  bound `∀ K > 0, RauchK.CurvLe lcConn K`, the Mayer–Vietoris long exact sequence `L` of the cover
  `M̂ = A ∪ B`, the identifications `eM`, `eN` with the free models, the commuting square `hsq`
  with the concrete matrix `wConcrete`, the identification `hX` of the `X`-slot with the singular
  homology of `M̂`, and `h0 : H_0(M̂) ≅ ℤ`.
* `Work.Final.Mhat4` — `M̂` as a `Closed4Manifold`, with every instance field from
  `Work.Space.RTData`.
* `Work.Final.isAspherical_Mhat4` — Cartan–Hadamard: `M̂` is aspherical.  The connection is the
  Levi-Civita connection `Work.LeviCivita.lcConn`, with `lcConn_compat` and `lcConn_torsion`
  delivered, and the curvature bound is the field `curvLe`.
* `Work.Final.isIntegerHomologySphere_Mhat4` — Mayer–Vietoris: `H_k(M̂; ℤ) ≅ H_k(S⁴; ℤ)` in every
  degree, from `Work.HomologyMV.intHomology_of_concrete` and
  `Work.Homology.intHomology_sphere_four`.
* `Work.Final.aspherical_integer_homology_four_sphre` — **the challenge theorem**, from a single
  `instance : FinalInputs`.
* `Work.Final.FinalInputs.ofSecNonpos` — the variant in which the curvature input is the pointwise
  `sec ≤ 0` form produced by the curvature bridge (turned into `curvLe` by
  `Work.CartanHadamard.curvLe_all`).
* `Work.Final.FinalInputs.ofConnected` — the variant in which the degree-`0` input `h0` is derived
  from `hX 0` and the path connectedness of `M̂`.
* `Work.Final.coverMVLES` — the Mayer–Vietoris long exact sequence of an open cover, in the index
  convention of `Work.HomologyMV.MVLES`; together with `coverMVLES_hX` it produces the fields `L`
  and `hX` of `FinalInputs` (see `FinalInputs.ofCover`).

See `NOTES_FINAL.md` for the report.
-/
import Submission.Work.Final.Framework
import Submission.Work.Final.Basic
import Submission.Work.Final.Mhat
import Submission.Work.Final.Homology
import Submission.Work.Final.Cover
import Submission.Work.Final.MhatCover
import Submission.Work.Final.Main
import Submission.Work.Final.Discharge
import Submission.Work.Final.mvRightX_zero_surjective
import Submission.Work.Final.chrB_eq_koszulChr
import Submission.Work.Final.secNonpos_of_chartModels
import Submission.Work.Final.curvLe_of_models
import Submission.Work.Final.CurvField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Final

end Work.Final
