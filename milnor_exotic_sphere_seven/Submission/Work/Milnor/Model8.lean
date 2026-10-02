import Mathlib
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.Collar
import Submission.Work.Morse.Transfer
import Submission.Work.Milnor.mk_to_vk

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A common model space for the disc bundle and `ℝ⁸`

The closed `8`-manifold `X = D(ξ) ∪_F D⁸` of `Submission/NOTES.md` §9.3 is built by gluing the
open disc bundle `Vk (-2)` to `ℝ⁸` along open collars, in the sense of `Submission.Glue.Data`.
`Glue.Data` requires both pieces to be charted on the *same* model space `H`; `Vk k` is charted on
`MSpace8 = ℝ⁴ × ℍ`, so here we put the same model on `ℝ⁸`:

* `vkModelIso : ℝ⁴ × ℍ ≃ ℝ⁸` (a continuous linear equivalence);
* `instChartedSpaceEuclid8` — the charted space structure on `ℝ⁸` obtained by pushing the standard
  structure forward along `vkModelIso.symm`, i.e. modelling `ℝ⁸` on `MSpace8`;
* `instIsManifoldEuclid8` — with that structure, `ℝ⁸` is a smooth `MSpace8`-manifold;
* `CapData` — the type of gluing data on the pair `(Vk (-2), ℝ⁸)` over the model `MSpace8`;
* `cappedSpace D` — the glued space itself, the closed `8`-manifold `X`.

The two pushed instances are given a **low priority** so that they can never win a type class search
against the pre-existing instances of the library (in particular `𝓡 8`-smoothness of `ℝ⁸` itself);
they are only found when the model `MSpace8` is explicitly wanted.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor

noncomputable section

/-- The linear isometry `ℝ⁴ × ℍ ≃ ℝ⁸` identifying the model space of the disc bundle `Vk k` with
`ℝ⁸`. -/
def vkModelIso : MSpace8 ≃L[ℝ] EuclideanSpace ℝ (Fin 8) :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4)))
      Quaternion.linearIsometryEquivTuple.toContinuousLinearEquiv).trans
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 4) (m := 4)).symm

/-- The charted space structure on `ℝ⁸` modelled on `MSpace8 = ℝ⁴ × ℍ`, obtained by pushing the
standard atlas forward along `vkModelIso.symm`.  Low priority: it never competes with the standard
`ℝ⁸`-structures. -/
instance (priority := 10) instChartedSpaceEuclid8 :
    ChartedSpace MSpace8 (EuclideanSpace ℝ (Fin 8)) :=
  Work.Morse.pushChartedSpace (Work.Morse.modelHomeo (𝓡 8) vkModelIso.symm)

/-- With the pushed charted space structure, `ℝ⁸` is a smooth manifold modelled on `MSpace8`. -/
instance (priority := 10) instIsManifoldEuclid8 :
    IsManifold 𝓘(ℝ, MSpace8) ∞ (EuclideanSpace ℝ (Fin 8)) :=
  Work.Morse.push_isManifold (M := EuclideanSpace ℝ (Fin 8)) (I := 𝓡 8) vkModelIso.symm

/-- The type of gluing data on the pair `(Vk (-2), ℝ⁸)` over the common model space `MSpace8`.
An element of `CapData` is a pair of open collars (one in the disc bundle `ξ = Vk (-2)`, one in
`ℝ⁸`) together with a *diffeomorphism* between them; its glued space is the closed `8`-manifold
`X = D(ξ) ∪_F D⁸`.  The diffeomorphism is only available when `Mk (-2) ≅ S⁷` smoothly, i.e. inside
the proof by contradiction of the theorem. -/
def CapData : Type _ :=
  Submission.Glue.Data 𝓘(ℝ, MSpace8) ∞ (Vk (-2)) (EuclideanSpace ℝ (Fin 8))

/-- The glued space of a capping datum: the closed `8`-manifold `X = D(ξ) ∪_F D⁸`, as a type with
its quotient topology.  It is a smooth manifold by `Work.Glue.glued_isManifold`. -/
abbrev cappedSpace (D : CapData) : Type _ := D.Glued

/-- A *smooth identification* of the sphere bundle `Mk (-2)` with the unit sphere `S⁷ ⊆ ℝ⁸`, i.e.
the data used to cap the disc bundle.  (This is the hypothesis of the proof by contradiction: such
an `F` exists only if `Mk (-2)` is diffeomorphic to `S⁷`.)  It is recorded as a bundled
diffeomorphism, so that statements about it can be written with unbundled names. -/
def IsCappingDiffeo
    (F : Submission.Milnor.Mk (-2) → Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) : Prop :=
  ∃ (e : Submission.Milnor.Mk (-2) ≃ₘ⟮(𝓡 4).prod (𝓡 3), 𝓡 7⟯
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1), ⇑e = F

/-- The conditions on a capping datum `D`: the glued collars are the collar of the disc bundle and
the exterior of the ball of radius `1/2` in `ℝ⁸`, and the identification on the unit sphere bundle
is `F`.  These conditions pin down the glued manifold `X = D(ξ) ∪_F D⁸` up to diffeomorphism. -/
def IsCappingDatum
    (F : Submission.Milnor.Mk (-2) → Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1)
    (D : CapData) : Prop :=
  D.U = collar (-2) ∧ D.V = {z : EuclideanSpace ℝ (Fin 8) | 1 / 2 < ‖z‖} ∧
    (∀ q : Submission.Milnor.Mk (-2),
      (D.φ (mkToVkFun (-2) q) : EuclideanSpace ℝ (Fin 8)) =
        (F q : EuclideanSpace ℝ (Fin 8)))

end

end Work.Milnor
