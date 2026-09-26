import Mathlib
import Submission.Work.Smooth.OneManifold.Defs
import Submission.Work.Smooth.OneManifold.Basic
import Submission.Work.Smooth.OneManifold.Plane.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.Plane.Slicing

namespace Work.EpsW

open Set

open LeanEval.KnotTheory.PardonDistortion in
/-- **The image of the open interval under an injective arc is a topological `1`-manifold.**  If `F : [0,1] → ℝ³` is continuous and injective then `F '' (0,1)` is locally Euclidean of dimension one: `F` is a homeomorphism of the compact interval onto its image (`Continuous.homeoOfEquivCompactToT2`), and the restriction to the open interval is a homeomorphism onto `F '' (0,1)`, which is therefore homeomorphic to the open interval. -/
theorem localEuclidean_image_Ioo {F : C(Work.Smooth.Plane.ArcInterval, R3)}
    (hF : Function.Injective F) :
    Work.Smooth.OneManifold.IsLocallyEuclidean
      (F '' {x : Work.Smooth.Plane.ArcInterval | (x : ℝ) ∈ Set.Ioo 0 1}) := by
  -- the open interval inside the closed interval `[0,1]`
  set I : Set Work.Smooth.Plane.ArcInterval := {x | (x : ℝ) ∈ Set.Ioo 0 1} with hIdef
  -- `I` is homeomorphic to `(0,1) ⊆ ℝ`, which is locally an arc
  have hIoo : Work.Smooth.SphereJordan.IsLocallyArc ↥I :=
    Work.Smooth.OneManifold.isLocallyArc_of_homeomorph
      (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph
        (U := Set.Icc (0:ℝ) 1) (s := Set.Ioo (0:ℝ) 1) Set.Ioo_subset_Icc_self)
      (Work.Smooth.OneManifold.isLocallyArc_Ioo 0 1)
  -- `F` is a homeomorphism of the compact interval onto its image
  have hZsub : F '' I ⊆ Set.range (F : Work.Smooth.Plane.ArcInterval → R3) := by
    rintro z ⟨x, hx, rfl⟩; exact ⟨x, rfl⟩
  let Fr : Work.Smooth.Plane.ArcInterval →
      ↥(Set.range (F : Work.Smooth.Plane.ArcInterval → R3)) :=
    fun x => ⟨F x, ⟨x, rfl⟩⟩
  have hFr_inj : Function.Injective Fr := by
    intro x y hxy
    exact hF (congrArg Subtype.val hxy)
  have hFr_surj : Function.Surjective Fr := by
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := hz
    exact ⟨x, rfl⟩
  have hFr_cont : Continuous Fr := Continuous.subtype_mk F.continuous (fun x => ⟨x, rfl⟩)
  let e : Work.Smooth.Plane.ArcInterval ≃ₜ
      ↥(Set.range (F : Work.Smooth.Plane.ArcInterval → R3)) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective Fr ⟨hFr_inj, hFr_surj⟩) hFr_cont
  have he_apply : ∀ x, (e x : R3) = F x := fun x => rfl
  -- `e` carries `I` onto `F '' I`
  have hiff : ∀ x : Work.Smooth.Plane.ArcInterval, (x ∈ I ↔ (e x : R3) ∈ F '' I) := by
    intro x
    rw [he_apply]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := hF hyx
      rwa [this] at hy
  have hsub : ↥I ≃ₜ
      ↥{y : ↥(Set.range (F : Work.Smooth.Plane.ArcInterval → R3)) | (y : R3) ∈ F '' I} :=
    Homeomorph.subtype e hiff
  -- assemble the homeomorphism `↥I ≃ₜ ↥(F '' I)`
  let φ : ↥I ≃ₜ ↥(F '' I) :=
    hsub.trans (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph hZsub).symm
  exact Work.Smooth.OneManifold.isLocallyArc_of_homeomorph φ hIoo

end Work.EpsW
