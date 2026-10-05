import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.Geometry
import Submission.Work.RPB.Port.Drive.smooth_jordan_separation
import Submission.Work.RPB.B1.jordan_separation_smooth
import Submission.Work.RPB.B1.jordan_separation_C
import Submission.Work.RPB1a.exists_smooth_embedding_descend
import Submission.Work.RPB1a.isJordanCurveSet_range_of_descend
import Submission.Work.RPB1a.frontier_image_of_open_closure
import Submission.Work.RPB1a.outside_transport

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real Topology Manifold
open Manifold
open Work.RPB1a

/-- N4: a smooth loop bounds a Jordan domain `D`, with `frontier D = range v`, `Dᶜ` connected and
`range v` homeomorphic to the circle.

Route (in-house; `TauCeti.IsJordanCurve` is the definitionally identical `IsJordanCurveSet`, so no
outside library is needed).  Transfer `v` to `ℝ × ℝ` with `Complex.equivRealProdCLM` and descend it
through `Circle.exp` to an embedding `γ : Circle → ℝ × ℝ` (`Work.RPB.B1.jordan_separation_C`
exports `exists_continuous_descend`; regularity and immersion come from `v` being a smooth
immersed loop, so `γ` is an `IsSmoothEmbedding`, cf. `Work.RPB.B1.jordan_separation_smooth`).
`Work.RPB.Port.Drive.smooth_jordan_separation γ hγ` then gives `ins`, `out` with
`IsOpen`, `IsPathConnected`, `ins` bounded nonempty, `out` unbounded nonempty,
`(range γ)ᶜ = ins ∪ out`, `Disjoint ins out`, **and the closure facts**
`closure ins = ins ∪ range γ`, `closure out = out ∪ range γ`.

Take `D := e.symm '' ins`.  Then: `IsOpen D`, `IsConnected D` (path-connected); `Bornology.IsBounded
D`; `Disjoint D (range v)` (from `range v = e.symm '' range γ`); `frontier D = range v` (from
`IsOpen ins` and `closure ins = ins ∪ range γ`); `range v ⊆ closure (D ∪ range v)ᶜ`, because
`(D ∪ range v)ᶜ = e.symm '' out` and `range v ⊆ closure (e.symm '' out)` by the second closure fact;
`IsConnected Dᶜ`, because `Dᶜ = e.symm '' (closure out)` and closures of connected sets are
connected; and `IsJordanCurveSet (frontier D)`, i.e. `Nonempty (frontier D ≃ₜ Circle)` with
`frontier D = range v = e.symm '' range γ`, from the embedding `γ` of the compact space `Circle`
into `ℝ × ℝ` (a continuous injective map on a compact Hausdorff space is an embedding). -/
theorem jordan_domain_of_loop (v : ℝ → ℂ) (hv : IsSmoothLoop v) :
    ∃ D : Set ℂ, IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧ Disjoint D (range v) ∧
      frontier D = range v ∧ range v ⊆ closure (D ∪ range v)ᶜ ∧ IsConnected Dᶜ ∧
      IsJordanCurveSet (frontier D) := by
  -- Descend the loop to an embedded circle `γ : Circle → ℝ × ℝ`.
  obtain ⟨γ, hemb, _hγcont, _hγinj, _hγexp, hrangeγ⟩ := exists_smooth_embedding_descend v hv
  -- `range v` is the image of `range γ` under the inverse linear homeomorphism.
  have hrangev : Set.range v = Complex.equivRealProdCLM.symm '' Set.range γ := by
    rw [hrangeγ, Set.image_image]
    have hcomp : (fun x : ℂ => Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM x))
        = id := by
      funext x
      exact ContinuousLinearEquiv.symm_apply_apply _ x
    rw [hcomp, Set.image_id]
  -- Jordan separation in `ℝ × ℝ`, with the closure facts.
  obtain ⟨ins, out, hinsopen, _houtopen, hinspc, houtpc, hinsbdd, _houtbdd, _hinsne, _houtne,
    hcover, hdisj, hcl1, hcl2⟩ :=
    Work.RPB.Port.Drive.smooth_jordan_separation γ hemb
  -- `ins` misses the curve.
  have hins_sub : ins ⊆ (Set.range γ)ᶜ := by
    intro x hx
    rw [hcover]
    exact Or.inl hx
  have hdisj_ins : Disjoint ins (Set.range γ) := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact hins_sub ha hb
  -- The image of `ins` under the inverse linear homeomorphism is open on the `ℂ` side.
  have hpre : ∀ s : Set (ℝ × ℝ),
      Complex.equivRealProdCLM.symm '' s = Complex.equivRealProdCLM ⁻¹' s := by
    intro s
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨Complex.equivRealProdCLM x, by simpa using hx,
        ContinuousLinearEquiv.symm_apply_apply _ x⟩
  refine ⟨Complex.equivRealProdCLM.symm '' ins, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- open
    rw [hpre ins]
    exact hinsopen.preimage Complex.equivRealProdCLM.continuous
  · -- connected
    exact hinspc.isConnected.image ⇑Complex.equivRealProdCLM.symm
      Complex.equivRealProdCLM.symm.continuous.continuousOn
  · -- bounded
    exact Complex.equivRealProdCLM.symm.lipschitzWith.isBounded_image hinsbdd
  · -- disjoint from the curve
    rw [hrangev]
    refine (Set.subset_compl_iff_disjoint_left.mp ?_).symm
    rw [← Set.image_compl_eq (f := ⇑Complex.equivRealProdCLM.symm)
      (Complex.equivRealProdCLM.symm.bijective)]
    exact Set.image_mono hins_sub
  · -- frontier
    exact frontier_image_of_open_closure ins γ v hinsopen hcl1 hdisj_ins hrangev
  · -- the curve lies in the closure of the outside
    exact (outside_transport ins out γ v houtpc hcover hdisj hcl2 hrangev).1
  · -- the complement is connected
    exact (outside_transport ins out γ v houtpc hcover hdisj hcl2 hrangev).2
  · -- the frontier is homeomorphic to the circle
    rw [frontier_image_of_open_closure ins γ v hinsopen hcl1 hdisj_ins hrangev]
    exact isJordanCurveSet_range_of_descend v γ hemb hrangeγ

end Work.RPB1a
