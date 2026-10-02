import Submission.Work.Tubular.Collapse

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# The API of a tube chart

The consequences of the tubular neighbourhood theorem as recorded in `Work.Tubular.TubeChart`:

* `Work.Tubular.TubeChart.tubeMap_injOn` — the tubular map is injective on the closed disc bundle;
* `Work.Tubular.TubeChart.isCompact_U` — the tube is compact (it is the continuous image of the
  compact closed disc bundle, `Work.Tubular.compactSpace_normalDiscSub`);
* `Work.Tubular.TubeChart.exists_box` — the tube is contained in a coordinate box, hence the collapse
  is constant on the boundary of a large cube (`Work.Tubular.tubeGenLoop`);
* `Work.Tubular.TubeChart.tubeMap_mem_openTube_iff` — the open tube is exactly the image of the open
  disc bundle, so `tubeMap` restricts to a bijection of the open disc bundle onto the open tube;
* `Work.Tubular.TubeChart.continuousOn_openTube_inv` — the inverse is continuous on the open tube.
-/

open scoped Manifold ContDiff Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {N : ℕ} {E : EmbeddingData V N} {ε : ℝ}

namespace TubeChart

/-- The tubular map is injective on the closed `ε`-disc bundle: its inverse is `inv`. -/
theorem tubeMap_injOn (C : TubeChart E ε) :
    Set.InjOn (tubeMap E) {p : NormalTotal E | normalNorm E p ≤ ε} :=
  fun p hp q hq h => by
    rw [← C.inv_tubeMap p hp, ← C.inv_tubeMap q hq, h]

/-- The tubular map is surjective from the closed disc bundle onto the tube. -/
theorem tubeMap_surjOn (C : TubeChart E ε) :
    ∀ y ∈ C.U, ∃ p : NormalTotal E, normalNorm E p ≤ ε ∧ tubeMap E p = y :=
  fun y hy => ⟨C.inv y, C.inv_mem y hy, C.tubeMap_inv y hy⟩

/-- The tube is exactly the image of the closed disc bundle. -/
theorem image_normalClosedDiscSet (C : TubeChart E ε) :
    tubeMap E '' {p : NormalTotal E | normalNorm E p ≤ ε} = C.U := C.image_closedDiscSet

/-- **The tube is compact**, being the continuous image of the closed disc bundle
(`Work.Tubular.compactSpace_normalDiscSub`). -/
theorem isCompact_U (C : TubeChart E ε) [CompactSpace (NormalDiscSub E ε)] : IsCompact C.U := by
  rw [← image_normalClosedDiscSet C]
  have h := (isCompact_univ (X := NormalDiscSub E ε)).image
      ((continuous_tubeMap E).comp continuous_subtype_val)
  rw [Set.image_comp, Subtype.coe_image_univ] at h
  exact h

/-- **The tube is contained in a box.**  Since `C.U` is the image of the closed disc bundle under
`(x,w) ↦ e x + w`, and `e` is continuous on the compact `V.pt` while `‖w‖ ≤ ε`, the tube is bounded
in every coordinate — this is the radius `R` for which the collapse is constant on the boundary of
the cube (see `Work.Tubular.tubeCollapseCube_boundary`). -/
theorem exists_box (C : TubeChart E ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ y ∈ C.U, ∀ i : Fin N, |y i| < R := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x : V.pt, ‖E.e x‖ ≤ M := by
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_univ
      (E.smooth.continuous.continuousOn : ContinuousOn E.e Set.univ)
    exact ⟨M, fun x => hM x (Set.mem_univ x)⟩
  refine ⟨|M| + ε + 2, by have := C.eps_pos; positivity, fun y hy i => ?_⟩
  rw [← image_normalClosedDiscSet C] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  have hle : |(tubeMap E p) i| ≤ ‖tubeMap E p‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (tubeMap E p) i
  have hbd : ‖tubeMap E p‖ < |M| + ε + 2 := by
    calc ‖tubeMap E p‖ = ‖E.e p.1.1 + p.1.2‖ := rfl
      _ ≤ ‖E.e p.1.1‖ + ‖p.1.2‖ := norm_add_le _ _
      _ ≤ M + ε := by
          have : ‖p.1.2‖ ≤ ε := hp
          linarith [hM p.1.1]
      _ < |M| + ε + 2 := by
          have := le_abs_self M
          linarith
  exact lt_of_le_of_lt hle hbd

/-- A point of the ambient space lies in the open tube exactly when its normal foot lies in the open
disc bundle. -/
theorem mem_openTube_iff (C : TubeChart E ε) {y : Euc N} :
    y ∈ C.openTube ↔ ∃ p : NormalTotal E, normalNorm E p < ε ∧ tubeMap E p = y :=
  Iff.rfl

/-- The tubular map of a point of the open disc bundle lies in the open tube. -/
theorem tubeMap_mem_openTube (C : TubeChart E ε) {p : NormalTotal E}
    (hp : normalNorm E p < ε) : tubeMap E p ∈ C.openTube :=
  ⟨p, hp, rfl⟩

/-- The normal foot of a point of the open tube lies in the open disc bundle. -/
theorem normalNorm_inv_lt (C : TubeChart E ε) {y : Euc N} (hy : y ∈ C.openTube) :
    normalNorm E (C.inv y) < ε := by
  obtain ⟨p, hp, hpy⟩ := hy
  rw [← hpy, C.inv_tubeMap p (le_of_lt hp)]
  exact hp

/-- The inverse of the tubular map is a left inverse on the open tube. -/
theorem inv_tubeMap_of_mem_openTube (C : TubeChart E ε) {y : Euc N} (hy : y ∈ C.openTube) :
    tubeMap E (C.inv y) = y :=
  C.tubeMap_inv y (C.openTube_subset_U hy)

/-- The inverse of the tubular map is continuous on the open tube. -/
theorem continuousOn_openTube_inv (C : TubeChart E ε) :
    ContinuousOn C.inv C.openTube :=
  C.continuousOn_inv.mono C.openTube_subset_U

/-- The inverse of the tubular map is smooth on the open tube. -/
theorem contMDiffOn_openTube_inv (C : TubeChart E ε) :
    ContMDiffOn 𝓘(ℝ, Euc N) ((𝓡 8).prod 𝓘(ℝ, Euc N)) ∞
      (fun y => ((C.inv y).1.1, (C.inv y).1.2)) C.openTube :=
  C.contMDiffOn_inv

/-- The open tube is a neighbourhood of the image of the embedding. -/
theorem image_subset_openTube (C : TubeChart E ε) : Set.range E.e ⊆ C.openTube :=
  fun _ ⟨x, hx⟩ => hx ▸ C.mem_openTube x

/-- The normal foot of a point of the open tube is the unique point of the open disc bundle mapping
to it. -/
theorem eq_inv_of_tubeMap_eq (C : TubeChart E ε) {p : NormalTotal E} (hp : normalNorm E p < ε)
    {y : Euc N} (hy : tubeMap E p = y) : C.inv y = p := by
  rw [← hy, C.inv_tubeMap p (le_of_lt hp)]

end TubeChart

/-- **The tubular map restricts to a bijection of the open disc bundle onto the open tube**, with
inverse the normal-foot map `inv`.  This is the "homeomorphism onto an open neighbourhood of `V`"
form of the tubular neighbourhood theorem; continuity of the inverse is
`Work.Tubular.TubeChart.continuousOn_openTube_inv`. -/
theorem tubeMap_bijective_openDisc (C : TubeChart E ε) :
    Set.BijOn (tubeMap E) {p : NormalTotal E | normalNorm E p < ε} C.openTube := by
  refine ⟨fun p hp => C.tubeMap_mem_openTube hp, ?_, ?_⟩
  · intro p hp q hq h
    rw [← C.inv_tubeMap p (le_of_lt hp), ← C.inv_tubeMap q (le_of_lt hq), h]
  · intro y hy
    exact ⟨C.inv y, C.normalNorm_inv_lt hy, C.inv_tubeMap_of_mem_openTube hy⟩

end

end Work.Tubular
