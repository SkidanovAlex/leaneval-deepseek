import Mathlib
import Submission.Work.EQ.exists_uniformizing_cover
import Submission.Work.EQ.H0_regular_aux
import Submission.Work.EQ.isOpen_image_connectedComponent_of_isLocalHomeomorph
import Submission.Work.EQ.H0_secondCountable

set_option linter.style.haveILetI false

open scoped Manifold Topology
open _root_.Topology

namespace Work.EQ

/-- **Restriction of a local homeomorphism to a connected component.**  If `f : X → Y` is a local
homeomorphism with locally connected codomain and `x : X`, then the restriction of `f` to the
connected component of `x` is again a local homeomorphism.

Around `y ∈ connectedComponent x` the map `f` agrees with an open partial homeomorphism `e`.  Let
`D := connectedComponentIn e.target (e y)` be the connected component of `e y` in the open set
`e.target`, an open connected neighbourhood of `e y`, and `U := e.symm '' D`.  Then `e.symm '' D`
is open, and, being a continuous image of a connected set containing `y`, it is contained in
`connectedComponent y = connectedComponent x`.  Hence `e` restricts to a homeomorphism
`U ≅ D` with `U` open in `connectedComponent x`, which is the desired chart. -/
theorem isLocalHomeomorph_subtype_connectedComponent {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyConnectedSpace Y] {f : X → Y} (hf : IsLocalHomeomorph f) (x : X) :
    IsLocalHomeomorph (fun y : ↥(connectedComponent x) => f y) := by
  classical
  refine IsLocalHomeomorph.mk _ fun y => ?_
  obtain ⟨e, hye, he⟩ := hf (y : X)
  set D : Set Y := connectedComponentIn e.target (e (y : X)) with hDdef
  have hDopen : IsOpen D := e.open_target.connectedComponentIn
  have hDsub : D ⊆ e.target := connectedComponentIn_subset _ _
  have hDmem : e (y : X) ∈ D := mem_connectedComponentIn (e.map_source hye)
  set U : Set X := e.symm '' D with hUdef
  have hUopen : IsOpen U :=
    e.symm.isOpen_image_of_subset_source hDopen
      (by rw [OpenPartialHomeomorph.symm_source]; exact hDsub)
  have hUsub : U ⊆ connectedComponent (y : X) := by
    have hconn : IsPreconnected U :=
      isPreconnected_connectedComponentIn.image _ (e.continuousOn_symm.mono hDsub)
    have hymem : (y : X) ∈ U := ⟨e (y : X), hDmem, e.left_inv hye⟩
    exact hconn.subset_connectedComponent hymem
  have hUsubS : U ⊆ connectedComponent x := by
    rw [connectedComponent_eq y.2]
    exact hUsub
  have hfval : ∀ q : ↥(connectedComponent x), f q = e q := fun q => congrFun he q
  refine ⟨{ toFun := fun q => f q
            invFun := fun z => if hz : z ∈ D then
              (⟨e.symm z, hUsubS ⟨z, hz, rfl⟩⟩ : ↥(connectedComponent x)) else y
            source := Subtype.val ⁻¹' U
            target := D
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := hUopen.preimage continuous_subtype_val
            open_target := hDopen
            continuousOn_toFun := (hf.continuous.comp continuous_subtype_val).continuousOn
            continuousOn_invFun := ?_ }, ?_, ?_⟩
  · rintro q ⟨z, hzD, hz⟩
    have h1 : f q = z := by rw [hfval q, ← hz, e.right_inv (hDsub hzD)]
    rwa [h1]
  · rintro z hz
    simp only [dite_eq_left hz]
    exact ⟨z, hz, rfl⟩
  · rintro q ⟨z, hzD, hz⟩
    have h1 : f q = z := by rw [hfval q, ← hz, e.right_inv (hDsub hzD)]
    simp only [h1, dite_eq_left hzD]
    exact Subtype.ext hz
  · rintro z hz
    simp only [dite_eq_left hz]
    rw [he]
    exact e.right_inv (hDsub hz)
  · rw [continuousOn_iff_continuous_domRestrict]
    have hcont : Continuous (fun w : D => e.symm (w : Y)) :=
      (e.continuousOn_symm.mono hDsub).domRestrict
    have h1 : Continuous (fun w : D => (⟨e.symm (w : Y), ⟨(w : Y), w.2, rfl⟩⟩ : ↥U)) :=
      hcont.subtype_mk _
    have h2 : Continuous (fun w : D =>
        (⟨e.symm (w : Y), hUsubS ⟨(w : Y), w.2, rfl⟩⟩ : ↥(connectedComponent x))) :=
      (continuous_inclusion hUsubS).comp h1
    have heq : (D.domRestrict (fun z => if hz : z ∈ D then
          (⟨e.symm z, hUsubS ⟨z, hz, rfl⟩⟩ : ↥(connectedComponent x)) else y))
        = fun w : D => (if hz : (w : Y) ∈ D then
          (⟨e.symm (w : Y), hUsubS ⟨(w : Y), hz, rfl⟩⟩ : ↥(connectedComponent x)) else y) := by
      funext w
      rfl
    rw [heq]
    refine h2.congr fun w => ?_
    symm
    rw [dite_eq_left w.2]
  · exact ⟨e (y : X), hDmem, e.left_inv hye⟩
  · intro q hq
    rfl

/-- **No connected component of `H0` is compact** (the version of
`Work.EQ.not_compactSpace_connectedComponent` without the spurious `LocallyConnectedSpace (H0 a h)`
hypothesis).  If `S := connectedComponent P` were compact, then `ψ₁ '' S` would be compact and open
in `ℂ` — openness is `Work.EQ.isOpen_image_connectedComponent_of_isLocalHomeomorph`, which uses the
local connectedness of `ℂ` rather than of `H0` — and nonempty, hence a clopen nonempty subset of
the connected space `ℂ`, so all of `ℂ`.  But `ψ₁` never vanishes on `H0`
(`Work.EQ.psi1_ne_zero_of_mem`), a contradiction. -/
theorem not_compactSpace_connectedComponent_of_isLocalHomeomorph {a : ℝ} {h : ℂ → ℂ}
    (hét : IsLocalHomeomorph (fun q : H0 a h => (q : ChainData).2.1)) (P : H0 a h) :
    ¬ CompactSpace ↥(connectedComponent P) := by
  intro hcomp
  haveI : CompactSpace ↥(connectedComponent P) := hcomp
  set φ : ↥(connectedComponent P) → ℂ := fun q => (((q : H0 a h)) : ChainData).2.1 with hφ
  have hφcont : Continuous φ := hét.continuous.comp continuous_subtype_val
  have hrange : Set.range φ =
      (fun q : H0 a h => (q : ChainData).2.1) '' connectedComponent P := by
    ext z; constructor
    · rintro ⟨q, rfl⟩; exact ⟨(q : H0 a h), q.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  have hopen : IsOpen (Set.range φ) := by
    rw [hrange]
    exact isOpen_image_connectedComponent_of_isLocalHomeomorph hét P
  have hcompact : IsCompact (Set.range φ) := isCompact_range hφcont
  have hne : (Set.range φ).Nonempty := ⟨φ ⟨P, mem_connectedComponent⟩, ⟨_, rfl⟩⟩
  have hclopen : IsClopen (Set.range φ) := ⟨hcompact.isClosed, hopen⟩
  have huniv : Set.range φ = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    exact isPreconnected_univ.subset_isClopen hclopen (by simpa using hne)
  have hzero : (0 : ℂ) ∈ Set.range φ := by rw [huniv]; exact Set.mem_univ 0
  obtain ⟨q, hq⟩ := hzero
  exact psi1_ne_zero_of_mem (q : H0 a h).2 hq

/-- **Uniformization of a component of `H0` (Rychlik Theorem 10–11, step 1).**  Every connected
component `S` of `H0` is a Riemann surface (spread over `ℂ` by `ψ₁`) which is holomorphically
covered either by the plane `ℂ` or by the upper half plane `ℍ` (equivalently, by the unit disc
after the Cayley transform).

Route.  `S := connectedComponent P` is connected, Hausdorff and second countable
(`Work.EQ.H0_secondCountable`), and `ψ₁` restricts to a local homeomorphism `S → ℂ`: for `x ∈ S`
and a local inverse `e` of `ψ₁` at `x`, the restriction of `e` to a small connected open subset of
`e.target` containing `e x`, pulled back along `e.symm`, is a chart.  With
`Work.EQ.UnivCover.exists_chartedSpace_of_isLocalHomeomorph` (target `ℂ`) this makes `S` a
complex 1-manifold spread over `ℂ`, i.e. a Riemann surface (`IsManifold mℂ 1 S`).
`S` is not compact: the argument of `Work.EQ.not_compactSpace_connectedComponent` — if `S` were
compact then `ψ₁ '' S` would be compact and open in `ℂ` (openness is
`Work.EQ.isOpen_image_connectedComponent_of_isLocalHomeomorph`; the existing
`Work.EQ.not_compactSpace_connectedComponent` carries an extra `LocallyConnectedSpace (H0 a h)`
hypothesis which is NOT needed and is not an instance, so redo that step) and would avoid `0`
(`Work.EQ.psi1_ne_zero_of_mem`), hence would be a nonempty clopen proper subset of the connected
space `ℂ`, absurd.  Then apply `Work.EQ.exists_uniformizing_cover` to `S` (note `mℂ` is
`modelWithCornersSelf ℂ ℂ`). -/
theorem H0_component_uniformization {a : ℝ} {h : ℂ → ℂ}
    (hét : IsLocalHomeomorph (fun q : H0 a h => (q : ChainData).2.1)) (P : H0 a h) :
    ∃ (_ : ChartedSpace ℂ ↥(connectedComponent P)),
      IsManifold (modelWithCornersSelf ℂ ℂ) 1 ↥(connectedComponent P) ∧
        ((∃ p : ℂ → ↥(connectedComponent P),
            IsCoveringMap p ∧ MDifferentiable (modelWithCornersSelf ℂ ℂ)
              (modelWithCornersSelf ℂ ℂ) p) ∨
          ∃ p : UpperHalfPlane → ↥(connectedComponent P),
            IsCoveringMap p ∧ MDifferentiable (modelWithCornersSelf ℂ ℂ)
              (modelWithCornersSelf ℂ ℂ) p) := by
  have hφ : IsLocalHomeomorph (fun q : ↥(connectedComponent P) =>
      ((q : H0 a h) : ChainData).2.1) :=
    isLocalHomeomorph_subtype_connectedComponent hét P
  obtain ⟨instC, hman, -⟩ :=
    UnivCover.exists_chartedSpace_of_isLocalHomeomorph (X := ℂ) hφ
  letI : ChartedSpace ℂ ↥(connectedComponent P) := instC
  haveI : IsManifold (modelWithCornersSelf ℂ ℂ) 1 ↥(connectedComponent P) := hman
  haveI : SecondCountableTopology ↥(connectedComponent P) := H0_component_secondCountable P
  haveI : PreconnectedSpace ↥(connectedComponent P) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
  haveI : Nonempty ↥(connectedComponent P) := ⟨P, mem_connectedComponent⟩
  haveI : ConnectedSpace ↥(connectedComponent P) :=
    (connectedSpace_iff _).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨instC, hman,
    exists_uniformizing_cover (X := ↥(connectedComponent P))
      (not_compactSpace_connectedComponent_of_isLocalHomeomorph hét P)⟩

end Work.EQ
