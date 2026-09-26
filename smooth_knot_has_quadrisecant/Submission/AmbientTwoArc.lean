import Mathlib
import Submission.RealIntervalShape

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

/-!
# S163 — the ambient two-arc theorem, slice (a): the coordinate
transport of the overlap along the arc charts (module
Submission/AmbientTwoArc.lean)

`RealIntervalShape.lean` (S162) supplied the real-line model: every
nonempty open connected subset of ℝ is homeomorphic to `(0,1)`, and the
union of two such sets with nonempty intersection is again one (the
coordinate two-arc union).  This module lifts the FIRST half of the
model to an ambient space `X`: given an open arc `U ⊆ X` with chart
`φ : (0,1) ≃ₜ {x // x ∈ U}` and any open set `V`, the overlap
`W = U ∩ V` transports to the chart as `A = {t ∈ (0,1) | φ t ∈ V}`, and
— when `W` is connected — `A` is again an open arc `A ≃ₜ (0,1)`
(**`overlap_pullback_arc`**).  The symmetric pullback `B` for the second
chart is the same theorem with `U,V` interchanged, and the two pullbacks
are identified by the canonical homeo `B ≃ₜ A` (both ≃ₜ
`{x // x ∈ U ∩ V}`).

Together these are exactly the "transporting the coordinates along the
overlapping chart" subgoals of the ambient two-arc theorem (ROADMAP
S153 slice (b2) / S162 STATUS slice (a)).  The ambient two-arc theorem
itself — for `X` Hausdorff + locally-interval-charted (a topological
1-manifold), `U,V` open arcs with `φ,ψ` charts and `U∩V` connected, the
union `U∪V ≃ₜ (0,1)` — assembles from this module by the four-step
outline recorded in the ROADMAP S163 entry: (1) pull both overlaps back
to the charts (this module, DONE); (2) classify the pullbacks as open
intervals `(a,b) ⊆ (0,1)` (RealIntervalShape, DONE); (3) the
facing-normalization: in a Hausdorff locally-interval ambient only the
facing/containment end-arrangements occur (branch-point exclusion at
seam points; the ROADMAP S154 correction — still OPEN, recorded as
lemma `facing_overlap_after_restriction`); (4) apply the ordered
two-chart gluing `two_chart_glue_homeo` (TwoChartGlue S157, DONE).  The
containment case `V ⊆ U` is fully proved here
(**`two_arc_contained`**).  Everything in this module is verified (no
axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- Coordinate transport of the overlap along a chart: for a chart
`φ : (0,1) ≃ₜ {x // x ∈ U}`, the pullback of `V` to the chart
`{t // (φ t : X) ∈ V}` is homeomorphic (via `φ`) to `{x : X // x ∈ U ∩ V}`. -/
noncomputable def overlapPullbackHomeo {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) :
    ({t : OpenRealInterval 0 1 // (φ t : X) ∈ V}) ≃ₜ {x : X // x ∈ U ∩ V} := by
  let A := {t : OpenRealInterval 0 1 // (φ t : X) ∈ V}
  let W := {x : X // x ∈ U ∩ V}
  let F : A → W := fun t => ⟨(φ t : X), ⟨(φ t).2, t.2⟩⟩
  let G : W → A := fun w => ⟨φ.symm ⟨(w : X), (w.2).1⟩, by
    have hx : (φ (φ.symm ⟨(w : X), (w.2).1⟩) : X) = (w : X) := by
      exact congrArg (fun z : {x : X // x ∈ U} => (z : X))
        (φ.apply_symm_apply ⟨(w : X), (w.2).1⟩)
    rw [hx]
    exact w.2.2⟩
  have hFG : Function.LeftInverse G F := by
    intro t
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ)) (φ.symm_apply_apply t)
    simpa [F, G] using h
  have hGF : Function.RightInverse G F := by
    intro w
    apply Subtype.ext
    exact congrArg (fun z : {x : X // x ∈ U} => (z : X))
      (φ.apply_symm_apply ⟨(w : X), (w.2).1⟩)
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact Continuous.subtype_val (φ.continuous.comp continuous_subtype_val)
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact φ.symm.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val (by intro w; exact w.2.1))
  let e : A ≃ W := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact Homeomorph.mk e hFc hGc

/-- Restricting a homeomorphism to a subset gives a homeomorphism onto the
image: `↑A ≃ₜ ↑(e '' A)`. -/
noncomputable def homeoRestrictImage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) : ({x : X // x ∈ A}) ≃ₜ ({y : Y // y ∈ e '' A}) := by
  let S := {x : X // x ∈ A}
  let T := {y : Y // y ∈ e '' A}
  let F : S → T := fun x => ⟨e x.1, by
    refine ⟨x.1, x.2, ?_⟩
    rfl⟩
  let G : T → S := fun y => ⟨e.symm y.1, by
    rcases y.2 with ⟨x, hxA, hx⟩
    have heq : e.symm y.1 = x := by
      apply e.injective
      rw [e.apply_symm_apply, hx]
    rwa [heq]⟩
  have hFG : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    exact e.symm_apply_apply x.1
  have hGF : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    dsimp [F, G]
    exact e.apply_symm_apply y.1
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact e.continuous.comp continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact e.symm.continuous.comp continuous_subtype_val
  let ee : S ≃ T := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact Homeomorph.mk ee hFc hGc

/-- The pullback of an open set `V` to the chart domain is open in `(0,1)`. -/
theorem overlapPullback_isOpen {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (hV : IsOpen V) :
    IsOpen {t : OpenRealInterval 0 1 | (φ t : X) ∈ V} := by
  have hAt' : {t : OpenRealInterval 0 1 | (φ t : X) ∈ V} =
      (fun t : OpenRealInterval 0 1 => (φ t : X)) ⁻¹' V := by
    ext t; rfl
  rw [hAt']
  exact hV.preimage (Continuous.subtype_val φ.continuous)

/-- **Coordinate-transport arc theorem**: if the overlap `U ∩ V` of an open
set `V` with the open arc `U` is connected (as a subspace of `X`), then the
pullback of `V` to the chart of `U` is again an open arc:
`{t ∈ (0,1) | φ t ∈ V} ≃ₜ (0,1)`.  Proof: transport the overlap to the chart
(`overlapPullbackHomeo`), view the chart inside the real line through a chart
`ℝ ≃ₜ (0,1)` (`homeoRestrictImage` + the classification
`open_connected_ℝ_homeo_openUnit` of RealIntervalShape S162). -/
theorem overlap_pullback_arc {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (hV : IsOpen V)
    (hconn : ConnectedSpace {x : X // x ∈ U ∩ V}) :
    Nonempty ({t : OpenRealInterval 0 1 // (φ t : X) ∈ V} ≃ₜ OpenRealInterval 0 1) := by
  let A := {t : OpenRealInterval 0 1 // (φ t : X) ∈ V}
  let At : Set (OpenRealInterval 0 1) := {t : OpenRealInterval 0 1 | (φ t : X) ∈ V}
  have hAhomeo : A ≃ₜ {x : X // x ∈ U ∩ V} := by
    dsimp [A]
    exact overlapPullbackHomeo φ
  have hAconn : ConnectedSpace A := (hAhomeo.symm.connectedSpace_iff).mp hconn
  haveI : ConnectedSpace A := hAconn
  rcases homeo_real_openUnit with ⟨eR⟩
  let F : A → ℝ := fun a => (eR.symm (a : OpenRealInterval 0 1) : ℝ)
  have hFcont : Continuous F := by
    dsimp [F]
    exact eR.symm.continuous.comp continuous_subtype_val
  let S : Set ℝ := Set.range F
  have hSpreim : S = eR.toFun ⁻¹' At := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      dsimp [At]
      have he : eR (eR.symm (a : OpenRealInterval 0 1)) = (a : OpenRealInterval 0 1) :=
        eR.apply_symm_apply (a : OpenRealInterval 0 1)
      rw [he]
      exact a.2
    · intro hy
      dsimp [At] at hy
      refine ⟨⟨eR y, hy⟩, ?_⟩
      exact eR.symm_apply_apply y
  have hSopen : IsOpen S := by
    rw [hSpreim]
    exact (overlapPullback_isOpen φ hV).preimage eR.continuous
  have hSconn : IsConnected S := by
    have hSuniv : S = F '' (univ : Set A) := by
      ext y; simp [S]
    rw [hSuniv]
    exact IsConnected.image (isConnected_univ (α := A)) F hFcont.continuousOn
  rcases open_connected_ℝ_homeo_openUnit hSopen hSconn.2 hSconn.1 with ⟨e2⟩
  have himg : (eR.symm) '' At = S := by
    apply Eq.trans _ hSpreim.symm
    ext y
    constructor
    · rintro ⟨t, ht, hty⟩
      dsimp [At]
      have he : eR (eR.symm t) = eR y := congrArg eR hty
      have ht' : t = eR y := by simpa using he
      rw [← ht']
      exact ht
    · intro hy
      dsimp [At] at hy
      refine ⟨eR y, hy, ?_⟩
      exact eR.symm_apply_apply y
  let hr : A ≃ₜ ({x : ℝ // x ∈ S}) := by
    dsimp [A, At]
    exact (homeoRestrictImage (eR.symm) At).trans (Homeomorph.setCongr himg)
  exact ⟨hr.trans e2⟩

/-- Reassociation homeo for equal sets of an ambient type `X` (identity on
values). -/
noncomputable def setEqSubtypeHomeoX {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s = t) :
    ({x : X // x ∈ s}) ≃ₜ ({x : X // x ∈ t}) := by
  let e : ({x : X // x ∈ s}) ≃ ({x : X // x ∈ t}) :=
    { toFun := fun x => ⟨x.1, by simpa [h] using x.2⟩,
      invFun := fun y => ⟨y.1, by simpa [← h] using y.2⟩,
      left_inv := by intro x; apply Subtype.ext; rfl,
      right_inv := by intro y; apply Subtype.ext; rfl }
  refine ⟨e, ?_, ?_⟩
  · dsimp [e]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val
  · dsimp [e]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val

/-- **The ambient two-arc theorem, containment case**: if `V ⊆ U` (the second
arc lies inside the first) then the union `U ∪ V = U` is an arc.  (Together
with the engine's `two_chart_glue_homeo` and the facing-normalization lemma
to come this covers the ambient two-arc theorem of slice (a).) -/
theorem two_arc_contained {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hVU : V ⊆ U) (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  have h : U ∪ V = U := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx
      · exact hVU hx
    · intro hx
      exact Or.inl hx
  exact ⟨(setEqSubtypeHomeoX h).trans φ.symm⟩

/-- For an open set `N₀ : Set X`, the points of the subspace
`M := {x // x ∈ U ∪ V}` lying in `N₀` reassociate homeomorphically with
`{x // x ∈ N₀}` (identity on values). -/
noncomputable def subspaceOverlapReassoc {X : Type*} [TopologicalSpace X] {U V N₀ : Set X}
    (hN₀ : N₀ ⊆ U ∪ V) :
    ({m : {x : X // x ∈ U ∪ V} // (m : X) ∈ N₀}) ≃ₜ ({x : X // x ∈ N₀}) := by
  let M := {x : X // x ∈ U ∪ V}
  let S := {m : M // (m : X) ∈ N₀}
  let T := {x : X // x ∈ N₀}
  let F : S → T := fun m => ⟨((m : M) : X), m.2⟩
  let G : T → S := fun x => ⟨⟨(x : X), hN₀ x.2⟩, x.2⟩
  have hFG : Function.LeftInverse G F := by
    intro m
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hGF : Function.RightInverse G F := by
    intro x
    apply Subtype.ext
    rfl
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val.comp continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact Continuous.subtype_mk continuous_subtype_val (by intro x; exact hN₀ x.2)
  let e : S ≃ T := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact Homeomorph.mk e hFc hGc

/-- **The union of two open arcs is locally interval-charted**: every point of
`{x // x ∈ U ∪ V}` (where `U`, `V` are open arcs of a Hausdorff ambient `X`)
has an open neighbourhood homeomorphic to an open real interval — for `x ∈ U`
take (the subspace part of) `U` itself, which is open in the union and carries
the `U`-chart. -/
theorem two_arc_union_locallyInterval {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) :
    LocallyIntervalChart {x : X // x ∈ U ∪ V} := by
  let M := {x : X // x ∈ U ∪ V}
  intro x
  by_cases hxU : (x : X) ∈ U
  · -- x ∈ U: use U as the neighbourhood
    refine ⟨{m : M | (m : X) ∈ U}, ?_, ?_, 0, 1, ?_⟩
    · have hpre : {m : M | (m : X) ∈ U} = (fun m : M => (m : X)) ⁻¹' U := by
        ext m; rfl
      rw [hpre]
      exact hUopen.preimage continuous_subtype_val
    · exact hxU
    · have hsub : U ⊆ U ∪ V := by intro x hx; exact Or.inl hx
      refine ⟨φ.trans (subspaceOverlapReassoc (U := U) (V := V) (N₀ := U) hsub).symm⟩
  · -- x ∈ V (x ∉ U): from x.2
    have hxV : (x : X) ∈ V := by
      rcases x.2 with h | h
      · exact False.elim (hxU h)
      · exact h
    refine ⟨{m : M | (m : X) ∈ V}, ?_, ?_, 0, 1, ?_⟩
    · have hpre : {m : M | (m : X) ∈ V} = (fun m : M => (m : X)) ⁻¹' V := by
        ext m; rfl
      rw [hpre]
      exact hVopen.preimage continuous_subtype_val
    · exact hxV
    · have hsub : V ⊆ U ∪ V := by intro x hx; exact Or.inr hx
      refine ⟨ψ.trans (subspaceOverlapReassoc (U := U) (V := V) (N₀ := V) hsub).symm⟩

/-- **The union of two open arcs of a Hausdorff second-countable ambient is a
topological 1-manifold** (`IsOneManifold` of OneManifold S153) — no
connectedness of the overlap is needed.  This is the dichotomy's local input
for the ambient two-arc theorem (slice (a)). -/
theorem two_arc_union_isOneManifold {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) :
    IsOneManifold {x : X // x ∈ U ∪ V} := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact two_arc_union_locallyInterval (U := U) (V := V) hUopen hVopen φ ψ
