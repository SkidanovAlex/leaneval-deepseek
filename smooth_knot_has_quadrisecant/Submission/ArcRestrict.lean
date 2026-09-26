import Mathlib
import Submission.OneManifold
import Submission.RealIntervalShape
import Submission.AmbientTwoArc

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S235 — the sub-arc restriction: an arc chart restricted to a
coordinate sub-interval is again an arc chart (module
Submission/ArcRestrict.lean)

Route (α) / the maximal-chart route of the interval-side dichotomy (S216
recommendation) lists the generic analogue of the O-side chart cells
(S211/S213) as a needed piece: "restriction of an arc chart to a sub-arc
is an arc chart" — from `homeo_Ioo_openUnit` + the subtype-reassociating
homeos.  This module supplies that generically (PURE Mathlib +
OneManifold/RealIntervalShape/AmbientTwoArc; nothing problem-specific).
Content (namespace LeanEval.KnotTheory.Quadrisecant, sorry-free):

1. **`coordArc e lo hi`** — the coordinate sub-arc of an open arc `U`
   (chart `e : (0,1) ≃ₜ U`): the points of `U` whose chart coordinate
   lies in `(lo,hi)` (an ambient set of `X`, the value-image of the
   coordinate-restricted `U`-subtype);
2. **`coordArc_mem_iff`** — the membership identity: `x ∈ coordArc` iff
   `x ∈ U` with chart coordinate in `(lo,hi)` (the usable form for
   membership arguments);
3. **`isOpen_coordArc`** — `coordArc` is open in `X` whenever `U` is
   open (the coordinate set `{t | lo < t < hi}` is open in `(0,1)`, its
   image under the chart homeo is open in the `U`-subtype, and the
   value-coercion from the subtype of an open set is an open map —
   `isOpenMap_coe_of_isOpen`);
4. **`oriIooHomeo`** — the real reassociation of the ORI-coordinate
   subtype `{t : (0,1) // (t : ℝ) ∈ (lo,hi)}` with the plain interval
   subtype `{r : ℝ // r ∈ Ioo lo hi}` for `0 ≤ lo < hi ≤ 1`;
5. **`subIoo_chart_openUnit`** — the ORI-side restriction: every
   coordinate sub-interval subtype `{t : (0,1) // (t : ℝ) ∈ (lo,hi)}`
   is itself `≃ₜ ORI 0 1` (via `oriIooHomeo` + the affine
   `homeo_Ioo_openUnit lo hi`).  Together with `isOpen_coordArc` this is
   the real-coordinate content of "an arc chart restricted to a
   coordinate sub-interval is again an arc chart": the X-level chart
   `{x : X // x ∈ coordArc e lo hi} ≃ₜ ORI 0 1` is the composition of
   the carrier reassociation, the chart restriction `e.symm`, and
   `subIoo_chart_openUnit` — the individual homeos are recorded as
   future work (they need classical-choice plumbing of the image
   witnesses; recorded in ROADMAP S235, NOT sorries).

Everything here is verified (no axioms, no `sorry`).  The sub-arc
restriction is consumed by the per-level boundary analysis of the
interval side (a prefix's terminal sub-arcs, overlap sub-arcs of chart
cells) and by the maximal-chart argument of the S206 extraction.
-/

/-- The value-coercion from the subtype of an OPEN set to the ambient is
an open map: `val '' S` is open in `X` for every open `S` of the subtype
`{x // x ∈ U}` (the subtype topology is induced by `val`, so an open
`S` equals `val ⁻¹' W` for an open `W ⊆ X`; `val '' S = W ∩ U` is then
open). -/
lemma isOpenMap_coe_of_isOpen {X : Type*} [TopologicalSpace X] {U : Set X}
    (hUopen : IsOpen U) : IsOpenMap (fun z : {x : X // x ∈ U} => (z : X)) := by
  intro S hSopen
  rcases (isOpen_induced_iff.mp hSopen) with ⟨W, hWopen, hWpre⟩
  have himg : ((fun z : {x : X // x ∈ U} => (z : X)) '' S) = W ∩ U := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzW : z ∈ (fun z : {x : X // x ∈ U} => (z : X)) ⁻¹' W := by
        simpa [← hWpre] using hz
      exact ⟨hzW, z.2⟩
    · intro hx
      refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
      rw [← hWpre]
      exact hx.1
  rw [himg]
  exact hWopen.inter hUopen

/-- The coordinate sub-arc of an open arc `U` (chart `e : (0,1) ≃ₜ U`)
over the coordinate interval `(lo,hi)`: the ambient set of the points of
`U` whose chart coordinate lies in `(lo,hi)`.  (Defined as the
value-image of the coordinate-restricted `U`-subtype, so no
membership-proof-dependent set comprehension is involved.) -/
def coordArc {X : Type*} [TopologicalSpace X] {U : Set X}
    (e : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (lo hi : ℝ) : Set X :=
  ((↑) : {x : X // x ∈ U} → X) ''
    {z : {x : X // x ∈ U} | ((e.symm z : OpenRealInterval 0 1) : ℝ) ∈ Set.Ioo lo hi}

/-- The membership identity for `coordArc`: `x ∈ coordArc U e lo hi`
iff `x ∈ U` with chart coordinate in `(lo,hi)` (existential over the
membership proof — the usable form for membership arguments). -/
theorem coordArc_mem_iff {X : Type*} [TopologicalSpace X] {U : Set X}
    (e : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (lo hi : ℝ) (x : X) :
    x ∈ coordArc e lo hi ↔
      ∃ hx : x ∈ U, ((e.symm ⟨x, hx⟩ : OpenRealInterval 0 1) : ℝ) ∈ Set.Ioo lo hi := by
  constructor
  · intro hx
    rcases hx with ⟨z, hz, hval⟩
    have hxU : x ∈ U := by
      subst x
      exact z.2
    have hcoord : ((e.symm ⟨x, hxU⟩ : OpenRealInterval 0 1) : ℝ) ∈ Set.Ioo lo hi := by
      subst x
      have hEq : (e.symm ⟨(z : X), z.2⟩ : OpenRealInterval 0 1) = e.symm z := rfl
      simpa [hEq] using hz
    exact ⟨hxU, hcoord⟩
  · intro hx
    rcases hx with ⟨hxU, hcoord⟩
    refine ⟨⟨x, hxU⟩, hcoord, rfl⟩

/-- The coordinate sub-arc is open in `X` whenever `U` is open.  Proof:
the coordinate set `T := {t : (0,1) | lo < t < hi}` is open in the
chart interval; its image under the chart homeo is open in the
`U`-subtype (`S = e '' T`); the value-coercion is an open map because
`U` is open (`isOpenMap_coe_of_isOpen`); and `coordArc` is exactly the
value-image of `S`. -/
theorem isOpen_coordArc {X : Type*} [TopologicalSpace X] {U : Set X}
    (hUopen : IsOpen U) (e : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (lo hi : ℝ) : IsOpen (coordArc e lo hi) := by
  let T : Set (OpenRealInterval 0 1) := {t : OpenRealInterval 0 1 | (t : ℝ) ∈ Set.Ioo lo hi}
  let S : Set {x : X // x ∈ U} := {z : {x : X // x ∈ U} |
    ((e.symm z : OpenRealInterval 0 1) : ℝ) ∈ Set.Ioo lo hi}
  have hTopen : IsOpen T := by
    dsimp [T]
    exact isOpen_Ioo.preimage continuous_subtype_val
  have hSopen : IsOpen S := by
    have hTS : e '' T = S := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        dsimp [S, T] at ht ⊢
        rw [e.symm_apply_apply t]
        exact ht
      · intro hz
        dsimp [S] at hz
        let t : OpenRealInterval 0 1 := e.symm z
        have hzT : (t : ℝ) ∈ Set.Ioo lo hi := hz
        have hmemT : t ∈ T := by
          dsimp [T]
          exact hzT
        refine ⟨t, hmemT, ?_⟩
        exact e.apply_symm_apply z
    rw [← hTS]
    exact e.isOpenMap T hTopen
  have hval : coordArc e lo hi = ((↑) : {x : X // x ∈ U} → X) '' S := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨z, hz, rfl⟩
      exact ⟨z, by simpa [S] using hz, rfl⟩
    · intro hx
      rcases hx with ⟨z, hz, rfl⟩
      dsimp [coordArc, S]
      exact ⟨z, hz, rfl⟩
  rw [hval]
  exact isOpenMap_coe_of_isOpen hUopen S hSopen

/-- **The real reassociation**: the ORI-coordinate subtype `{t : (0,1) //
(t:ℝ) ∈ (lo,hi)}` is homeomorphic to the plain real interval subtype
`{r : ℝ // r ∈ Ioo lo hi}` for `0 ≤ lo < hi ≤ 1` (the coordinate values
lie in `(0,1)` because `(lo,hi) ⊆ (0,1)`). -/
noncomputable def oriIooHomeo (lo hi : ℝ) (hlo0 : 0 ≤ lo) (hhi1 : hi ≤ 1) :
    ({t : OpenRealInterval 0 1 // (t : ℝ) ∈ Set.Ioo lo hi}) ≃ₜ
      {r : ℝ // r ∈ Set.Ioo lo hi} := by
  let A := {t : OpenRealInterval 0 1 // (t : ℝ) ∈ Set.Ioo lo hi}
  let B := {r : ℝ // r ∈ Set.Ioo lo hi}
  let F : A → B := fun t => ⟨(t.1 : ℝ), t.2⟩
  let G : B → A := fun r => ⟨⟨(r : ℝ), ⟨lt_of_le_of_lt hlo0 r.2.1, lt_of_lt_of_le r.2.2 hhi1⟩⟩, r.2⟩
  have hFG : Function.LeftInverse G F := by
    intro t
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hGF : Function.RightInverse G F := by
    intro r
    apply Subtype.ext
    rfl
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val.comp continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact Continuous.subtype_mk continuous_subtype_val (by
      intro r
      exact ⟨lt_of_le_of_lt hlo0 r.2.1, lt_of_lt_of_le r.2.2 hhi1⟩)
  let e' : A ≃ B := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact Homeomorph.mk e' hFc hGc

/-- **The ORI-side sub-arc chart**: every coordinate sub-interval
subtype `{t : (0,1) // (t : ℝ) ∈ (lo,hi)}` of the open unit interval is
itself `≃ₜ ORI 0 1` for `0 ≤ lo < hi ≤ 1` — the real-coordinate content
of "restriction of an arc chart to a coordinate sub-interval": via the
reassociation `oriIooHomeo` and the affine interval homeo
`homeo_Ioo_openUnit lo hi`.  (The X-level chart of `coordArc` is the
composition of this with the carrier reassociation and the chart
restriction — recorded in the module doc and ROADMAP S235.) -/
theorem subIoo_chart_openUnit (lo hi : ℝ) (hlo0 : 0 ≤ lo) (hlt : lo < hi)
    (hhi1 : hi ≤ 1) :
    Nonempty ({t : OpenRealInterval 0 1 // (t : ℝ) ∈ Set.Ioo lo hi} ≃ₜ
      OpenRealInterval 0 1) := by
  rcases homeo_Ioo_openUnit lo hi hlt with ⟨f⟩
  exact ⟨(oriIooHomeo lo hi hlo0 hhi1).trans f⟩

end LeanEval.KnotTheory.Quadrisecant