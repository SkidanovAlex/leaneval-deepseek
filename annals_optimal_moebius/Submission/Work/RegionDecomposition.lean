import Submission.Work.FrontierSeparation

open OptimalMoebius Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# T1-ii Layer 3, part B (step 1): the frontier is the union of the
slice-point components

For `C := flatComponent f p` (`p ∈ interior (FlatSet f)`), the frontier
`𝓕 := ∂C ∩ stripInterior` equals the union of the frontier components
through the slice points:

    𝓕 = ⋃_{z ∈ frSlice f p} frComp f p z

(`frSlice_union_components`).  Every frontier point lies in its own
component, which equals the component of the unique slice point it
contains (`frComponent_slice_point` + `frComponent_eq_of_mem`), and each
slice-point component is a connected component of `𝓕`, hence inside
`𝓕`.  Also: the slice-point-indexed components are pairwise distinct
(`frSlice_component_injective`): a component is a full chord (Layer 1)
meeting `{x0 = 1/2}` in exactly one point, so two slice points in the
same component coincide.

Build: `lake build Submission.Work.RegionDecomposition` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- **The frontier of a flat component in the open strip is the union of
the components through its slice points.** -/
theorem frSlice_union_components {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    frontier (flatComponent f p) ∩ stripInterior =
      ⋃ z ∈ frSlice f p, frComp f p z := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion₂]
    rcases frComponent_slice_point hf ha hp hx with ⟨z, hzS, hzC⟩
    refine ⟨z, hzS, ?_⟩
    have hxcomp : x ∈ frComp f p x := mem_connectedComponentIn hx
    have hEq : frComp f p x = frComp f p z := (frComponent_eq_of_mem hzC).symm
    rw [hEq] at hxcomp
    exact hxcomp
  · intro hx
    rw [Set.mem_iUnion₂] at hx
    rcases hx with ⟨z, hzS, hxz⟩
    exact (connectedComponentIn_subset (frontier (flatComponent f p) ∩ stripInterior) z hxz)

/-- Two slice points lie in the same frontier component only if they are
equal: a component is a full chord meeting `{x0 = 1/2}` in a unique
point. -/
lemma frSlice_component_injective {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {z₁ z₂ : ℝ²}
    (hz₁ : z₁ ∈ frSlice f p) (hz₂ : z₂ ∈ frSlice f p)
    (hcomp : frComp f p z₁ = frComp f p z₂) : z₁ = z₂ := by
  have hz₁𝓕 : z₁ ∈ frontier (flatComponent f p) ∩ stripInterior := mem_frontierStrip_of_frSlice hz₁
  have hz₂𝓕 : z₂ ∈ frontier (flatComponent f p) ∩ stripInterior := mem_frontierStrip_of_frSlice hz₂
  have hz₁K : z₁ ∈ frComp f p z₁ := mem_connectedComponentIn hz₁𝓕
  have hz₁₂ : z₁ ∈ frComp f p z₂ := by
    rw [hcomp] at hz₁K
    exact hz₁K
  rcases frontierComponent_full_chord hf ha hp hz₂𝓕.2 hz₂𝓕.1 with ⟨α, β, hchord⟩
  have hz₁Γ : z₁ ∈ stripChord α β := by
    rwa [← hchord]
  have hz₂Γ : z₂ ∈ stripChord α β := by
    have hz₂K : z₂ ∈ frComp f p z₂ := mem_connectedComponentIn hz₂𝓕
    rwa [← hchord]
  have h₁0 : z₁ 0 = 1 / 2 := (mem_frSlice_iff.mp hz₁).2
  have h₂0 : z₂ 0 = 1 / 2 := (mem_frSlice_iff.mp hz₂).2
  have h₁1 : z₁ 1 = sideH₁ α β (1 / 2) := by
    rw [mem_stripChord] at hz₁Γ
    exact hz₁Γ.2.trans (by rw [h₁0])
  have h₂1 : z₂ 1 = sideH₁ α β (1 / 2) := by
    rw [mem_stripChord] at hz₂Γ
    exact hz₂Γ.2.trans (by rw [h₂0])
  ext i <;> fin_cases i <;> simp [h₁0, h₂0, h₁1, h₂1]

/-- The frontier component through a frontier point is the component of
its (unique) slice point. -/
lemma frComp_eq_of_frontier_slice {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {e : ℝ²}
    (he : e ∈ frontier (flatComponent f p) ∩ stripInterior) :
    ∃ z : ℝ², z ∈ frSlice f p ∧ frComp f p e = frComp f p z := by
  rcases frComponent_slice_point hf ha hp he with ⟨z, hzS, hzC⟩
  exact ⟨z, hzS, (frComponent_eq_of_mem hzC).symm⟩

def frHeights (f : ℝ² → ℝ³) (p : ℝ²) : Set ℝ :=
  {h : ℝ | ∃ z : ℝ², z ∈ frSlice f p ∧ z 1 = h}

/-- Membership in the height set. -/
lemma mem_frHeights_iff {f : ℝ² → ℝ³} {p : ℝ²} {h : ℝ} :
    h ∈ frHeights f p ↔ ∃ z : ℝ², z ∈ frSlice f p ∧ z 1 = h := by rfl

/-- A slice point is the point over its own height: `z = !₂[1/2, z 1]`. -/
lemma frSlice_point_eq_of_height {f : ℝ² → ℝ³} {p z : ℝ²} (hz : z ∈ frSlice f p) :
    z = !₂[1 / 2, z 1] := by
  have hz0 : z 0 = 1 / 2 := (mem_frSlice_iff.mp hz).2
  ext i <;> fin_cases i
  · simp [hz0]
  · simp

/-- The map from the slice to its heights is injective: two slice points
with the same height coincide (both lie over `x0 = 1/2`). -/
lemma frSlice_eq_of_height_eq {f : ℝ² → ℝ³} {p z₁ z₂ : ℝ²}
    (hz₁ : z₁ ∈ frSlice f p) (hz₂ : z₂ ∈ frSlice f p) (h : z₁ 1 = z₂ 1) : z₁ = z₂ := by
  have h₁ : z₁ = !₂[1 / 2, z₁ 1] := frSlice_point_eq_of_height hz₁
  have h₂ : z₂ = !₂[1 / 2, z₂ 1] := frSlice_point_eq_of_height hz₂
  rw [h₁, h₂, h]

/-- The slice heights are finite (the slice is finite). -/
theorem finite_frHeights {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) : (frHeights f p).Finite := by
  rw [show frHeights f p = (fun z : ℝ² => z 1) '' frSlice f p by rfl]
  exact Set.Finite.image (fun z : ℝ² => z 1) (finite_frSlice hf ha hp)

/-- The slice point over a given slice height. -/
def frSlicePoint (f : ℝ² → ℝ³) (p : ℝ²) (h : ℝ) : ℝ² := !₂[1 / 2, h]

/-- The slice point over a slice height is a slice point, with that
height. -/
lemma frSlicePoint_mem {f : ℝ² → ℝ³} {p : ℝ²} {h : ℝ} (hh : h ∈ frHeights f p) :
    frSlicePoint f p h ∈ frSlice f p ∧ (frSlicePoint f p h) 1 = h := by
  rcases (mem_frHeights_iff.mp hh) with ⟨z, hz, hz₁⟩
  have hz' : z = frSlicePoint f p h := by
    rw [frSlicePoint, ← hz₁]
    exact frSlice_point_eq_of_height hz
  constructor
  · rwa [← hz']
  · simp [frSlicePoint]

/-- The component at a slice height: the frontier component through the
slice point over `h`. -/
def frCompAt (f : ℝ² → ℝ³) (p : ℝ²) (h : ℝ) : Set ℝ² :=
  frComp f p (frSlicePoint f p h)

/-- The component at a slice height is a full chord. -/
lemma frCompAt_full_chord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h : ℝ}
    (hh : h ∈ frHeights f p) :
    ∃ α β : ℝ, frCompAt f p h = stripChord α β := by
  rcases frSlicePoint_mem hh with ⟨hz, hh1⟩
  exact frontierComponent_full_chord hf ha hp
    (mem_frontierStrip_of_frSlice hz).2 (mem_frontierStrip_of_frSlice hz).1

/-- The slice height of a component at height `h` is `h` itself, and the
component meets the slice at its point over `h`. -/
lemma frCompAt_slice {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h : ℝ}
    (hh : h ∈ frHeights f p) :
    frSlicePoint f p h ∈ frCompAt f p h := by
  rcases frSlicePoint_mem hh with ⟨hz, hh1⟩
  exact mem_connectedComponentIn (mem_frontierStrip_of_frSlice hz)

/-- Every frontier point's component is the component at the height of
its slice point: `frComp f p e = frCompAt f p (z 1)` for the slice point
`z` in `e`'s component. -/
lemma frComp_eq_frCompAt {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {e z : ℝ²}
    (he : e ∈ frontier (flatComponent f p) ∩ stripInterior)
    (hzS : z ∈ frSlice f p) (hzC : z ∈ frComp f p e) :
    frComp f p e = frCompAt f p (z 1) := by
  have hz' : z = frSlicePoint f p (z 1) := by
    rw [frSlicePoint]
    exact frSlice_point_eq_of_height hzS
  have hcomp : frComp f p e = frComp f p z := (frComponent_eq_of_mem hzC).symm
  rw [hcomp, hz']
  rfl

/-- Distinct slice heights give distinct components: the component at
height `h₁` differs from that at height `h₂` whenever `h₁ ≠ h₂`
(different slice points, and two slice points in one component are
equal). -/
lemma frCompAt_ne_of_ne {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hne : h₁ ≠ h₂) :
    frCompAt f p h₁ ≠ frCompAt f p h₂ := by
  intro hcomp
  rcases frSlicePoint_mem hh₁ with ⟨hz₁, hh₁'⟩
  rcases frSlicePoint_mem hh₂ with ⟨hz₂, hh₂'⟩
  have hz : frSlicePoint f p h₁ = frSlicePoint f p h₂ := by
    rw [frCompAt, frCompAt] at hcomp
    exact frSlice_component_injective hf ha hp hz₁ hz₂ hcomp
  have hh : h₁ = h₂ := by
    have hc := congrArg (fun w : ℝ² => w 1) hz
    simp [frSlicePoint] at hc
    exact hc
  exact hne hh

/-- **Ordering by slice height**: for two slice heights `h₁ < h₂`, the
component at `h₁` lies entirely in the half-strip below the component at
`h₂`, and the component at `h₂` entirely in the half-strip above the
component at `h₁` (`frComponent_separated` specialised to slice
points). -/
theorem frCompAt_order {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    ∃ α₁ β₁ α₂ β₂ : ℝ,
      frCompAt f p h₁ = stripChord α₁ β₁ ∧ frCompAt f p h₂ = stripChord α₂ β₂ ∧
      frCompAt f p h₁ ⊆ belowChord α₂ β₂ ∧ frCompAt f p h₂ ⊆ aboveChord α₁ β₁ := by
  rcases frSlicePoint_mem hh₁ with ⟨hz₁, h₁'⟩
  rcases frSlicePoint_mem hh₂ with ⟨hz₂, h₂'⟩
  have hne : frComp f p (frSlicePoint f p h₁) ≠ frComp f p (frSlicePoint f p h₂) := by
    simpa [frCompAt] using (frCompAt_ne_of_ne hf ha hp hh₁ hh₂ (ne_of_lt hlt))
  rcases frComponent_separated hf ha hp
    (mem_frontierStrip_of_frSlice hz₁).1 (mem_frontierStrip_of_frSlice hz₁).2
    (mem_frontierStrip_of_frSlice hz₂).1 (mem_frontierStrip_of_frSlice hz₂).2
    (by simp [frSlicePoint]) (by simp [frSlicePoint])
    hne (by rwa [← h₁', ← h₂']) with ⟨α₁, β₁, α₂, β₂, h₁c, h₂c, h₁b, h₂a⟩
  refine ⟨α₁, β₁, α₂, β₂, ?_, ?_, h₁b, h₂a⟩
  · simpa [frCompAt] using h₁c
  · simpa [frCompAt] using h₂c




/-- The complement `W` of the frontier inside the open strip:
`stripInterior` with the frontier of `C := flatComponent f p` removed
(equals `stripInterior \ 𝓕` since `𝓕 ⊆ stripInterior`). -/
def frW (f : ℝ² → ℝ³) (p : ℝ²) : Set ℝ² :=
  stripInterior \ frontier (flatComponent f p)

/-- Membership in `W`. -/
lemma mem_frW_iff {f : ℝ² → ℝ³} {p x : ℝ²} :
    x ∈ frW f p ↔ x ∈ stripInterior ∧ x ∉ frontier (flatComponent f p) := by rfl

/-- `W` is open (the open strip minus the closed frontier). -/
lemma isOpen_frW (f : ℝ² → ℝ³) (p : ℝ²) : IsOpen (frW f p) := by
  rw [show frW f p = stripInterior ∩ (frontier (flatComponent f p))ᶜ by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hx.2⟩
    · intro hx
      exact ⟨hx.1, hx.2⟩]
  exact stripInterior_isOpen.inter (isClosed_frontier (s := flatComponent f p)).isOpen_compl

/-- `C := flatComponent f p` is contained in `W` (it is open, hence
disjoint from its frontier). -/
lemma flatComponent_subset_frW {f : ℝ² → ℝ³} {p : ℝ²} :
    flatComponent f p ⊆ frW f p := by
  intro x hx
  rw [mem_frW_iff]
  constructor
  · exact flatComponent_subset_stripInterior f p hx
  · intro hxF
    have hxopen : x ∈ interior (flatComponent f p) := by
      rw [(isOpen_flatComponent f p).interior_eq]
      exact hx
    rw [frontier] at hxF
    exact hxF.2 hxopen

/-- The closure of `C` meets `W` exactly in `C`. -/
lemma closure_frW_eq_self {f : ℝ² → ℝ³} {p : ℝ²} :
    closure (flatComponent f p) ∩ frW f p = flatComponent f p := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxcl, hxW⟩
    rw [mem_frW_iff] at hxW
    by_contra hxC
    have hxfront : x ∈ frontier (flatComponent f p) := by
      rw [frontier]
      constructor
      · exact hxcl
      · intro hxi
        have hxopen : x ∈ flatComponent f p := by
          rwa [← (isOpen_flatComponent f p).interior_eq]
        exact hxC hxopen
    exact hxW.2 hxfront
  · intro hx
    exact ⟨subset_closure hx, flatComponent_subset_frW hx⟩

/-- **A preconnected subset of `W` that meets `C` lies entirely in
`C`** (`C` is relatively open and closed in `W`, and `W \ C` is open). -/
lemma preconnected_frW_subset_C {f : ℝ² → ℝ³} {p : ℝ²} {s : Set ℝ²}
    (hsS : s ⊆ frW f p) (hspre : IsPreconnected s)
    (hsC : (s ∩ flatComponent f p).Nonempty) : s ⊆ flatComponent f p := by
  apply IsPreconnected.subset_left_of_subset_union (u := flatComponent f p)
    (v := frW f p \ flatComponent f p) (isOpen_flatComponent f p) ?_ ?_ ?_ hsC hspre
  · have hvc : frW f p \ flatComponent f p =
        frW f p ∩ (closure (flatComponent f p))ᶜ := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨hyW, hyC⟩
        refine ⟨hyW, ?_⟩
        intro hycl
        have hyC' : y ∈ flatComponent f p := by
          have hcl := closure_frW_eq_self (f := f) (p := p)
          have hy' : y ∈ closure (flatComponent f p) ∩ frW f p := ⟨hycl, hyW⟩
          rwa [hcl] at hy'
        exact hyC hyC'
      · intro hy
        rcases hy with ⟨hyW, hycl⟩
        exact ⟨hyW, by
          intro hyC
          exact hycl (subset_closure hyC)⟩
    rw [hvc]
    exact (isOpen_frW f p).inter (isClosed_closure.isOpen_compl)
  · rw [Set.disjoint_left]
    intro y hy hyW
    exact hyW.2 hy
  · intro y hy
    by_cases hyC : y ∈ flatComponent f p
    · exact Or.inl hyC
    · exact Or.inr ⟨hsS hy, hyC⟩

/-- **`C` is the connected component of `W` through `p`.** -/
theorem flatComponent_eq_connectedComponentIn_frW {f : ℝ² → ℝ³} {p : ℝ²}
    (hp : p ∈ flatComponent f p) :
    flatComponent f p = connectedComponentIn (frW f p) p := by
  ext x
  constructor
  · intro hx
    exact IsPreconnected.subset_connectedComponentIn (F := frW f p)
      (isPreconnected_flatComponent f p) hp (flatComponent_subset_frW (f := f) (p := p)) hx
  · intro hx
    have hVsub : connectedComponentIn (frW f p) p ⊆ frW f p :=
      connectedComponentIn_subset (frW f p) p
    have hpW : p ∈ frW f p := flatComponent_subset_frW (f := f) (p := p) hp
    exact preconnected_frW_subset_C (f := f) (p := p)
      hVsub (isPreconnected_connectedComponentIn)
      ⟨p, mem_connectedComponentIn hpW, hp⟩ hx

