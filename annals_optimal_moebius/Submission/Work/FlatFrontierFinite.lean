import Submission.Work.FlatBetween
import Submission.Commons.Topology.Compactness.finite_of_isCompact_of_isolated

open OptimalMoebius Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# T1-ii Layer 2: the frontier of a flat component has FINITELY many
components (the slice on the centre line `x0 = 1/2` is finite)

Let `C := flatComponent f p`, `p ∈ interior (FlatSet f)`.  Each frontier
component of `C` is a full-width chord (Layer 1,
`frontierComponent_full_chord`), hence meets the vertical centre line
`x0 = 1/2` in exactly one point.  The SLICE
`frSlice f p := ∂C ∩ {x0 = 1/2}` is therefore in bijection with the set
of frontier components.  This file shows the slice is FINITE:

* `frSlice_isCompact` — the slice is bounded (FlatBounded: the whole
  frontier is within a bounded distance of `p`) and closed, hence
  compact (`ProperSpace.isCompact_closedBall`).
* `frSlice_isolated` — every point of the slice is isolated in the slice:
  a whole ball around the point meets `𝓕` only inside its own frontier
  component (`frontierComponent_isolated_locally`), and the component is
  a full chord meeting `{x0 = 1/2}` only at that point (Layer 1).
* `finite_frSlice` — compact + every point isolated ⟹ finite (generic
  lemma `Commons.Topology.Compactness.finite_of_isCompact_of_isolated`
  (proved by the fleet in the shared commons).
* `finite_frComponents` — the SET of frontier components is finite
  (inject each component into the slice via its unique slice point).

Build: `lake build Submission.Work.FlatFrontierFinite` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The frontier components of `C := flatComponent f p`, as a set of
subsets of the plane. -/
def frComponents (f : ℝ² → ℝ³) (p : ℝ²) : Set (Set ℝ²) :=
  {K : Set ℝ² | ∃ e : ℝ²,
    e ∈ frontier (flatComponent f p) ∩ stripInterior ∧ K = frComp f p e}

/-- The frontier slice of `C := flatComponent f p` on the vertical centre
line `x0 = 1/2`. -/
def frSlice (f : ℝ² → ℝ³) (p : ℝ²) : Set ℝ² :=
  frontier (flatComponent f p) ∩ {x : ℝ² | x 0 = 1 / 2}

/-- Membership in the slice. -/
lemma mem_frSlice_iff {f : ℝ² → ℝ³} {p z : ℝ²} :
    z ∈ frSlice f p ↔ z ∈ frontier (flatComponent f p) ∧ z 0 = 1 / 2 := by
  rfl

/-- Slice points lie on the frontier of the component. -/
lemma frSlice_subset_frontier (f : ℝ² → ℝ³) (p : ℝ²) :
    frSlice f p ⊆ frontier (flatComponent f p) := by
  intro z hz
  exact (mem_frSlice_iff.mp hz).1

/-- The centre line is closed. -/
lemma isClosed_centreLine : IsClosed ({x : ℝ² | x 0 = 1 / 2} : Set ℝ²) := by
  have hf : Continuous (fun x : ℝ² => x 0) := by fun_prop
  rw [show {x : ℝ² | x 0 = 1 / 2} = (fun x : ℝ² => x 0) ⁻¹' {(1 / 2 : ℝ)} by ext x; simp]
  exact IsClosed.preimage hf isClosed_singleton

/-- The slice is closed. -/
lemma frSlice_isClosed (f : ℝ² → ℝ³) (p : ℝ²) : IsClosed (frSlice f p) := by
  exact (isClosed_frontier (s := flatComponent f p)).inter isClosed_centreLine

/-- A slice point lies in `𝓕 = ∂C ∩ stripInterior` (its `x0 = 1/2` lies
in the open interval). -/
lemma mem_frontierStrip_of_frSlice {f : ℝ² → ℝ³} {p z : ℝ²} (hz : z ∈ frSlice f p) :
    z ∈ frontier (flatComponent f p) ∩ stripInterior := by
  rw [mem_frSlice_iff] at hz
  exact ⟨hz.1, by
    rw [stripInterior]
    constructor <;> linarith [hz.2]⟩

/-- The slice is bounded (the whole frontier is bounded — FlatBounded),
hence compact. -/
theorem frSlice_isCompact {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) : IsCompact (frSlice f p) := by
  have hx₀C : p ∈ flatComponent f p := mem_flatComponent hp
  rcases frontier_flatComponent_bounded hf ha hx₀C with ⟨R, hR0, hR⟩
  refine (ProperSpace.isCompact_closedBall p R).of_isClosed_subset (frSlice_isClosed f p) ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact hR z (frSlice_subset_frontier f p hz)

/-- Each point of the slice is isolated in the slice: a small ball around
it contains no other slice point. -/
theorem frSlice_isolated {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    ∀ z ∈ frSlice f p, ∃ ρ : ℝ, 0 < ρ ∧ frSlice f p ∩ Metric.ball z ρ ⊆ {z} := by
  intro z hz
  have hz𝓕 : z ∈ frontier (flatComponent f p) ∩ stripInterior := mem_frontierStrip_of_frSlice hz
  have hzK : z ∈ frComp f p z := mem_connectedComponentIn hz𝓕
  rcases frontierComponent_isolated_locally hf ha (e := z) (x := z) hzK with ⟨ρ, hρ, hiso⟩
  rcases frontierComponent_full_chord hf ha hp hz𝓕.2 hz𝓕.1 with ⟨α, β, hchord⟩
  refine ⟨ρ, hρ, ?_⟩
  intro y hy
  rw [Set.mem_singleton_iff]
  have hy𝓕 : y ∈ frontier (flatComponent f p) ∩ stripInterior := mem_frontierStrip_of_frSlice hy.1
  have hyK : y ∈ frComp f p z := hiso y hy𝓕 hy.2
  have hz_in_chord : z ∈ stripChord α β := by
    rw [← hchord]
    exact hzK
  have hy_in_chord : y ∈ stripChord α β := by
    rw [← hchord]
    exact hyK
  have hy0 : y 0 = 1 / 2 := (mem_frSlice_iff.mp hy.1).2
  have hz0 : z 0 = 1 / 2 := (mem_frSlice_iff.mp hz).2
  have hy1 : y 1 = sideH₁ α β (1 / 2) := by
    rw [mem_stripChord] at hy_in_chord
    exact hy_in_chord.2.trans (by rw [hy0])
  have hz1 : z 1 = sideH₁ α β (1 / 2) := by
    rw [mem_stripChord] at hz_in_chord
    exact hz_in_chord.2.trans (by rw [hz0])
  ext i <;> fin_cases i <;> simp [hy0, hz0, hy1, hz1]

/-- **The slice is finite.** -/
theorem finite_frSlice {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) : (frSlice f p).Finite := by
  classical
  apply Commons.Topology.Compactness.finite_of_isCompact_of_isolated (frSlice_isCompact hf ha hp)
  intro z hz
  rcases frSlice_isolated hf ha hp z hz with ⟨ρ, hρ, hsub⟩
  refine ⟨Metric.ball z ρ, Metric.isOpen_ball, ?_⟩
  apply le_antisymm
  · intro y hy
    have hyz : y ∈ {z} := hsub ⟨hy.2, hy.1⟩
    exact hyz
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    constructor
    · rw [Metric.mem_ball, dist_self]
      exact hρ
    · exact hz

/-- The component through a point of another component's set is that same
component (components of a space are disjoint or equal). -/
lemma frComponent_eq_of_mem {f : ℝ² → ℝ³} {p e z : ℝ²} (hz : z ∈ frComp f p e) :
    frComp f p z = frComp f p e := by
  exact (connectedComponentIn_eq (F := frontier (flatComponent f p) ∩ stripInterior) hz).symm

/-- Every frontier component contains a point of the slice (its unique
point over `x0 = 1/2`). -/
lemma frComponent_slice_point {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {e : ℝ²}
    (he : e ∈ frontier (flatComponent f p) ∩ stripInterior) :
    ∃ z : ℝ², z ∈ frSlice f p ∧ z ∈ frComp f p e := by
  rcases frontierComponent_full_chord hf ha hp he.2 he.1 with ⟨α, β, hchord⟩
  let z : ℝ² := !₂[1 / 2, sideH₁ α β (1 / 2)]
  have hz0 : z 0 = 1 / 2 := by simp [z]
  have hzChord : z ∈ stripChord α β := by
    rw [mem_stripChord]
    constructor
    · rw [stripInterior]
      constructor
      · rw [hz0]; norm_num
      · rw [hz0]; norm_num
    · rw [hz0]
      simp [z]
  have hzComp : z ∈ frComp f p e := by
    rw [hchord]
    exact hzChord
  have hzFront : z ∈ frontier (flatComponent f p) :=
    (connectedComponentIn_subset (frontier (flatComponent f p) ∩ stripInterior) e hzComp).1
  refine ⟨z, ?_, hzComp⟩
  rw [mem_frSlice_iff]
  exact ⟨hzFront, hz0⟩

/-- **Layer 2 (T1-ii): the frontier components of a flat component form a
FINITE set.**  Inject each component into the finite slice through its
unique slice point. -/
theorem finite_frComponents {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) : (frComponents f p).Finite := by
  classical
  have hSliceFin : Finite (frSlice f p) := Set.finite_coe_iff.mpr (finite_frSlice hf ha hp)
  have hpick : ∀ K : frComponents f p, ∃ z : frSlice f p, (z : ℝ²) ∈ (K : Set ℝ²) := by
    intro K
    rcases K.2 with ⟨e, he, hK⟩
    rcases frComponent_slice_point hf ha hp he with ⟨z, hzSlice, hzComp⟩
    refine ⟨⟨z, hzSlice⟩, ?_⟩
    rw [hK]
    exact hzComp
  let pick : frComponents f p → frSlice f p := fun K => Classical.choose (hpick K)
  have hpick' : ∀ K : frComponents f p, ((pick K : frSlice f p) : ℝ²) ∈ (K : Set ℝ²) :=
    fun K => Classical.choose_spec (hpick K)
  have hinj : Function.Injective pick := by
    intro K₁ K₂ hEq
    apply Subtype.ext
    rcases K₁.2 with ⟨e₁, he₁, hK₁s⟩
    rcases K₂.2 with ⟨e₂, he₂, hK₂s⟩
    have hw₁ : ((pick K₁ : frSlice f p) : ℝ²) ∈ (K₁ : Set ℝ²) := hpick' K₁
    have hw₂ : ((pick K₂ : frSlice f p) : ℝ²) ∈ (K₂ : Set ℝ²) := hpick' K₂
    have hval : ((pick K₁ : frSlice f p) : ℝ²) = ((pick K₂ : frSlice f p) : ℝ²) :=
      congrArg Subtype.val hEq
    have hw : ((pick K₁ : frSlice f p) : ℝ²) ∈ (K₂ : Set ℝ²) := by
      rwa [hval]
    rw [hK₁s] at hw₁
    rw [hK₂s] at hw
    have hzw₁ : (pick K₁ : frSlice f p).1 ∈ frComp f p e₁ := hw₁
    have hzw₂ : (pick K₁ : frSlice f p).1 ∈ frComp f p e₂ := hw
    calc
      (K₁ : Set ℝ²) = frComp f p e₁ := hK₁s
      _ = frComp f p (pick K₁ : frSlice f p).1 := (frComponent_eq_of_mem hzw₁).symm
      _ = frComp f p e₂ := frComponent_eq_of_mem hzw₂
      _ = (K₂ : Set ℝ²) := hK₂s.symm
  have hFin : Finite (frComponents f p) := Finite.of_injective pick hinj
  exact Set.finite_coe_iff.mp hFin

end Submission.PaperBand
