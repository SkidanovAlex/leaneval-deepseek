import Mathlib
import Submission.Work.Smooth.JordanSeparation.GridWalkDefs
import Submission.Work.Smooth.JordanSeparation.gridWalk_basic
import Submission.Work.Smooth.JordanSeparation.simplyConnectedSpace_onePoint_complex

/-!
# Approximating a loop in an open set by a grid walk
-/

/-- Restrict a path to a subset containing its range. -/
def Path.toSubtype {X : Type*} [TopologicalSpace X] {S : Set X} {a b : X} (ha : a ∈ S)
    (hb : b ∈ S) (p : Path a b) (hp : Set.range p ⊆ S) : Path (⟨a, ha⟩ : ↥S) (⟨b, hb⟩ : ↥S) :=
  Path.mk ⟨fun t => (⟨p t, hp ⟨t, rfl⟩⟩ : ↥S),
      Continuous.subtype_mk p.continuous fun t => hp ⟨t, rfl⟩⟩
    (Subtype.ext p.source) (Subtype.ext p.target)

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-! ### The safety radius -/

/-- **Safety radius.**  For a path `γ` in an open subset `U ⊆ ℂ` there is `δ > 0` such that the
closed ball of radius `δ` around every point of the trace of `γ` is contained in `U`. -/
theorem exists_ball_subset_of_path {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U)) :
    ∃ δ > 0, ∀ t : unitInterval, ball (γ t : ℂ) δ ⊆ U := by
  classical
  set T : Set ℂ := range (fun t : unitInterval => (γ t : ℂ)) with hT
  have hTcomp : IsCompact T := isCompact_range (continuous_subtype_val.comp γ.continuous)
  have hTU : T ⊆ U := fun z hz => by rcases hz with ⟨t, rfl⟩; exact (γ t).2
  choose ε hεpos hεU using fun z : ↥T =>
    Metric.mem_nhds_iff.mp (hU.mem_nhds (hTU z.2))
  obtain ⟨s, hscov⟩ := hTcomp.elim_finite_subcover
    (fun z : ↥T => ball (z : ℂ) (ε z / 2)) (fun z => isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (by have := hεpos ⟨z, hz⟩; linarith)⟩)
  have hTne : T.Nonempty := ⟨(γ 0 : ℂ), ⟨0, rfl⟩⟩
  have hsne : s.Nonempty := by
    obtain ⟨z, hz⟩ := hTne
    have h1 := hscov hz
    rw [mem_iUnion] at h1
    obtain ⟨i, hi⟩ := h1
    rw [mem_iUnion] at hi
    obtain ⟨hi', -⟩ := hi
    exact ⟨i, hi'⟩
  set δ : ℝ := s.inf' hsne (fun z => ε z / 2) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    rw [Finset.lt_inf'_iff hsne]
    intro b _
    have := hεpos b
    linarith
  refine ⟨δ, hδpos, ?_⟩
  intro t w hw
  have hcover := hscov (show (γ t : ℂ) ∈ T from ⟨t, rfl⟩)
  rw [mem_iUnion] at hcover
  obtain ⟨i, hi⟩ := hcover
  rw [mem_iUnion] at hi
  obtain ⟨hi', hit⟩ := hi
  have hmin : δ ≤ ε i / 2 := by
    rw [hδ]
    exact Finset.inf'_le (f := fun z : ↥T => ε z / 2) hi'
  have hdist : dist (γ t : ℂ) (i : ℂ) < ε i / 2 := mem_ball.mp hit
  apply hεU i
  rw [mem_ball]
  have htri : dist w (i : ℂ) ≤ dist w (γ t : ℂ) + dist (γ t : ℂ) (i : ℂ) := dist_triangle _ _ _
  have hw' : dist w (γ t : ℂ) < δ := mem_ball.mp hw
  linarith

/-! ### Homotopy of paths in a convex subset -/

/-- **Two paths in `↥U` with the same endpoints and values in a convex subset `B ⊆ U` are
homotopic in `↥U`.** -/
theorem homotopic_of_convex_subset {U : Set ℂ} {B : Set ℂ} (hB : Convex ℝ B)
    (hBne : B.Nonempty) (hBU : B ⊆ U) {a b : U} (p q : Path a b)
    (hpB : ∀ t, (p t : ℂ) ∈ B) (hqB : ∀ t, (q t : ℂ) ∈ B) :
    Path.Homotopic p q := by
  haveI : ContractibleSpace ↥B := Convex.contractibleSpace hB hBne
  haveI : SimplyConnectedSpace ↥B := inferInstance
  have haB : (a : ℂ) ∈ B := by have := hpB 0; rwa [p.source] at this
  have hbB : (b : ℂ) ∈ B := by have := hpB 1; rwa [p.target] at this
  have hinc : Continuous fun z : ↥B => (⟨(z : ℂ), hBU z.2⟩ : U) :=
    Continuous.subtype_mk continuous_subtype_val (fun z => hBU z.2)
  let ι : C(↥B, U) := ⟨fun z => ⟨(z : ℂ), hBU z.2⟩, hinc⟩
  have hp'mem : Set.range (p.map continuous_subtype_val) ⊆ B := by
    rintro y ⟨t, rfl⟩; exact hpB t
  have hq'mem : Set.range (q.map continuous_subtype_val) ⊆ B := by
    rintro y ⟨t, rfl⟩; exact hqB t
  set p' : Path (⟨(a:ℂ), haB⟩ : ↥B) (⟨(b:ℂ), hbB⟩ : ↥B) :=
    Path.toSubtype haB hbB (p.map continuous_subtype_val) hp'mem with hp'def
  set q' : Path (⟨(a:ℂ), haB⟩ : ↥B) (⟨(b:ℂ), hbB⟩ : ↥B) :=
    Path.toSubtype haB hbB (q.map continuous_subtype_val) hq'mem with hq'def
  have h' : Path.Homotopic p' q' := SimplyConnectedSpace.paths_homotopic p' q'
  have hmap := Path.Homotopic.map h' ι
  have e1 : p'.map (f := fun z => (ι z : U)) ι.continuous = p := by ext t; rfl
  have e2 : q'.map (f := fun z => (ι z : U)) ι.continuous = q := by ext t; rfl
  rw [e1, e2] at hmap
  exact hmap

end

end Work.Smooth.JordanSeparation
