import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Chain.Sub.Basic
import Submission.Work.Engulf.Chain.Sub.RelInt
import Submission.Work.Engulf.Chain.Sub.exists_coarse_face_superset

/-!
# `Submission.Work.Engulf.Chain.Sub.Transfer`

Transport of the coarse-complex hypotheses to a fine subdivision, for the outer shelling loop of
`Work.Engulf.Chain.E5`:

* `smoothChart_subdiv` : `SmoothChart p X Γ L f ψ` passes to a subdivision `Γ₁` of `Γ`;
* `card_le_of_simp_subset_subdivides` : the vertex bound `Cfg.dimH` passes to a subdivision.
-/

open Set Metric PL

set_option maxHeartbeats 1000000

namespace Work.Engulf.Chain

variable {N : ℕ} {n : ℕ} {M : Type*} [MetricSpace M]

/-- `SmoothChart` passes to a subdivision. -/
theorem smoothChart_subdiv {Γ Γ₁ : PL.Cx N} (hsub : PL.Subdivides Γ₁ Γ) {p : ℕ} {X : Set M}
    {L : Set (PL.E N)} {f : PL.E N → M} {ψ : PL.CubeChart n M}
    (hL : Work.Engulf.IsSubSp Γ L) (h : Work.Engulf.SmoothChart p X Γ L f ψ) :
    Work.Engulf.SmoothChart p X Γ₁ L f ψ := by
  obtain ⟨hdom, hlin⟩ := h
  refine ⟨hdom, ?_⟩
  intro s hs hsL y hy hcube
  obtain ⟨e, he, heL, hse⟩ := Work.Engulf.Chain.Sub.exists_coarse_face_superset hsub hL hs hsL
  obtain ⟨δ, hδ, A, hA⟩ := hlin e he heL y (hse hy) hcube
  exact ⟨δ, hδ, A, fun z hz => hA z ⟨hse hz.1, hz.2⟩⟩

/-- `SmoothChart` is insensitive to changing `f` off the frozen set `L`. -/
theorem smoothChart_of_eqOn {Γ : PL.Cx N} {p : ℕ} {X : Set M} {L : Set (PL.E N)}
    {f g : PL.E N → M} {ψ : PL.CubeChart n M} (h : Work.Engulf.SmoothChart p X Γ L f ψ)
    (heq : ∀ x ∈ L, g x = f x) : Work.Engulf.SmoothChart p X Γ L g ψ := by
  obtain ⟨hdom, hlin⟩ := h
  refine ⟨hdom, ?_⟩
  intro s hs hsL y hy hcube
  rw [heq y (hsL hy)] at hcube
  obtain ⟨δ, hδ, A, hA⟩ := hlin s hs hsL y hy hcube
  exact ⟨δ, hδ, A, fun z hz => ⟨(hA z hz).1, by rw [heq z (hsL hz.1), (hA z hz).2]⟩⟩

/-- `Tame` is insensitive to changing `f` off the frozen set `L`. -/
theorem tame_of_eqOn {Γ : PL.Cx N} {p : ℕ} {X : Set M} {L : Set (PL.E N)}
    {f g : PL.E N → M} (h : Work.Engulf.Tame n p X Γ L f) (heq : ∀ x ∈ L, g x = f x) :
    Work.Engulf.Tame n p X Γ L g := by
  intro x
  obtain ⟨ψ, hx, hs⟩ := h x
  exact ⟨ψ, hx, smoothChart_of_eqOn hs heq⟩

/-- The `vectorSpan` of an affinely independent vertex set has dimension `card - 1`. -/
theorem finrank_vectorSpan_add_one {s : Finset (PL.E N)}
    (hs : s.Nonempty) (hind : AffineIndependent ℝ (fun v : ↥s => (v : PL.E N))) :
    Module.finrank ℝ (vectorSpan ℝ (s : Set (PL.E N))) + 1 = s.card := by
  haveI : Nonempty ↥s := hs.to_subtype
  have h := hind.finrank_vectorSpan_add_one (k := ℝ)
  have hrange : Set.range (fun v : ↥s => (v : PL.E N)) = (s : Set (PL.E N)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩; exact v.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange, Fintype.card_coe] at h
  exact h

/-- The vertex bound (`Cfg.dimH`) of the coarse complex passes to a subdivision. -/
theorem card_le_of_simp_subset_subdivides {Γ Γ₁ : PL.Cx N} (hsub : PL.Subdivides Γ₁ Γ)
    {H : Set (PL.E N)} (hH : Work.Engulf.IsSubSp Γ H) {k : ℕ}
    (hbound : ∀ t ∈ Γ.faces, PL.simp t ⊆ H → t.card ≤ k)
    {s : Finset (PL.E N)} (hs : s ∈ Γ₁.faces) (h : PL.simp s ⊆ H) : s.card ≤ k := by
  classical
  obtain ⟨e, he, heH, hse⟩ := Work.Engulf.Chain.Sub.exists_coarse_face_superset hsub hH hs h
  have hle : s.card ≤ e.card := by
    have hspan : affineSpan ℝ (s : Set (PL.E N)) ≤ affineSpan ℝ (e : Set (PL.E N)) := by
      rw [← affineSpan_convexHull (𝕜 := ℝ) (s : Set (PL.E N)),
        ← affineSpan_convexHull (𝕜 := ℝ) (e : Set (PL.E N))]
      exact affineSpan_mono ℝ hse
    have hdir : Module.finrank ℝ (affineSpan ℝ (s : Set (PL.E N))).direction
        ≤ Module.finrank ℝ (affineSpan ℝ (e : Set (PL.E N))).direction :=
      Submodule.finrank_mono (AffineSubspace.direction_le hspan)
    have hs' : Module.finrank ℝ (affineSpan ℝ (s : Set (PL.E N))).direction + 1 = s.card := by
      rw [direction_affineSpan ℝ (s : Set (PL.E N))]
      exact finrank_vectorSpan_add_one (Γ₁.nonempty_of_mem_faces hs) (Γ₁.indep hs)
    have he' : Module.finrank ℝ (affineSpan ℝ (e : Set (PL.E N))).direction + 1 = e.card := by
      rw [direction_affineSpan ℝ (e : Set (PL.E N))]
      exact finrank_vectorSpan_add_one (Γ.nonempty_of_mem_faces he) (Γ.indep he)
    omega
  exact le_trans hle (hbound e he heH)

end Work.Engulf.Chain
