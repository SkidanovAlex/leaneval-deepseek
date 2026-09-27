import Mathlib
import Submission.Work.Drive.Whitney.modelChart

/-!
# The `Oo` clauses of the model chart, with the Hausdorff hypothesis

`Work.Drive.Whitney.modelChartOo` is FALSE as stated: the doubled-origin line
(`Submission.Work.Drive.Whitney.doubledOriginLine`, module `OoCex`) is a smooth 1-manifold which is
*not* Hausdorff, and on it the frontier of the finger can contain a point whose image under the
finger is *not* on the boundary of the model slab, so that no admissible `Oo` covers it.

This file records the (true) version with `[T2Space M]` added — which is exactly the hypothesis
available in every consumer (`ModelChartDataAll` carries `[T2Space M] [CompactSpace M]
[SecondCountableTopology M]`).  The only use of Hausdorffness is that the image of the *compact*
set `closure reg` under `σ` is closed, so that `closure W₀ ⊆ σ '' closure reg`: every frontier point
of the finger is the image of a parameter in `closure reg`, and a parameter in `reg` itself would
put the point into the finger, so the parameter is on the boundary of the slab.
-/

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric

/-- **The `Oo` clauses of the model chart, with `[T2Space M]`.**  The open set
`{|x| > A} ∪ {‖v‖² > B}` is fixed by the model shear (`m·l = 0` there) and contains the image of
the frontier of the finger. -/
theorem modelChartOo_of_t2 {n k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (c m l : ℝ → ℝ) (A B : ℝ)
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Mdl k)
    (Θ : Mdl k → EuclideanSpace ℝ (Fin (2 * n)))
    (hΘΦ : ∀ y, Θ (Φ y) = y) (hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ) (hΘc : Continuous Θ)
    (σ : ℝ × EuclideanSpace ℝ (Fin k) → M) (hσc : Continuous σ)
    (hσ : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| ≤ 3 / 2 → ‖p.2‖ ≤ 1 →
      f (σ p) = Θ (p.1, c p.1, 0, p.2))
    (hW₀o : IsOpen (σ '' {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| < 3 / 2 ∧ ‖p.2‖ < 1}))
    (hA : A < 3 / 2) (hB : B < 1)
    (hm : ∀ x : ℝ, A < |x| → m x = 0) (hl : ∀ t : ℝ, B < t → l t = 0) :
    ∃ Oo : Set (Mdl k), IsOpen Oo ∧
      (∀ ξ ∈ Oo, m ξ.1 * l (‖ξ.2.2.2‖ ^ 2) = 0) ∧
      f '' frontier (σ '' {p : ℝ × EuclideanSpace ℝ (Fin k) |
        |p.1| < 3 / 2 ∧ ‖p.2‖ < 1}) ⊆ Θ '' Oo := by
  classical
  set reg : Set (ℝ × EuclideanSpace ℝ (Fin k)) := {p | |p.1| < 3 / 2 ∧ ‖p.2‖ < 1} with hreg
  set W₀ : Set M := σ '' reg with hW₀
  refine ⟨{ξ : Mdl k | A < |ξ.1| ∨ B < ‖ξ.2.2.2‖ ^ 2}, ?_, ?_, ?_⟩
  · have h1 : IsOpen {ξ : Mdl k | A < |ξ.1|} :=
      isOpen_lt continuous_const continuous_fst.abs
    have h2 : IsOpen {ξ : Mdl k | B < ‖ξ.2.2.2‖ ^ 2} :=
      isOpen_lt continuous_const
        (((continuous_snd.comp continuous_snd).comp continuous_snd).norm.pow 2)
    convert h1.union h2 using 1
    ext ξ
    simp only [Set.mem_union, Set.mem_ofPred_eq]
  · intro ξ hξ
    rcases hξ with h | h
    · rw [hm _ h, zero_mul]
    · rw [hl _ h, mul_zero]
  · have hcl : IsClosed {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| ≤ 3 / 2 ∧ ‖p.2‖ ≤ 1} := by
      refine IsClosed.inter ?_ ?_
      · exact isClosed_le continuous_fst.abs continuous_const
      · exact isClosed_le continuous_snd.norm continuous_const
    have hclreg : closure reg ⊆
        {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| ≤ 3 / 2 ∧ ‖p.2‖ ≤ 1} :=
      closure_minimal (fun p hp => ⟨le_of_lt hp.1, le_of_lt hp.2⟩) hcl
    have hbdd : reg ⊆ Metric.closedBall (0 : ℝ × EuclideanSpace ℝ (Fin k)) 2 := by
      intro p hp
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
      exact ⟨by rw [Real.norm_eq_abs]; linarith [hp.1], by linarith [hp.2]⟩
    have hK : IsCompact (closure reg) :=
      (isCompact_closedBall (0 : ℝ × EuclideanSpace ℝ (Fin k)) 2).of_isClosed_subset
        isClosed_closure (closure_minimal hbdd isClosed_closedBall)
    have hclosed : IsClosed (σ '' closure reg) := (hK.image hσc).isClosed
    have hclW : closure W₀ ⊆ σ '' closure reg :=
      closure_minimal (fun y hy => by
        obtain ⟨q, hq, rfl⟩ := hy
        exact ⟨q, subset_closure hq, rfl⟩) hclosed
    rintro y ⟨x, hx, rfl⟩
    have hxcl : x ∈ closure W₀ := frontier_subset_closure hx
    obtain ⟨p, hpcl, hpσ⟩ := hclW hxcl
    have hpb := hclreg hpcl
    have hpnot : p ∉ reg := by
      intro hpr
      have hxW : x ∈ W₀ := ⟨p, hpr, hpσ⟩
      have hxnot : x ∉ interior W₀ := hx.2
      rw [hW₀o.interior_eq] at hxnot
      exact hxnot hxW
    have hbdy : |p.1| = 3 / 2 ∨ ‖p.2‖ = 1 := by
      by_contra hcon
      rw [not_or] at hcon
      exact hpnot ⟨lt_of_le_of_ne hpb.1 hcon.1, lt_of_le_of_ne hpb.2 hcon.2⟩
    have hfx : f x = Θ (p.1, c p.1, 0, p.2) := by
      rw [← hpσ]
      exact hσ p hpb.1 hpb.2
    refine ⟨Φ (f x), ?_, hΘΦ (f x)⟩
    rw [show Φ (f x) = (p.1, c p.1, 0, p.2) from by rw [hfx, hΦΘ]]
    rcases hbdy with h | h
    · left
      rw [h]
      exact hA
    · right
      rw [h]
      simpa using hB

end Work.Drive.Whitney
