import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.CorridorDefs
import Submission.Work.Noncompact.CompressionTube.immersedLine

/-!
# Auxiliary lemmas for the per-stage recursion of the two lanes

Small bricks used by the recursion of `twoLanes_of_corridorChain`:

* `exists_germ_in_open` — the straight chart germ in a prescribed direction issued from a point of
  an *open* set stays in it for small positive parameters.  This discharges the `hgerm` hypothesis
  of `immersedArcWithGerm` / `exists_middle_arc_confined` at every stage of the recursion;
* `disjoint_of_corridor_confinement` — with the per-corridor confinement `P i ⊆ C i` the pieces two
  or more indices apart are automatically disjoint (`hsep` for `|i - j| ≥ 2`), so only the
  consecutive case of `hsep` needs the germ argument.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology Function
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- **The straight germ issued from a point of an open set stays in it.** -/
theorem exists_germ_in_open {R : Set M} (hR : IsOpen R) {σ : M} (hσ : σ ∈ R)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hcsrc : σ ∈ c.source)
    (u : EuclideanSpace ℝ (Fin n)) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t ≤ e → c.symm (c σ + t • u) ∈ R := by
  have htarget : c σ ∈ c.target := c.map_source hcsrc
  have hcont : ContinuousAt (fun t : ℝ => c.symm (c σ + t • u)) 0 :=
    ContinuousAt.comp (g := ⇑c.symm) (f := fun t : ℝ => c σ + t • u) (x := 0)
      (c.continuousOn_symm.continuousAt (c.open_target.mem_nhds (by simpa using htarget)))
      ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt)
  have hval : c.symm (c σ + (0:ℝ) • u) = σ := by
    rw [zero_smul, add_zero]; exact c.left_inv hcsrc
  have hpre : (fun t : ℝ => c.symm (c σ + t • u)) ⁻¹' R ∈ 𝓝 (0 : ℝ) := by
    exact hcont.preimage_mem_nhds (by rw [hval]; exact hR.mem_nhds hσ)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨δ / 2, by positivity, ?_⟩
  intro t ht0 htd
  exact hδsub (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]
    linarith)

/-- **The rootedness ball of an *initial* straight germ.**  The mirror of
`exists_trace_ball` (`immersedLine.lean`): for a continuous injective arc `Q` leaving the point
`s = Q 0` along the straight chart germ of direction `u` and radius `e`, there is a radius `ρ > 0`
such that the closed chart ball of radius `ρ` is contained in any prescribed neighbourhood of `s`
and the *trace of `Q` inside the open ball of radius `ρ` is contained in the germ*, i.e.
`Q t ∈ ball ⟹ t ∈ Icc 0 e`.  This is the `hQroot` hypothesis of
`inter_image_subset_singleton_of_germs` for the *departing* piece of a junction.

Proof: apply `exists_trace_ball` to the reversed arc `t ↦ Q (1 - t)`, whose terminal germ is the
initial germ of `Q` in the direction `-u`. -/
theorem exists_trace_ball_initial {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {Q : ℝ → M} (hQc : Continuous Q) (hQinj : Set.InjOn Q (Set.Icc (0:ℝ) 1))
    {s : M} (hs : Q 0 = s) (hsrc : s ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (hgerm : ∀ t : ℝ, 0 ≤ t → t ≤ e → Q t = c.symm (c s + t • u))
    {C : Set M} (hC : IsOpen C) (hsC : s ∈ C) :
    ∃ ρ : ℝ, 0 < ρ ∧ c.symm '' Metric.closedBall (c s) ρ ⊆ C ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Q t ∈ c.symm '' Metric.ball (c s) ρ →
        t ∈ Set.Icc (0:ℝ) e) := by
  classical
  have hrevc : Continuous fun t : ℝ => Q (1 - t) :=
    hQc.comp (continuous_const.sub continuous_id)
  have hrevinj : Set.InjOn (fun t : ℝ => Q (1 - t)) (Set.Icc (0:ℝ) 1) := by
    intro a ha b hb hab
    have ha' : 1 - a ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ha.2], by linarith [ha.1]⟩
    have hb' : 1 - b ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
    have := hQinj ha' hb' hab
    linarith
  have hrev1 : (fun t : ℝ => Q (1 - t)) 1 = s := by simpa using hs
  have hrevgerm : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 →
      (fun t' : ℝ => Q (1 - t')) t = c.symm (c s + (t - 1) • (-u)) := by
    intro t ht1 ht2
    have h1 : (0:ℝ) ≤ 1 - t := by linarith
    have h2 : 1 - t ≤ e := by linarith
    show Q (1 - t) = c.symm (c s + (t - 1) • (-u))
    rw [hgerm (1 - t) h1 h2]
    have hsm : (t - 1) • (-u) = (1 - t) • u := by
      rw [smul_neg, ← neg_smul]
      congr 1
      ring
    rw [hsm]
  obtain ⟨ρ, hρ, hball, hroot⟩ := exists_trace_ball (n := n) (P := fun t : ℝ => Q (1 - t))
    hrevc hrevinj hrev1 hsrc (u := -u) he he1 hrevgerm hC hsC
  refine ⟨ρ, hρ, hball, ?_⟩
  intro t ht hmem
  have ht' : (1 - t) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have := hroot (1 - t) ht' (by simpa using hmem)
  exact ⟨by linarith [this.2], by linarith [this.1]⟩

variable {b : M} {W : Set M}

/-- **Per-corridor confinement gives the separation for pieces two indices apart.** -/
theorem disjoint_of_corridor_confinement (h : CorridorChain b W) {P : ℕ → Set M}
    (hP : ∀ i : ℕ, P i ⊆ h.C i) :
    ∀ i j : ℕ, i + 2 ≤ j → Disjoint (P i) (P j) := by
  intro i j hij
  have hd : 2 ≤ Nat.dist i j := by
    simp only [Nat.dist]
    omega
  exact Disjoint.mono (hP i) (hP j) (h.disjoint i j hd)

end

end Work.Noncompact.CompressionTube
