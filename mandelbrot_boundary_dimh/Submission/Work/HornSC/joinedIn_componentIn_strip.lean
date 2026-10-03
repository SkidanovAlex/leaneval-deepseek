import Mathlib
import Submission.Work.HornSC.Toolkit

namespace Work.HornSC

/-- Points of the (closed, convex) horizontal strip `{|im z| ≤ η}` that lie in a set `Ω` which is
*open in the strip* (in the sense that every point of `Ω` has a Euclidean ball whose intersection
with the strip is contained in `Ω`) are joined inside `Ω` to every point of the connected component
of their base point.

The strip is convex, so `Ω` carries a basis of path connected neighbourhoods: for `p ∈ Ω` the sets
`ball p δ ∩ Ω` are path connected (segments between their points stay in `ball p δ ∩ {|im| ≤ η}`,
hence in `Ω` by the openness hypothesis).  Consequently the set of points of `Ω` that `x` is joined
to is both open and closed in the subspace `Ω`, and since it meets the connected component
`connectedComponentIn Ω x` it contains it. -/
theorem joinedIn_componentIn_strip {η : ℝ} {Ω : Set ℂ} (hΩS : Ω ⊆ {z : ℂ | |z.im| ≤ η})
    (hΩ : ∀ u ∈ Ω, ∃ δ : ℝ, 0 < δ ∧ Metric.ball u δ ∩ {z : ℂ | |z.im| ≤ η} ⊆ Ω)
    {x w : ℂ} (hw : w ∈ connectedComponentIn Ω x) : JoinedIn Ω x w := by
  classical
  have hxC : x ∈ Ω := connectedComponentIn_nonempty_iff.mp ⟨w, hw⟩
  -- the strip is convex
  have hSconv : Convex ℝ {z : ℂ | |z.im| ≤ η} := by
    have h : {z : ℂ | |z.im| ≤ η} = Complex.imCLM ⁻¹' Set.Icc (-η) η := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Icc, Complex.imCLM_apply, abs_le, Set.mem_ofPred_eq]
    rw [h]
    exact (convex_Icc (-η) η).linear_preimage Complex.imCLM.toLinearMap
  -- a choice of a Euclidean radius around every point of `Ω`
  let D : Ω → ℝ := fun p => Classical.choose (hΩ (p : ℂ) p.2)
  have hDpos : ∀ p : Ω, 0 < D p := fun p => (Classical.choose_spec (hΩ (p : ℂ) p.2)).1
  have hDsub : ∀ p : Ω, Metric.ball (p : ℂ) (D p) ∩ {z : ℂ | |z.im| ≤ η} ⊆ Ω :=
    fun p => (Classical.choose_spec (hΩ (p : ℂ) p.2)).2
  -- points of `ball p (D p) ∩ Ω` are joined to `p` inside `Ω`
  have key : ∀ p : Ω, ∀ y ∈ Metric.ball (p : ℂ) (D p) ∩ Ω, JoinedIn Ω (p : ℂ) y := by
    intro p y hy
    have hT : Convex ℝ (Metric.ball (p : ℂ) (D p) ∩ {z : ℂ | |z.im| ≤ η}) :=
      (convex_ball (p : ℂ) (D p)).inter hSconv
    have hpT : (p : ℂ) ∈ Metric.ball (p : ℂ) (D p) ∩ {z : ℂ | |z.im| ≤ η} :=
      ⟨Metric.mem_ball_self (hDpos p), hΩS p.2⟩
    have hyT : y ∈ Metric.ball (p : ℂ) (D p) ∩ {z : ℂ | |z.im| ≤ η} := ⟨hy.1, hΩS hy.2⟩
    exact (hT.isPathConnected ⟨_, hpT⟩).joinedIn _ hpT y hyT |>.mono (hDsub p)
  -- the set of points of `Ω` joined to `x`
  let Q : Set Ω := {p : Ω | JoinedIn Ω x (p : ℂ)}
  have hQopen : IsOpen Q := by
    rw [Metric.isOpen_iff]
    intro p hp
    refine ⟨D p, hDpos p, ?_⟩
    intro q hq
    have hq' : (q : ℂ) ∈ Metric.ball (p : ℂ) (D p) := by
      have := Metric.mem_ball.mp hq
      rw [Metric.mem_ball]
      simpa [Subtype.dist_eq] using this
    exact JoinedIn.trans hp (key p (q : ℂ) ⟨hq', q.2⟩)
  have hQclosed : IsClosed Q := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro p hp
    refine ⟨D p, hDpos p, ?_⟩
    intro q hq hqQ
    have hq' : (q : ℂ) ∈ Metric.ball (p : ℂ) (D p) := by
      have := Metric.mem_ball.mp hq
      rw [Metric.mem_ball]
      simpa [Subtype.dist_eq] using this
    exact hp (JoinedIn.trans hqQ (key p (q : ℂ) ⟨hq', q.2⟩).symm)
  -- the connected component of `x` is preconnected in the subspace `Ω`
  have hpre : IsPreconnected (Subtype.val ⁻¹' connectedComponentIn Ω x : Set Ω) := by
    have h1 : (Subtype.val ⁻¹' connectedComponentIn Ω x : Set Ω)
        = connectedComponent (⟨x, hxC⟩ : Ω) := by
      ext p
      rw [connectedComponentIn_eq_image hxC]
      constructor
      · rintro ⟨k, hk, hkp⟩
        have : k = p := Subtype.ext hkp
        simpa [this] using hk
      · intro hp; exact ⟨p, hp, rfl⟩
    rw [h1]
    exact isPreconnected_connectedComponent
  -- a preconnected set meeting a clopen set is contained in it
  have hsub := IsPreconnected.subset_left_of_subset_union
      (s := (Subtype.val ⁻¹' connectedComponentIn Ω x : Set Ω)) (u := Q) (v := Qᶜ)
      hQopen hQclosed.isOpen_compl disjoint_compl_right
      (by intro p _; rw [Set.union_compl_self]; exact Set.mem_univ p)
      ⟨⟨x, hxC⟩, mem_connectedComponentIn hxC, JoinedIn.refl hxC⟩
      hpre
  have hwΩ : w ∈ Ω := connectedComponentIn_subset Ω x hw
  have hmem : (⟨w, hwΩ⟩ : Ω) ∈ (Subtype.val ⁻¹' connectedComponentIn Ω x : Set Ω) := hw
  exact hsub hmem

end Work.HornSC
