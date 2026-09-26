import Mathlib
import Submission.Helpers
import Submission.Work.Drive.noInflectionAPI
import Submission.Work.Drive.shortSecantsFree_of_noInflection
import Submission.Work.Drive.counting_lemma_at_meridian
import Submission.Work.Drive.isPathConnected_component_liftedTrisecant
import Submission.Work.Drive.no_translate_path_in_lifted_trisecant

/-!
# Brick (d) with the "Kuperberg general position" residual made explicit

Brick (d) of the Kuperberg–Pannwitz argument (`NonSeparatingArcAvoidingO r`, resp. its strip form
`StripCrosscutAvoidingO r`) is **not** derivable from `IsSmoothKnot r`, `QuadrisecantFree r`,
`TorusGeneralPositionTransverse r` and `hinfl` alone: the pointwise general-position hypothesis
`hg` does not exclude a chord which is *tangent* to the knot at one endpoint whose line carries no
third knot point, and such a tangent chord produces points of `closure A \ A` (`A = liftedTrisecant
r`) with an infinite vertical trace — see `Work.Drive.closure_liftedTrisecant_eq_or_tangent` for the
exact localisation of `closure A \ A`.  This is exactly Kuperberg's general position (his Lemma 2.4:
finiteness of the set of *special points*, i.e. of the parameters at which the secant-direction map
fails to be a transverse immersion).

This module proves brick (d) **assuming** the two consequences of Kuperberg's general position that
the strip machinery consumes:

* `hclosed : IsClosed (liftedTrisecant r)` — the trisecant locus is closed in the strip (no tangent
  chord with an escaping middle);
* `hfib : ∃ ξ, (liftedTrisecant r ∩ {x = ξ}).Finite` — the vertical trace over one meridian is
  finite (Kuperberg's "π_L(·,a) is at most two-to-one with transverse double points" at one
  parameter `a`).

Under those, every connected component of `A` is bounded in the first coordinate, and the proved
strip theorem `Commons.Topology.Strip.strip_crosscut_bounded_away` (applied after rescaling the
period strip to the unit strip) yields the crosscut.  The unconditional statement requested as
`Work.Drive.avoidingArc_of_generic_noInflection` is *not* provable from the four knot hypotheses;
these two hypotheses are precisely the missing input.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set
open scoped unitInterval

/-! ## 1. Period invariance of the lifted trisecant locus -/

/-- `liftedTrisecant r` is invariant under the shift `x ↦ x + period`: the deck generator `σ =
stripFlip` of the strip cover satisfies `σ² = (x,y) ↦ (x + period, y)` and preserves
`liftedTrisecant r`. -/
lemma liftedTrisecant_add_period (r : ℝ → Space) :
    ∀ q : ℝ × ℝ, q ∈ liftedTrisecant r ↔ (q.1 + period, q.2) ∈ liftedTrisecant r := by
  intro q
  have h1 : stripFlip q ∈ liftedTrisecant r ↔ q ∈ liftedTrisecant r :=
    stripFlip_mem_liftedTrisecant
  have h2 : stripFlip (stripFlip q) ∈ liftedTrisecant r ↔ stripFlip q ∈ liftedTrisecant r :=
    stripFlip_mem_liftedTrisecant
  rw [stripFlip_stripFlip q] at h2
  exact ⟨fun hp => h2.mpr (h1.mpr hp), fun hp => h1.mp (h2.mp hp)⟩

/-! ## 2. Every component of `A` is bounded in the first coordinate -/

/-- **Boundedness of the components of the lifted trisecant locus from one finite vertical trace.**
`A = liftedTrisecant r` is `period`-periodic, its components are path connected
(`isPathConnected_component_liftedTrisecant`) and no point of `A` is joined inside `A` to its own
translate (`no_translate_path_in_lifted_trisecant`).  Hence, if the vertical trace of `A` over a
single meridian is finite, no component of `A` can be unbounded in the first coordinate: an
unbounded component would meet one of its own nonzero translates (counting lemma
`Work.Drive.counting_lemma_at_meridian`) and then, being path connected, would carry an honest
translate path. -/
theorem components_liftedTrisecant_bounded_of_finite_fibre {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hq : QuadrisecantFree r) (hg : TorusGeneralPositionTransverse r)
    (hfib : ∃ ξ : ℝ, (liftedTrisecant r ∩ {q : ℝ × ℝ | q.1 = ξ}).Finite) :
    ∀ z : ℝ × ℝ, z ∈ liftedTrisecant r →
      Bornology.IsBounded (Prod.fst '' connectedComponentIn (liftedTrisecant r) z) := by
  obtain ⟨ξ, hξ⟩ := hfib
  have hper := liftedTrisecant_add_period r
  have hpc := isPathConnected_component_liftedTrisecant hr hq hg
  have hno : ∀ z : ℝ × ℝ, z ∈ liftedTrisecant r →
      ¬ JoinedIn (liftedTrisecant r) z (z.1 + period, z.2) :=
    fun z hz => no_translate_path_in_lifted_trisecant hr hq hg hz
  intro z hz
  by_contra hunb
  set C : Set (ℝ × ℝ) := connectedComponentIn (liftedTrisecant r) z with hC
  have hCsub : C ⊆ liftedTrisecant r := by
    rw [hC]; exact connectedComponentIn_subset _ _
  have hCpc : IsPreconnected C := by
    rw [hC]; exact isPreconnected_connectedComponentIn
  by_cases hdisj : ∀ m : ℕ, 0 < m →
      (C ∩ (fun q : ℝ × ℝ => (q.1 + (m : ℝ) * period, q.2)) '' C) = ∅
  · exact hunb (hC ▸ counting_lemma_at_meridian period_pos hper hξ hCsub hCpc hdisj)
  · push Not at hdisj
    obtain ⟨m, hm, hne⟩ := hdisj
    obtain ⟨u, hu⟩ := hne
    rw [Set.mem_inter_iff] at hu
    obtain ⟨huC, ⟨w, hwC, huw⟩⟩ := hu
    have hu' : (w.1 + (m : ℝ) * period, w.2) = u := huw
    have hwCu : (w.1 + (m : ℝ) * period, w.2) ∈ C := hu'.symm ▸ huC
    have hpcC : IsPathConnected C := by rw [hC]; exact hpc z hz
    have hjoin : JoinedIn C w ((w.1 + (m : ℝ) * period, w.2)) :=
      hpcC.joinedIn w hwC _ hwCu
    have hjoinA : JoinedIn (liftedTrisecant r) w ((w.1 + (m : ℝ) * period, w.2)) :=
      hjoin.mono hCsub
    obtain ⟨γ, hγ⟩ := hjoinA
    have hγ1 : γ 1 = ((γ 0).1 + (m : ℝ) * period, (γ 0).2) := by
      have hs : γ 0 = w := Path.source _
      have ht : γ 1 = (w.1 + (m : ℝ) * period, w.2) := Path.target _
      rw [hs, ht]
    obtain ⟨z', hz', hJ⟩ :=
      Commons.Topology.Strip.exists_translate_path_of_winding_nat period_pos hper
        (fun t => hγ t) hm hγ1
    exact hno z' hz' hJ

/-! ## 3. A bottom–top crosscut of the period strip -/

/-- **The rescaled strip-crosscut theorem**: if `A ⊆ ℝ × (0, period)` is closed, bounded away from
the two edge lines and all of whose connected components have bounded first-coordinate projection,
then there is a continuous path from the bottom edge to the top edge of the period strip whose
interior avoids `A`.

Proof: `(x,y) ↦ (x, period * y)` is a homeomorphism carrying the period strip onto the unit strip
and preserving first coordinates; apply `Commons.Topology.Strip.strip_crosscut_bounded_away` to the
image of `A` and rescale the result back. -/
theorem exists_crosscut_period {A : Set (ℝ × ℝ)} (hA : IsClosed A)
    (hstrip : A ⊆ {z : ℝ × ℝ | 0 < z.2 ∧ z.2 < period})
    (haway : Disjoint (closure A) {z : ℝ × ℝ | z.2 ≤ 0 ∨ period ≤ z.2})
    (hbdd : ∀ z ∈ A, Bornology.IsBounded (Prod.fst '' connectedComponentIn A z)) :
    ∃ γ : C(I, ℝ × ℝ), (γ 0).2 = 0 ∧ (γ 1).2 = period ∧
      ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 →
        0 < (γ t).2 ∧ (γ t).2 < period ∧ γ t ∉ A := by
  set F : Set (ℝ × ℝ) := {q : ℝ × ℝ | (q.1, period * q.2) ∈ A} with hFdef
  have hper : (0 : ℝ) < period := period_pos
  -- `F` lies in the unit strip
  have hFsub : F ⊆ {z : ℝ × ℝ | 0 < z.2 ∧ z.2 < 1} := by
    intro q hq
    have h := hstrip hq
    have h1 : 0 < period * q.2 := h.1
    have h2 : period * q.2 < period := h.2
    exact ⟨by nlinarith, by nlinarith⟩
  -- `F` is closed in the plane
  have hFclosed : IsClosed F := by
    have hcont : Continuous fun q : ℝ × ℝ => (q.1, period * q.2) :=
      continuous_fst.prodMk (continuous_const.mul continuous_snd)
    have : F = (fun q : ℝ × ℝ => (q.1, period * q.2)) ⁻¹' A := rfl
    rw [this]
    exact hA.preimage hcont
  have hclosed : IsClosed (F ∪ {z : ℝ × ℝ | z.2 ≤ 0 ∨ 1 ≤ z.2}) :=
    hFclosed.union ((isClosed_le continuous_snd continuous_const).union
      (isClosed_le continuous_const continuous_snd))
  -- `closure F` misses the edges (transported from `haway` through the rescaling)
  have hcontψ : Continuous fun q : ℝ × ℝ => (q.1, period * q.2) :=
    continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have haway' : Disjoint (closure F) {z : ℝ × ℝ | z.2 ≤ 0 ∨ 1 ≤ z.2} := by
    rw [Set.disjoint_left]
    intro q hq hq'
    have hclF : closure F ⊆ (fun q : ℝ × ℝ => (q.1, period * q.2)) ⁻¹' closure A :=
      closure_minimal (fun y hy => subset_closure hy) (isClosed_closure.preimage hcontψ)
    have hmem : (q.1, period * q.2) ∈ closure A := hclF hq
    have hnot := Set.disjoint_left.mp haway hmem
    rcases hq' with h | h
    · exact hnot (Or.inl (by show period * q.2 ≤ 0; nlinarith))
    · exact hnot (Or.inr (by show period ≤ period * q.2; nlinarith))
  -- components of `F` are bounded
  have hbddF : ∀ z : ℝ × ℝ, z ∈ F →
      Bornology.IsBounded (Prod.fst '' connectedComponentIn F z) := by
    intro z hz
    have hzA : (z.1, period * z.2) ∈ A := hz
    have hψ : ∀ q : ℝ × ℝ, q ∈ F ↔ (q.1, period * q.2) ∈ A := fun q => Iff.rfl
    have himg : (fun q : ℝ × ℝ => (q.1, period * q.2)) ''
        connectedComponentIn F z ⊆ connectedComponentIn A (z.1, period * z.2) := by
      refine IsPreconnected.subset_connectedComponentIn ?_ ⟨z, mem_connectedComponentIn hz, rfl⟩ ?_
      · exact (isPreconnected_connectedComponentIn).image _
          (continuous_fst.prodMk (continuous_const.mul continuous_snd)).continuousOn
      · rintro q ⟨w, hw, rfl⟩
        exact (hψ w).mp (connectedComponentIn_subset F z hw)
    have hb := hbdd _ hzA
    refine hb.subset ?_
    rintro x ⟨q, hq, rfl⟩
    exact ⟨(q.1, period * q.2), himg ⟨q, hq, rfl⟩, rfl⟩
  obtain ⟨γ', h0, h1, hint⟩ :=
    Commons.Topology.Strip.strip_crosscut_bounded_away F hclosed hFsub haway' hbddF
  refine ⟨⟨fun t => ((γ' t).1, period * (γ' t).2),
      continuous_fst.comp γ'.continuous |>.prodMk (continuous_const.mul (continuous_snd.comp γ'.continuous))⟩,
    ?_, ?_, ?_⟩
  · show period * (γ' 0).2 = 0
    rw [h0]; ring
  · show period * (γ' 1).2 = period
    rw [h1]; ring
  · intro t ht0 ht1
    obtain ⟨hpos, hlt, hna⟩ := hint t ht0 ht1
    have h1' : 0 < period * (γ' t).2 := by nlinarith
    have h2' : period * (γ' t).2 < period := by nlinarith
    exact ⟨h1', h2', hna⟩

/-! ## 4. Brick (d) in strip form, with the general-position residual assumed -/

/-- **Brick (d) with the correct extra hypotheses.**  For a quadrisecant-free knot in transverse
general position without inflections, if moreover the lifted trisecant locus is closed (no
`closure A \ A`) and has finite vertical trace over one meridian, then there is a bottom–top
crosscut of the strip avoiding `A`; by the verified reduction
`nonSeparatingArcAvoidingO_of_stripCrosscut` this is `NonSeparatingArcAvoidingO r`. -/
theorem stripCrosscutAvoidingO_of_isClosed_finite_fibre {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hq : QuadrisecantFree r) (hg : TorusGeneralPositionTransverse r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (hclosed : IsClosed (liftedTrisecant r))
    (hfib : ∃ ξ : ℝ, (liftedTrisecant r ∩ {q : ℝ × ℝ | q.1 = ξ}).Finite) :
    StripCrosscutAvoidingO r := by
  obtain ⟨δ, hδ, hbound⟩ := shortSecantsFree_of_noInflection hr hinfl
  have hstrip : liftedTrisecant r ⊆ {z : ℝ × ℝ | 0 < z.2 ∧ z.2 < period} := by
    intro q hq'
    have h := hbound q hq'
    exact ⟨by linarith, by linarith⟩
  have haway : Disjoint (closure (liftedTrisecant r))
      {z : ℝ × ℝ | z.2 ≤ 0 ∨ period ≤ z.2} := by
    rw [Set.disjoint_left]
    intro q hq hq'
    have hcl : closure (liftedTrisecant r) ⊆ {z : ℝ × ℝ | δ ≤ z.2 ∧ z.2 ≤ period - δ} :=
      closure_minimal hbound (isClosed_le continuous_const continuous_snd |>.inter
        (isClosed_le continuous_snd continuous_const))
    have h1 : δ ≤ q.2 ∧ q.2 ≤ period - δ := hcl hq
    rcases hq' with h | h <;> linarith [h1.1, h1.2, hδ]
  obtain ⟨γ, h0, h1, hint⟩ :=
    exists_crosscut_period hclosed hstrip haway
      (components_liftedTrisecant_bounded_of_finite_fibre hr hq hg hfib)
  exact ⟨γ, h0, h1, (fun t ht0 ht1 => ⟨(hint t ht0 ht1).1, (hint t ht0 ht1).2.1⟩),
    (fun t ht0 ht1 => (hint t ht0 ht1).2.2)⟩

end Work.Drive
