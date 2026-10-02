import Mathlib
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELRig

/-- A point of the near side of a pair curve never lies in the closure of the far side: the
closure of the (open) far side is the far side together with the pair curve, and both are
disjoint from the near side. -/
theorem elr_notMem_closure_far {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    {P : Work.EL.CoPair hN} (h : Work.EL.PairSides hN P) {z : ℂ}
    (hz : z ∈ Work.EL.pairSideNear P) : z ∉ closure (Work.EL.pairSide P) := by
  intro hcl
  rw [closure_eq_self_union_frontier, h.frontier_far] at hcl
  rcases hcl with hfar | hcurve
  · exact (Set.disjoint_left.mp h.disjoint hfar) hz
  · exact (h.notMem_curve_of_mem_near hz) hcurve

/-- **The nest shift iterated.**  The landing point of the level-`n` pair of the nest at `z₁` is
mapped by `F^n` onto the landing point of the level-`0` pair: `F^n (Q n).y = (Q 0).y`. -/
theorem elr_nest_iterate_shift {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {z₁ : ℂ} {Pa : Set ℂ}
    (nest : Work.EL.Z1Nest hN z₁ Pa) (n : ℕ) :
    (Work.EL.F c)^[n] ((nest.Q n).y) = (nest.Q 0).y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, nest.shift n, ih]

/-- **R-d, `reach`.**  Assuming the equator `E = Ψ '' ℝ` is contained in the filled Julia set,
the equator contains a preimage `u` of `z₀ = f^4 z₁` (with `F u = z₀`, `F u ∈ E`), and it
contains the branch point `b₂` (which is fixed by `F`). -/
theorem reach {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa)
    {R₀ : ℝ}
    (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa)
    (htail : ∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ (x : ℂ) ∈ Work.EL.pairSideNear nest.P0)
    (tr : Work.EL.B2Data d.hN d.z₁)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    ∃ u : ℂ, u ∈ Work.EL.equator fl ∧
      Work.EL.F c u = (LeanEval.ComplexAnalysis.Tantibar c)^[4] d.z₁ ∧
      Work.EL.F c u ∈ Work.EL.equator fl ∧
      tr.b₂ ∈ Work.EL.equator fl ∧ Work.EL.F c tr.b₂ = tr.b₂ := by
  have hEK : Work.EL.equator fl ⊆ Work.EL.K c := Work.EL.equator_subset_K fl hE
  have hconn : IsPreconnected (Work.EL.equator fl) := Work.EL.equator_preconnected fl
  -- a point `e` of the equator, near `z₁`, in the near side of the `α`-pair
  obtain ⟨R', hR'⟩ := htail
  obtain ⟨Rs, hRs⟩ := fl.Ψ_small 1 (by norm_num)
  let x0 : ℝ := min (-R' - 1) (-Rs - 1) - 1
  have hx0R' : x0 < -R' := by
    have h : min (-R' - 1) (-Rs - 1) ≤ -R' - 1 := min_le_left _ _
    simp only [x0]; linarith
  have hx0Rs : x0 < -Rs := by
    have h : min (-R' - 1) (-Rs - 1) ≤ -Rs - 1 := min_le_right _ _
    simp only [x0]; linarith
  let e : ℂ := fl.Ψ (x0 : ℂ)
  have heE : e ∈ Work.EL.equator fl := ⟨x0, rfl⟩
  have he_ne : e ≠ d.z₁ := (hRs (x0 : ℂ) (by simpa using hx0Rs)).1
  have he_nearP0 : e ∈ Work.EL.pairSideNear nest.P0 := hR' x0 hx0R'
  have hε : 0 < ‖e - d.z₁‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr he_ne
  -- the nest region shrinks below the distance `‖e - z₁‖`
  obtain ⟨N, hNshrink⟩ := nest.shrinks ‖e - d.z₁‖ hε
  -- hence `e` leaves the near side of `Q N`, while the equator tail enters it: `E` crosses the
  -- pair curve of `Q N` and the separation lemma (T7) gives `(Q N).y ∈ E`
  have hyNE : (nest.Q N).y ∈ Work.EL.equator fl := by
    have heK : e ∈ Work.EL.K c := hE x0
    have he_notNear : e ∉ Work.EL.pairSideNear (nest.Q N) := by
      intro hnear
      exact absurd (hNshrink N le_rfl e heK hnear he_nearP0) (lt_irrefl _)
    have hz1near : d.z₁ ∈ Work.EL.pairSideNear (nest.Q N) := nest.z1_near_Q N
    obtain ⟨δ, hδpos, hδball⟩ := Metric.isOpen_iff.mp (nest.sides_Q N).isOpen_near d.z₁ hz1near
    obtain ⟨Rd, hRd⟩ := fl.Ψ_small δ hδpos
    let x1 : ℝ := -Rd - 1
    have hx1 : x1 < -Rd := by simp only [x1]; linarith
    have he'ball : fl.Ψ (x1 : ℂ) ∈ Metric.ball d.z₁ δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact (hRd (x1 : ℂ) (by simpa using hx1)).2
    have he'near : fl.Ψ (x1 : ℂ) ∈ Work.EL.pairSideNear (nest.Q N) := hδball he'ball
    have he'E : fl.Ψ (x1 : ℂ) ∈ Work.EL.equator fl := ⟨x1, rfl⟩
    by_cases hcurve : e ∈ Work.EL.pairCurve (nest.Q N)
    · -- `e` already lies on the pair curve, hence at the landing point, which is in `E`
      have hy : e = (nest.Q N).y := by
        have hmem := (Work.EL.pairCurve_inter_K_subset (hN := d.hN) (P := nest.Q N)) ⟨hcurve, heK⟩
        simpa using hmem
      rw [← hy]; exact heE
    · -- otherwise `e` lies in the far side, and separation (T7) applies
      have he_far : e ∈ Work.EL.pairSide (nest.Q N) := by
        rcases (nest.sides_Q N).mem_or_mem hcurve with h | h
        · exact h
        · exact absurd h he_notNear
      exact Work.EL.separation (nest.sides_Q N) hEK hconn heE he_far he'E
        (elr_notMem_closure_far (nest.sides_Q N) he'near)
  -- push the level-`N` landing point down the nest to the level-`0` one
  have hQ0E : (nest.Q 0).y ∈ Work.EL.equator fl := by
    have hmaps := (Work.EL.mapsTo_equator fl).iterate N
    have h := hmaps hyNE
    rwa [elr_nest_iterate_shift nest N] at h
  refine ⟨(nest.Q 0).y, hQ0E, nest.base_shift, (Work.EL.mapsTo_equator fl) hQ0E, ?_, ?_⟩
  · -- `b₂ ∈ E` by separation (T7) on the arm-`A` pair of the tripod
    have hz1arm : d.z₁ ∈ Work.EL.pairSide
        (Work.EL.armPairA d.hN tr.b₂ tr.tripod.lands_a tr.tripod.lands_b) := by
      have h := tr.z1_mem_A; simp only [Work.EL.armOf, Work.EL.armA] at h; exact h
    have harmOpen : IsOpen (Work.EL.pairSide
        (Work.EL.armPairA d.hN tr.b₂ tr.tripod.lands_a tr.tripod.lands_b)) :=
      tr.tripod.sides_A.isOpen_far
    obtain ⟨δ₂, hδ₂pos, hδ₂ball⟩ := Metric.isOpen_iff.mp harmOpen d.z₁ hz1arm
    obtain ⟨Ra, hRa⟩ := fl.Ψ_small δ₂ hδ₂pos
    let x2 : ℝ := -Ra - 1
    have hx2 : x2 < -Ra := by simp only [x2]; linarith
    have ha_ball : fl.Ψ (x2 : ℂ) ∈ Metric.ball d.z₁ δ₂ := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact (hRa (x2 : ℂ) (by simpa using hx2)).2
    have ha_arm : fl.Ψ (x2 : ℂ) ∈ Work.EL.pairSide
        (Work.EL.armPairA d.hN tr.b₂ tr.tripod.lands_a tr.tripod.lands_b) := hδ₂ball ha_ball
    have ha_E : fl.Ψ (x2 : ℂ) ∈ Work.EL.equator fl := ⟨x2, rfl⟩
    have hz0E : (LeanEval.ComplexAnalysis.Tantibar c)^[4] d.z₁ ∈ Work.EL.equator fl := by
      rw [← nest.base_shift]; exact (Work.EL.mapsTo_equator fl) hQ0E
    have hz0_notcl : (LeanEval.ComplexAnalysis.Tantibar c)^[4] d.z₁ ∉ closure (Work.EL.pairSide
        (Work.EL.armPairA d.hN tr.b₂ tr.tripod.lands_a tr.tripod.lands_b)) := by
      have h := tr.z0_notMem_clA; simp only [Work.EL.armOf, Work.EL.armA] at h; exact h
    have hb2E := Work.EL.separation tr.tripod.sides_A hEK hconn ha_E ha_arm hz0E hz0_notcl
    exact hb2E
  · -- `b₂` is fixed by `F`
    have hfix := Function.iterate_fixed tr.b2_fix 5
    exact hfix

end Work.ELRig
