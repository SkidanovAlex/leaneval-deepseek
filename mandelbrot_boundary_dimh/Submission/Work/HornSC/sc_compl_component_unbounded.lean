import Mathlib
import Submission.Work.HornSC.Tools
import Submission.Work.HornSC.exists_compact_gap_of_compl_sphere_not_preconnected
import Submission.Work.HornSC.not_hasArg_of_jordan_curve
import Submission.Work.HornSC.no_bounded_component_of_preconnected_compl_sphere
import Submission.Work.HornSC.exists_jordan_curve_of_gap

/-!
# A simply connected plane domain has no bounded complementary component

Target: `Work.HornSC.sc_compl_component_unbounded`.

Route (classical characterisation "`Ω` simply connected ⟺ `ℂ̂ \ Ω` connected"):

* the complement of `Ω` in the Riemann sphere `OnePoint ℂ` is connected (step `hpre` below),
  because otherwise it has a clopen piece `S ⊆ Ωᶜ` at positive distance from the rest of `Ωᶜ`
  (`exists_compact_gap_of_compl_sphere_not_preconnected`), and the gap supplies a Jordan curve in
  `Ω` surrounding a point of `S` (`exists_jordan_curve_of_gap`), which winds non-trivially
  (`not_hasArg_of_jordan_curve`) — contradicting the simple connectivity of `Ω` through the
  holomorphic argument monodromy `Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton`;
* a connected sphere-complement has no bounded complementary component
  (`no_bounded_component_of_preconnected_compl_sphere`).
-/

namespace Work.HornSC

open Set

/-- **A loop in a simply connected domain has zero winding about every point it misses.**
`f` is a continuous `1`-periodic curve with values in the open set `U`, and `a ∉ U`; then
`t ↦ f t - a` admits a continuous `1`-periodic argument function. -/
theorem hasArg_of_simplyConnected {U : TopologicalSpace.Opens ℂ} (hUc : IsConnected (U : Set ℂ))
    (hsc : SimplyConnectedSpace ↥U) {a : ℂ} (ha : a ∉ (U : Set ℂ))
    {f : ℝ → ℂ} (hf : Continuous f) (hper : ∀ t : ℝ, f (t + 1) = f t)
    (hmem : ∀ t : ℝ, f t ∈ (U : Set ℂ)) :
    Commons.Topology.Winding.HasArg (fun t : ℝ => f t - a) 0 := by
  classical
  haveI : ConnectedSpace ↥U := isConnected_iff_connectedSpace.mp hUc
  haveI : SimplyConnectedSpace ↥U := hsc
  haveI : Subsingleton (Additive (FundamentalGroup ↥U ⟨f 0, hmem 0⟩) →+ ℝ) :=
    Work.SC.subsingleton_hom_additive_fundamentalGroup_of_simplyConnected _
  have hGhol : Submission.HolomorphicOnX (fun y : ↥U => (y : ℂ) - a) Set.univ :=
    Work.Mori.holomorphicOnX_opens_sub_const U a
  have hGne : ∀ y : ↥U, (y : ℂ) - a ≠ 0 := fun y h => ha (sub_eq_zero.mp h ▸ y.2)
  have hloop : Continuous (fun t : ℝ => (⟨f t, hmem t⟩ : ↥U)) := hf.subtype_mk hmem
  have hlper : ∀ t : ℝ, (fun s : ℝ => (⟨f s, hmem s⟩ : ↥U)) (t + 1)
      = (fun s : ℝ => (⟨f s, hmem s⟩ : ↥U)) t := fun t => Subtype.ext (hper t)
  have hga := Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton (X := ↥U)
    (x := ⟨f 0, hmem 0⟩) hGhol hGne hloop hlper
  simpa using hga

/-- **Surrounding a compact set in a gap.**  If `S` is compact, nonempty, and at positive distance
from a closed set `S'`, then there is a closed curve in the complement of `S ∪ S'` (a loop
`f : ℝ → ℂ`, continuous and `1`-periodic) that winds non-trivially around every prescribed point of
`S` (`¬ HasArg (f - a) 0`). -/
theorem loop_not_hasArg_of_gap {S S' : Set ℂ} (hS : IsCompact S) (hSne : S.Nonempty)
    (hS' : IsClosed S') (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ S', δ ≤ dist s s')
    {a : ℂ} (ha : a ∈ S) :
    ∃ f : ℝ → ℂ, Continuous f ∧ Function.Periodic f 1 ∧ (∀ t : ℝ, f t ∉ S ∪ S') ∧
      ¬ Commons.Topology.Winding.HasArg (fun t : ℝ => f t - a) 0 := by
  obtain ⟨γ, hγinj, hγrange, hγna, hγbdd⟩ := exists_jordan_curve_of_gap hS hSne hS' hgap ha
  refine ⟨fun t : ℝ => γ (Circle.exp (2 * Real.pi * t)), ?_, ?_, ?_, ?_⟩
  · exact γ.continuous.comp (by fun_prop)
  · intro t
    have h2 : 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi := by ring
    simp only [h2, Circle.exp_add, Circle.exp_two_pi, mul_one]
  · intro t
    exact hγrange ⟨Circle.exp (2 * Real.pi * t), rfl⟩
  · exact not_hasArg_of_jordan_curve hγinj hγna hγbdd

theorem sc_compl_component_unbounded (X : Set ℂ) (hXo : IsOpen X) (hXc : IsConnected X)
    (hXsc : SimplyConnectedSpace ↥X) {z : ℂ} (hz : z ∉ X) :
    ¬ Bornology.IsBounded (connectedComponentIn Xᶜ z) := by
  have hpre : IsPreconnected ((OnePoint.some '' X : Set (OnePoint ℂ))ᶜ) := by
    by_contra hnp
    obtain ⟨S, hSc, hSne, hSsub, δ, hδpos, hδ⟩ := exists_compact_gap_of_compl_sphere_not_preconnected hXo hnp
    -- `S' := Xᶜ \ S` is closed, since the gap bounds the distance to the compact `S`
    have hScl : IsClosed (Xᶜ \ S) := by
      have hset : Xᶜ \ S = Xᶜ ∩ Set.iInter (fun s : S => {w : ℂ | δ ≤ dist (s : ℂ) w}) := by
        ext w
        simp only [Set.mem_sdiff, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_iInter,
          Set.mem_ofPred_eq]
        constructor
        · intro hw
          exact ⟨hw.1, fun s => hδ s s.2 w hw.1 hw.2⟩
        · rintro ⟨hw1, hw2⟩
          refine ⟨hw1, fun hwS => ?_⟩
          have h := hw2 ⟨w, hwS⟩
          rw [dist_self] at h
          exact absurd h (not_le.mpr hδpos)
      rw [hset]
      exact hXo.isClosed_compl.inter
        (isClosed_iInter fun s : S =>
          isClosed_le continuous_const (continuous_const.dist continuous_id))
    have hgap' : ∃ δ' : ℝ, 0 < δ' ∧ ∀ s ∈ S, ∀ s' ∈ Xᶜ \ S, δ' ≤ dist s s' :=
      ⟨δ, hδpos, fun s hs s' hs' => hδ s hs s' hs'.1 hs'.2⟩
    obtain ⟨f, hfc, hfper, hfout, hno⟩ :=
      loop_not_hasArg_of_gap hSc hSne hScl hgap' hSne.some_mem
    have hfX : ∀ t : ℝ, f t ∈ X := by
      intro t
      have h1 : f t ∉ S ∪ (Xᶜ \ S) := hfout t
      have h2 : S ∪ (Xᶜ \ S) = Xᶜ := by
        ext w
        constructor
        · rintro (hw | hw)
          · exact hSsub hw
          · exact hw.1
        · intro hw
          by_cases hwS : w ∈ S
          · exact Or.inl hwS
          · exact Or.inr ⟨hw, hwS⟩
      rw [h2] at h1
      simpa using h1
    have haX : hSne.some ∉ X := fun h => (hSsub hSne.some_mem) h
    exact hno (hasArg_of_simplyConnected (U := ⟨X, hXo⟩) (a := hSne.some) (f := f)
      hXc hXsc haX hfc hfper hfX)
  exact no_bounded_component_of_preconnected_compl_sphere hXo hpre z hz

end Work.HornSC
