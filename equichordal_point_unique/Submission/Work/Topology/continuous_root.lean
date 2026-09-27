import Mathlib
import Submission.Work.Topology.uniform_bound_Ici_of_tendsto

set_option linter.style.haveILetI false

namespace Work.Topology

/-- **A continuous `k`-th root on a preconnected subset of `ℝ`.**

Let `I ⊆ ℝ` be preconnected (i.e. an interval), `g : ℝ → ℂ` continuous on `I` and nowhere zero on
`I`, and `k ≥ 1`. Then `g` has a continuous `k`-th root on `I`: there is `t : ℝ → ℂ`, continuous on
`I`, with `t s ^ k = g s` for all `s ∈ I` (and hence `t s ≠ 0` there).

Route. `I` is preconnected in `ℝ`, hence `OrdConnected` (`IsPreconnected.ordConnected`) hence convex
(`Set.OrdConnected.convex`); a convex set is contractible and locally path connected
(`Convex.contractibleSpace`, `Convex.locallyPathConnectedSpace`), so `↥I` is simply connected and
locally path connected and the `k`-th power covering `isCoveringMap_npow` on `ℂ \ {0}` has a unique
continuous lift (`IsCoveringMap.existsUnique_continuousMap_lifts`) of `s ↦ ⟨g s, ·⟩` sending a base
point `s₀ ∈ I` to any chosen `k`-th root of `g s₀` (e.g. `(g s₀) ^ ((k : ℂ)⁻¹)`, using
`Complex.cpow_nat_inv_pow`). Restrict the lift to `I`.  (The empty case `I = ∅` is immediate.) -/
theorem continuous_root {I : Set ℝ} (hI : IsPreconnected I)
    {g : ℝ → ℂ} (hg : ContinuousOn g I) (hne : ∀ s ∈ I, g s ≠ 0) {k : ℕ} (hk : 0 < k) :
    ∃ t : ℝ → ℂ, ContinuousOn t I ∧ (∀ s ∈ I, t s ^ k = g s) ∧ ∀ s ∈ I, t s ≠ 0 := by
  classical
  rcases I.eq_empty_or_nonempty with hIe | hIne
  · rw [hIe]
    exact ⟨fun _ => 0, continuousOn_empty _, by simp, by simp⟩
  obtain ⟨s₀, hs₀⟩ := hIne
  -- `I` is an interval, hence convex, contractible and locally path connected.
  have hIoc : I.OrdConnected := hI.ordConnected
  have hcvx : Convex ℝ I := hIoc.convex
  letI : ContractibleSpace I := hcvx.contractibleSpace ⟨s₀, hs₀⟩
  letI : LocallyPathConnectedSpace I := hcvx.locallyPathConnectedSpace
  -- The `k`-th power map on `ℂ \ {0}` is a covering map.
  let p : {z : ℂ // z ≠ 0} → {z : ℂ // z ≠ 0} := fun z => ⟨z.1 ^ k, pow_ne_zero k z.2⟩
  have hp : IsCoveringMap p := isCoveringMap_npow k (Nat.cast_ne_zero.mpr hk.ne')
  -- The map `s ↦ ⟨g s, ·⟩` into `ℂ \ {0}` and the chosen base point.
  let f : C(I, {z : ℂ // z ≠ 0}) :=
    ⟨fun s => ⟨g s, hne s s.2⟩, hg.domRestrict.subtype_mk _⟩
  let e₀ : {z : ℂ // z ≠ 0} :=
    ⟨(g s₀) ^ ((k : ℂ)⁻¹), (Complex.cpow_ne_zero_iff).2 (Or.inl (hne s₀ hs₀))⟩
  have he : p e₀ = f ⟨s₀, hs₀⟩ := by
    refine Subtype.ext ?_
    exact Complex.cpow_nat_inv_pow (g s₀) hk.ne'
  -- Lift `f` through the covering map.
  obtain ⟨F, ⟨hF₀, hFlift⟩, -⟩ := hp.existsUnique_continuousMap_lifts f ⟨s₀, hs₀⟩ e₀ he
  -- Restrict the lift to `I`.
  let t : ℝ → ℂ := fun s => if hs : s ∈ I then (F ⟨s, hs⟩).1 else 0
  have ht : ∀ x : I, t x = (F x).1 := by intro x; simp [t]
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    refine Continuous.congr (continuous_subtype_val.comp F.continuous) fun x => ?_
    exact (ht x).symm
  · intro s hs
    have h1 := congrArg Subtype.val (congrFun hFlift ⟨s, hs⟩)
    simp only [Function.comp_apply] at h1
    rw [ht ⟨s, hs⟩]
    exact h1
  · intro s hs
    rw [ht ⟨s, hs⟩]
    exact (F ⟨s, hs⟩).2

end Work.Topology
