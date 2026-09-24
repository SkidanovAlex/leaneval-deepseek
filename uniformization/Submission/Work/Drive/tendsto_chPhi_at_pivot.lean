import Mathlib
import Submission.Work.Drive.chPhiProduct
import Submission.Work.Drive.pair_chGadget_tendsto
import Submission.Work.Drive.tendsto_gPhi_at_pivot
import Submission.Work.Drive.atlas_transition_deriv

namespace Work.Drive

open scoped Manifold ContDiff Topology

open Filter Set Metric

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The gadget of the chart family is non-zero at every point which is neither of its two
pivots.  This is the chart-family analogue of `Work.Drive.gadget_ne_zero_of_ne_pivots`. -/
lemma chGadget_ne_zero_of_ne_pivots {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X}
    {ρ : ℕ → ℝ} {i : ℕ} {x : X}
    (hP : a i ∈ (c i).source) (hQ : a (i + 1) ∈ (c i).source)
    (hx₁ : x ≠ a i) (hx₂ : x ≠ a (i + 1)) : chGadget c a ρ i x ≠ 0 := by
  unfold chGadget
  by_cases h1 : x ∈ (c i).source ∧ ‖(c i) x - chP c a i‖ ≤ 2 * ρ i
  · rw [if_pos h1]
    have hxs : x ∈ (c i).source := h1.1
    have hA : (c i) x - chP c a i ≠ 0 := by
      intro h
      rw [chP, sub_eq_zero] at h
      exact hx₁ ((c i).injOn hxs hP h)
    have hB : (c i) x - chQ c a i ≠ 0 := by
      intro h
      rw [chQ, sub_eq_zero] at h
      exact hx₂ ((c i).injOn hxs hQ h)
    exact phase_ne_zero (div_ne_zero hA hB)
  · rw [if_neg h1]
    by_cases h2 : x ∈ (c i).source ∧ ‖(c i) x - chP c a i‖ < 8 * ρ i
    · rw [if_pos h2]
      exact Complex.exp_ne_zero _
    · rw [if_neg h2]
      exact one_ne_zero

/-- At the pivot `a j` with `j ≥ 1` the locally finite product `chPhi c a ρ` of the gadgets of the
chosen chart family has a non-zero limit along the punctured neighbourhood.  This is the
chart-family analogue of `Work.Drive.tendsto_gPhi_at_pivot`: near `a j` the product is an honest
finite product, whose only singular factors are the two gadgets `j - 1` and `j`; their product has
a non-zero limit by `Work.Drive.pair_chGadget_tendsto`, and all the remaining factors are
continuous and non-zero at `a j`. -/
theorem tendsto_chPhi_at_pivot {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ}
    (hca : ∀ i : ℕ, c i ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X)
    (hρ : ∀ i, 0 < ρ i)
    (hinj : Function.Injective a)
    (hchain : ∀ i : ℕ, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source ∧
      ‖(c i) (a (i + 1)) - (c i) (a i)‖ < ρ i)
    (hwell : ∀ i, closure {y : X | y ∈ (c i).source ∧
      (c i) y ∈ Metric.ball ((c i) (a i)) (8 * ρ i)} ⊆ (c i).source)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ {y : X | y ∈ (c i).source ∧
      (c i) y ∈ Metric.ball ((c i) (a i)) (8 * ρ i)}).Nonempty}.Finite)
    {j : ℕ} (hj : 1 ≤ j) :
    ∃ C : ℂ, C ≠ 0 ∧ Filter.Tendsto (Work.Drive.chPhi c a ρ)
      (nhdsWithin (a j) {(a j)}ᶜ) (nhds C) := by
  classical
  have hj1 : j - 1 + 1 = j := Nat.sub_add_cancel hj
  -- the pivot conditions in the form used by the gadget lemmas
  have hsrc : ∀ i : ℕ, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source :=
    fun i => ⟨(hchain i).1, (hchain i).2.1⟩
  have hlf' : ∀ A : Set X, IsCompact A →
      {i : ℕ | (A ∩ chBall c a ρ i).Nonempty}.Finite :=
    fun A hA => by simpa [chBall] using hlf A hA
  have hclose : ∀ i : ℕ, ‖chQ c a i - chP c a i‖ < 2 * ρ i := by
    intro i
    have h := (hchain i).2.2
    have hq : ‖chQ c a i - chP c a i‖ = ‖(c i) (a (i + 1)) - (c i) (a i)‖ := by
      simp [chQ, chP]
    rw [hq]
    linarith [hρ i]
  -- the pair of consecutive gadgets has a non-zero limit at the shared pivot
  obtain ⟨cP, hcPne, hPair⟩ :=
    pair_chGadget_tendsto (c := c) (a := a) (ρ := ρ) hj hca hρ hchain hinj
  -- local finiteness: near `a j` only the gadgets indexed by a fixed finite set can be non-trivial
  obtain ⟨F₀, hF₀⟩ := exists_finset_eventually_chGadget_ne_one (c := c) (a := a) (ρ := ρ)
    hρ hlf' (a j)
  -- remove the two singular indices and reinsert them, so that the product splits off cleanly
  set S : Finset ℕ := (F₀.erase (j - 1)).erase j with hSdef
  set F : Finset ℕ := insert (j - 1) (insert j S) with hFdef
  have hF₀F : F₀ ⊆ F := by
    intro i hi
    rw [hFdef]
    by_cases h1 : i = j - 1
    · exact Finset.mem_insert.mpr (Or.inl h1)
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      by_cases h2 : i = j
      · exact Finset.mem_insert.mpr (Or.inl h2)
      · refine Finset.mem_insert.mpr (Or.inr ?_)
        rw [hSdef, Finset.mem_erase, Finset.mem_erase]
        exact ⟨h2, h1, hi⟩
  have hFev : ∀ᶠ y in 𝓝 (a j), ∀ i : ℕ, chGadget c a ρ i y ≠ 1 → i ∈ F :=
    hF₀.mono fun y hy i hi => hF₀F (hy i hi)
  have hSne : (j - 1) ∉ S := by
    rw [hSdef]
    exact fun h => Finset.notMem_erase (j - 1) F₀ (Finset.mem_of_mem_erase h)
  have hje : j ∉ S := by
    rw [hSdef]
    exact fun h => (Finset.mem_erase.mp h).1 rfl
  have hnot1 : j - 1 ∉ insert j S := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact absurd h (by omega)
    · exact hSne h
  -- the product splits into the "rest" product times the pair
  have hsplit : ∀ᶠ y in 𝓝 (a j),
      (∏ i ∈ S, chGadget c a ρ i y) * (chGadget c a ρ (j - 1) y * chGadget c a ρ j y) =
        chPhi c a ρ y := by
    filter_upwards [hFev] with y hy
    rw [chPhi_eq_prod_of (F := F) hy, hFdef,
      Finset.prod_insert (f := fun i => chGadget c a ρ i y) hnot1,
      Finset.prod_insert (f := fun i => chGadget c a ρ i y) hje]
    ring
  -- the "rest" product is continuous at the pivot
  have hRestT : Filter.Tendsto (fun y : X => ∏ i ∈ S, chGadget c a ρ i y) (𝓝 (a j))
      (𝓝 (∏ i ∈ S, chGadget c a ρ i (a j))) := by
    refine tendsto_finsetProd S (fun i hi => ?_)
    rw [hSdef] at hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hij1 : i ≠ j - 1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hi)).1
    exact (continuousAt_chGadget (c := c) (a := a) (ρ := ρ) (i := i) (x := a j) (hρ i)
      (hclose i) (hsrc i).1 (hsrc i).2 (hwell i)
      (fun h => hij (hinj h).symm) (fun h => hij1 (by have h' : j = i + 1 := hinj h; omega))).tendsto
  -- the "rest" product is non-zero at the pivot
  have hRestne : (∏ i ∈ S, chGadget c a ρ i (a j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    rw [hSdef] at hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hij1 : i ≠ j - 1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hi)).1
    exact chGadget_ne_zero_of_ne_pivots (hsrc i).1 (hsrc i).2
      (fun h => hij (hinj h).symm) (fun h => hij1 (by have h' : j = i + 1 := hinj h; omega))
  refine ⟨(∏ i ∈ S, chGadget c a ρ i (a j)) * cP, mul_ne_zero hRestne hcPne, ?_⟩
  have hprod : Filter.Tendsto
      (fun y : X => (∏ i ∈ S, chGadget c a ρ i y) *
        (chGadget c a ρ (j - 1) y * chGadget c a ρ j y))
      (nhdsWithin (a j) {(a j)}ᶜ) (nhds ((∏ i ∈ S, chGadget c a ρ i (a j)) * cP)) :=
    (hRestT.mono_left nhdsWithin_le_nhds).mul hPair
  exact hprod.congr' (Filter.Eventually.filter_mono nhdsWithin_le_nhds hsplit)

end

end Work.Drive
