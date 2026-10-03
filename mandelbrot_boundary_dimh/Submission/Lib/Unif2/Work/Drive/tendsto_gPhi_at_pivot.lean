import Mathlib
import Submission.Lib.Unif2.Work.Drive.phaseChainDefs
import Submission.Lib.Unif2.Work.Drive.pair_gadget_tendsto
import Submission.Lib.Unif2.Work.Drive.continuousAt_gadget
import Submission.Lib.Unif2.Work.Drive.deriv_chart_transition_ne_zero

/-!
# The limit of the telescoping product of gadgets at a pivot

`Work.Drive.gPhi a ρ = ∏ᶠ i, gadget a ρ i` is the locally finite product of the transfer
gadgets of the pivot chain `a` with radii `ρ` (see `Submission/Work/Drive/phaseChainDefs.lean`).

At the pivot `a j` with `j ≥ 1` the individual gadgets `gadget a ρ (j - 1)` and `gadget a ρ j` are
singular, but their *product* has a non-zero limit along the punctured neighbourhood of `a j`
(`Work.Drive.pair_gadget_tendsto`).  This file proves that the full product `gPhi a ρ` itself has a
non-zero limit at `a j`: by local finiteness of the supports, near `a j` the product `gPhi a ρ` is
an honest finite product of gadgets, all of whose factors except the two singular ones are
continuous at `a j` and non-zero at `a j`.  Hence the limit is the product of the (non-zero) limit
of the pair and of the (non-zero) value of the remaining finite product.
-/

open Filter Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The gadget is non-zero at every point which is neither of its two pivots. -/
lemma gadget_ne_zero_of_ne_pivots {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X}
    (hsrc : a (i + 1) ∈ (chartAt ℂ (a i)).source)
    (hx₁ : x ≠ a i) (hx₂ : x ≠ a (i + 1)) : gadget a ρ i x ≠ 0 := by
  unfold gadget
  by_cases h1 : x ∈ (chartAt ℂ (a i)).source ∧ ‖(chartAt ℂ (a i)) x - gP a i‖ ≤ 2 * ρ i
  · rw [if_pos h1]
    have hxs : x ∈ (chartAt ℂ (a i)).source := h1.1
    have hA : (chartAt ℂ (a i)) x - gP a i ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      exact hx₁ ((chartAt ℂ (a i)).injOn hxs (mem_chart_source ℂ (a i)) h)
    have hB : (chartAt ℂ (a i)) x - gQ a i ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      exact hx₂ ((chartAt ℂ (a i)).injOn hxs hsrc h)
    exact phase_ne_zero (div_ne_zero hA hB)
  · rw [if_neg h1]
    by_cases h2 : x ∈ (chartAt ℂ (a i)).source ∧ ‖(chartAt ℂ (a i)) x - gP a i‖ < 8 * ρ i
    · rw [if_pos h2]
      exact Complex.exp_ne_zero _
    · rw [if_neg h2]
      exact one_ne_zero

theorem tendsto_gPhi_at_pivot {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {a : ℕ → X} {ρ : ℕ → ℝ}
    (hρ : ∀ i, 0 < ρ i)
    (hinj : Function.Injective a)
    (hstep : ∀ i, a (i + 1) ∈ Work.Drive.gB a ρ i)
    (hwell : ∀ i, closure (Work.Drive.gU a ρ i) ⊆ (chartAt ℂ (a i)).source)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ Work.Drive.gU a ρ i).Nonempty}.Finite)
    {j : ℕ} (hj : 1 ≤ j) :
    ∃ c : ℂ, c ≠ 0 ∧ Filter.Tendsto (Work.Drive.gPhi a ρ)
      (nhdsWithin (a j) {(a j)}ᶜ) (nhds c) := by
  classical
  -- the two indices whose gadgets are singular at `a j`
  have hj1 : j - 1 + 1 = j := Nat.sub_add_cancel hj
  -- the pair of consecutive gadgets has a non-zero limit at the shared pivot
  have hT : deriv (((chartAt ℂ (a (j - 1))).symm.trans (chartAt ℂ (a j))) : ℂ → ℂ)
      ((chartAt ℂ (a (j - 1))) (a j)) ≠ 0 :=
    deriv_chart_transition_ne_zero (x := a (j - 1)) (y := a j)
      (by simpa only [hj1] using step_src hstep (j - 1))
  obtain ⟨cP, hcPne, hP⟩ := pair_gadget_tendsto hj hρ hinj hstep hT
  -- local finiteness: near `a j` only the gadgets indexed by a fixed finite set can be non-trivial
  obtain ⟨F₀, hF₀⟩ := exists_finset_eventually_gadget_ne_one hρ hlf (a j)
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
  have hFev : ∀ᶠ y in 𝓝 (a j), ∀ i : ℕ, gadget a ρ i y ≠ 1 → i ∈ F :=
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
      (∏ i ∈ S, gadget a ρ i y) * (gadget a ρ (j - 1) y * gadget a ρ j y) = gPhi a ρ y := by
    filter_upwards [hFev] with y hy
    rw [gPhi_eq_prod_of (F := F) hy, hFdef,
      Finset.prod_insert (f := fun i => gadget a ρ i y) hnot1,
      Finset.prod_insert (f := fun i => gadget a ρ i y) hje]
    ring
  -- the "rest" product is continuous at the pivot
  have hRestT : Filter.Tendsto (fun y : X => ∏ i ∈ S, gadget a ρ i y) (𝓝 (a j))
      (𝓝 (∏ i ∈ S, gadget a ρ i (a j))) := by
    refine tendsto_finsetProd S (fun i hi => ?_)
    rw [hSdef] at hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hij1 : i ≠ j - 1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hi)).1
    exact (continuousAt_gadget (a := a) (ρ := ρ) (i := i) (x := a j) (hρ i)
      (norm_gQ_sub_gP_lt hρ hstep i) (step_src hstep i) (hwell i)
      (fun h => hij (hinj h).symm) (fun h => hij1 (by have h' : j = i + 1 := hinj h; omega))).tendsto
  -- the "rest" product is non-zero at the pivot
  have hRestne : (∏ i ∈ S, gadget a ρ i (a j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    rw [hSdef] at hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hij1 : i ≠ j - 1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hi)).1
    exact gadget_ne_zero_of_ne_pivots (step_src hstep i)
      (fun h => hij (hinj h).symm) (fun h => hij1 (by have h' : j = i + 1 := hinj h; omega))
  refine ⟨(∏ i ∈ S, gadget a ρ i (a j)) * cP, mul_ne_zero hRestne hcPne, ?_⟩
  have hprod : Filter.Tendsto
      (fun y : X => (∏ i ∈ S, gadget a ρ i y) * (gadget a ρ (j - 1) y * gadget a ρ j y))
      (nhdsWithin (a j) {(a j)}ᶜ) (nhds ((∏ i ∈ S, gadget a ρ i (a j)) * cP)) :=
    (hRestT.mono_left nhdsWithin_le_nhds).mul hP
  exact hprod.congr' (Filter.Eventually.filter_mono nhdsWithin_le_nhds hsplit)

end Work.Drive
