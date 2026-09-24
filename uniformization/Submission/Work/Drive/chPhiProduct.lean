import Mathlib
import Submission.Work.Drive.chartGadget
import Submission.Work.Drive.continuousAt_chGadget
import Submission.Work.Drive.continuousAt_chPhi_of_notMem_range

/-!
# The locally finite product of the chart-family transfer gadgets

`Work.Drive.chGadget c a ρ i` (`Submission/Work/Drive/chartGadget.lean`) is the transfer gadget
attached to the *chosen* chart `c i` of the maximal atlas, at the two pivots `a i`, `a (i+1)`.  This
file builds the product `chPhi c a ρ = ∏ᶠ i, chGadget c a ρ i` — the chart-family analogue of
`Work.Drive.gPhi` — with the three properties the assembly of the global phase needs:

* it is continuous away from the pivots (`continuousAt_chPhi`);
* it has modulus one away from the pivots (`norm_chPhi_eq_one_of_notMem_range`);
* only finitely many factors differ from `1` near a given point
  (`exists_finset_eventually_chGadget_ne_one`), which is what makes the product locally a *finite*
  product of continuous factors.

The product is *definitionally* the inline `∏ᶠ i, chGadget c a ρ i x` appearing in
`Work.Drive.continuousAt_chPhi_of_notMem_range`, so the continuity statement is an immediate
restatement of that (proved) theorem.
-/

open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The locally finite product of the chart-family transfer gadgets. -/
def chPhi (c : ℕ → OpenPartialHomeomorph X ℂ) (a : ℕ → X) (ρ : ℕ → ℝ) (x : X) : ℂ :=
  ∏ᶠ i : ℕ, chGadget c a ρ i x

/-- Where only the indices in `F` can contribute, the infinite product is the product over `F`. -/
lemma chPhi_eq_prod_of {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ}
    {F : Finset ℕ} {y : X} (h : ∀ i : ℕ, chGadget c a ρ i y ≠ 1 → i ∈ F) :
    chPhi c a ρ y = ∏ i ∈ F, chGadget c a ρ i y :=
  finprod_eq_prod_of_mulSupport_subset _ (fun i hi => h i (Function.mem_mulSupport.mp hi))

lemma eventually_chPhi_eq_prod {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ}
    {F : Finset ℕ} {p : X}
    (h : ∀ᶠ y in 𝓝 p, ∀ i : ℕ, chGadget c a ρ i y ≠ 1 → i ∈ F) :
    chPhi c a ρ =ᶠ[𝓝 p] fun y : X => ∏ i ∈ F, chGadget c a ρ i y := by
  filter_upwards [h] with y hy
  exact chPhi_eq_prod_of hy

/-- Only finitely many gadgets differ from `1` at a given point. -/
lemma finite_setOf_chGadget_ne_one {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ}
    (hρ : ∀ i, 0 < ρ i)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ chBall c a ρ i).Nonempty}.Finite)
    (x : X) : {i : ℕ | chGadget c a ρ i x ≠ 1}.Finite :=
  (hlf {x} isCompact_singleton).subset (fun i hi =>
    ⟨x, mem_singleton_iff.mpr rfl, mem_chBall.mpr (chGadget_ne_one_mem (hρ i) hi)⟩)

/-- Local finiteness in the finset-witness form. -/
lemma exists_finset_eventually_chGadget_ne_one {c : ℕ → OpenPartialHomeomorph X ℂ}
    {a : ℕ → X} {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ chBall c a ρ i).Nonempty}.Finite) (p : X) :
    ∃ F : Finset ℕ, ∀ᶠ y in 𝓝 p, ∀ i : ℕ, chGadget c a ρ i y ≠ 1 → i ∈ F := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  obtain ⟨K, hKc, hKnhds⟩ := exists_compact_mem_nhds p
  refine ⟨(hlf K hKc).toFinset, Filter.eventually_of_mem hKnhds fun y hy i hi => ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨y, hy, mem_chBall.mpr (chGadget_ne_one_mem (hρ i) hi)⟩

/-- Away from the pivots the product of the gadgets is continuous. -/
theorem continuousAt_chPhi {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ}
    (hρ : ∀ i, 0 < ρ i)
    (hsrc : ∀ i, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source)
    (hclose : ∀ i, ‖chQ c a i - chP c a i‖ < 2 * ρ i)
    (hwell : ∀ i, closure {y : X | y ∈ (c i).source ∧
      (c i) y ∈ Metric.ball ((c i) (a i)) (8 * ρ i)} ⊆ (c i).source)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ {y : X | y ∈ (c i).source ∧
      (c i) y ∈ Metric.ball ((c i) (a i)) (8 * ρ i)}).Nonempty}.Finite)
    {p : X} (hp : ∀ i : ℕ, p ≠ a i) : ContinuousAt (chPhi c a ρ) p := by
  have h := continuousAt_chPhi_of_notMem_range (c := c) (a := a) (ρ := ρ) hρ hsrc hclose hwell
    (fun A hA => by simpa [chBall] using hlf A hA) hp
  exact h

/-- Away from the pivots the product of the gadgets has modulus one. -/
lemma norm_chPhi_eq_one_of_notMem_range {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X}
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hsrc : ∀ i, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ chBall c a ρ i).Nonempty}.Finite)
    {x : X} (hx : ∀ i : ℕ, x ≠ a i) : ‖chPhi c a ρ x‖ = 1 := by
  have hfin := finite_setOf_chGadget_ne_one (c := c) (a := a) (ρ := ρ) hρ hlf x
  rw [chPhi, finprod_eq_prod_of_mulSupport_subset_of_finite _
    (s := {i : ℕ | chGadget c a ρ i x ≠ 1}) (fun i hi => hi) hfin]
  rw [norm_prod]
  refine Finset.prod_eq_one fun i hi => ?_
  rw [hfin.mem_toFinset] at hi
  exact norm_chGadget_eq_one (hsrc i).1 (hsrc i).2 (hx i) (hx (i + 1))


/-- Away from the pivots the product of the gadgets does not vanish. -/
lemma chPhi_ne_zero_of_notMem_range {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X}
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hsrc : ∀ i, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ chBall c a ρ i).Nonempty}.Finite)
    {x : X} (hx : ∀ i : ℕ, x ≠ a i) : chPhi c a ρ x ≠ 0 := by
  intro h
  have := norm_chPhi_eq_one_of_notMem_range hρ hsrc hlf hx
  rw [h, norm_zero] at this
  exact zero_ne_one this

end Work.Drive
