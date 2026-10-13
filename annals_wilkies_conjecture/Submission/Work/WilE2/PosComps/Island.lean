import Mathlib
import Submission.Work.WilE2.PosComps.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical Topology Filter

namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E

/-! ## Components of the positive set, islands and their critical points.

Support module for `Work.WilE2.posComps_finite`. -/

theorem closure_component_subset_cube {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    (x₀ : Fin k → ℝ) :
    closure (connectedComponentIn (posSet c Q) x₀) ⊆ cubeC k :=
  closure_minimal (fun _ hy => (connectedComponentIn_subset (posSet c Q) x₀ hy).1)
    (isClosed_cubeC k)

/-- Every point of `posSet c Q` in the interior of the cube has a ball around it inside its
component. -/
theorem exists_ball_subset_component {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    {x : Fin k → ℝ} (hx : x ∈ posSet c Q) (hint : x ∈ interior (cubeC k)) :
    ∃ ρ > 0, Metric.ball x ρ ⊆ connectedComponentIn (posSet c Q) x := by
  obtain ⟨ρ₁, hρ₁, hsub₁⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hint)
  obtain ⟨ρ₂, hρ₂, hsub₂⟩ := Metric.mem_nhds_iff.mp ((isOpen_eaEval_pos c Q).mem_nhds hx.2)
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  have hball : IsPreconnected (Metric.ball x (min ρ₁ ρ₂)) := (convex_ball x _).isPreconnected
  refine hball.subset_connectedComponentIn (Metric.mem_ball_self (lt_min hρ₁ hρ₂)) ?_
  intro y hy
  exact ⟨interior_subset (hsub₁ (Metric.ball_subset_ball (min_le_left _ _) hy)),
    hsub₂ (Metric.ball_subset_ball (min_le_right _ _) hy)⟩

/-- A component of the positive set contained in the interior of the cube is open. -/
theorem component_open_of_interior {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    {x₀ : Fin k → ℝ} (hint : connectedComponentIn (posSet c Q) x₀ ⊆ interior (cubeC k)) :
    IsOpen (connectedComponentIn (posSet c Q) x₀) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨ρ, hρ, hball⟩ := exists_ball_subset_component c Q
    (connectedComponentIn_subset _ _ hx) (hint hx)
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x hρ) ?_
  intro y hy
  rw [connectedComponentIn_eq hx]
  exact hball hy

/-- On the boundary of a component of the positive set the function is nonpositive. -/
theorem component_closure_le {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    {x₀ : Fin k → ℝ} (hx₀ : x₀ ∈ posSet c Q) {y : Fin k → ℝ}
    (hy : y ∈ closure (connectedComponentIn (posSet c Q) x₀))
    (hyc : y ∉ connectedComponentIn (posSet c Q) x₀) :
    eaEval c Q y ≤ 0 := by
  by_contra h
  push Not at h
  have hyS : y ∈ posSet c Q := ⟨closure_component_subset_cube c Q x₀ hy, h⟩
  have hpre : IsPreconnected (connectedComponentIn (posSet c Q) x₀ ∪ {y}) :=
    (isPreconnected_connectedComponentIn (F := posSet c Q) (x := x₀)).subset_closure
      (fun z hz => Or.inl hz)
      (Set.union_subset subset_closure (Set.singleton_subset_iff.mpr hy))
  have hsub : connectedComponentIn (posSet c Q) x₀ ∪ {y} ⊆ posSet c Q :=
    Set.union_subset (connectedComponentIn_subset _ _) (Set.singleton_subset_iff.mpr hyS)
  have hx : x₀ ∈ connectedComponentIn (posSet c Q) x₀ ∪ {y} :=
    Or.inl (mem_connectedComponentIn hx₀)
  exact hyc (hpre.subset_connectedComponentIn hx hsub (Or.inr rfl))

/-- **The maximum of `eaEval c Q` on the closure of a component is attained inside it.** -/
theorem exists_max_of_component {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    {x₀ : Fin k → ℝ} (hx₀ : x₀ ∈ posSet c Q) :
    ∃ y ∈ connectedComponentIn (posSet c Q) x₀,
      (∀ w ∈ closure (connectedComponentIn (posSet c Q) x₀), eaEval c Q w ≤ eaEval c Q y) ∧
      0 < eaEval c Q y := by
  have hcl := closure_component_subset_cube c Q x₀
  have hcomp : IsCompact (closure (connectedComponentIn (posSet c Q) x₀)) :=
    (isCompact_cubeC k).of_isClosed_subset isClosed_closure hcl
  have hne : (closure (connectedComponentIn (posSet c Q) x₀)).Nonempty :=
    ⟨x₀, subset_closure (mem_connectedComponentIn hx₀)⟩
  obtain ⟨y, hy, hymax⟩ :=
    hcomp.exists_isMaxOn hne (Work.WilE5.Flat.continuous_eaEval c Q).continuousOn
  have hxcl : x₀ ∈ closure (connectedComponentIn (posSet c Q) x₀) :=
    subset_closure (mem_connectedComponentIn hx₀)
  have hyC : y ∈ connectedComponentIn (posSet c Q) x₀ := by
    by_contra hyc
    have h1 : eaEval c Q x₀ ≤ eaEval c Q y := (isMaxOn_iff.mp hymax) x₀ hxcl
    have h2 : eaEval c Q y ≤ 0 := component_closure_le c Q hx₀ hy hyc
    exact (not_lt_of_ge (h1.trans h2)) hx₀.2
  exact ⟨y, hyC, fun w hw => (isMaxOn_iff.mp hymax) w hw,
    lt_of_lt_of_le hx₀.2 ((isMaxOn_iff.mp hymax) x₀ hxcl)⟩

/-- Extraction of a coordinate from a sum of `• proj`. -/
theorem sum_mul_single {k : ℕ} (c : Fin k → ℝ) (i : Fin k) :
    (∑ j : Fin k, c j * (Pi.single i (1 : ℝ) : Fin k → ℝ) j) = c i := by
  have h : ∀ j : Fin k, c j * (Pi.single i (1 : ℝ) : Fin k → ℝ) j
      = (if j = i then c j else 0) := by
    intro j
    by_cases hj : j = i
    · rw [if_pos hj, hj, Pi.single_eq_same, mul_one]
    · rw [if_neg hj, Pi.single_eq_of_ne hj, mul_zero]
  simp only [h]
  rw [Finset.sum_ite_eq']
  simp

/-- **An island contains a critical point of `Q + u·x`** whenever the perturbation is small
compared with the maximum of `Q` on the island. -/
theorem exists_crit_of_island {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    {x₀ y : Fin k → ℝ} (hx₀ : x₀ ∈ posSet c Q)
    (hy : y ∈ connectedComponentIn (posSet c Q) x₀)
    (hymax : ∀ w ∈ closure (connectedComponentIn (posSet c Q) x₀), eaEval c Q w ≤ eaEval c Q y)
    (hint : connectedComponentIn (posSet c Q) x₀ ⊆ interior (cubeC k))
    (u : Fin k → ℝ) (hsmall : 2 * (∑ i, |u i|) < eaEval c Q y) :
    ∃ z ∈ connectedComponentIn (posSet c Q) x₀,
      ∀ i, eaEval c (eaD c i Q) z = - u i := by
  classical
  set C := connectedComponentIn (posSet c Q) x₀ with hC
  set F : (Fin k → ℝ) → ℝ := (fun z : Fin k → ℝ => eaEval c Q z) + linCLM u with hF
  have hFapply : ∀ z : Fin k → ℝ, F z = eaEval c Q z + linCLM u z := fun z => rfl
  have hCopen : IsOpen C := component_open_of_interior c Q hint
  have hcl : closure C ⊆ cubeC k := closure_component_subset_cube c Q x₀
  have hcomp : IsCompact (closure C) :=
    (isCompact_cubeC k).of_isClosed_subset isClosed_closure hcl
  have hne : (closure C).Nonempty := ⟨y, subset_closure hy⟩
  have hcont : Continuous F :=
    (Work.WilE5.Flat.continuous_eaEval c Q).add (linCLM u).continuous
  obtain ⟨z, hz, hzmax⟩ := hcomp.exists_isMaxOn hne hcont.continuousOn
  have hycl : y ∈ closure C := subset_closure hy
  have hzC : z ∈ C := by
    by_contra hzc
    have hycube : y ∈ cubeC k := hcl hycl
    have hzcube : z ∈ cubeC k := hcl hz
    have hQz : eaEval c Q z ≤ 0 := component_closure_le c Q hx₀ hz hzc
    have h1 : -(∑ i, |u i|) ≤ linCLM u y := by
      have := linCLM_abs_le u hycube
      linarith [neg_abs_le (linCLM u y)]
    have h2 : linCLM u z ≤ ∑ i, |u i| := linCLM_le_sum_abs u hzcube
    have h3 : F y ≤ F z := (isMaxOn_iff.mp hzmax) y hycl
    rw [hFapply y, hFapply z] at h3
    linarith
  have hlocal : IsLocalMax F z :=
    (hzmax.isLocalMaxOn).isLocalMax
      (Filter.mem_of_superset (hCopen.mem_nhds hzC) subset_closure)
  have hfderiv : fderiv ℝ F z = 0 := hlocal.fderiv_eq_zero
  have hF' : HasFDerivAt F
      ((∑ i, eaEval c (eaD c i Q) z • ContinuousLinearMap.proj i) + linCLM u) z :=
    (Work.WilE5.Calc.hasFDerivAt_eaEval c Q z).add (linCLM u).hasFDerivAt
  have hderiv : (∑ i, eaEval c (eaD c i Q) z • ContinuousLinearMap.proj i) + linCLM u
      = ∑ i, (eaEval c (eaD c i Q) z + u i) • ContinuousLinearMap.proj i := by
    simp only [linCLM]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← add_smul]
  have hzero : (∑ i, (eaEval c (eaD c i Q) z + u i) • ContinuousLinearMap.proj i
      : (Fin k → ℝ) →L[ℝ] ℝ) = 0 := by
    rw [← hderiv, ← hF'.fderiv]
    exact hfderiv
  refine ⟨z, hzC, fun i => ?_⟩
  have h1 : (∑ j : Fin k, (eaEval c (eaD c j Q) z + u j) *
      ((Pi.single i (1 : ℝ) : Fin k → ℝ) j)) = 0 := by
    have h2 := congrArg
      (fun (L : (Fin k → ℝ) →L[ℝ] ℝ) => L (Pi.single i (1 : ℝ) : Fin k → ℝ)) hzero
    simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, smul_eq_mul] using h2
  have h3 := sum_mul_single (fun j => eaEval c (eaD c j Q) z + u j) i
  rw [h3] at h1
  linarith

end Work.WilE2
