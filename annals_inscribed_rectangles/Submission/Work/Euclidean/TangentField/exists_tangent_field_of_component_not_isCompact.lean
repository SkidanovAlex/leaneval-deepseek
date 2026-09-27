import Mathlib
import Submission.Work.ManifoldParity.GraphManifold
import Submission.Work.ManifoldParity.CircleParam
import Submission.Work.OneDim.classify_connected_one_manifold
import Submission.Work.ManifoldParity.OpensInclusion
import Submission.Work.ManifoldParity.curve_tangent_chart
import Submission.Work.ManifoldParity.exists_tangentField_of_closed_curves
import Submission.Work.Euclidean.TangentField.exists_param_component_of_not_isCompact

/-!
# A tangent field on a non-compact connected component

A non-compact connected component of a locally-graph set `K ⊆ ℝⁿ` is diffeomorphic to `ℝ`
(`Work.Euclidean.TangentField.exists_param_component_of_not_isCompact`, itself built on
`Work.OneDim.classify_connected_one_manifold`), hence parametrised by an injective smooth curve
`γ : ℝ → ℝⁿ` with nowhere vanishing velocity whose range is the image of the component.  This file
transports the velocity of `γ` back to the range of `γ` (`curveVel`), and shows that the resulting
field is continuous (`curveVel_continuousOn`, using the local surjectivity
`Work.ManifoldParity.exists_open_nhds_param_of_range` of a regular curve in a locally-graph set),
non-vanishing (`curveVel_ne_zero`) and tangent to every graph chart of `K`
(`curveVel_tangent`, via `Work.ManifoldParity.curve_tangent_chart`).

The main statement is `exists_tangent_field_of_component_not_isCompact`.
-/

namespace Work.Euclidean.TangentField

open scoped Manifold Topology
open Set Filter

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- **The velocity of an injective curve, transported to its range.**  At a point of the range this
is the velocity of `γ` at a parameter of the point; outside the range it is `0`. -/
def curveVel (γ : ℝ → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y => if hy : y ∈ Set.range γ then fderiv ℝ γ (Classical.choose hy) 1 else 0

theorem curveVel_eq_of_mem {γ : ℝ → EuclideanSpace ℝ (Fin n)}
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Set.range γ) :
    curveVel γ y = fderiv ℝ γ (Classical.choose hy) 1 := dif_pos hy

/-- **The velocity field is well defined on the range of the curve** (no periodicity is needed
here, only injectivity). -/
theorem curveVel_eq_of (γ : ℝ → EuclideanSpace ℝ (Fin n))
    (hinj : Function.Injective γ) (t : ℝ) :
    curveVel γ (γ t) = fderiv ℝ γ t 1 := by
  have hy : γ t ∈ Set.range γ := ⟨t, rfl⟩
  rw [curveVel_eq_of_mem hy, hinj (Classical.choose_spec hy)]

theorem curveVel_ne_zero {γ : ℝ → EuclideanSpace ℝ (Fin n)}
    (hvel : ∀ t, fderiv ℝ γ t 1 ≠ 0) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Set.range γ) :
    curveVel γ y ≠ 0 := by
  rw [curveVel_eq_of_mem hy]; exact hvel _

/-- **The transported velocity is tangent to every graph chart of `K`.** -/
theorem curveVel_tangent (K : Set (EuclideanSpace ℝ (Fin n)))
    (γ : ℝ → EuclideanSpace ℝ (Fin n))
    (hsm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) γ)
    (hvel : ∀ t, fderiv ℝ γ t 1 ≠ 0)
    (hγK : ∀ t, γ t ∈ K) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Set.range γ)
    (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ → EuclideanSpace ℝ (Fin n))
    (hchart : Work.ManifoldParity.IsGraphChart K i V η) (hyV : y ∈ V) :
    ∃ c : ℝ, c ≠ 0 ∧ curveVel γ y
      = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (y i)) (1:ℝ)) := by
  have hys : γ (Classical.choose hy) = y := Classical.choose_spec hy
  have hγV : γ (Classical.choose hy) ∈ V := by rw [hys]; exact hyV
  obtain ⟨c, hc, hce⟩ := Work.ManifoldParity.curve_tangent_chart K i V η hchart γ hsm hγK
    (Classical.choose hy) hγV (hvel _)
  rw [curveVel_eq_of_mem hy, hce,
    show (γ (Classical.choose hy)) i = y i from congrArg (fun v => v i) hys]
  exact ⟨c, hc, rfl⟩

/-- **Continuity of the transported velocity.**  This is where the local graph structure of `K` is
used: by `Work.ManifoldParity.exists_open_nhds_param_of_range`, points of `K` near `γ t₀` are
`γ s` for `s` arbitrarily close to `t₀`, so the transported velocity is continuous on the range. -/
theorem curveVel_continuousOn (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : Work.ManifoldParity.HasLocalGraphCharts K)
    (γ : ℝ → EuclideanSpace ℝ (Fin n))
    (hsm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) γ)
    (hvel : ∀ t, fderiv ℝ γ t 1 ≠ 0) (hinj : Function.Injective γ)
    (hγK : ∀ t, γ t ∈ K) :
    ContinuousOn (curveVel γ) (Set.range γ) := by
  intro x₀ hx₀
  obtain ⟨t₀, ht₀⟩ := hx₀
  have hFcont : Continuous fun t : ℝ => fderiv ℝ γ t 1 :=
    ((hsm.continuous_fderiv (by simp)).clm_apply continuous_const)
  rw [Metric.continuousWithinAt_iff']
  intro η hη
  obtain ⟨ε, hεpos, hεsub⟩ :=
    Metric.mem_nhds_iff.mp ((Metric.continuousAt_iff'.mp hFcont.continuousAt) η hη)
  obtain ⟨O, hOo, hx₀O, hOsub⟩ :=
    Work.ManifoldParity.exists_open_nhds_param_of_range K hgra hsm hvel hγK t₀ ε hεpos
  have hx₀O' : x₀ ∈ O := by rw [← ht₀]; exact hx₀O
  refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (hOo.mem_nhds hx₀O'))) ?_
  rintro x ⟨hxrange, hxO⟩
  have hxK : x ∈ K := by obtain ⟨u, hu⟩ := hxrange; rw [← hu]; exact hγK u
  obtain ⟨s, hsε, hsr⟩ := hOsub x ⟨hxK, hxO⟩
  have h1 : curveVel γ x = fderiv ℝ γ s 1 := by rw [← hsr]; exact curveVel_eq_of γ hinj s
  have h2 : curveVel γ x₀ = fderiv ℝ γ t₀ 1 := by rw [← ht₀]; exact curveVel_eq_of γ hinj t₀
  change dist (curveVel γ x) (curveVel γ x₀) < η
  rw [h1, h2]
  exact hεsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hsε)

/-- A non-compact connected component of a locally-graph set admits a continuous non-vanishing
tangent field, parallel to all the graph charts of `K` at its points.

Route: `Work.Euclidean.TangentField.exists_homeomorph_component_of_not_isCompact` (a sibling
delegation in the same directory, a repackaging of the already-proved
`exists_param_component_of_not_isCompact`: import whichever is available, otherwise prove the
statement inline) gives a homeomorphism `e : ℝ ≃ₜ ↥(connectedComponent x)` which is smooth with
nowhere vanishing manifold derivative.  Composing `e` with the inclusions into the ambient space
gives a curve `γ : ℝ → ℝⁿ` which is smooth, injective, with range the component and `γ' ≠ 0`
(chain rule: the manifold derivative of each inclusion is injective, by
`Work.ManifoldParity.mfderiv_subtype_val_injective` and
`Work.ManifoldParity.mfderiv_subtype_val_opens_graph_injective`).  Since `γ` is a homeomorphism onto
its range (composition of homeomorphisms), the transport `U y := γ' (γ⁻¹ y)` of the velocity back to
the component is continuous and non-vanishing, and it is tangent to every graph chart of `K` at the
points of the component (a smooth curve lying in a locally-graph set is tangent to its charts: use
`Work.ManifoldParity.curve_tangent_chart` with the curve `γ` and the parameter `γ⁻¹ y`).  Define `U`
to be zero outside the component. -/
theorem exists_tangent_field_of_component_not_isCompact {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : Work.ManifoldParity.HasLocalGraphCharts K) (x : ↥K)
    (hne : ¬ IsCompact (connectedComponent x)) :
    ∃ U : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContinuousOn U (Subtype.val '' (connectedComponent x)) ∧
      (∀ y ∈ Subtype.val '' (connectedComponent x), U y ≠ 0) ∧
      (∀ y ∈ Subtype.val '' (connectedComponent x),
        ∀ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin n)))
          (η : ℝ → EuclideanSpace ℝ (Fin n)),
        Work.ManifoldParity.IsGraphChart K i V η → y ∈ V →
        ∃ c : ℝ, c ≠ 0 ∧
          U y = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (y i)) (1:ℝ))) := by
  classical
  -- the smooth `1`-manifold structure of `↥K` given by the local graph charts
  letI : ChartedSpace Work.ManifoldParity.ME1 ↥K := Work.ManifoldParity.graphChartedSpace K hgra
  -- a parametrisation of the non-compact component by `ℝ`
  obtain ⟨γ, hγsm, hγinj, hγrange, hγvel⟩ :=
    Work.Euclidean.TangentField.exists_param_component_of_not_isCompact K hgra x hne
  -- the ambient curve
  set Gc : ℝ → EuclideanSpace ℝ (Fin n) := fun t => ((γ t : ↥K) : EuclideanSpace ℝ (Fin n))
    with hGcdef
  have hGcsm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) Gc := by
    have h1 : ContMDiff (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (((⊤ : ℕ∞) : WithTop ℕ∞)) Gc := by
      have h2 : ContMDiff (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (((⊤ : ℕ∞) : WithTop ℕ∞))
          ((Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) ∘ γ) :=
        (Work.ManifoldParity.contMDiff_subtype_val_graph K hgra).comp hγsm
      exact h2
    exact (contMDiff_iff_contDiff).mp h1
  have hGcinj : Function.Injective Gc := fun a b hab => hγinj (Subtype.ext hab)
  have hGcrange : Set.range Gc = Subtype.val '' connectedComponent x := by
    rw [show Set.range Gc
        = Subtype.val '' Set.range γ from Set.range_comp Subtype.val γ, hγrange]
  have hGcvel : ∀ t : ℝ, fderiv ℝ Gc t 1 ≠ 0 := by
    intro t hv
    have hchain : mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) Gc t
        = (mfderiv (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) (γ t)) ∘SL
          (mfderiv (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ Work.ManifoldParity.ME1) γ t) :=
      mfderiv_comp t
        ((Work.ManifoldParity.contMDiff_subtype_val_graph K hgra).contMDiffAt.mdifferentiableAt
          (by simp))
        (hγsm.contMDiffAt.mdifferentiableAt (by simp))
    have hch2 : fderiv ℝ Gc t
        = (mfderiv (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) (γ t)) ∘SL
          (mfderiv (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ Work.ManifoldParity.ME1) γ t) := by
      rw [← mfderiv_eq_fderiv, hchain]
    have h0 : (mfderiv (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) (γ t))
        ((mfderiv (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ Work.ManifoldParity.ME1) γ t) 1) = 0 := by
      have hthis : ((mfderiv (modelWithCornersSelf ℝ Work.ManifoldParity.ME1)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (Subtype.val : ↥K → EuclideanSpace ℝ (Fin n)) (γ t)) ∘SL
          (mfderiv (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ Work.ManifoldParity.ME1) γ t)) 1 = 0 := by
        rw [← hch2]; exact hv
      exact hthis
    exact hγvel t (Work.ManifoldParity.mfderiv_subtype_val_injective K hgra (γ t)
      (h0.trans (map_zero _).symm))
  have hGcK : ∀ t : ℝ, Gc t ∈ K := fun t => (γ t).2
  refine ⟨curveVel Gc, ?_, ?_, ?_⟩
  · rw [← hGcrange]
    exact curveVel_continuousOn K hgra Gc hGcsm hGcvel hGcinj hGcK
  · intro y hy
    rw [← hGcrange] at hy
    exact curveVel_ne_zero hGcvel hy
  · intro y hy i V η hchart hyV
    rw [← hGcrange] at hy
    exact curveVel_tangent K Gc hGcsm hGcvel hGcK hy i V η hchart hyV

end

end Work.Euclidean.TangentField
