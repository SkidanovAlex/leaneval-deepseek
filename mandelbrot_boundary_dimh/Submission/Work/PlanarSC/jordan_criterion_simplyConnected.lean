import Submission.Work.PlanarSC.JCVocab
import Submission.Work.PlanarSC.exists_compact_gap_of_component
import Submission.Work.PlanarSC.JCGap.exists_jordan_curve_of_gap
import Submission.Work.PlanarSC.exists_polyomino_hull
import Submission.Work.PlanarSC.polyomino_simplyConnected
import Submission.Work.Horn.Basin.simplyConnectedSpace_of_hulls

/-!
# The Jordan criterion for simple connectivity of a plane domain

Target (the statement of this module):

> if `V ⊆ ℂ` is open and connected and every Jordan curve `γ` in `V` has **all** its bounded
> complementary components inside `V`, then `V` is simply connected.

The vocabulary (`jordanRegion`, the dyadic grid loops) is in `Submission.Work.PlanarSC.JCVocab`,
which this module imports, so that the modules that import this one for the vocabulary keep
working.

## Route used here

The hypothesis `hJ` of the criterion is the strong "`V` contains the closed region of every Jordan
curve it contains" form.  The proof has two halves.

* **`hJ` kills the holes (`no_bounded_component_of_jordanCriterion`).**  Let `K` be a bounded
  connected component of `Vᶜ` and `z ∈ K`.  `Work.PlanarSC.exists_compact_gap_of_component` produces
  a compact `S` with `z ∈ S ⊆ Vᶜ` at positive distance `δ` from `Vᶜ ∖ S`; the distance bound extends
  to `S' := closure (Vᶜ ∖ S)`, so `Work.PlanarSC.JCGap.exists_jordan_curve_of_gap` yields an
  injective `γ` with `range γ ⊆ (S ∪ S')ᶜ`, `z ∉ range γ` and `z` in a bounded complementary
  component of `γ`.  Since `(S ∪ S')ᶜ ⊆ V` (any point of `Vᶜ` outside `S` lies in `S'`), the
  hypothesis `hJ` forces `z ∈ V`, a contradiction.

* **"No holes" gives simple connectivity (`simplyConnectedSpace_of_jordanCriterion`).**  By the hull
  criterion `Work.Horn.Basin.simplyConnectedSpace_of_hulls` it suffices that every compact `K ⊆ V`
  lies in a simply connected `W ⊆ V`: `Work.PlanarSC.exists_polyomino_hull` produces a hole-free
  dyadic polyomino `P` with `K ⊆ P ⊆ V`, and `Work.PlanarSC.polyomino_simplyConnected` says that `P`
  is simply connected.

The vocabulary module `JCVocab` is imported (and hence re-exported) so that the modules which
import this one for the grid vocabulary keep working; the proof below does not use it.
-/

open Set

namespace Work.PlanarSC

noncomputable section

/-- A connected component of a closed subset of `ℂ` is closed. -/
theorem connectedComponentIn_isClosed_of_isClosed {S : Set ℂ} (hS : IsClosed S) (a : ℂ) :
    IsClosed (connectedComponentIn S a) := by
  by_cases ha : a ∈ S
  · have h1 : IsPreconnected (closure (connectedComponentIn S a)) :=
      isPreconnected_connectedComponentIn.closure
    have h2 : a ∈ closure (connectedComponentIn S a) :=
      subset_closure (mem_connectedComponentIn ha)
    have h3 : closure (connectedComponentIn S a) ⊆ S :=
      calc closure (connectedComponentIn S a) ⊆ closure S :=
            closure_mono (connectedComponentIn_subset S a)
        _ = S := hS.closure_eq
    exact isClosed_of_closure_subset (h1.subset_connectedComponentIn h2 h3)
  · rw [connectedComponentIn_eq_empty ha]
    exact isClosed_empty

/-- **`hJ` forbids bounded complementary components of `Vᶜ`.**  If `V` contains the closed region of
every Jordan curve it contains, then every component of `Vᶜ` is unbounded. -/
theorem no_bounded_component_of_jordanCriterion {V : Set ℂ} (hVo : IsOpen V) (hVc : IsConnected V)
    (hJ : JordanCriterion V) :
    ∀ z : ℂ, z ∉ V → ¬ Bornology.IsBounded (connectedComponentIn (Vᶜ) z) := by
  intro z hzV hbdd
  have hzVc : z ∈ Vᶜ := hzV
  have hzK : z ∈ connectedComponentIn (Vᶜ) z := mem_connectedComponentIn hzVc
  have hKclosed : IsClosed (connectedComponentIn (Vᶜ) z) :=
    connectedComponentIn_isClosed_of_isClosed hVo.isClosed_compl z
  have hKcpt : IsCompact (connectedComponentIn (Vᶜ) z) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKclosed, hbdd⟩
  have hKconn : IsConnected (connectedComponentIn (Vᶜ) z) :=
    ⟨⟨z, hzK⟩, isPreconnected_connectedComponentIn⟩
  have hKmax : ∀ S : Set ℂ, IsPreconnected S → connectedComponentIn (Vᶜ) z ⊆ S → S ⊆ Vᶜ →
      S = connectedComponentIn (Vᶜ) z := by
    intro S hSpre hKS hSsub
    exact (hSpre.subset_connectedComponentIn (hKS hzK) hSsub).antisymm hKS
  obtain ⟨S, hScpt, hzS, hSVc, δ, hδpos, hgap⟩ :=
    exists_compact_gap_of_component hVo hVc hKcpt hKconn (connectedComponentIn_subset (Vᶜ) z)
      hKmax hzK
  -- The gap extends to the closure of `Vᶜ ∖ S`.
  set S' : Set ℂ := closure (Vᶜ \ S) with hS'def
  have hS'closed : IsClosed S' := isClosed_closure
  have hgap' : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ S', δ ≤ dist s s' := by
    refine ⟨δ, hδpos, fun s hs s' hs' => ?_⟩
    have hsub : (Vᶜ \ S) ⊆ {x : ℂ | δ ≤ dist s x} := fun x hx => hgap s hs x hx.1 hx.2
    have hcl : IsClosed {x : ℂ | δ ≤ dist s x} :=
      isClosed_le continuous_const (by fun_prop)
    exact hcl.closure_subset_iff.mpr hsub hs'
  obtain ⟨γ, hγinj, hγrange, hzγ, hzγbdd⟩ :=
    JCGap.exists_jordan_curve_of_gap hScpt ⟨z, hzS⟩ hS'closed hgap' hzS
  -- Every point of the curve lies in `V`.
  have hrangeV : Set.range γ ⊆ V := by
    rintro w ⟨t, rfl⟩
    by_contra hwV
    have hwVc : γ t ∈ Vᶜ := hwV
    have hw' : γ t ∉ S ∪ S' := hγrange ⟨t, rfl⟩
    exact hw' (Or.inr (subset_closure ⟨hwVc, fun hS => hw' (Or.inl hS)⟩))
  exact hzV (hJ γ hγinj hrangeV z hzγ hzγbdd)

/-- **A plane domain without holes is simply connected.**  If no connected component of `Vᶜ` is
bounded, then every compact `K ⊆ V` lies in a simply connected polyomino inside `V`, and the hull
criterion gives `SimplyConnectedSpace V`. -/
theorem simplyConnectedSpace_of_jordanCriterion {V : Set ℂ} (hVo : IsOpen V) (hVc : IsConnected V)
    (hJ : JordanCriterion V) : SimplyConnectedSpace V := by
  refine Work.Horn.Basin.simplyConnectedSpace_of_hulls (fun K hKcpt hKV => ?_)
  obtain ⟨n, S, hKS, hSV, hne, hpre, hprec⟩ :=
    exists_polyomino_hull hVo hVc (no_bounded_component_of_jordanCriterion hVo hVc hJ) hKcpt hKV
  exact ⟨dyadicPolyomino n S, polyomino_simplyConnected S hne hpre hprec, hKS, hSV⟩

theorem jordan_criterion_simplyConnected {V : Set ℂ} (hVo : IsOpen V) (hVc : IsConnected V)
    (hJ : ∀ (γ : C(Circle, ℂ)), Function.Injective γ → Set.range γ ⊆ V →
      ∀ z : ℂ, z ∉ Set.range γ → Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z) →
        z ∈ V) :
    SimplyConnectedSpace V :=
  simplyConnectedSpace_of_jordanCriterion hVo hVc hJ

end

end Work.PlanarSC
