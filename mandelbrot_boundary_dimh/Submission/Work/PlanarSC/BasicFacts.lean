import Mathlib
import Submission.Work.PlanarSC.PolyDefs

/-!
# The two complementary components of a Jordan curve

Let `γ : C(Circle, ℂ)` be injective — so that its image is a Jordan curve — and let `U`, `V` be open,
connected, disjoint subsets of the complement of `range γ` covering it, with `U` bounded and `V`
unbounded.  Then `U` is the *inside* and `V` the *outside* of the curve:

* `U` and `V` are exactly the two connected components of `(range γ)ᶜ`;
* `range γ` is the frontier of both;
* `Uᶜ = closure V` is connected;
* `U` has no bounded complementary component;
* the Jordan criterion holds for `U`.
-/

open Set

namespace Work.PlanarSC

variable {γ : C(Circle, ℂ)} {U V : Set ℂ}

/-- `(range γ)ᶜ` is not preconnected: it is the union of the two nonempty disjoint open sets
`U`, `V`. -/
theorem range_compl_not_isPreconnected (hUo : IsOpen U) (hVo : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = (Set.range γ)ᶜ) :
    ¬ IsPreconnected (Set.range γ)ᶜ := by
  intro hpre
  obtain ⟨u, hu⟩ := hUc.1
  obtain ⟨v, hv⟩ := hVc.1
  have hu' : u ∈ (Set.range γ)ᶜ := by rw [← hcover]; exact Or.inl hu
  have hv' : v ∈ (Set.range γ)ᶜ := by rw [← hcover]; exact Or.inr hv
  rcases IsPreconnected.subset_or_subset hUo hVo hdisj (by rw [hcover]) hpre with h | h
  · exact (Set.disjoint_left.mp hdisj) (h hv') hv
  · exact (Set.disjoint_left.mp hdisj) hu (h hu')

/-- `U` is the connected component of any of its points inside `(range γ)ᶜ`. -/
theorem U_eq_connectedComponentIn (hUo : IsOpen U) (hVo : IsOpen V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = (Set.range γ)ᶜ) (hUc : IsConnected U) {u : ℂ} (hu : u ∈ U) :
    U = connectedComponentIn ((Set.range γ)ᶜ) u := by
  have hUsub : U ⊆ (Set.range γ)ᶜ := fun x hx => by rw [← hcover]; exact Or.inl hx
  refine Set.Subset.antisymm ?_ ?_
  · exact hUc.2.subset_connectedComponentIn hu hUsub
  · rintro z hz
    have hsub : connectedComponentIn ((Set.range γ)ᶜ) u ⊆ U ∪ V := fun w hw => by
      rw [hcover]
      exact connectedComponentIn_subset _ _ hw
    rcases IsPreconnected.subset_or_subset hUo hVo hdisj hsub
      isPreconnected_connectedComponentIn with h | h
    · exact h hz
    · exact absurd (h (mem_connectedComponentIn (hUsub hu))) (Set.disjoint_left.mp hdisj hu)

/-- `V` is the connected component of any of its points inside `(range γ)ᶜ`. -/
theorem V_eq_connectedComponentIn (hUo : IsOpen U) (hVo : IsOpen V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = (Set.range γ)ᶜ) (hVc : IsConnected V) {v : ℂ} (hv : v ∈ V) :
    V = connectedComponentIn ((Set.range γ)ᶜ) v := by
  have hVsub : V ⊆ (Set.range γ)ᶜ := fun x hx => by rw [← hcover]; exact Or.inr hx
  refine Set.Subset.antisymm ?_ ?_
  · exact hVc.2.subset_connectedComponentIn hv hVsub
  · rintro z hz
    have hsub : connectedComponentIn ((Set.range γ)ᶜ) v ⊆ U ∪ V := fun w hw => by
      rw [hcover]
      exact connectedComponentIn_subset _ _ hw
    rcases IsPreconnected.subset_or_subset hUo hVo hdisj hsub
      isPreconnected_connectedComponentIn with h | h
    · exact absurd (h (mem_connectedComponentIn (hVsub hv))) (Set.disjoint_right.mp hdisj hv)
    · exact h hz

/-- The curve is the frontier of the bounded component. -/
theorem frontier_U_eq (hγ : Function.Injective γ) (hUo : IsOpen U) (hVo : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = (Set.range γ)ᶜ) :
    frontier U = Set.range γ := by
  obtain ⟨u, hu⟩ := hUc.1
  have hnc : ¬ IsPreconnected (Set.range γ)ᶜ :=
    range_compl_not_isPreconnected hUo hVo hUc hVc hdisj hcover
  rw [U_eq_connectedComponentIn hUo hVo hdisj hcover hUc hu]
  exact Commons.Topology.Connected.frontier_component_compl_range γ hγ hnc u
    (by rw [← hcover]; exact Or.inl hu)

/-- The curve is the frontier of the unbounded component. -/
theorem frontier_V_eq (hγ : Function.Injective γ) (hUo : IsOpen U) (hVo : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = (Set.range γ)ᶜ) :
    frontier V = Set.range γ := by
  obtain ⟨v, hv⟩ := hVc.1
  have hnc : ¬ IsPreconnected (Set.range γ)ᶜ :=
    range_compl_not_isPreconnected hUo hVo hUc hVc hdisj hcover
  rw [V_eq_connectedComponentIn hUo hVo hdisj hcover hVc hv]
  exact Commons.Topology.Connected.frontier_component_compl_range γ hγ hnc v
    (by rw [← hcover]; exact Or.inr hv)

/-- Every point of the curve is a limit point of the unbounded component. -/
theorem range_subset_closure_V (hγ : Function.Injective γ) (hUo : IsOpen U) (hVo : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = (Set.range γ)ᶜ) :
    Set.range γ ⊆ closure V := by
  rw [← frontier_V_eq hγ hUo hVo hUc hVc hdisj hcover]
  exact frontier_subset_closure

/-- The complement of the inside region is the closure of the outside region. -/
theorem compl_U_eq_closure_V (hγ : Function.Injective γ) (hUo : IsOpen U) (hVo : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = (Set.range γ)ᶜ) :
    Uᶜ = closure V := by
  have hfr : frontier V = Set.range γ := frontier_V_eq hγ hUo hVo hUc hVc hdisj hcover
  have hcl : closure V = V ∪ Set.range γ := by
    rw [closure_eq_self_union_frontier, hfr]
  rw [hcl]
  ext z
  constructor
  · intro hz
    by_cases hzr : z ∈ Set.range γ
    · exact Or.inr hzr
    · have hzs : z ∈ (Set.range γ)ᶜ := hzr
      rw [← hcover] at hzs
      rcases hzs with h | h
      · exact absurd h hz
      · exact Or.inl h
  · rintro (h | h)
    · exact fun hc => (Set.disjoint_left.mp hdisj) hc h
    · intro hc
      have : z ∈ (Set.range γ)ᶜ := (hcover ▸ (Or.inl hc))
      exact this h

/-- The inside of a Jordan curve has no bounded complementary component. -/
theorem no_bounded_component_compl_U (hγ : Function.Injective γ) (hUo : IsOpen U)
    (hVo : IsOpen V) (hUc : IsConnected U) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hVb : ¬ Bornology.IsBounded V) (hcover : U ∪ V = (Set.range γ)ᶜ) :
    ∀ z : ℂ, z ∉ U → ¬ Bornology.IsBounded (connectedComponentIn Uᶜ z) := by
  intro z hz
  have hcl : Uᶜ = closure V := compl_U_eq_closure_V hγ hUo hVo hUc hVc hdisj hcover
  have hzcl : z ∈ closure V := by rw [← hcl]; exact hz
  have hsub : closure V ⊆ connectedComponentIn Uᶜ z :=
    IsPreconnected.subset_connectedComponentIn hVc.2.closure hzcl
      (fun x hx => by rw [hcl]; exact hx)
  intro hbdd
  exact hVb ((hbdd.subset hsub).subset subset_closure)

end Work.PlanarSC
