import Mathlib
import Submission.Work.Drive.SeparationBase

namespace Work.Drive

open Set Topology

/-- **A path-connected set meeting a path component is contained in it.**

If `S ⊆ F` is path-connected and meets the path component of `x` in `F`, then `S` is contained
in that path component.  (This is the maximality of `pathComponentIn`, phrased in the form used
to identify the side of a local separation.) -/
lemma pathConnected_subset_pathComponentIn_of_inter_nonempty {X : Type*} [TopologicalSpace X]
    {F S : Set X} {x : X} (hS : IsPathConnected S) (hSF : S ⊆ F)
    (hne : (S ∩ pathComponentIn F x).Nonempty) : S ⊆ pathComponentIn F x := by
  obtain ⟨z, hzS, hzC⟩ := hne
  have hsub : S ⊆ pathComponentIn F z := hS.subset_pathComponentIn hzS hSF
  rwa [pathComponentIn_congr hzC] at hsub

/-- **Every path component that meets `K` accumulates at all of `K`.**

Let `K` be closed and preconnected, locally separated into two sides at every one of its points
(the hypothesis `hsep`), and let `C = pathComponentIn Kᶜ x` be a path component of the complement.
If `closure C` meets `K`, then `closure C` contains `K`.

The proof does not need any Jordan-type input: the set `T = K ∩ closure C`, viewed inside the
preconnected space `K`, is clopen — it is closed as the trace of `closure C`, and it is open
because at a point of `K` the local separation exhibits a neighbourhood whose intersection with
`K` lies on one side of the two-sided decomposition, hence in `closure C`.  A nonempty clopen
subset of a preconnected space is everything. -/
lemma subset_closure_pathComponentIn {K : Set (ℝ × ℝ)}
    (hsep : ∀ p ∈ K, ∃ U U₁ U₂ : Set (ℝ × ℝ), LocalSep K U U₁ U₂ ∧ p ∈ U)
    (hpre : IsPreconnected K) {x : ℝ × ℝ} (hx : x ∈ Kᶜ)
    (hne : (K ∩ closure (pathComponentIn Kᶜ x)).Nonempty) :
    K ⊆ closure (pathComponentIn Kᶜ x) := by
  set C : Set (ℝ × ℝ) := pathComponentIn Kᶜ x with hCdef
  have hCK : C ⊆ Kᶜ := by rw [hCdef]; exact pathComponentIn_subset
  set T : Set ↥K := {q | (q : ℝ × ℝ) ∈ closure C} with hTdef
  haveI : PreconnectedSpace ↥K := Subtype.preconnectedSpace hpre
  have hTclosed : IsClosed T := by
    rw [hTdef]
    exact isClosed_closure.preimage continuous_subtype_val
  have hTopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    rw [mem_nhds_subtype]
    obtain ⟨V, V₁, V₂, hV, hqV⟩ := hsep (q : ℝ × ℝ) q.property
    -- `q ∈ closure C` and `V` is a neighbourhood of `q`, so `C` meets `V`
    have hCV : (V ∩ C).Nonempty := mem_closure_iff.mp hq V hV.isOpen_U hqV
    obtain ⟨z, hzV, hzC⟩ := hCV
    refine ⟨V, hV.isOpen_U.mem_nhds hqV, ?_⟩
    intro q' hq'V
    have hV₁K : V₁ ⊆ Kᶜ := by
      intro y hy
      have h : y ∈ V₁ ∪ V₂ := Or.inl hy
      rw [hV.union] at h
      exact h.2
    have hV₂K : V₂ ⊆ Kᶜ := by
      intro y hy
      have h : y ∈ V₁ ∪ V₂ := Or.inr hy
      rw [hV.union] at h
      exact h.2
    -- `z ∈ V \ K = V₁ ∪ V₂`
    have hzVK : z ∈ V₁ ∪ V₂ := by
      have h1 : z ∈ V \ K := ⟨hzV, hCK hzC⟩
      rw [← hV.union] at h1
      exact h1
    rcases hzVK with hzV₁ | hzV₂
    · have hV₁C : V₁ ⊆ C :=
        pathConnected_subset_pathComponentIn_of_inter_nonempty hV.pc₁ hV₁K ⟨z, hzV₁, hzC⟩
      exact closure_mono hV₁C (hV.acc₁ (q' : ℝ × ℝ) ⟨hq'V, q'.property⟩)
    · have hV₂C : V₂ ⊆ C :=
        pathConnected_subset_pathComponentIn_of_inter_nonempty hV.pc₂ hV₂K ⟨z, hzV₂, hzC⟩
      exact closure_mono hV₂C (hV.acc₂ (q' : ℝ × ℝ) ⟨hq'V, q'.property⟩)
  have hTne : T.Nonempty := by
    obtain ⟨w, hwK, hwC⟩ := hne
    exact ⟨⟨w, hwK⟩, hwC⟩
  have hTclopen : IsClopen T := ⟨hTclosed, hTopen⟩
  have hTuniv : T = univ := IsClopen.eq_univ hTclopen hTne
  intro y hy
  have : (⟨y, hy⟩ : ↥K) ∈ T := by rw [hTuniv]; exact mem_univ _
  rw [hTdef] at this
  exact this

theorem accumulating_components_eq {K : Set (ℝ × ℝ)} (hKclosed : IsClosed K)
    (hsep : ∀ p ∈ K, ∃ U U₁ U₂ : Set (ℝ × ℝ), LocalSep K U U₁ U₂ ∧ p ∈ U)
    (hpre : IsPreconnected K) {p : ℝ × ℝ} (hp : p ∈ K) {U U₁ U₂ : Set (ℝ × ℝ)}
    (hU : LocalSep K U U₁ U₂) (hpU : p ∈ U) {y₁ y₂ : ℝ × ℝ} (hy₁ : y₁ ∈ U₁) (hy₂ : y₂ ∈ U₂) :
    ∀ q ∈ K, ∀ C : Set (ℝ × ℝ), (∃ x : ℝ × ℝ, x ∈ Kᶜ ∧ C = pathComponentIn Kᶜ x) →
      (q ∈ closure C ↔ C = pathComponentIn Kᶜ y₁ ∨ C = pathComponentIn Kᶜ y₂) := by
  have hU₁K : U₁ ⊆ Kᶜ := by
    intro y hy
    have h : y ∈ U₁ ∪ U₂ := Or.inl hy
    rw [hU.union] at h
    exact h.2
  have hU₂K : U₂ ⊆ Kᶜ := by
    intro y hy
    have h : y ∈ U₁ ∪ U₂ := Or.inr hy
    rw [hU.union] at h
    exact h.2
  -- the two sides contain `y₁` resp. `y₂` and are subsets of the corresponding path components
  have hU₁pc : U₁ ⊆ pathComponentIn Kᶜ y₁ := hU.pc₁.subset_pathComponentIn hy₁ hU₁K
  have hU₂pc : U₂ ⊆ pathComponentIn Kᶜ y₂ := hU.pc₂.subset_pathComponentIn hy₂ hU₂K
  intro q hq C hC
  obtain ⟨x, hx, rfl⟩ := hC
  constructor
  · -- if the component accumulates at `q ∈ K`, it accumulates at all of `K`, in particular at `p`,
    -- and the local separation at `p` identifies it with one of the two sides
    intro hqC
    have hne : (K ∩ closure (pathComponentIn Kᶜ x)).Nonempty := ⟨q, hq, hqC⟩
    have hsub := subset_closure_pathComponentIn hsep hpre hx hne
    have hpC : p ∈ closure (pathComponentIn Kᶜ x) := hsub hp
    have hCU : (U ∩ pathComponentIn Kᶜ x).Nonempty :=
      mem_closure_iff.mp hpC U hU.isOpen_U hpU
    obtain ⟨z, hzU, hzC⟩ := hCU
    have hzK : z ∉ K := pathComponentIn_subset hzC
    have hzUK : z ∈ U \ K := ⟨hzU, hzK⟩
    rw [← hU.union] at hzUK
    rcases hzUK with hzU₁ | hzU₂
    · left
      have hU₁C : U₁ ⊆ pathComponentIn Kᶜ x :=
        pathConnected_subset_pathComponentIn_of_inter_nonempty hU.pc₁ hU₁K ⟨z, hzU₁, hzC⟩
      have hy₁C : y₁ ∈ pathComponentIn Kᶜ x := hU₁C hy₁
      have hcongr : pathComponentIn Kᶜ y₁ = pathComponentIn Kᶜ x := pathComponentIn_congr hy₁C
      exact hcongr.symm
    · right
      have hU₂C : U₂ ⊆ pathComponentIn Kᶜ x :=
        pathConnected_subset_pathComponentIn_of_inter_nonempty hU.pc₂ hU₂K ⟨z, hzU₂, hzC⟩
      have hy₂C : y₂ ∈ pathComponentIn Kᶜ x := hU₂C hy₂
      have hcongr : pathComponentIn Kᶜ y₂ = pathComponentIn Kᶜ x := pathComponentIn_congr hy₂C
      exact hcongr.symm
  · -- conversely both sides accumulate at every point of `K`
    intro h
    rcases h with h | h
    · rw [h]
      exact (subset_closure_pathComponentIn hsep hpre (hU₁K hy₁)
        ⟨p, hp, closure_mono hU₁pc (hU.acc₁ p ⟨hpU, hp⟩)⟩) hq
    · rw [h]
      exact (subset_closure_pathComponentIn hsep hpre (hU₂K hy₂)
        ⟨p, hp, closure_mono hU₂pc (hU.acc₂ p ⟨hpU, hp⟩)⟩) hq

end Work.Drive
