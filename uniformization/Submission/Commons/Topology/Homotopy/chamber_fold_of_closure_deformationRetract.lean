import Mathlib.Topology.UnitInterval

open Set Topology

namespace Commons.Topology.Homotopy

/-- **A chamber fold from a deformation retraction of the closure of the chamber.**

Let `c, S ⊆ U` with `c` open and every boundary point of `c` that lies in `U` lying in `S`.  If the closure of `c` strongly deformation retracts onto `S` (a homotopy of `closure c`, fixing `S ∩ closure c`, starting at the identity and ending in `S`), then there is a fold `Φ : U × I → U` which is the identity outside `c`, fixes `S` pointwise, stays in `c ∪ S` and ends in `S`.

This turns the "one-sided collar" geometry of a chamber into the fold data required by `Commons.Topology.Homotopy.deformationRetract_of_chamber_folds`.  Continuity proof: on `closure c` the fold agrees with `H`, and on the complement of `interior (closure c)` it is the identity (since `c ⊆ interior (closure c)`); these two *closed* sets cover `U`, so `ContinuousOn.union_of_isClosed` applies. -/
theorem chamber_fold_of_closure_deformationRetract {U : Type*} [TopologicalSpace U]
    (c S : Set U) (hc : IsOpen c)
    (hbd : ∀ ⦃x : U⦄, x ∈ closure c → x ∉ c → x ∈ S)
    (H : ↥(closure c) × unitInterval → ↥(closure c)) (hHc : Continuous H)
    (hH0 : ∀ x : ↥(closure c), H (x, 0) = x)
    (hH1 : ∀ x : ↥(closure c), (H (x, 1) : U) ∈ S)
    (hHfix : ∀ x : ↥(closure c), (x : U) ∈ S → ∀ t : unitInterval, H (x, t) = x) :
    ∃ Φ : U × unitInterval → U, Continuous Φ ∧ (∀ x : U, Φ (x, 0) = x) ∧
      (∀ x : U, x ∈ S → ∀ t : unitInterval, Φ (x, t) = x) ∧
      (∀ x : U, x ∉ c → ∀ t : unitInterval, Φ (x, t) = x) ∧
      (∀ x : U, x ∈ c → ∀ t : unitInterval, Φ (x, t) ∈ c ∪ S) ∧
      (∀ x : U, x ∈ c → Φ (x, 1) ∈ S) := by
  classical
  -- Every boundary point of `closure c` is a boundary point of `c`, hence in `S`.
  have hfront : ∀ ⦃x : U⦄, x ∈ closure c → x ∉ interior (closure c) → x ∈ S := by
    intro x hxc hxi
    have hfx : x ∈ frontier (closure c) := by
      rw [frontier, mem_sdiff]
      exact ⟨by rwa [closure_closure], hxi⟩
    have hfc : x ∈ frontier c := (frontier_closure_subset (s := c)) hfx
    rw [frontier, mem_sdiff] at hfc
    obtain ⟨hcl, hint⟩ := hfc
    exact hbd hcl (by rwa [hc.interior_eq] at hint)
  -- The candidate fold.
  let f : U × unitInterval → U := fun p =>
    if hp : p.1 ∈ closure c then (H (⟨p.1, hp⟩, p.2) : U) else p.1
  have hf_eq : ∀ (p : U × unitInterval) (hp : p.1 ∈ closure c),
      f p = (H (⟨p.1, hp⟩, p.2) : U) := by
    intro p hp
    simp only [f]
    exact dif_pos hp
  have hf_eq' : ∀ (p : U × unitInterval), p.1 ∉ closure c → f p = p.1 := by
    intro p hp
    simp only [f]
    exact dif_neg hp
  -- Two closed sets covering `U × I`.
  let A : Set (U × unitInterval) := {p | p.1 ∈ closure c}
  let B : Set (U × unitInterval) := {p | p.1 ∉ interior (closure c)}
  have hAclosed : IsClosed A := by
    have h : A = Prod.fst ⁻¹' closure c := rfl
    rw [h]
    exact isClosed_closure.preimage continuous_fst
  have hBclosed : IsClosed B := by
    have h : B = Prod.fst ⁻¹' (interior (closure c))ᶜ := rfl
    rw [h]
    exact isOpen_interior.isClosed_compl.preimage continuous_fst
  have hcover : A ∪ B = univ := by
    ext p
    simp only [A, B, mem_union, mem_ofPred_eq, mem_univ, iff_true]
    by_cases hp : p.1 ∈ closure c
    · exact Or.inl hp
    · exact Or.inr fun hmem => hp (interior_subset hmem)
  have hfA : ContinuousOn f A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hg : Continuous (fun a : A => (H (⟨a.1.1, a.2⟩, a.1.2) : U)) := by
      have h1 : Continuous (fun a : A => (⟨a.1.1, a.2⟩ : ↥(closure c))) :=
        (continuous_fst.comp continuous_subtype_val).subtype_mk (fun a => a.2)
      have h2 : Continuous (fun a : A => a.1.2) :=
        continuous_snd.comp continuous_subtype_val
      exact continuous_subtype_val.comp (hHc.comp (h1.prodMk h2))
    have heq : A.domRestrict f = fun a : A => (H (⟨a.1.1, a.2⟩, a.1.2) : U) := by
      funext a
      rw [Set.domRestrict_apply]
      simpa using hf_eq (↑a) a.2
    rw [heq]
    exact hg
  have hfB : ContinuousOn f B := by
    refine ContinuousOn.congr (f := fun p : U × unitInterval => p.1) (g := f)
      continuous_fst.continuousOn ?_
    intro p hp
    have hpb : p.1 ∉ interior (closure c) := by simpa only [B, mem_ofPred_eq] using hp
    by_cases hpc : p.1 ∈ closure c
    · rw [hf_eq p hpc]
      have hS : p.1 ∈ S := hfront hpc hpb
      have := hHfix ⟨p.1, hpc⟩ hS p.2
      simpa using congrArg Subtype.val this
    · rw [hf_eq' p hpc]
  have hf : Continuous f := by
    have hunion : ContinuousOn f (A ∪ B) :=
      hfA.union_of_isClosed hfB hAclosed hBclosed
    rw [hcover] at hunion
    rwa [continuousOn_univ] at hunion
  refine ⟨f, hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ closure c
    · rw [hf_eq (x, 0) hx]
      simpa using congrArg Subtype.val (hH0 ⟨x, hx⟩)
    · rw [hf_eq' (x, 0) hx]
  · intro x hxS t
    by_cases hx : x ∈ closure c
    · rw [hf_eq (x, t) hx]
      simpa using congrArg Subtype.val (hHfix ⟨x, hx⟩ hxS t)
    · rw [hf_eq' (x, t) hx]
  · intro x hxc t
    by_cases hx : x ∈ closure c
    · rw [hf_eq (x, t) hx]
      have hS : x ∈ S := hbd hx hxc
      simpa using congrArg Subtype.val (hHfix ⟨x, hx⟩ hS t)
    · rw [hf_eq' (x, t) hx]
  · intro x hx t
    have hxc : x ∈ closure c := subset_closure hx
    have hval : f (x, t) = (H (⟨x, hxc⟩, t) : U) := by
      have := hf_eq (x, t) hxc
      simpa using this
    rw [hval]
    by_cases hy : (H (⟨x, hxc⟩, t) : U) ∈ c
    · exact Or.inl hy
    · exact Or.inr (hbd (H (⟨x, hxc⟩, t)).2 hy)
  · intro x hx
    have hxc : x ∈ closure c := subset_closure hx
    have hval : f (x, 1) = (H (⟨x, hxc⟩, 1) : U) := by
      have := hf_eq (x, 1) hxc
      simpa using this
    rw [hval]
    exact hH1 ⟨x, hxc⟩

end Commons.Topology.Homotopy