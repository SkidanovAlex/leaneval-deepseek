import Mathlib

namespace Work.CFTLib.Topology

section PiBasis

variable {ι : Type*} {A : ι → Type*} [∀ i, TopologicalSpace (A i)]

/-- In a finite product, every neighbourhood of a point contains a "box" whose sides are
neighbourhoods of the corresponding coordinates. -/
lemma exists_univ_pi_subset_of_mem_nhds [Finite ι] (a : ∀ i, A i) {s : Set (∀ i, A i)}
    (hs : s ∈ nhds a) :
    ∃ t : ∀ i, Set (A i), (∀ i, t i ∈ nhds (a i)) ∧ Set.univ.pi t ⊆ s := by
  classical
  rw [nhds_pi, Filter.mem_pi'] at hs
  obtain ⟨I, t, ht, hsub⟩ := hs
  refine ⟨fun i => if i ∈ I then t i else Set.univ, fun i => ?_, ?_⟩
  · by_cases hi : i ∈ I
    · simp only [hi, ↓reduceIte]; exact ht i
    · simp only [hi, ↓reduceIte]; exact Filter.univ_mem
  · intro u hu
    apply hsub
    intro i hi
    have hui : u i ∈ (if i ∈ I then t i else Set.univ) := Set.mem_univ_pi.mp hu i
    simp only [Finset.mem_coe] at hi
    simpa only [hi, ↓reduceIte] using hui

end PiBasis

section Main

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [T2Space Γ] [TotallyDisconnectedSpace Γ]

/-- Every neighbourhood of the identity in a compact totally disconnected topological group
contains an open normal subgroup. -/
lemma exists_openNormalSubgroup_sub_nhds_one {U : Set Γ} (hU : U ∈ nhds (1 : Γ)) :
    ∃ H : OpenNormalSubgroup Γ, (H : Set Γ) ⊆ U := by
  obtain ⟨V, hVU, hVopen, h1V⟩ := mem_nhds_iff.mp hU
  exact (ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVopen h1V).imp
    fun H hH => hH.trans hVU

/-- For `x : Fin n → Γ` and a neighbourhood `O` of `x`, there is an open normal subgroup `U`
such that the coset block `{y | ∀ i, (x i)⁻¹ * y i ∈ U}` of `x` is contained in `O`. -/
lemma exists_block_subset (n : ℕ) (x : Fin n → Γ) {O : Set (Fin n → Γ)}
    (hO : O ∈ nhds x) :
    ∃ U : OpenNormalSubgroup Γ, ∀ y : Fin n → Γ,
      (∀ i, (x i)⁻¹ * y i ∈ (U : Subgroup Γ)) → y ∈ O := by
  classical
  by_cases hn : n = 0
  · subst hn
    obtain ⟨U, -⟩ := exists_openNormalSubgroup_sub_nhds_one
      (show (Set.univ : Set Γ) ∈ nhds (1 : Γ) from Filter.univ_mem)
    refine ⟨U, fun y _ => ?_⟩
    have hyx : y = x := by funext i; exact i.elim0
    rw [hyx]
    exact mem_of_mem_nhds hO
  · haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    have hTc : Continuous (fun u : Fin n → Γ => fun i => x i * u i) := by
      have hfun : (fun u : Fin n → Γ => fun i => x i * u i) =
          (fun _ : Fin n → Γ => (fun i => x i)) * id := by funext u i; rfl
      rw [hfun]
      exact continuous_const.mul continuous_id
    have hpt : (fun i : Fin n => x i * (fun _ : Fin n => (1 : Γ)) i) = x := by
      funext i; simp
    have ht : Filter.Tendsto (fun u : Fin n → Γ => fun i => x i * u i)
        (nhds (fun _ : Fin n => (1 : Γ))) (nhds x) := by
      have h := hTc.tendsto (fun _ : Fin n => (1 : Γ))
      rwa [hpt] at h
    have hmem : (fun u : Fin n → Γ => fun i => x i * u i) ⁻¹' O ∈
        nhds (fun _ : Fin n => (1 : Γ)) := ht hO
    obtain ⟨t, ht', hsub⟩ := exists_univ_pi_subset_of_mem_nhds (fun _ : Fin n => (1 : Γ)) hmem
    have hsub' : ∀ u : Fin n → Γ, u ∈ Set.univ.pi t → (fun i => x i * u i) ∈ O :=
      fun u hu => hsub hu
    choose Ui hUi using fun i => exists_openNormalSubgroup_sub_nhds_one (ht' i)
    refine ⟨Finset.inf' Finset.univ Finset.univ_nonempty Ui, fun y hy => ?_⟩
    have hu : (fun i => (x i)⁻¹ * y i) ∈ Set.univ.pi t := by
      rw [Set.mem_univ_pi]
      intro i
      exact hUi i (Finset.inf'_le Ui (Finset.mem_univ i) (hy i))
    have hres : (fun i => x i * (fun j => (x j)⁻¹ * y j) i) ∈ O :=
      hsub' (fun i => (x i)⁻¹ * y i) hu
    have h2 : y = (fun i => x i * (fun j => (x j)⁻¹ * y j) i) := by funext i; simp
    rwa [h2]

end Main

section DiscreteTarget

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [T2Space Γ] [TotallyDisconnectedSpace Γ]
  {M : Type*} [TopologicalSpace M] [DiscreteTopology M]

/-- A continuous map from `Fin n → Γ` to a discrete space is constant on the coset blocks of a
single open normal subgroup. -/
lemma exists_openNormalSubgroup_factors (n : ℕ) (f : (Fin n → Γ) → M) (hf : Continuous f) :
    ∃ U : OpenNormalSubgroup Γ, ∀ x y : Fin n → Γ,
      (∀ i, (x i)⁻¹ * y i ∈ (U : Subgroup Γ)) → f x = f y := by
  classical
  have hblock : ∀ x : Fin n → Γ, ∃ U : OpenNormalSubgroup Γ, ∀ y : Fin n → Γ,
      (∀ i, (x i)⁻¹ * y i ∈ (U : Subgroup Γ)) → y ∈ f ⁻¹' {f x} := by
    intro x
    exact exists_block_subset n x
      (hf.continuousAt.preimage_mem_nhds ((isOpen_discrete {f x}).mem_nhds rfl))
  choose Ux hUx using hblock
  let bl : (Fin n → Γ) → Set (Fin n → Γ) :=
    fun x => {y | ∀ i, (x i)⁻¹ * y i ∈ (Ux x : Subgroup Γ)}
  have hbl_open : ∀ x, IsOpen (bl x) := by
    intro x
    have hset : bl x = ⋂ i : Fin n,
        (fun y : Fin n → Γ => (x i)⁻¹ * y i) ⁻¹' (Ux x : Set Γ) := by
      ext y
      rw [Set.mem_iInter]
      exact Iff.rfl
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      ((continuous_const : Continuous (fun _ : Fin n → Γ => (x i)⁻¹)).mul
        (continuous_apply i)).isOpen_preimage (Ux x : Set Γ) (Ux x).isOpen
  have hcover : (Set.univ : Set (Fin n → Γ)) ⊆ ⋃ x, bl x := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, by intro i; simp⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover bl hbl_open hcover
  have hsne : s.Nonempty := by
    have hmem := hs (Set.mem_univ (fun _ : Fin n => (1 : Γ)))
    rw [Set.mem_iUnion] at hmem
    obtain ⟨z, hz⟩ := hmem
    rw [Set.mem_iUnion] at hz
    exact ⟨z, hz.1⟩
  let U : OpenNormalSubgroup Γ := Finset.inf' s hsne Ux
  refine ⟨U, fun x y hxy => ?_⟩
  have hmem := hs (Set.mem_univ y)
  rw [Set.mem_iUnion] at hmem
  obtain ⟨z, hz⟩ := hmem
  rw [Set.mem_iUnion] at hz
  obtain ⟨hzs, hbz⟩ := hz
  have hbzi : ∀ i, (z i)⁻¹ * y i ∈ (Ux z : Subgroup Γ) := hbz
  have hzx : ∀ i, (z i)⁻¹ * x i ∈ (Ux z : Subgroup Γ) := by
    intro i
    have h1 : (z i)⁻¹ * y i ∈ (Ux z : Subgroup Γ) := hbzi i
    have h2 : (y i)⁻¹ * x i ∈ (Ux z : Subgroup Γ) := by
      have h3 : ((x i)⁻¹ * y i)⁻¹ ∈ (U : Subgroup Γ) := (U : Subgroup Γ).inv_mem (hxy i)
      have h4 : (y i)⁻¹ * x i = ((x i)⁻¹ * y i)⁻¹ := by group
      rw [h4]
      exact Finset.inf'_le Ux hzs h3
    have key : ((z i)⁻¹ * y i) * ((y i)⁻¹ * x i) ∈ (Ux z : Subgroup Γ) :=
      (Ux z : Subgroup Γ).mul_mem h1 h2
    rwa [show ((z i)⁻¹ * y i) * ((y i)⁻¹ * x i) = (z i)⁻¹ * x i from by group] at key
  calc f x = f z := hUx z x hzx
    _ = f y := (hUx z y hbzi).symm

/-- Every continuous map from a power of a compact totally disconnected topological group to a
discrete space factors through the corresponding power of a finite quotient. -/
theorem factorThroughFiniteQuotient
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [T2Space Γ] [TotallyDisconnectedSpace Γ]
    {M : Type} [TopologicalSpace M] [DiscreteTopology M]
    (n : ℕ) (f : (Fin n → Γ) → M) (hf : Continuous f) :
    ∃ (U : OpenNormalSubgroup Γ) (F : (Fin n → Γ ⧸ (U : Subgroup Γ)) → M),
      ∀ x : Fin n → Γ, f x = F (fun i => QuotientGroup.mk (x i)) := by
  classical
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_factors (Γ := Γ) (M := M) n f hf
  refine ⟨U, fun q => f (fun i => Quotient.out (q i)), fun x => ?_⟩
  exact hU x (fun i => Quotient.out (QuotientGroup.mk (x i)))
    (fun i => QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk (x i))).symm)

end DiscreteTarget

end Work.CFTLib.Topology
