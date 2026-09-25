import Mathlib
import Submission.Work.RelatorRank.Bridge

/-!
# Dense generating families detected on open normal quotients

**Namespace** `Work.RelatorRank.DenseGenerating`.

A family `gen : ι → Γ` in a (compact, totally disconnected) topological group *densely generates*
`Γ` exactly when, for every open normal subgroup `U ≤ Γ`, the images of the `gen i` generate the
finite quotient `Γ ⧸ U`:

`DenseGenerating gen ↔ ∀ U : OpenNormalSubgroup Γ, closure (range (mk' U ∘ gen)) = ⊤`.

This is the profinite "generators are detected on finite quotients" principle: an abstract subgroup
of `Γ` is dense iff it meets every coset of every open (normal) subgroup, i.e. iff its image in each
`Γ ⧸ U` is everything.  The two ingredients are proved below:

* `map_eq_top_iff_sup_ker` : for a surjective `f : G →* N`, the image `K.map f` is all of `N`
  iff `K ⊔ f.ker = ⊤` (a purely algebraic statement about subgroups);
* `topClosure_eq_top_iff_forall_openNormal` : `K` is dense in `Γ` iff `K ⊔ U = ⊤` for every open
  normal subgroup `U`.  The forward direction uses that a dense subgroup meets every coset of an
  open subgroup; the converse uses `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`
  (open normal subgroups form a basis of neighbourhoods of `1`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Work.RelatorRank.DenseGenerating

open TopologicalSpace

/-- **Algebraic form of the quotient criterion.**  For a surjective group homomorphism
`f : G →* N` and a subgroup `K ≤ G`, the image `K.map f` is all of `N` if and only if
`K` together with the kernel of `f` generates `G`. -/
theorem map_eq_top_iff_sup_ker {G N : Type*} [Group G] [Group N] (f : G →* N)
    (hf : Function.Surjective f) (K : Subgroup G) : K.map f = ⊤ ↔ K ⊔ f.ker = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro g _
    have hg : f g ∈ K.map f := by rw [h]; exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hg
    obtain ⟨k, hk, hfk⟩ := hg
    have hz : k⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfk, inv_mul_cancel]
    rw [Subgroup.mem_sup_of_normal_right]
    exact ⟨k, hk, k⁻¹ * g, hz, by group⟩
  · intro h
    rw [eq_top_iff]
    intro y _
    obtain ⟨g, rfl⟩ := hf y
    have hg : g ∈ K ⊔ f.ker := by rw [h]; exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_right] at hg
    obtain ⟨k, hk, z, hz, rfl⟩ := hg
    rw [map_mul, MonoidHom.mem_ker.mp hz, mul_one]
    exact Subgroup.mem_map_of_mem f hk

/-- **The profinite density criterion.**  A subgroup `K` of a compact totally disconnected
topological group `Γ` is dense (equivalently, its topological closure is `⊤`) if and only if it
maps onto every open normal quotient, i.e. `K ⊔ U = ⊤` for every open normal subgroup `U ≤ Γ`. -/
theorem topClosure_eq_top_iff_forall_openNormal {Γ : Type*} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (K : Subgroup Γ) :
    K.topologicalClosure = ⊤ ↔ ∀ U : OpenNormalSubgroup Γ, K ⊔ (U : Subgroup Γ) = ⊤ := by
  constructor
  · intro h U
    have hd : Dense (K : Set Γ) := (topologicalClosure_eq_top_iff_dense K).mp h
    rw [eq_top_iff]
    intro g _
    have hgc : g ∈ closure (K : Set Γ) := by rw [hd.closure_eq]; exact Set.mem_univ g
    have hopen : IsOpen ((fun x => g * x) '' (U : Set Γ)) :=
      (Homeomorph.mulLeft g).isOpenMap _ U.isOpen
    have hmem : g ∈ (fun x => g * x) '' (U : Set Γ) := ⟨1, U.one_mem, mul_one g⟩
    obtain ⟨k, ⟨u, huU, hku⟩, hkK⟩ := mem_closure_iff.mp hgc _ hopen hmem
    rw [Subgroup.mem_sup_of_normal_right]
    exact ⟨k, hkK, u⁻¹, U.inv_mem huU, by rw [← hku, mul_assoc, mul_inv_cancel, mul_one]⟩
  · intro h
    refine (topologicalClosure_eq_top_iff_dense K).mpr ?_
    rw [dense_iff_inter_open]
    intro V hVopen hVne
    obtain ⟨g, hgV⟩ := hVne
    have hWopen : IsOpen {x : Γ | g * x ∈ V} := hVopen.preimage (continuous_const.mul continuous_id)
    have h1W : (1 : Γ) ∈ {x : Γ | g * x ∈ V} := by simpa using hgV
    obtain ⟨H, hHW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWopen h1W
    have hg_top : g ∈ K ⊔ (H : Subgroup Γ) := by rw [h H]; exact Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_right] at hg_top
    obtain ⟨k, hkK, z, hzH, hkz⟩ := hg_top
    have hzW : g * z⁻¹ ∈ V := hHW (H.inv_mem hzH)
    refine ⟨k, ?_, hkK⟩
    have : k = g * z⁻¹ := by rw [← hkz, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact hzW

/-- **Dense generation is detected on open normal quotients.**  A family `gen : ι → Γ` densely
generates a compact totally disconnected topological group `Γ` if and only if for every open normal
subgroup `U ≤ Γ` the images of the `gen i` generate the finite quotient `Γ ⧸ U`. -/
theorem denseGenerating_iff_forall_openNormalSubgroup {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {ι : Type*} (gen : ι → Γ) :
    DenseGenerating gen ↔ ∀ U : OpenNormalSubgroup Γ,
      Subgroup.closure (Set.range fun i => (QuotientGroup.mk' U.toSubgroup) (gen i)) = ⊤ := by
  have hmap : ∀ (U : OpenNormalSubgroup Γ),
      Subgroup.closure (Set.range fun i => (QuotientGroup.mk' U.toSubgroup) (gen i))
        = (Subgroup.closure (Set.range gen)).map (QuotientGroup.mk' U.toSubgroup) := by
    intro U
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨gen i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hD : DenseGenerating gen ↔ ∀ U : OpenNormalSubgroup Γ,
      (Subgroup.closure (Set.range gen)).map (QuotientGroup.mk' U.toSubgroup) = ⊤ := by
    rw [show DenseGenerating gen ↔ (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤
      from Iff.rfl, topClosure_eq_top_iff_forall_openNormal]
    constructor
    · intro h U
      rw [map_eq_top_iff_sup_ker _ (QuotientGroup.mk'_surjective U.toSubgroup) _,
        QuotientGroup.ker_mk']
      exact h U
    · intro h U
      have h' := (map_eq_top_iff_sup_ker (QuotientGroup.mk' U.toSubgroup)
        (QuotientGroup.mk'_surjective U.toSubgroup) (Subgroup.closure (Set.range gen))).mp (h U)
      rwa [QuotientGroup.ker_mk'] at h'
  rw [hD]
  constructor
  · intro h U; rw [hmap U]; exact h U
  · intro h U; rw [← hmap U]; exact h U

end Work.RelatorRank.DenseGenerating
