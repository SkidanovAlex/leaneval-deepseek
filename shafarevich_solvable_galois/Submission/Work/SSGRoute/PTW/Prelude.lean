import Mathlib
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFT.Ideles.globalCFT_totallyDisconnectedSpace_unityIdeles
import Submission.NK.GlobalCFT.Ideles.globalCFT_principalSubgroup_isClosed
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionIntegers_iInf_maximalIdeal_pow_eq_bot
import Submission.NK.GlobalCFT.LocalField.Topology
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup
import Submission.NK.ProfiniteP.ProPCore.totallyDisconnectedSpace_quotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary topological-group lemmas for the `p`-power criterion in the idèle class group

This module collects the general facts about compact Hausdorff topological groups used in
`Submission/Work/SSGRoute/PTW/mem_pthPower_of_all_open_index_p_subgroups.lean`:

* `connectedComponentOfOne_map_le`: a continuous homomorphism maps the identity component into
  the identity component.
* `isPreconnected_of_isPreconnected_image_mk`: **extension of (pre)connectedness** — a subgroup
  `A` of a topological group is preconnected if it contains a preconnected subgroup `N` and its
  image in `G ⧸ N` is preconnected.
* `totallyDisconnectedSpace_quotient_connectedComponentOfOne`: the quotient of a compact
  Hausdorff topological group by its identity component is totally disconnected (profinite).
* `totallyDisconnectedSpace_quotient_of_connectedComponentOfOne_le`: the quotient of a compact
  Hausdorff topological group by a closed normal subgroup containing the identity component is
  totally disconnected.

They are stated for arbitrary topological groups so that they are reusable.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.SSGRoute.PTW

/-- The identity component of a topological group is a normal subgroup. -/
instance connectedComponentOfOne_normal (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : (Subgroup.connectedComponentOfOne G).Normal :=
  Subgroup.Normal.mk fun x hx g => by
    have hcont : Continuous (fun y : G => g * y * g⁻¹) :=
      (continuous_const_mul g).mul continuous_const
    have h := Continuous.image_connectedComponent_subset hcont 1 ⟨x, hx, rfl⟩
    simp only [mul_one, mul_inv_cancel] at h
    exact h

/-- A continuous homomorphism of topological groups maps the identity component into the
identity component of the target. -/
theorem connectedComponentOfOne_map_le {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G →* H) (hφ : Continuous φ) :
    (Subgroup.connectedComponentOfOne G).map φ ≤ Subgroup.connectedComponentOfOne H := by
  rintro y ⟨x, hx, rfl⟩
  have h := Continuous.image_connectedComponent_subset hφ 1 ⟨x, hx, rfl⟩
  rw [map_one] at h
  exact h

/-- **Extension of (pre)connectedness.**  Let `N ≤ A` be subgroups of a topological group, with
`N` preconnected.  If the image of `A` in `G ⧸ N` is preconnected, then `A` is preconnected.

Each coset `xN` with `x ∈ A` is preconnected and contained in `A`, hence lies in one of the two
pieces of a disconnection of `A`; this makes the images of the two pieces in `G ⧸ N` disjoint, and
preconnectedness of the image of `A` finishes the argument. -/
theorem isPreconnected_of_isPreconnected_image_mk {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {N : Subgroup G} [N.Normal] {A : Subgroup G} (hNA : N ≤ A)
    (hN : IsPreconnected (N : Set G))
    (hA : IsPreconnected ((QuotientGroup.mk' N) '' (A : Set G))) :
    IsPreconnected (A : Set G) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hAu hAuv
  have hAuv' : ∀ y : G, y ∈ (A : Set G) → y ∈ u → y ∈ v → False := by
    intro y hyA hyu hyv
    have hmem : y ∈ (A : Set G) ∩ (u ∩ v) := ⟨hyA, hyu, hyv⟩
    rw [hAuv] at hmem
    exact hmem
  have hmem_coset : ∀ (x b : G), (QuotientGroup.mk' N) x = (QuotientGroup.mk' N) b →
      b ∈ (fun n => x * n) '' (N : Set G) := by
    intro x b h
    exact ⟨x⁻¹ * b, (QuotientGroup.eq (a := x) (b := b)).mp h, by group⟩
  have hself : ∀ (x : G), x ∈ (fun n => x * n) '' (N : Set G) := by
    intro x
    exact ⟨1, N.one_mem, by simp⟩
  have hsub : ∀ x ∈ (A : Set G), (fun n => x * n) '' (N : Set G) ⊆ (A : Set G) := by
    rintro x hx y ⟨n, hn, rfl⟩
    exact A.mul_mem hx (hNA hn)
  have hcoset : ∀ x ∈ (A : Set G),
      (fun n => x * n) '' (N : Set G) ⊆ u ∨ (fun n => x * n) '' (N : Set G) ⊆ v := by
    intro x hx
    refine (isPreconnected_iff_subset_of_disjoint.mp
      (hN.image _ (continuous_const_mul x).continuousOn)) u v hu hv ?_ ?_
    · intro y hy; exact hAu (hsub x hx hy)
    · rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨y, hyS, hyu, hyv⟩
      exact hAuv' y (hsub x hx hyS) hyu hyv
  have hopen : ∀ w : Set G, IsOpen w → IsOpen ((QuotientGroup.mk' N) '' w) := by
    intro w hw
    have h := (QuotientGroup.isOpenMap_coe (N := N)) w hw
    simpa [QuotientGroup.mk'_apply] using h
  have hmemA : ∀ {x a : G}, (QuotientGroup.mk' N) x = (QuotientGroup.mk' N) a → a ∈ (A : Set G) →
      x ∈ (A : Set G) := by
    intro x a hxa ha
    have hNx : a⁻¹ * x ∈ N := QuotientGroup.eq.mp hxa.symm
    have hx : x = a * (a⁻¹ * x) := by group
    rw [hx]
    exact A.mul_mem ha (hNA hNx)
  have hcover : (QuotientGroup.mk' N) '' (A : Set G) ⊆
      (QuotientGroup.mk' N) '' u ∪ (QuotientGroup.mk' N) '' v := by
    rintro z ⟨a, ha, rfl⟩
    rcases hAu ha with h | h
    · exact Or.inl ⟨a, h, rfl⟩
    · exact Or.inr ⟨a, h, rfl⟩
  have hdisj : ((QuotientGroup.mk' N) '' (A : Set G)) ∩
      ((QuotientGroup.mk' N) '' u ∩ (QuotientGroup.mk' N) '' v) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hzA, hzu, hzv⟩
    obtain ⟨a, haA, hza⟩ := hzA
    obtain ⟨x, hxu, hzx⟩ := hzu
    obtain ⟨y, hyv, hzy⟩ := hzv
    have hxa : (QuotientGroup.mk' N) x = (QuotientGroup.mk' N) a := hzx.trans hza.symm
    have hya : (QuotientGroup.mk' N) y = (QuotientGroup.mk' N) a := hzy.trans hza.symm
    have hxN : x ∈ (fun n => a * n) '' (N : Set G) := hmem_coset a x hxa.symm
    have hyN : y ∈ (fun n => a * n) '' (N : Set G) := hmem_coset a y hya.symm
    rcases hcoset a haA with h | h
    · exact hAuv' y (hmemA hya haA) (h hyN) hyv
    · exact hAuv' x (hmemA hxa haA) hxu (h hxN)
  rcases (isPreconnected_iff_subset_of_disjoint.mp hA) ((QuotientGroup.mk' N) '' u)
      ((QuotientGroup.mk' N) '' v) (hopen u hu) (hopen v hv) hcover hdisj with H | H
  · left
    intro a ha
    have hza : (QuotientGroup.mk' N) a ∈ (QuotientGroup.mk' N) '' u := H ⟨a, ha, rfl⟩
    obtain ⟨x, hxu, hxa⟩ := hza
    have hxA : x ∈ (A : Set G) := hmemA hxa ha
    rcases hcoset x hxA with h | h
    · exact h (hmem_coset x a hxa)
    · exact (hAuv' x hxA hxu (h (hself x))).elim
  · right
    intro a ha
    have hza : (QuotientGroup.mk' N) a ∈ (QuotientGroup.mk' N) '' v := H ⟨a, ha, rfl⟩
    obtain ⟨y, hyv, hya⟩ := hza
    have hyA : y ∈ (A : Set G) := hmemA hya ha
    rcases hcoset y hyA with h | h
    · exact (hAuv' y hyA (h (hself y)) hyv).elim
    · exact h (hmem_coset y a hya)

/-- **The quotient of a compact Hausdorff topological group by its identity component is totally
disconnected** (equivalently, profinite).

The preimage `A` of the identity component of the quotient contains the identity component `G₀`,
and the extension lemma `isPreconnected_of_isPreconnected_image_mk` (applied with `N = G₀`, which
is preconnected) shows that `A` is preconnected; as `A ∋ 1` this forces `A ⊆ G₀`, whence the
identity component of the quotient is trivial. -/
theorem totallyDisconnectedSpace_quotient_connectedComponentOfOne {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] :
    TotallyDisconnectedSpace
      (G ⧸ Subgroup.connectedComponentOfOne G) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  set G₀ := Subgroup.connectedComponentOfOne G with hG₀
  set A : Subgroup G := (Subgroup.connectedComponentOfOne (G ⧸ G₀)).comap (QuotientGroup.mk' G₀)
    with hA
  have hpre : IsPreconnected ((QuotientGroup.mk' G₀) '' (G₀ : Set G)) :=
    (isPreconnected_connectedComponent (x := (1 : G))).image
      ((QuotientGroup.mk' G₀) : G → G ⧸ G₀)
      (QuotientGroup.continuous_mk (N := G₀)).continuousOn
  have hmap2 : Subgroup.map (QuotientGroup.mk' G₀) A =
      Subgroup.connectedComponentOfOne (G ⧸ G₀) := by
    rw [hA, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective G₀)]
    simp
  have hGN : G₀ ≤ A := by
    intro x hx
    have h1 : (1 : G ⧸ G₀) ∈ (QuotientGroup.mk' G₀) '' (G₀ : Set G) :=
      ⟨1, G₀.one_mem, by simp⟩
    exact hpre.subset_connectedComponent h1 ⟨x, hx, rfl⟩
  have hApre : IsPreconnected (A : Set G) := by
    refine isPreconnected_of_isPreconnected_image_mk hGN isPreconnected_connectedComponent ?_
    have hmap : ((QuotientGroup.mk' G₀) '' (A : Set G)) =
        (Subgroup.connectedComponentOfOne (G ⧸ G₀) : Set (G ⧸ G₀)) := by
      rw [← Subgroup.coe_map, hmap2]
    rw [hmap]
    exact isPreconnected_connectedComponent
  have hAle : A ≤ G₀ := hApre.subset_connectedComponent A.one_mem
  have hbot : Subgroup.map (QuotientGroup.mk' G₀) A = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hAle
  have hmem : Subgroup.connectedComponentOfOne (G ⧸ G₀) = ⊥ := by
    rw [← hmap2, hbot]
  have hc := congrArg (fun S : Subgroup (G ⧸ G₀) => (S : Set (G ⧸ G₀))) hmem
  rw [Subgroup.coe_bot] at hc
  exact hc

/-- A bijective continuous homomorphism of topological groups with compact Hausdorff domain is a
homeomorphism (a continuous bijection from a compact space to a Hausdorff space is a
homeomorphism). -/
noncomputable def homeomorphOfMulEquivOfCompact {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] (e : G ≃* H) (he : Continuous e) [CompactSpace G]
    [T2Space H] : G ≃ₜ H := by
  refine Equiv.toHomeomorph e.toEquiv (fun s => ⟨fun hs => ?_, fun hs => hs.preimage he⟩)
  have hclosed : IsClosedMap (e : G → H) := he.isClosedMap
  have hsurj : Function.Surjective (e : G → H) := e.surjective
  have hcomp : (e : G → H) '' (e ⁻¹' s)ᶜ = sᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ hy
      exact hx (show (e : G → H) x ∈ s from hy)
    · intro hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, fun hx => hy hx, rfl⟩
  have hs' : s = ((e : G → H) '' (e ⁻¹' s)ᶜ)ᶜ := by
    rw [hcomp, compl_compl]
  rw [hs']
  exact (hclosed _ hs.isClosed_compl).isOpen_compl

/-- **The quotient of a compact Hausdorff topological group by a closed normal subgroup
containing the identity component is totally disconnected.**

Indeed `G ⧸ N` is a quotient of the profinite group `G ⧸ G₀` by `N ⧸ G₀`. -/
theorem totallyDisconnectedSpace_quotient_of_connectedComponentOfOne_le {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] {N : Subgroup G}
    [N.Normal] (hN : IsClosed (N : Set G)) (hGN : Subgroup.connectedComponentOfOne G ≤ N) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  set G₀ := Subgroup.connectedComponentOfOne G with hG₀
  haveI h4 : TotallyDisconnectedSpace (G ⧸ G₀) :=
    totallyDisconnectedSpace_quotient_connectedComponentOfOne
  haveI hKn : (N.map (QuotientGroup.mk' G₀)).Normal := inferInstance
  have hKclosed : IsClosed ((N.map (QuotientGroup.mk' G₀) : Subgroup (G ⧸ G₀)) :
      Set (G ⧸ G₀)) := by
    have hclosedmap : IsClosedMap (QuotientGroup.mk' G₀ : G → G ⧸ G₀) :=
      (QuotientGroup.continuous_mk (N := G₀)).isClosedMap
    simpa [Subgroup.coe_map] using hclosedmap _ hN
  haveI h5 : TotallyDisconnectedSpace
      ((G ⧸ G₀) ⧸ (N.map (QuotientGroup.mk' G₀))) :=
    NK.ProfiniteP.ProPCore.totallyDisconnectedSpace_quotient hKclosed
  set e : (G ⧸ G₀) ⧸ (N.map (QuotientGroup.mk' G₀)) → G ⧸ N :=
    (QuotientGroup.quotientQuotientEquivQuotient G₀ N hGN :
      (G ⧸ G₀) ⧸ (N.map (QuotientGroup.mk' G₀)) → G ⧸ N) with he_def
  have hfun : (fun g : G => e ((QuotientGroup.mk' (N.map (QuotientGroup.mk' G₀)))
      ((QuotientGroup.mk' G₀) g))) = (QuotientGroup.mk' N : G → G ⧸ N) := by
    funext g
    rw [he_def]
    change (QuotientGroup.quotientQuotientEquivQuotientAux G₀ N hGN)
      ((QuotientGroup.mk' (N.map (QuotientGroup.mk' G₀))) ((QuotientGroup.mk' G₀) g)) =
      (QuotientGroup.mk' N) g
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk G₀ N hGN g
  have he1 : Continuous (fun g : G => e ((QuotientGroup.mk' (N.map (QuotientGroup.mk' G₀)))
      ((QuotientGroup.mk' G₀) g))) := by
    rw [hfun]
    exact QuotientGroup.continuous_mk
  have he2 : Continuous (fun z : G ⧸ G₀ =>
      e ((QuotientGroup.mk' (N.map (QuotientGroup.mk' G₀))) z)) :=
    (QuotientGroup.isQuotientMap_mk G₀).continuous_iff.mpr he1
  have he : Continuous e :=
    (QuotientGroup.isQuotientMap_mk (N.map (QuotientGroup.mk' G₀))).continuous_iff.mpr he2
  exact (homeomorphOfMulEquivOfCompact
    (QuotientGroup.quotientQuotientEquivQuotient G₀ N hGN) he).totallyDisconnectedSpace


end Work.SSGRoute.PTW
