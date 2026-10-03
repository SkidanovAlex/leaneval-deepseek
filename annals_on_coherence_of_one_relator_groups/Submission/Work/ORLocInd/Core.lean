/-
# Node N4: virtual torsion-freeness and local indicability --- main results

This module assembles the two theorems of node N4 of the route design:

* `oneRelator_virtually_torsionFree` : every one-relator group has a normal torsion-free subgroup
  of finite index (Fischer--Karrass--Solitar 1972; the reduction from the FKS finite quotient to
  virtual torsion-freeness uses the Magnus--Karrass--Solitar torsion theorem);
* `torsionFree_subgroup_locallyIndicable` : every torsion-free subgroup of a one-relator group is
  locally indicable (Brodskii 1980; Howie 2000, Corollary 3.2).

Both are stated with the literature input as an explicit, named hypothesis, so that this node is
independent of the (large) combinatorial input node N2:

* `Work.ORLocInd.HasTorsionInput G` bundles a `RootPresentation G = ⟨X | u ^ l⟩` (`u` not a proper
  power), the Magnus--Karrass--Solitar torsion theory `TorsionTheory P` (`u` has order exactly `l`,
  every torsion element is conjugate into `⟨u⟩`) and the Fischer--Karrass--Solitar finite quotient
  `HasFKSTorsionQuotient P` (a finite quotient in which the image of `u` has order exactly `l`);
* `Work.ORLocInd.BrodskiiHowieInput G` is Brodskii's theorem in the form used by the paper: every
  torsion-free subgroup of `G` is locally indicable.

The genuinely formalised mathematics of this module is:

* `virtuallyTorsionFree_of_hasTorsionInput`: FKS finite quotient + KMS torsion theory give virtual
  torsion-freeness (the kernel of the FKS quotient is torsion-free);
* `exists_finiteQuotient_of_virtuallyTorsionFree`: conversely, virtual torsion-freeness and the KMS
  torsion theory produce a finite quotient in which the root has order exactly `l`, so the two forms
  of FKS are equivalent over KMS;
* `virtuallyLocallyIndicable_of_oneRelator`: FKS + Brodskii give that a one-relator group is
  virtually locally indicable --- the form in which the paper uses the two theorems;
* `virtuallyTorsionFree_of_virtuallyLocallyIndicable`, `virtuallyLocallyIndicable_iff_exists`: the
  relation between the two "virtual" notions and torsion-freeness of the finite index subgroup
  (via `Group.LocallyIndicable.isTorsionFree`);
* `OneRelatorInput`, `hasTorsionInput_of_kms_of_virtuallyTorsionFree`, and the module
  `Submission.Work.ORLocInd.Bridge.N2`, which discharges the Magnus--Karrass--Solitar half of the
  input from node N2's `Work.OROneRel.OneRelatorCombinatorics`.
-/
import Submission.Work.ORLocInd.Basic

set_option autoImplicit false

-- The hypotheses `hG : Group.OneRelator G` below are kept for faithfulness to the route design,
-- even where the proof only needs the explicit literature input.
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd

/-! ## 1. Torsion-freeness -/

theorem IsTorsionFree.of_isMulTorsionFree {G : Type*} [Group G] [IsMulTorsionFree G] :
    IsTorsionFree G := fun _ hg => hg.eq_one'

theorem IsTorsionFree.subgroup {G : Type*} [Group G] (h : IsTorsionFree G) (H : Subgroup G) :
    IsTorsionFree H := by
  intro x hx
  have hx' : IsOfFinOrder ((x : H) : G) := MonoidHom.isOfFinOrder H.subtype hx
  exact Subtype.ext (h _ hx')

theorem IsTorsionFree.of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : IsTorsionFree H) : IsTorsionFree G := by
  intro g hg
  exact hf (by rw [h _ (MonoidHom.isOfFinOrder f hg), map_one])

theorem IsTorsionFree.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsTorsionFree G) : IsTorsionFree H :=
  h.of_injective (e.symm : H →* G) e.symm.injective

theorem IsTorsionFree.subsingleton_of_finite {G : Type*} [Group G] [Finite G]
    (h : IsTorsionFree G) : Subsingleton G :=
  ⟨fun a b => by
    have hab : a / b = 1 := h _ (isOfFinOrder_of_finite _)
    simpa [div_eq_one] using hab⟩

/-- The trivial subgroup is torsion-free whenever the ambient group is. -/
theorem IsTorsionFree.top {G : Type*} [Group G] (h : IsTorsionFree G) :
    IsTorsionFree (⊤ : Subgroup G) :=
  h.of_injective (⊤ : Subgroup G).subtype Subtype.coe_injective

/-! ## 2. Local indicability -/

theorem Group.LocallyIndicable.isTorsionFree {G : Type*} [Group G] (h : Group.LocallyIndicable G) :
    IsTorsionFree G := by
  intro g hg
  by_contra hg1
  have hHmem : g ∈ Subgroup.closure ({g} : Set G) := Subgroup.subset_closure (Set.mem_singleton g)
  have hHne : Subgroup.closure ({g} : Set G) ≠ ⊥ := by
    intro hbot
    have : g ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact hHmem
    exact hg1 (by simpa using this)
  have hfg : (Subgroup.closure ({g} : Set G)).FG :=
    (Subgroup.fg_iff _).mpr ⟨{g}, rfl, Set.finite_singleton g⟩
  obtain ⟨f, hf⟩ := h _ hfg hHne
  have hg' : IsOfFinOrder (⟨g, hHmem⟩ : ↥(Subgroup.closure ({g} : Set G))) := by
    obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext (by simpa using hgn)⟩
  have hf1 : f ⟨g, hHmem⟩ = 1 :=
    (MonoidHom.isOfFinOrder f hg').eq_one'
  obtain ⟨x, hx⟩ := hf (Multiplicative.ofAdd 1)
  have hxmem : (x : G) ∈ Subgroup.zpowers g := by
    rw [Subgroup.zpowers_eq_closure]; exact x.2
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hx_eq : x = (⟨g, hHmem⟩ : Subgroup.closure ({g} : Set G)) ^ n := by
    refine Subtype.ext ?_
    rw [← hn]
    simp
  have hfx : f x = 1 := by rw [hx_eq, map_zpow, hf1, one_zpow]
  rw [hx] at hfx
  exact absurd (by simpa using congrArg Multiplicative.toAdd hfx : (1 : ℤ) = 0) one_ne_zero

theorem Group.LocallyIndicable.of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : Group.LocallyIndicable H) : Group.LocallyIndicable G := by
  intro K hK hKne
  haveI : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr hK
  obtain ⟨g, hg⟩ := h (f.comp K.subtype).range
    ((Group.fg_iff_subgroup_fg _).mp
      (Group.fg_of_surjective (f.comp K.subtype).rangeRestrict_surjective))
    (by
      intro hbot
      apply hKne
      apply le_antisymm _ bot_le
      intro x hx
      have hx1 : (f.comp K.subtype) ⟨x, hx⟩ = 1 := by
        have : (f.comp K.subtype) ⟨x, hx⟩ ∈ (⊥ : Subgroup H) := by
          rw [← hbot]; exact ⟨⟨x, hx⟩, rfl⟩
        simpa using this
      exact hf (by rw [map_one]; exact hx1))
  refine ⟨g.comp (f.comp K.subtype).rangeRestrict, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hg y
  obtain ⟨z, hz⟩ := (f.comp K.subtype).rangeRestrict_surjective x
  exact ⟨z, by rw [MonoidHom.comp_apply, hz, hx]⟩

theorem Group.LocallyIndicable.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Group.LocallyIndicable G) : Group.LocallyIndicable H :=
  h.of_injective (e.symm : H →* G) e.symm.injective

theorem Group.LocallyIndicable.subgroup {G : Type*} [Group G] (h : Group.LocallyIndicable G)
    (H : Subgroup G) : Group.LocallyIndicable H := by
  intro K hK hKbot
  haveI : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr hK
  obtain ⟨g, hg⟩ := h (H.subtype.comp K.subtype).range
    ((Group.fg_iff_subgroup_fg _).mp
      (Group.fg_of_surjective (H.subtype.comp K.subtype).rangeRestrict_surjective))
    (by
      intro hbot
      apply hKbot
      apply le_antisymm _ bot_le
      intro x hx
      have hx1 : (H.subtype.comp K.subtype) ⟨x, hx⟩ = 1 := by
        have : (H.subtype.comp K.subtype) ⟨x, hx⟩ ∈ (⊥ : Subgroup G) := by
          rw [← hbot]; exact ⟨⟨x, hx⟩, rfl⟩
        simpa using this
      exact Subtype.ext (by simpa using hx1))
  refine ⟨g.comp (H.subtype.comp K.subtype).rangeRestrict, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hg y
  obtain ⟨z, hz⟩ := (H.subtype.comp K.subtype).rangeRestrict_surjective x
  exact ⟨z, by rw [MonoidHom.comp_apply, hz, hx]⟩

/-! ## 3. The virtual notions -/

theorem VirtuallyTorsionFree.of_finiteIndex {G : Type*} [Group G]
    (h : ∃ G' : Subgroup G, G'.FiniteIndex ∧ IsTorsionFree G') : VirtuallyTorsionFree G := by
  obtain ⟨G', hfi, htf⟩ := h
  haveI := hfi
  let f : ↥G'.normalCore →* ↥(G'.normalCore.subgroupOf G') :=
    { toFun := fun x => ⟨⟨(x : G), G'.normalCore_le x.2⟩, x.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (congrArg (fun y : ↥(G'.normalCore.subgroupOf G') => (y : G)) hab)
  exact ⟨G'.normalCore, G'.normalCore_normal, inferInstance,
    IsTorsionFree.of_injective f hinj (htf.subgroup (G'.normalCore.subgroupOf G'))⟩

theorem VirtuallyTorsionFree.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : VirtuallyTorsionFree G) : VirtuallyTorsionFree H := by
  obtain ⟨G', hN, hfi, htf⟩ := h
  haveI : G'.FiniteIndex := hfi
  refine ⟨G'.map (e : G →* H), hN.map (e : G →* H) e.surjective, ?_, ?_⟩
  · rw [Subgroup.finiteIndex_iff, Subgroup.index_map_of_bijective e.bijective]
    exact hfi.index_ne_zero
  · exact IsTorsionFree.of_mulEquiv
      (Subgroup.equivMapOfInjective G' (e : G →* H) e.injective) htf

theorem VirtuallyLocallyIndicable.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : VirtuallyLocallyIndicable G) : VirtuallyLocallyIndicable H := by
  obtain ⟨G', hN, hfi, hli⟩ := h
  haveI : G'.FiniteIndex := hfi
  refine ⟨G'.map (e : G →* H), hN.map (e : G →* H) e.surjective, ?_, ?_⟩
  · rw [Subgroup.finiteIndex_iff, Subgroup.index_map_of_bijective e.bijective]
    exact hfi.index_ne_zero
  · exact Group.LocallyIndicable.of_mulEquiv
      (Subgroup.equivMapOfInjective G' (e : G →* H) e.injective) hli

theorem virtuallyTorsionFree_of_virtuallyLocallyIndicable {G : Type u} [Group G]
    (h : VirtuallyLocallyIndicable G) : VirtuallyTorsionFree G := by
  obtain ⟨G', hN, hfi, hli⟩ := h
  exact ⟨G', hN, hfi, Group.LocallyIndicable.isTorsionFree hli⟩

theorem virtuallyLocallyIndicable_iff_exists {G : Type u} [Group G] :
    VirtuallyLocallyIndicable G ↔ ∃ G' : Subgroup G,
      G'.Normal ∧ G'.FiniteIndex ∧ IsTorsionFree G' ∧ Group.LocallyIndicable G' :=
  ⟨fun ⟨G', hN, hfi, hli⟩ => ⟨G', hN, hfi, Group.LocallyIndicable.isTorsionFree hli, hli⟩,
   fun ⟨G', hN, hfi, _, hli⟩ => ⟨G', hN, hfi, hli⟩⟩

/-! ## 4. The FKS/KMS argument: virtual torsion-freeness -/

theorem isTorsionFree_ker_of_orderOf {G : Type*} [Group G] {u : G} {l : ℕ}
    (hu : orderOf u = l)
    (hconj : ∀ g : G, IsOfFinOrder g → ∃ (k : ℕ) (c : G), g = c * u ^ k * c⁻¹)
    {Q : Type*} [Group Q] (φ : G →* Q) (hφ : orderOf (φ u) = l) :
    IsTorsionFree φ.ker := by
  intro x hx
  have hxG : IsOfFinOrder ((x : φ.ker) : G) := MonoidHom.isOfFinOrder φ.ker.subtype hx
  obtain ⟨k, c, hc⟩ := hconj (x : G) hxG
  have hbase : φ c * (φ u) ^ k * (φ c)⁻¹ = 1 := by
    have h := congrArg φ hc
    simp only [map_mul, map_pow, map_inv] at h
    rw [show ((x : φ.ker) : G) = (x : G) from rfl, x.2] at h
    exact h.symm
  have hpow : (φ u) ^ k = 1 := by
    calc (φ u) ^ k = (φ c)⁻¹ * (φ c * (φ u) ^ k * (φ c)⁻¹) * (φ c) := by group
      _ = 1 := by rw [hbase]; group
  have hl : l ∣ k := by
    have h1 : orderOf (φ u) ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rwa [hφ] at h1
  have huk : u ^ k = 1 := by
    have h1 : orderOf u ∣ k := by rw [hu]; exact hl
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  refine Subtype.ext ?_
  show (x : G) = 1
  rw [hc, huk, mul_one, mul_inv_cancel]

theorem isTorsionFree_of_orderOf_one {G : Type*} [Group G] {u : G} (hu : orderOf u = 1)
    (hconj : ∀ g : G, IsOfFinOrder g → ∃ (k : ℕ) (c : G), g = c * u ^ k * c⁻¹) :
    IsTorsionFree G := by
  have hu1 : u = 1 := orderOf_eq_one_iff.mp hu
  intro g hg
  obtain ⟨k, c, hc⟩ := hconj g hg
  rw [hc, hu1, one_pow, mul_one, mul_inv_cancel]

theorem virtuallyTorsionFree_of_hasTorsionInput {G : Type u} [Group G] (h : HasTorsionInput G) :
    VirtuallyTorsionFree G := by
  obtain ⟨P, hKMS, hFKS⟩ := h
  rcases eq_or_lt_of_le P.one_le_l with hl | hl
  · refine VirtuallyTorsionFree.of_finiteIndex ⟨⊤, inferInstance, ?_⟩
    refine IsTorsionFree.top (isTorsionFree_of_orderOf_one ?_ hKMS.torsion_conj)
    rw [hKMS.orderOf_root, hl]
  · obtain ⟨Q, hQ, hQfin, φ, hφ⟩ := hFKS
    letI := hQ
    letI := hQfin
    refine ⟨MonoidHom.ker φ, ?_, ?_, ?_⟩
    · exact MonoidHom.normal_ker φ
    · exact Subgroup.finiteIndex_ker φ
    · exact isTorsionFree_ker_of_orderOf hKMS.orderOf_root hKMS.torsion_conj φ hφ

/-- Over the Magnus--Karrass--Solitar torsion theory, virtual torsion-freeness is equivalent to the
existence of a finite quotient in which the root of the presentation has order exactly `l`: the
kernel of any finite quotient is normal of finite index, and no torsion element of `G` is killed
exactly when the root keeps its order. -/
theorem exists_finiteQuotient_of_virtuallyTorsionFree {G : Type u} [Group G]
    (P : RootPresentation G) (hKMS : TorsionTheory P) (h : VirtuallyTorsionFree G) :
    HasFKSTorsionQuotient P := by
  obtain ⟨N, hN, hNfi, hNtf⟩ := h
  haveI := hN
  haveI := hNfi
  have hlpos : 0 < P.l := P.one_le_l
  refine ⟨G ⧸ N, inferInstance, inferInstance, QuotientGroup.mk' N, ?_⟩
  have hdvd : orderOf (QuotientGroup.mk' N P.rootElem) ∣ P.l :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, P.rootElem_pow, map_one])
  have hm : ∀ m : ℕ, (QuotientGroup.mk' N P.rootElem) ^ m = 1 → P.l ∣ m := by
    intro m hm
    have hmem : P.rootElem ^ m ∈ N := by
      have hq : (((P.rootElem ^ m : G)) : G ⧸ N) = 1 := by
        have h2 : QuotientGroup.mk' N (P.rootElem ^ m) = 1 := by rw [map_pow]; exact hm
        simpa using h2
      exact (QuotientGroup.eq_one_iff (P.rootElem ^ m)).mp hq
    have hone : P.rootElem ^ m = 1 := by
      have hfin : IsOfFinOrder (⟨P.rootElem ^ m, hmem⟩ : ↥N) := by
        refine isOfFinOrder_iff_pow_eq_one.mpr ⟨P.l, hlpos, ?_⟩
        refine Subtype.ext ?_
        show (P.rootElem ^ m) ^ P.l = 1
        rw [← pow_mul, mul_comm, pow_mul, P.rootElem_pow, one_pow]
      have h3 := hNtf ⟨P.rootElem ^ m, hmem⟩ hfin
      simpa using congrArg (fun y : ↥N => (y : G)) h3
    have h1 : orderOf P.rootElem ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hone
    rwa [hKMS.orderOf_root] at h1
  exact Nat.dvd_antisymm hdvd (hm _ (pow_orderOf_eq_one _))

/-- With the two bundled literature inputs of node N4, a group is virtually locally indicable: the
torsion-free finite-index subgroup produced by FKS is locally indicable by Brodskii's theorem. -/
theorem virtuallyLocallyIndicable_of_hasTorsionInput {G : Type u} [Group G]
    (ht : HasTorsionInput G) (hb : BrodskiiHowieInput G) : VirtuallyLocallyIndicable G := by
  obtain ⟨G', hN, hfi, htf⟩ := virtuallyTorsionFree_of_hasTorsionInput ht
  exact ⟨G', hN, hfi, hb G' htf⟩

/-- The bundled form of the previous lemma (`Work.ORLocInd.OneRelatorInput`). -/
theorem VirtuallyLocallyIndicable.of_oneRelatorInput {G : Type u} [Group G]
    (h : OneRelatorInput G) : VirtuallyLocallyIndicable G :=
  virtuallyLocallyIndicable_of_hasTorsionInput h.1 h.2

end Work.ORLocInd
