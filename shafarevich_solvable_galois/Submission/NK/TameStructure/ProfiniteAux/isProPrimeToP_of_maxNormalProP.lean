/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The tame inertia is pro-prime-to-`p`

Let `V ⊴ G` be the *maximal* normal pro-`p` subgroup of a profinite group `G` (in the sense that
`V` is pro-`p` and contains every normal pro-`p` subgroup), let `I ⊴ G` be a closed normal subgroup
with `V ≤ I`, and suppose the image `H = I/V` of `I` in `G ⧸ V` is pro-cyclic
(`NK.LocalTame.IsProCyclic`).  Then `H` is **pro-prime-to-`p`**.

The proof: a pro-cyclic profinite group which is not pro-prime-to-`p` has a nontrivial
*characteristic* pro-`p` subgroup
(`NK.TameStructure.ProCyclic.exists_characteristic_proP_of_not_isProPrimeToP`); being
characteristic in `H` and `H` normal in `G ⧸ V`, its image in `G ⧸ V` is normal there, and its
preimage in `G` is a normal pro-`p` subgroup strictly containing `V`, contradicting maximality.

This derives the field `isProPrimeToP_tameInertia` of `NK.TameData.TameInertiaInput`
(NSW, *Cohomology of Number Fields*, (7.5.11)) from the maximality of the wild inertia.
-/
import Submission.NK.TameStructure.ProCyclic.exists_characteristic_proP_of_not_isProPrimeToP
import Submission.NK.TameStructure.ProfiniteAux.isProP_of_normal_of_quotient
import Submission.NK.ProfiniteP.ProPCore.totallyDisconnectedSpace_quotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace NK.TameStructure.ProfiniteAux

open NK.LocalTame

/-- **A characteristic subgroup of a normal subgroup is normal in the ambient group.** -/
theorem map_subtype_normal_of_characteristic {G : Type*} [Group G] {H : Subgroup G}
    {N : Subgroup ↥H} (hN : N.Characteristic) (hH : H.Normal) : (N.map H.subtype).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  -- conjugation by `g` restricts to an automorphism of `↥H`
  let ψ : ↥H ≃* ↥H :=
    { toFun := fun x => ⟨g * x.1 * g⁻¹, by simpa using Subgroup.Normal.conj_mem hH x.1 x.2 g⟩
      invFun := fun x => ⟨g⁻¹ * x.1 * g, by
        simpa using Subgroup.Normal.conj_mem hH x.1 x.2 g⁻¹⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc]
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  have hψ : N.map ψ.toMonoidHom = N := (Subgroup.characteristic_iff_map_eq.mp hN) ψ
  have hcomp : Subgroup.map (((MulAut.conj g : G ≃* G) : G →* G).comp H.subtype) N =
      Subgroup.map (H.subtype.comp ψ.toMonoidHom) N := by
    congr 1
  have step : Subgroup.map (H.subtype.comp ψ.toMonoidHom) N =
      Subgroup.map H.subtype (Subgroup.map ψ.toMonoidHom N) :=
    (Subgroup.map_map N H.subtype ψ.toMonoidHom).symm
  refine (Subgroup.map_map N (((MulAut.conj g : G ≃* G) : G →* G)) H.subtype).trans ?_
  rw [hcomp, step, hψ]

/-- **An extension of pro-`p` groups, in the form used below**: if `V ⊴ G` is pro-`p` and the
quotient `K ⧸ V` of a subgroup `K ⊇ V` is pro-`p`, then `K` is pro-`p`. -/
theorem isProP_of_isProP_subgroupOf_quotient {G : Type*} [Group G] {p : ℕ} {V K : Subgroup G}
    [V.Normal] (hVK : V ≤ K) (hV : IsProP p ↥V)
    (hquot : IsProP p (↥K ⧸ V.subgroupOf K)) : IsProP p ↥K :=
  isProP_of_normal_of_quotient
    ((isProP_congr (Subgroup.subgroupOfEquivOfLe hVK) p).mpr hV) hquot

/-- **The tame inertia is pro-prime-to-`p`** (NSW (7.5.11)), from the maximality of the wild
inertia `V` and the pro-cyclicity of `I/V` — see the file header. -/
theorem isProPrimeToP_of_maxNormalProP {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {p : ℕ} (hp : p.Prime) {V I : Subgroup G} [V.Normal] (hVc : IsClosed (V : Set G))
    (hI : I.Normal) (hIc : IsClosed (I : Set G)) (hVp : NK.LocalTame.IsProP p ↥V)
    (hmax : ∀ N : Subgroup G, N.Normal → NK.LocalTame.IsProP p ↥N → N ≤ V)
    (hHn : (NK.LocalTame.quotientImage V I).Normal)
    (hcyc : NK.LocalTame.IsProCyclic ↥(NK.LocalTame.quotientImage V I)) :
    NK.LocalTame.IsProPrimeToP p ↥(NK.LocalTame.quotientImage V I) := by
  by_contra hcon
  haveI hTD : TotallyDisconnectedSpace (G ⧸ V) :=
    NK.ProfiniteP.ProPCore.totallyDisconnectedSpace_quotient hVc
  have hIcomp : IsCompact (I : Set G) := hIc.isCompact
  have hset : (QuotientGroup.mk' V) '' (I : Set G) = QuotientGroup.mk '' (I : Set G) := by
    apply Set.image_congr
    intro x _
    exact QuotientGroup.mk'_apply V x
  have hImcomp : IsCompact
      ((NK.LocalTame.quotientImage V I : Subgroup (G ⧸ V)) : Set (G ⧸ V)) := by
    rw [NK.LocalTame.quotientImage, Subgroup.coe_map, hset]
    exact hIcomp.image (QuotientGroup.continuous_mk (N := V))
  haveI hHcomp : CompactSpace ↥(NK.LocalTame.quotientImage V I) :=
    isCompact_iff_compactSpace.mp hImcomp
  -- a nontrivial characteristic pro-`p` subgroup of `I/V`
  obtain ⟨N, hNchar, hNne, hNpro⟩ :=
    ProCyclic.exists_characteristic_proP_of_not_isProPrimeToP hp hcyc hcon
  -- its image in `G ⧸ V` is normal, nontrivial and pro-`p`
  let N' : Subgroup (G ⧸ V) := N.map (NK.LocalTame.quotientImage V I).subtype
  haveI hN'norm : N'.Normal := map_subtype_normal_of_characteristic hNchar hHn
  have hN'pro : NK.LocalTame.IsProP p ↥N' :=
    (isProP_congr (Subgroup.equivMapOfInjective N
      (NK.LocalTame.quotientImage V I).subtype (fun _ _ h => Subtype.ext h)) p).mp hNpro
  have hN'ne : N' ≠ ⊥ := by
    intro hbot
    apply hNne
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have h : (NK.LocalTame.quotientImage V I).subtype n ∈ N' :=
      Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    rw [hbot] at h
    exact Subtype.ext (Subgroup.mem_bot.mp h)
  -- the preimage of `N'` in `G` is a normal pro-`p` subgroup strictly containing `V`
  let K : Subgroup G := N'.comap (QuotientGroup.mk' V)
  have hVK : V ≤ K := by
    intro x hx
    show (QuotientGroup.mk' V) x ∈ N'
    rw [show (QuotientGroup.mk' V) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact N'.one_mem
  have hKnorm : K.Normal := Subgroup.Normal.comap hN'norm _
  haveI := hKnorm
  have hKpro : NK.LocalTame.IsProP p ↥K := by
    refine isProP_of_isProP_subgroupOf_quotient hVK hVp ?_
    have hiso : Nonempty ((↥K ⧸ V.subgroupOf K) ≃* ↥N') := by
      let f : ↥K →* ↥N' :=
        { toFun := fun x => ⟨(QuotientGroup.mk' V) x.1,
            Subgroup.mem_comap.mp (show x.1 ∈ N'.comap (QuotientGroup.mk' V) from x.2)⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
      have hf : Function.Surjective f := by
        intro n
        obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (n.1 : G ⧸ V)
        refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
        show (QuotientGroup.mk' V) g ∈ N'
        rw [QuotientGroup.mk'_apply, hg]
        exact n.2
      have hker : V.subgroupOf K = MonoidHom.ker f := by
        ext x
        rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · refine Subtype.ext ?_
          show (QuotientGroup.mk' V) x.1 = 1
          exact (QuotientGroup.eq_one_iff x.1).mpr hx
        · have h : (QuotientGroup.mk' V) x.1 = 1 := by
            have h' := Subtype.ext_iff.mp hx
            simpa [f] using h'
          exact (QuotientGroup.eq_one_iff x.1).mp h
      exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩
    obtain ⟨e⟩ := hiso
    exact (isProP_congr e p).mpr hN'pro
  have hKgt : ¬ K ≤ V := by
    intro hle
    apply hN'ne
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (n : G ⧸ V)
    have hgK : g ∈ K := by
      show (QuotientGroup.mk' V) g ∈ N'
      rw [QuotientGroup.mk'_apply, hg]
      exact hn
    have hgV : g ∈ V := hle hgK
    have h1 : QuotientGroup.mk g = 1 := (QuotientGroup.eq_one_iff g).mpr hgV
    rw [hg] at h1
    exact h1
  exact hKgt (hmax K hKnorm hKpro)

end NK.TameStructure.ProfiniteAux
