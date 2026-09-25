import Mathlib
import Submission.NK.TameStructureDeep.Tame.TameInertiaCorrected
import Submission.NK.TameStructureDeep.Tame.wildInertiaSubgroup_eq_correctedWildInertia
import Submission.NK.TameStructureDeep.Tame.isProPrimeToP_correctedWildInertia
import Submission.NK.TameStructureDeep.Tame.inertiaQuotient
import Submission.NK.TameStructureDeep.Unramified
import Submission.NK.TameData.Definitions

/-!
# `TameInertiaInput` at a `𝔭`-adic completion

`NK.TameData.TameInertiaInput p κ K'` is the reduced form of the classical structure theorem
for the tamely ramified quotient `G_κ^{tr}` of the absolute Galois group of a `p`-adic field
(NSW, *Cohomology of Number Fields*, (7.5.7) Corollary and (7.5.11); Iwasawa).  Its four
arithmetic components are

* `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ/V_κ`;
* `I_κ/V_κ` is pro-prime-to-`p`;
* `[I_κ, I_κ] ≤ V_κ`;
* `G_κ ⧸ I_κ ≅ Ẑ`.

For `κ = K_𝔭` and `p = resCharAt 𝔭` all four are *theorems* of the tamely ramified layer
`Submission/Work/TameStructureDeep/Tame/`, proved for the **corrected** wild inertia
`V_κ = Gal(K'/κ^{tr}) = Tame.correctedWildInertia p π` (the fixing subgroup of the maximal tamely
ramified extension), while `TameInertiaInput` is stated for the *join*
`NK.LocalTame.wildInertiaSubgroup p = ⨆ {N ◁ G_κ : N pro-p}` of the normal pro-`p` subgroups.
The two agree — `Tame.wildInertiaSubgroup_eq_correctedWildInertia`, the classical identity
"the wild inertia is the maximal normal pro-`p` subgroup" — whence this file:

  `Tame.tameInertiaInput_adicCompletion_residueChar`: `TameInertiaInput (resCharAt 𝔭) (K_𝔭) K'`,
  with **no** hypothesis beyond `K'` being a separable closure of `K_𝔭`.

The only bookkeeping needed is the transport of the four statements from `correctedWildInertia p π`
to the join along that equality; the auxiliary lemma
`Tame.isProPrimeToP_quotientImage_eq` performs the (slightly delicate) transport of
`IsProPrimeToP` of the quotient image, where the ambient group `G_κ ⧸ V_κ` itself changes.

HISTORY: prior to `wildInertiaSubgroup_eq_correctedWildInertia`, `wildInertiaSubgroup` (the join)
was used both as the wild inertia and as the "corrected" one, and the join does *not* satisfy the
conjunct `V_κ ≤ I_κ` in general; the corrected definition was introduced to repair that.  This
file is the bridge between the two, and thereby the entry point of the whole tame layer into
`NK.TameData`.
-/

set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Tame

/-- **Transport of `IsProPrimeToP` of a quotient image along an equality of the subgroups.**
If `V = V'` are normal subgroups of `G`, then `I/V = I/V'` as abstract groups, so pro-prime-to-`p`
-ness of `↥(quotientImage V I)` is the same as that of `↥(quotientImage V' I)`.

The point is that the *ambient* group `G ⧸ V` changes with `V`, so the (definitionally distinct)
subgroups `quotientImage V I ≤ G ⧸ V` and `quotientImage V' I ≤ G ⧸ V'` have to be compared
through `QuotientGroup.congr V V' (MulEquiv.refl G)`, which is induced by the identity of `G`. -/
theorem isProPrimeToP_quotientImage_eq {G : Type*} [Group G] {V V' I : Subgroup G}
    [V.Normal] [V'.Normal] (h : V = V') (p : ℕ) :
    NK.LocalTame.IsProPrimeToP p ↥(NK.LocalTame.quotientImage V I) ↔
      NK.LocalTame.IsProPrimeToP p ↥(NK.LocalTame.quotientImage V' I) := by
  have hmap : V.map (MulEquiv.refl G : G →* G) = V' := by
    rw [show (MulEquiv.refl G : G →* G) = MonoidHom.id G from rfl, Subgroup.map_id]
    exact h
  let φ : G ⧸ V ≃* G ⧸ V' := QuotientGroup.congr V V' (MulEquiv.refl G) hmap
  -- `φ` is induced by the identity of `G`
  have hcomp1 : (φ : G ⧸ V →* G ⧸ V').comp (QuotientGroup.mk' V)
      = (QuotientGroup.mk' V').comp (MulEquiv.refl G : G →* G) := by
    ext x
    rfl
  have hcomp2 : (QuotientGroup.mk' V').comp (MulEquiv.refl G : G →* G) = QuotientGroup.mk' V' := by
    ext x
    rfl
  -- hence `φ` carries `I/V` to `I/V'`
  have key : (NK.LocalTame.quotientImage V I).map (φ : G ⧸ V →* G ⧸ V') =
      NK.LocalTame.quotientImage V' I := by
    rw [NK.LocalTame.quotientImage, NK.LocalTame.quotientImage, Subgroup.map_map, hcomp1,
      hcomp2]
  have e : ↥(NK.LocalTame.quotientImage V I) ≃* ↥(NK.LocalTame.quotientImage V' I) :=
    (MulEquiv.subgroupMap φ (NK.LocalTame.quotientImage V I)).trans
      (MulEquiv.subgroupCongr key)
  exact NK.LocalTame.isProPrimeToP_congr e p

/-- **`NK.TameData.TameInertiaInput` at every `𝔭`-adic completion.**

Every component is a theorem of the tamely ramified layer `Submission/Work/TameStructureDeep/Tame/`
for the corrected wild inertia `V_κ = Gal(K'/κ^{tr})`; here they are transported to the join
`NK.LocalTame.wildInertiaSubgroup p` along the identity
`Tame.wildInertiaSubgroup_eq_correctedWildInertia` (evaluated at any uniformiser `π` of `𝒪_κ`,
which exists since `𝒪_κ` is a discrete valuation ring, `Tame.exists_isUniformizerAt`).

* `isTameInertia`: `Tame.isMaxNormalProCyclicInQuotient_correctedWildInertia`, transported with
  `NK.LocalTame.Transfer.IsMaxNormalProCyclicInQuotient_map` along `MulEquiv.refl`;
* `isProPrimeToP_tameInertia`: `Tame.isProPrimeToP_correctedWildInertia`, transported with
  `Tame.isProPrimeToP_quotientImage_eq`;
* `tameInertia_commutator_mem`: `Tame.commutator_mem_correctedWildInertia` (the inertia fixes
  `κ^{ur}`, so the Kummer characters of `σ, τ` lie in `κ^{ur}` and are fixed), transported along
  the equality of subgroups;
* `unramifiedQuotient`: `NK.TameStructureDeep.unramifiedQuotient_adicCompletion`
  (`G_κ ⧸ I_κ ≅ Gal(κ^{ur}/κ) ≅ Ẑ`, the second isomorphism being the cyclotomic computation of
  `TameStructureDeep/Degree/`). -/
theorem tameInertiaInput_adicCompletion_residueChar {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] :
    NK.TameData.TameInertiaInput (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      (𝔭.adicCompletion K) K' := by
  obtain ⟨π, hπ⟩ := NK.TameStructureDeep.Tame.exists_isUniformizerAt 𝔭
  have hp : (NK.TameStructureDeep.Tame.resCharAt 𝔭).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hπ0 : (π : 𝔭.adicCompletion K) ≠ 0 :=
    NK.TameStructureDeep.Tame.uniformizer_ne_zero 𝔭 hπ
  haveI hnorm : (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K)
      (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).Normal :=
    NK.TameStructureDeep.Tame.correctedWildInertia_normal
      (p := NK.TameStructureDeep.Tame.resCharAt 𝔭) hp hπ0
  have hV : NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) =
      NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K) :=
    NK.TameStructureDeep.Tame.wildInertiaSubgroup_eq_correctedWildInertia 𝔭 hπ
  refine ⟨hp, ?_, ?_, ?_, ?_⟩
  · -- `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ/V_κ`
    have hmax : NK.LocalTame.IsMaxNormalProCyclicInQuotient
        (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K))
        (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭)) :=
      NK.TameStructureDeep.Tame.isMaxNormalProCyclicInQuotient_correctedWildInertia 𝔭 hπ
    have hmap : Subgroup.map
        (MulEquiv.refl (Gal(K'/𝔭.adicCompletion K)) : Gal(K'/𝔭.adicCompletion K) →* _)
        (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)) =
        NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) := by
      rw [show (MulEquiv.refl (Gal(K'/𝔭.adicCompletion K)) :
          Gal(K'/𝔭.adicCompletion K) →* _) = MonoidHom.id _ from rfl, Subgroup.map_id]
      exact hV.symm
    have hres := NK.LocalTame.Transfer.IsMaxNormalProCyclicInQuotient_map hmax
      (MulEquiv.refl (Gal(K'/𝔭.adicCompletion K))) hmap
    rwa [show (MulEquiv.refl (Gal(K'/𝔭.adicCompletion K)) :
        Gal(K'/𝔭.adicCompletion K) →* _) = MonoidHom.id _ from rfl, Subgroup.map_id] at hres
  · -- `I_κ/V_κ` is pro-prime-to-`p`
    have hmain : NK.LocalTame.IsProPrimeToP (NK.TameStructureDeep.Tame.resCharAt 𝔭)
        ↥(NK.LocalTame.quotientImage
          (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
            (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K))
          (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
            (NK.TameStructureDeep.Tame.resCharAt 𝔭))) :=
      NK.TameStructureDeep.Tame.isProPrimeToP_correctedWildInertia 𝔭 hπ
    exact (isProPrimeToP_quotientImage_eq hV (NK.TameStructureDeep.Tame.resCharAt 𝔭)).mpr hmain
  · -- `[I_κ, I_κ] ≤ V_κ`
    intro y hy z hz
    have hy' : y ∈ (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)).fixingSubgroup := by
      rw [← NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
        (κ := 𝔭.adicCompletion K) (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭)]
      exact hy
    have hz' : z ∈ (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)).fixingSubgroup := by
      rw [← NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
        (κ := 𝔭.adicCompletion K) (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭)]
      exact hz
    have hcom := NK.TameStructureDeep.Tame.commutator_mem_correctedWildInertia
      (κ := 𝔭.adicCompletion K) (K' := K') (p := NK.TameStructureDeep.Tame.resCharAt 𝔭)
      hp.ne_one (π := (π : 𝔭.adicCompletion K)) y z hy' hz'
    rwa [← hV] at hcom
  · -- `G_κ ⧸ I_κ ≅ Ẑ`
    exact NK.TameStructureDeep.unramifiedQuotient_adicCompletion (K := K) 𝔭

end NK.TameStructureDeep.Tame
