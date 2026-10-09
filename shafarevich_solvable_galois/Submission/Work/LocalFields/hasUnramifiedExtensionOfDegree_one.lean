import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Inputs
import Submission.Work.LocalFields.finrank_residueField_eq_one_of_surjective
import Submission.Work.LocalFields.comap_ringEquiv_uniformSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unramified extension of degree one

This file proves `Work.LocalFields.hasUnramifiedExtensionOfDegree_one`: every non-archimedean
local field `k` (in the sense of `Work.LocalFields.IsLocalField`) has a unique unramified
extension of degree one.

## A remark on the definition of `HasUnramifiedExtensionOfDegree`

`Work.LocalFields.HasUnramifiedExtensionOfDegree k n` quantifies its witness at universe level
`0` — its body is `∃ (l : Type) …, Module.finrank k l = n ∧ …` — while `k` itself is polymorphic
(`k : Type u`).  Consequently the case `n = 1` is *not* merely the trivial observation that `k` is
its own unramified extension of degree one: a witness `l : Type 0` with `Algebra k l` and
`Module.finrank k l = 1` is a *small model* of `k` (the algebra map `k → l` is injective because
`l` is a field, so `k` has to be `Small.{0}` for such a witness to exist at all), and the entire
local-field structure has to be transported across the universe-lowering equivalence.

Both halves of that are carried out below.

* `small_of_isLocalField` — every `IsLocalField` is a small type.  `IsLocalField` gives
  `ProperSpace k` for the normed field structure induced by the valuation, hence
  `SecondCountableTopology k`, hence `TopologicalSpace.SeparableSpace k`, and a separable metric
  space embeds isometrically into `ℓ^∞(ℕ, ℝ)`, a small type.
* The small model `Shrink k` is then equipped with the transferred field, algebra, valuation and
  uniform structures, and the transported data (integral ring, residue field, rank-one valuation,
  completeness, compactness) is checked to satisfy `IsLocalField`, `IsLocalFieldExtension`,
  `IsGalois`, `FiniteDimensional` and `IsUnramifiedLocalExtension`.

`small_of_hasUnramifiedExtensionOfDegree_one` records the implication "the statement implies
`Small.{0} k`" explicitly.

If `HasUnramifiedExtensionOfDegree` is ever changed so that the witness lives in the same universe
as `k` (`∃ (l : Type u) …`) — which is what the downstream uses (completions of number fields,
which are types in the same universe as the number field) can always provide — then the case
`n = 1` becomes immediate: take `l := k` with the identity algebra structure, the identity
`HasExtension` (`Valuation.HasExtension.id`), and note that the induced map of residue fields is
bijective (it is the identity, by `IsLocalRing.ResidueField.algebraMap_residue` together with
surjectivity of `IsLocalRing.residue`), so `finrank (𝓀[k]) (𝓀[k]) = 1` follows from
`Work.LocalFields.finrank_residueField_eq_one_of_surjective`.
-/

namespace Work.LocalFields

open scoped Valued

-- `Shrink k` carries a topology transferred from `k`
-- (`Shrink.instTopologicalSpace`, `Mathlib/Topology/Instances/Shrink.lean`).  We describe the
-- topology of the small model below through the valuation instead, and deactivate that instance
-- (within this file only) so that no two competing `TopologicalSpace (Shrink k)` instances are
-- in play.
attribute [-instance] Shrink.instTopologicalSpace

noncomputable section

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/-- The uniformity of a `Valued` structure is determined by its valuation. -/
theorem toUniformSpace_eq_of_v_eq {R : Type*} [Ring R] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (w w' : Valued R Γ₀) (h : w.v = w'.v) :
    w.toUniformSpace = w'.toUniformSpace := by
  rw [@Valued.toUniformSpace_eq R _ Γ₀ _ w, @Valued.toUniformSpace_eq R _ Γ₀ _ w', h]

/-- Every non-archimedean local field, in the sense of `Work.LocalFields.IsLocalField`, is a
*small* type: it is a separable metric space, hence embeds isometrically into `ℓ^∞(ℕ, ℝ)`. -/
theorem small_of_isLocalField {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
    [IsLocalField k] : Small.{0} k := by
  obtain ⟨f, hf⟩ := KuratowskiEmbedding.exists_isometric_embedding k
  exact small_of_injective hf.injective

/-- The statement of `hasUnramifiedExtensionOfDegree_one`, for a local field of arbitrary
universe, *implies* that `k` is a small type: a witness `l : Type 0` for
`HasUnramifiedExtensionOfDegree k 1` carries an injective ring map `k → l` (the algebra structure
map, injective because `l` is a field). -/
theorem small_of_hasUnramifiedExtensionOfDegree_one {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [IsLocalField k]
    (h : HasUnramifiedExtensionOfDegree k 1) : Small.{0} k := by
  obtain ⟨l, hlF, hlV, hlL, hlA, hlE, hlFD, hlG, -, -, -⟩ := h
  letI := hlF; letI := hlV; letI := hlL; letI := hlA; letI := hlE; letI := hlFD; letI := hlG
  exact small_of_injective (FaithfulSMul.algebraMap_injective k l)

/-- **The unramified extension of degree one.** -/
theorem hasUnramifiedExtensionOfDegree_one {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [Work.LocalFields.IsLocalField k] :
    Work.LocalFields.HasUnramifiedExtensionOfDegree k 1 := by
  letI hsmall : Small.{0} k := small_of_isLocalField
  -- the small model of `k`, with field and algebra structures transferred along `equivShrink`
  -- (these are the instances `Shrink.instField`, `Shrink.instAlgebra`)
  let l := Shrink.{0} k
  let e : k ≃ l := equivShrink k
  let he : l ≃ k := e.symm
  letI hFieldL : Field l := he.field
  letI hAlgL : Algebra k l := he.algebra k
  have hmap : (algebraMap k l : k → l) = e := by
    funext r
    rw [Equiv.algebraMap_def]
    rfl
  have hfin : Module.finrank k l = 1 := by
    apply Module.finrank_of_bijective_algebraMap
    rw [hmap]
    exact e.bijective
  -- the ring isomorphism `l ≃+* k` underlying `e`, and the valuation it induces on `l`
  let hring : l ≃+* k := he.ringEquiv
  let v_l : Valuation l (WithZero (Multiplicative ℤ)) :=
    (Valued.v (R := k)).comap (hring : l →+* k)
  letI hValL : Valued l (WithZero (Multiplicative ℤ)) := Valued.mk' v_l
  have hval_apply : ∀ x : l, Valued.v (R := l) x = Valued.v (R := k) (hring x) := fun _ => rfl
  have hring_apply : ∀ x : k, hring (e x) = x := fun x =>
    (Equiv.ringEquiv_apply he (e x)).trans (Equiv.symm_apply_apply e x)
  have hval_alg : ∀ z : k, Valued.v (R := l) (algebraMap k l z) = Valued.v (R := k) z := by
    intro z
    rw [congrFun hmap z, hval_apply, hring_apply]
  -- the valuation of `l` extends the valuation of `k`
  have hExt : (Valued.v (R := k)).HasExtension (Valued.v (R := l)) := by
    refine ⟨fun x y => ?_⟩
    simp only [Valuation.comap_apply]
    rw [hval_alg x, hval_alg y]
  letI hHasExt : (Valued.v (R := k)).HasExtension (Valued.v (R := l)) := hExt
  -- the value groups of the two valuations agree
  have hvm : valueMonoid (v_l : l →*₀ WithZero (Multiplicative ℤ)) = valueMonoid ((Valued.v (R := k)) : k →*₀ WithZero (Multiplicative ℤ)) := by
    ext b
    rw [mem_valueMonoid_iff, mem_valueMonoid_iff]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨hring x, by rw [← hx]; rfl⟩
    · rintro ⟨y, hy⟩
      refine ⟨hring.symm y, ?_⟩
      have h1 : (v_l : l →*₀ WithZero (Multiplicative ℤ)) (hring.symm y) = ((Valued.v (R := k)) : k →*₀ WithZero (Multiplicative ℤ)) y := by
        rw [show (v_l : l →*₀ WithZero (Multiplicative ℤ)) (hring.symm y) = v_l (hring.symm y) from rfl,
          show v_l (hring.symm y) = Valued.v (R := k) (hring (hring.symm y)) from rfl,
          show hring (hring.symm y) = y from RingEquiv.apply_symm_apply hring y,
          show Valued.v (R := k) y = ((Valued.v (R := k)) : k →*₀ WithZero (Multiplicative ℤ)) y from rfl]
      rw [h1, hy]
  have hvg : valueGroup (v_l : l →*₀ WithZero (Multiplicative ℤ)) = valueGroup ((Valued.v (R := k)) : k →*₀ WithZero (Multiplicative ℤ)) := by
    rw [valueGroup_def, valueGroup_def, hvm]
  -- the valuation of `l` has rank one
  have hRankOne : Nonempty (Valued.v (R := l)).RankOne := by
    haveI : IsCyclic (valueGroup (v_l : l →*₀ WithZero (Multiplicative ℤ))) := inferInstance
    haveI : Nontrivial (valueGroup (v_l : l →*₀ WithZero (Multiplicative ℤ))) := by rw [hvg]; infer_instance
    haveI : Valuation.IsRankOneDiscrete v_l := inferInstance
    exact ⟨Valuation.IsRankOneDiscrete.rankOne (v := v_l) (e := 2) one_lt_two⟩
  -- the `Valued` uniformity on `l` is the pullback of the one on `k` along `hring`
  have hUniformity : (Valued.mk' v_l).toUniformSpace =
      UniformSpace.comap (hring : l → k) (Valued.mk' (Valued.v (R := k))).toUniformSpace :=
    comap_ringEquiv_uniformSpace hring (Valued.v (R := k))
  have hUniformity' : (Valued.mk' v_l).toUniformSpace =
      UniformSpace.comap (hring : l → k) (inferInstance : UniformSpace k) := by
    rw [hUniformity, toUniformSpace_eq_of_v_eq (Valued.mk' (Valued.v (R := k)))
      (inferInstance : Valued k (WithZero (Multiplicative ℤ))) rfl]
  have hUnifInd : IsUniformInducing (hring : l → k) := by
    refine ⟨?_⟩
    have h : uniformity l =
        (uniformity k).comap (fun x : l × l => (hring x.1, hring x.2)) := by
      rw [hUniformity']
      rfl
    rw [h]
  -- continuity of the two directions of the equivalence
  have hcont_e : Continuous (e : k → l) := by
    have h2 : UniformContinuous (hring ∘ (e : k → l)) := by
      have h3 : (hring ∘ (e : k → l)) = (id : k → k) := funext hring_apply
      rw [h3]
      exact uniformContinuous_id
    exact ((IsUniformInducing.uniformContinuous_iff (f := (e : k → l)) (g := (hring : l → k))
      hUnifInd).mpr h2).continuous
  -- completeness of the small model: the `Valued` uniformity of `l` is (via `Valued.mk'`) the
  -- canonical uniformity of `v_l`, which by `hUniformity'` is the pullback of the uniformity of
  -- `k`, and `hring` is a bijection
  have hComplete : CompleteSpace l := by
    refine hUnifInd.completeSpace ?_
    rw [Set.range_eq_univ.mpr hring.surjective]
    exact completeSpace_iff_isComplete_univ.mp inferInstance
  -- compactness of the ring of integers of the small model.  Here we use the topology on
  -- `Shrink k` transferred from `k` (so that `l`'s topology is the topology induced by `hring`),
  -- together with the description of the integer rings by the valuation.
  have hCompact : CompactSpace ↥(Valued.integer l) := by
    rw [← isCompact_univ_iff]
    have hmem : ∀ y : ↥(Valued.v (R := k)).integer,
        Valued.v (R := l) (e y.1) ≤ 1 := by
      intro y
      rw [hval_apply (e y.1), hring_apply]
      exact (Valuation.mem_integer_iff _ _).mp y.2
    let Ψ : ↥(Valued.v (R := k)).integer → ↥(Valued.v (R := l)).integer :=
      fun y => ⟨e y.1, (Valuation.mem_integer_iff _ _).mpr (hmem y)⟩
    have hcontΨ : Continuous Ψ := by
      refine Continuous.subtype_mk ?_ _
      exact hcont_e.comp continuous_subtype_val
    have hsurjΨ : Function.Surjective Ψ := by
      intro x
      refine ⟨⟨hring x.1, (Valuation.mem_integer_iff _ _).mpr ?_⟩, ?_⟩
      · rw [← hval_apply x.1]
        exact (Valuation.mem_integer_iff _ _).mp x.2
      · refine Subtype.ext ?_
        show e (hring x.1) = x.1
        rw [show hring x.1 = he x.1 from rfl]
        exact Equiv.apply_symm_apply e x.1
    have himage : Ψ '' Set.univ = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ.mpr hsurjΨ]
    rw [← himage]
    exact IsCompact.image isCompact_univ hcontΨ
  letI hLocalL : IsLocalField l :=
    { rankOne := hRankOne, complete := hComplete, compactInteger := hCompact }
  letI hLFEL : IsLocalFieldExtension k l := ⟨hExt⟩
  -- the residue field extension has degree one
  have hInt_surj : Function.Surjective
      (algebraMap ↥(Valued.v (R := k)).integer ↥(Valued.v (R := l)).integer) := by
    intro y
    have hy : Valued.v (R := l) y.1 ≤ 1 := (Valuation.mem_integer_iff _ _).mp y.2
    refine ⟨⟨hring y.1, (Valuation.mem_integer_iff _ _).mpr ?_⟩, ?_⟩
    · rw [← hval_apply y.1]
      exact hy
    · refine Subtype.ext ?_
      rw [Valuation.HasExtension.val_algebraMap, congrFun hmap (hring y.1),
        show hring y.1 = he y.1 from rfl]
      exact Equiv.apply_symm_apply e y.1
  have hres : Module.finrank (Valued.ResidueField k) (Valued.ResidueField l) = 1 :=
    finrank_residueField_eq_one_of_surjective hInt_surj
  have hUnram : IsUnramifiedLocalExtension k l := by
    rw [IsUnramifiedLocalExtension, hres]
    exact hfin.symm
  letI hFinL : FiniteDimensional k l := Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
  letI hGalL : IsGalois k l := IsGalois.of_algEquiv (Equiv.algEquiv k he).symm
  have huniq : ∀ (l' : Type) (_ : Field l') (_ : Valued l' (WithZero (Multiplicative ℤ)))
      (_ : IsLocalField l') (_ : Algebra k l') (_ : IsLocalFieldExtension k l')
      (_ : FiniteDimensional k l') (_ : IsGalois k l'),
      Module.finrank k l' = 1 → IsUnramifiedLocalExtension k l' → Nonempty (l ≃ₐ[k] l') := by
    intro l' _ _ _ _ _ _ _ hfin' _
    obtain ⟨el⟩ := (Module.nonempty_algEquiv_iff_finrank_eq_one (R := k) (S := l)).mpr hfin
    obtain ⟨el'⟩ := (Module.nonempty_algEquiv_iff_finrank_eq_one (R := k) (S := l')).mpr hfin'
    exact ⟨el.symm.trans el'⟩
  exact ⟨l, hFieldL, hValL, hLocalL, hAlgL, hLFEL, hFinL, hGalL, hfin, hUnram, huniq⟩

end

-- restore the instance attribute removed above, so that importers of this module are unaffected
attribute [instance] Shrink.instTopologicalSpace

end Work.LocalFields
