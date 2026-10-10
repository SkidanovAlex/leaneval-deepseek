import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.classIncl_isCanonical
import Submission.Work.SSGRoute.phi_pair_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Level naturality of the pairing `phiAt` (the `λ`-coherence of `E5s`)

This file supplies, for the `Ω`-indexed dévissage `Work.SSGRoute.phi1_mono_step_in` (node `E5s` of
`DESIGN_FIX.md` §1), the **naturality of the level pairing under inflation**, i.e. the statement
that the family `L ↦ (h ↦ φ(y)(h))` attached to a class `y ∈ Ext¹_G(S.X₃, C_K)` is compatible with
inflation along the finite Galois levels `K ≤ L ≤ L' ≤ Ω`.

The mathematical content is the compatibility of the *canonical* inclusions of idèle class groups

  `classIncl k K L : res_{Gal(L/k)} C_K ⟶ C_L`

across three levels `K ≤ L ≤ L'`, which is the transitivity of `C_K → C_L → C_{L'}`.  It is proved
in the standard form:

* `place_liesOver_trans` — the place below a place in a tower is transitive (so the place-theoretic
  data of the composite is again `LiesOver`-data);
* `completionMap_comp_infinite` — the local completion maps at infinite places compose;
* `localAlgebraMapUnits_comp` — the local unit maps `K_vˣ → L_wˣ → M_{w'}ˣ` compose;
* `isCanonicalClassIncl_unique` — the canonical inclusion is unique (a place of a number field
  determines the place below it, and an idèle class determines its idèle);
* `isCanonical_isCanonicalClassIncl_comp` — hence the composite `C_K → C_L → C_{L'}` *is*
  `classIncl k K L'`; this is `classIncl_compat` below.

The four lemmas above are the ingredients of `classIncl_compat` (`C_K → C_L → C_{L'}` is
`C_K → C_{L'}`), which is what remains to be assembled from them: one has to compare the composite
with `classIncl k K L'` *as morphisms of representations*, i.e. transport the (definitionally
distinct, propositionally equal) sources

  `res_{Gal(L'/k)} (res_{Gal(L/k)} C_K)`   and   `res_{Gal(L'/k)} C_K`

along the canonical isomorphism `resResHom` of `PTDefs`.  The place-theoretic input
(`place_liesOver_trans`), the local input (`localAlgebraMapUnits_comp`) and the uniqueness input
(`isCanonicalClassIncl_unique`) are all proved below; only the `eqToHom` bookkeeping of that
transport is missing, and it is the reason this file stops here.

None of this uses the (still missing) bridge `E0b` between `groupCohomology` and `Ext`, nor `E4Ω`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory NK.GlobalCFT NumberField

/-! ## Transitivity of the place relation, and composition of the local maps -/

/-- **Transitivity of `Place.LiesOver` in a tower of number fields.**  If `w'` is a place of `M`
lying over `w : Place L` and `w` lies over `v : Place K`, for number fields `K ⊆ L ⊆ M`, then `w'`
lies over `v`.  (The infinite case is the transitivity of the restriction of an absolute value, the
finite case the transitivity of `Ideal.LiesOver`.) -/
theorem place_liesOver_trans {K L M : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {v : Place K} {w : Place L} {w' : Place M} (h1 : w'.LiesOver w) (h2 : w.LiesOver v) :
    w'.LiesOver v := by
  rcases h1 with ⟨w₁, w₀, rfl, rfl, hL1⟩ | ⟨q₁, q₀, rfl, rfl, hL1⟩
  · rcases h2 with ⟨w₂, v₀, hw, hv, hL2⟩ | ⟨q₂, Q₀, hq, hQ, hL2⟩
    · rw [Place.ofInfinite_inj] at hw
      subst hw
      subst hv
      exact Or.inl ⟨_, _, rfl, rfl, Norm.liesOver_trans hL1 hL2⟩
    · exact absurd hq Sum.inl_ne_inr
  · rcases h2 with ⟨w₂, v₀, hw, hv, hL2⟩ | ⟨q₂, Q₀, hq, hQ, hL2⟩
    · exact absurd hw Sum.inr_ne_inl
    · rw [Place.ofFinite_inj] at hq
      subst hq
      subst hQ
      exact Or.inr ⟨_, _, rfl, rfl, Ideal.LiesOver.trans q₁.asIdeal q₀.asIdeal Q₀.asIdeal⟩

/-- **Composition of the completion maps at infinite places.**  For a tower of number fields
`K ⊆ L ⊆ M` and infinite places `v ≤ w ≤ w'`, the canonical embeddings of the completions compose:
`K_v → L_w → M_{w'}` is `K_v → M_{w'}`, the composite of the isometries `K → L → M`. -/
theorem completionMap_comp_infinite {K L M : Type} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {v : NumberField.InfinitePlace K} {w : NumberField.InfinitePlace L}
    {w' : NumberField.InfinitePlace M} [w.LiesOver v] [w'.LiesOver w] [w'.LiesOver v] :
    (NumberField.LiesOver.completionMap (v := w) (w := w')).comp
        (NumberField.LiesOver.completionMap (v := v) (w := w)) =
      NumberField.LiesOver.completionMap (v := v) (w := w') := by
  refine RingHom.ext fun x => ?_
  induction x using NumberField.InfinitePlace.Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (NumberField.LiesOver.continuous_completionMap (v := w) (w := w')).comp
          (NumberField.LiesOver.continuous_completionMap (v := v) (w := w))
      · exact NumberField.LiesOver.continuous_completionMap (v := v) (w := w')
  | ih a =>
      rw [RingHom.comp_apply, NumberField.LiesOver.completionMap_coe,
        NumberField.LiesOver.completionMap_coe, NumberField.LiesOver.completionMap_coe]
      apply congrArg (fun z : WithAbs w'.1 => (z : w'.Completion))
      apply WithAbs.ofAbs_injective
      simp only [WithAbs.ofAbs_algebraMap, IsScalarTower.algebraMap_apply K L M]


/-- **Composition of the local unit maps.**  For a tower of number fields `K ⊆ L ⊆ M` and places
`v ≤ w ≤ w'`, the canonical local embeddings of the unit groups compose:
`K_vˣ → L_wˣ → M_{w'}ˣ` is `K_vˣ → M_{w'}ˣ`.  (Archimedean places: the completion maps compose,
`completionMap_comp_infinite`; nonarchimedean places: `adicCompletionMap_comp`; the remaining mixed
cases are impossible, a place of an extension over an infinite place being infinite.) -/
theorem localAlgebraMapUnits_comp {K L M : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] {v : Place K} {w : Place L} {w' : Place M} (h1 : w'.LiesOver w)
    (h2 : w.LiesOver v) (h3 : w'.LiesOver v) :
    (Place.localAlgebraMapUnits w' w h1).comp (Place.localAlgebraMapUnits w v h2) =
      Place.localAlgebraMapUnits w' v h3 := by
  rcases v with v₀ | Q₀ <;> rcases w with w₀ | q₀ <;> rcases w' with w₁ | q₁
  · -- archimedean
    have h1' : w₁.LiesOver w₀ := by
      rcases h1 with ⟨a, b, e1, e2, hL⟩ | ⟨q, Q, e1, e2, hL⟩
      · rw [Place.ofInfinite_inj] at e1 e2; subst e1; subst e2; exact hL
      · exact absurd e1 Sum.inl_ne_inr
    have h2' : w₀.LiesOver v₀ := by
      rcases h2 with ⟨a, b, e1, e2, hL⟩ | ⟨q, Q, e1, e2, hL⟩
      · rw [Place.ofInfinite_inj] at e1 e2; subst e1; subst e2; exact hL
      · exact absurd e1 Sum.inl_ne_inr
    have h3' : w₁.LiesOver v₀ := by
      rcases h3 with ⟨a, b, e1, e2, hL⟩ | ⟨q, Q, e1, e2, hL⟩
      · rw [Place.ofInfinite_inj] at e1 e2; subst e1; subst e2; exact hL
      · exact absurd e1 Sum.inl_ne_inr
    haveI := h1'; haveI := h2'; haveI := h3'
    simp only [Place.localAlgebraMapUnits, dif_pos h1', dif_pos h2', dif_pos h3']
    rw [← Units.map_comp]
    congr 1
    exact congrArg RingHom.toMonoidHom
      (completionMap_comp_infinite (v := v₀) (w := w₀) (w' := w₁))
  · exfalso
    exact Place.not_isFinite_ofInfinite w₀
      ((Place.isFinite_of_liesOver h1).mp (Place.isFinite_ofFinite q₁))
  · exfalso
    exact Place.not_isFinite_ofInfinite v₀
      ((Place.isFinite_of_liesOver h2).mp (Place.isFinite_ofFinite q₀))
  · exfalso
    exact Place.not_isFinite_ofInfinite v₀
      ((Place.isFinite_of_liesOver h2).mp (Place.isFinite_ofFinite q₀))
  · exfalso
    exact Place.not_isFinite_ofInfinite w₀
      ((Place.isFinite_of_liesOver h2).mpr (Place.isFinite_ofFinite Q₀))
  · exfalso
    exact Place.not_isFinite_ofInfinite w₀
      ((Place.isFinite_of_liesOver h1).mp (Place.isFinite_ofFinite q₁))
  · exfalso
    exact Place.not_isFinite_ofInfinite w₁
      ((Place.isFinite_of_liesOver h3).mpr (Place.isFinite_ofFinite Q₀))
  · -- nonarchimedean
    have h1' : q₁.asIdeal.LiesOver q₀.asIdeal := by
      rcases h1 with ⟨a, b, e1, e2, hL⟩ | ⟨q, Q, e1, e2, hL⟩
      · exact absurd e1 Sum.inr_ne_inl
      · rw [Place.ofFinite_inj] at e1 e2; subst e1; subst e2; exact hL
    have h2' : q₀.asIdeal.LiesOver Q₀.asIdeal := by
      rcases h2 with ⟨a, b, e1, e2, hL⟩ | ⟨q, Q, e1, e2, hL⟩
      · exact absurd e1 Sum.inr_ne_inl
      · rw [Place.ofFinite_inj] at e1 e2; subst e1; subst e2; exact hL
    have h3' : q₁.asIdeal.LiesOver Q₀.asIdeal := by
      rcases h3 with ⟨a, b, e1, e2, hL⟩ | ⟨q, Q, e1, e2, hL⟩
      · exact absurd e1 Sum.inr_ne_inl
      · rw [Place.ofFinite_inj] at e1 e2; subst e1; subst e2; exact hL
    haveI := h1'; haveI := h2'; haveI := h3'
    simp only [Place.localAlgebraMapUnits, dif_pos h1', dif_pos h2', dif_pos h3']
    rw [← Units.map_comp]
    congr 1
    exact congrArg RingHom.toMonoidHom
      (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp Q₀ q₀ q₁ h2' h1' h3')

/-! ## Uniqueness of the canonical inclusion of class groups -/

/-- **The canonical inclusion of idèle class groups is unique.**  A place of a finite extension
determines the place below it (`NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique`), hence the
idèle-level map, hence the induced map of class groups (the idèle class group is a quotient of the
idèles). -/
theorem isCanonicalClassIncl_unique {k K L : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K]
    (ι ι' : Rep.res (galRes k K L) (classesK k K) ⟶ classesK k L)
    (h : IsCanonicalClassIncl k K L ι) (h' : IsCanonicalClassIncl k K L ι') : ι = ι' := by
  obtain ⟨u, hu, φ, hφ, hι⟩ := h
  obtain ⟨u', hu', φ', hφ', hι'⟩ := h'
  have hu_eq : u = u' := funext fun w => Inclusion.globalCFT_liesOver_unique (hu w) (hu' w)
  have hφ_eq : φ = φ' := by
    subst hu_eq
    refine MonoidHom.ext fun x => Idele.ext fun w => ?_
    rw [hφ x w, hφ' x w]
  have hfun : ∀ y : ↥(classesK k K), ι.hom y = ι'.hom y := by
    intro y
    obtain ⟨z, hz⟩ : ∃ z : Idele K, y = Additive.ofMul (IdeleClassGroup.mk K z) := by
      obtain ⟨z, hz⟩ := IdeleClassGroup.mk_surjective K (Additive.toMul y)
      exact ⟨z, by change Additive.toMul y = IdeleClassGroup.mk K z; exact hz.symm⟩
    rw [hz]
    have hA : (Rep.Hom.hom ι) (Additive.ofMul (IdeleClassGroup.mk K z))
        = (Additive.ofMul (IdeleClassGroup.mk L (φ z)) : ↥(classesK k L)) := hι z
    have hB : (Additive.ofMul (IdeleClassGroup.mk L (φ z)) : ↥(classesK k L))
        = (Additive.ofMul (IdeleClassGroup.mk L (φ' z)) : ↥(classesK k L)) := by rw [hφ_eq]
    have hC : (Rep.Hom.hom ι') (Additive.ofMul (IdeleClassGroup.mk K z))
        = (Additive.ofMul (IdeleClassGroup.mk L (φ' z)) : ↥(classesK k L)) := hι' z
    exact hA.trans (hB.trans hC.symm)
  apply Rep.hom_ext
  ext y
  exact hfun y



end Work.SSGRoute
