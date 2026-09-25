import Mathlib
import Submission.Work.Tower.FrattiniLayer.Basic
import Submission.Work.Tower.FrattiniLayer.isUnramifiedOver_of_algEquiv
import Submission.Work.Tower.FrattiniLayer.baseChange_unramified

/-!
# Universality of the Frattini layer

The Frattini layer `frattiniLayer F Ω` is the compositum (computed in `Ω`) of all cubic
everywhere unramified Galois extensions of `F`.  Its defining property is that *every* finite
everywhere unramified abelian extension `E'/F` of exponent `3` embeds into it over `F`
(`frattiniLayer_universal`): `E'` is the compositum of its cubic subextensions, each of which is
a cubic everywhere unramified Galois extension of `F` and hence contributes to the Frattini
layer.

The statement is proved by picking an `F`-embedding `φ : E' →ₐ[F] Ω` and observing that the
(decreasing, by Galois theory) correspondence `H ↦ fixedField H` turns a decomposition
`⨅ H i = ⊥` of `Gal(E'/F)` into finitely many subgroups of index `3` into the equality
`E' = ⨆ i, fixedField (H i)`; each `fixedField (H i)` is cubic and everywhere unramified, so its
image in `Ω` lies in the Frattini layer, and images commute with `iSup`.

## Main results

* `elementaryAbelian_iInf_index_three_eq_bot`: a finite abelian group of exponent dividing `3`
  is the intersection of finitely many subgroups of index `3`.
* `iSup_fixedField_eq_top_of_iInf_eq_bot`, `finrank_fixedField_of_index_three`: the two pieces
  of the Galois correspondence used above.
* `frattiniLayer_universal`: the universality statement itself.
-/

set_option linter.style.haveILetI false

open NumberField
open scoped Classical

namespace Work.Tower.FrattiniLayer

/-- **A finite abelian group of exponent dividing `3` is the intersection of finitely many
subgroups of index `3`.**  Indeed such a group is a finite product of copies of `ℤ/3ℤ`; the
kernels of the coordinate projections then do the job.

(Stated for `[Group G] [IsMulCommutative G]` rather than `[CommGroup G]` so that it applies
verbatim to `Gal(E'/F)`, whose group structure is `AlgEquiv.aut`.) -/
theorem elementaryAbelian_iInf_index_three_eq_bot {G : Type*} [Group G] [IsMulCommutative G]
    [Finite G] (hexp : ∀ g : G, g ^ 3 = 1) :
    ∃ (ι : Type) (_ : Fintype ι) (H : ι → Subgroup G),
      (∀ i, (H i).index = 3) ∧ ⨅ i, H i = ⊥ := by
  classical
  letI : CommGroup G :=
    { toGroup := (inferInstance : Group G)
      mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  haveI : Fintype ι := hι
  -- The exponent condition forces every factor to be `ℤ/3ℤ`.
  have hn3 : ∀ i, n i = 3 := by
    intro i
    let x : (j : ι) → Multiplicative (ZMod (n j)) :=
      Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (n i)))
    have hx : (e.symm x) ^ 3 = 1 := hexp _
    have hx' : x ^ 3 = 1 := by
      have h := congrArg e hx
      simp only [map_pow, MulEquiv.apply_symm_apply, map_one] at h
      exact h
    have hcoord : (Multiplicative.ofAdd (1 : ZMod (n i))) ^ 3 = 1 := by
      have h := congr_fun hx' i
      simpa [x] using h
    have h7 : Multiplicative.ofAdd (3 • (1 : ZMod (n i))) = 1 := by
      rw [ofAdd_nsmul, hcoord]
    have h8 : (3 : ZMod (n i)) = 0 := by
      have h9 := ofAdd_eq_one.mp h7
      rwa [show (3 : ZMod (n i)) = 3 • (1 : ZMod (n i)) by simp]
    have h10 : n i ∣ 3 := (ZMod.natCast_eq_zero_iff 3 (n i)).mp h8
    rcases (Nat.dvd_prime Nat.prime_three).mp h10 with h | h
    · have := hn i; omega
    · exact h
  -- The coordinate projections and their kernels.
  let π : (i : ι) → G →* Multiplicative (ZMod (n i)) :=
    fun i => (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i).comp e.toMonoidHom
  have hπ : ∀ i, Function.Surjective (π i) := by
    intro i y
    exact ⟨e.symm (Pi.mulSingle (M := fun i => Multiplicative (ZMod (n i))) i y), by simp [π]⟩
  refine ⟨ι, hι, fun i => (π i).ker, ?_, ?_⟩
  · intro i
    rw [Subgroup.index_eq_card]
    refine (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (π i) (hπ i)).toEquiv).trans ?_
    rw [hn3 i]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  · apply le_antisymm _ bot_le
    intro g hg
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_iInf] at hg
    apply e.injective
    funext i
    have hgi : π i g = 1 := by simpa using hg i
    simpa [π] using hgi

/-- **Galois correspondence, supremum form.**  If a finite Galois extension `E/F` is generated
by the fixed fields of a family of subgroups whose intersection is trivial, then it is their
compositum: `E = ⨆ i, fixedField (H i)`. -/
theorem iSup_fixedField_eq_top_of_iInf_eq_bot {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] {ι : Type*} (H : ι → Subgroup (E ≃ₐ[F] E))
    (hH : ⨅ i, H i = ⊥) :
    (⨆ i, IntermediateField.fixedField (H i)) = ⊤ := by
  have h1 : (⨆ i, IntermediateField.fixedField (H i))
      = IsGalois.intermediateFieldEquivSubgroup.symm (⨆ i, OrderDual.toDual (H i)) := by
    rw [OrderIso.map_iSup]
    simp
  rw [h1, show (⨆ i, OrderDual.toDual (H i)) = OrderDual.toDual (⨅ i, H i) from by
      apply OrderDual.ofDual.injective
      simp]
  rw [hH]
  simp

/-- **Galois correspondence, degree count.**  The fixed field of a subgroup of index `3` of the
Galois group of a finite Galois extension `E/F` is an extension of `F` of degree `3`. -/
theorem finrank_fixedField_of_index_three {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (H : Subgroup (E ≃ₐ[F] E)) (hH : H.index = 3) :
    Module.finrank F ↥(IntermediateField.fixedField H) = 3 := by
  have key : Module.finrank F ↥(IntermediateField.fixedField H) * Nat.card ↥H
      = Nat.card ↥H * 3 := by
    calc Module.finrank F ↥(IntermediateField.fixedField H) * Nat.card ↥H
        = Module.finrank F ↥(IntermediateField.fixedField H)
            * Module.finrank ↥(IntermediateField.fixedField H) E := by
          rw [IntermediateField.finrank_fixedField_eq_card]
      _ = Module.finrank F E := Module.finrank_mul_finrank F ↥(IntermediateField.fixedField H) E
      _ = Nat.card (E ≃ₐ[F] E) := (IsGalois.card_aut_eq_finrank F E).symm
      _ = Nat.card ↥H * H.index := (Subgroup.card_mul_index H).symm
      _ = Nat.card ↥H * 3 := by rw [hH]
  exact Nat.mul_right_cancel Nat.card_pos (by rw [key, mul_comm])

/-- **The Frattini layer is universal for elementary abelian everywhere unramified extensions.**
Every finite Galois extension `E'/F` which is everywhere unramified, abelian and of exponent
dividing `3` admits an `F`-algebra homomorphism into the Frattini layer `frattiniLayer F Ω`:
`E'` is the compositum of its (finitely many) cubic subextensions, each of which is everywhere
unramified and contributes to the Frattini layer. -/
theorem frattiniLayer_universal {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω]
    (E' : Type*) [Field E'] [NumberField E'] [Algebra F E'] [FiniteDimensional F E']
    [IsGalois F E'] (hunr : Work.Tower.FrattiniLayer.IsUnramifiedOver F E')
    (hab : IsAbelianGalois F E') (hexp : ∀ σ : E' ≃ₐ[F] E', σ ^ 3 = 1) :
    Nonempty (E' →ₐ[F] ↥(Work.Tower.FrattiniLayer.frattiniLayer F Ω)) := by
  haveI : Algebra.IsAlgebraic F E' := Algebra.IsAlgebraic.of_finite F E'
  -- An `F`-embedding of `E'` into the algebraically closed field `Ω`.
  let φ : E' →ₐ[F] Ω := IsAlgClosed.lift
  -- The Galois group is an elementary abelian `3`-group: decompose it into index-`3` subgroups.
  haveI : IsMulCommutative (E' ≃ₐ[F] E') := hab.toIsMulCommutative
  obtain ⟨I, hI, H, hHidx, hHinf⟩ :=
    elementaryAbelian_iInf_index_three_eq_bot (G := E' ≃ₐ[F] E') hexp
  haveI : Fintype I := hI
  -- The corresponding cubic subextensions of `E'`.
  let K : I → IntermediateField F E' := fun i => IntermediateField.fixedField (H i)
  haveI hKgal : ∀ i, IsGalois F ↥(K i) := fun i => by
    haveI : (H i).Normal := Subgroup.normal_of_isMulCommutative (H i)
    exact IsGalois.of_fixedField_normal_subgroup (H i)
  have hKfin : ∀ i, Module.finrank F ↥(K i) = 3 := fun i =>
    finrank_fixedField_of_index_three (H i) (hHidx i)
  have hKunr : ∀ i, Work.Tower.FrattiniLayer.IsUnramifiedOver F ↥(K i) := fun i =>
    (isUnramifiedOver_tower (E := K i) hunr).1
  -- They generate `E'`.
  have hsup : (⨆ i, K i) = ⊤ := iSup_fixedField_eq_top_of_iInf_eq_bot H hHinf
  -- Their images in `Ω` are cubic everywhere unramified extensions of `F`, hence lie in the
  -- Frattini layer.
  have hImmem : ∀ i, IntermediateField.map φ (K i) ∈ cubicUnramifiedSet F Ω := fun i => by
    haveI : IsGalois F ↥(K i) := hKgal i
    refine ⟨?_, ?_, ?_⟩
    · rw [← LinearEquiv.finrank_eq (IntermediateField.equivMap (K i) φ).toLinearEquiv]
      exact hKfin i
    · exact IsGalois.of_algEquiv (IntermediateField.equivMap (K i) φ)
    · exact isUnramifiedOver_of_algEquiv (IntermediateField.equivMap (K i) φ) (hKunr i)
  have hImle : ∀ i, IntermediateField.map φ (K i) ≤ frattiniLayer F Ω := fun i =>
    le_iSup (fun M : ↥(cubicUnramifiedSet F Ω) => (M : IntermediateField F Ω))
      ⟨IntermediateField.map φ (K i), hImmem i⟩
  -- Images commute with `iSup`, so the image of `E'` also lies in the Frattini layer.
  have htop : IntermediateField.map φ (⊤ : IntermediateField F E') ≤ frattiniLayer F Ω := by
    rw [← hsup, (IntermediateField.gc_map_comap φ).l_iSup]
    exact iSup_le hImle
  refine ⟨φ.codRestrict (frattiniLayer F Ω).toSubalgebra fun x => ?_⟩
  exact htop ((IntermediateField.mem_map (⊤ : IntermediateField F E')).mpr ⟨x, trivial, rfl⟩)

end Work.Tower.FrattiniLayer
