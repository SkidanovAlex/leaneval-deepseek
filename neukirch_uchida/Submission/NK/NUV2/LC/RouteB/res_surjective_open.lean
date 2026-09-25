import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs

namespace NK.NUV2.LC.RouteB

universe u

/-- **The level-group inclusion is surjective as soon as `U ≤ V · Gal(K'/L)`.**  If every element of
`U` can be written as `v · n` with `v ∈ V` and `n ∈ Gal(K'/L)`, then every class of
`U/(U ⊓ Gal(K'/L))` is the class of an element of `V`.

(Local copy of `NK.NUV2.LC.RouteB.levelInclHom_surjective_of_le_sup_fixingSubgroup`; it is
self-contained and we do not want to depend on the in-flux sibling module.) -/
lemma levelInclHom_surjective_of_le_sup_fixingSubgroup' {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (hU : U ≤ V ⊔ L.fixingSubgroup) :
    Function.Surjective (NK.BrauerHasse.levelInclHom h L) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H u =>
    obtain ⟨v, hv, n, hn, hvn⟩ := Subgroup.mem_sup_of_normal_right.mp (hU u.2)
    refine ⟨QuotientGroup.mk ⟨v, hv⟩, ?_⟩
    rw [NK.BrauerHasse.levelInclHom, QuotientGroup.map_mk]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    show v⁻¹ * (u : Gal(K'/K)) ∈ L.fixingSubgroup
    rw [← hvn]
    have h2 : v⁻¹ * (v * n) = n := by group
    rw [h2]
    exact hn

/-- Helper: the intersection `(C ⊔ Gal(K'/L)) ⊓ U` is an open subgroup of `Gal(K'/K)` whenever `U`
is open (it contains the open subgroup `Gal(K'/L) ⊓ U`). -/
lemma isOpen_sup_fixingSubgroup_inf {K K' : Type u} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {C U : Subgroup Gal(K'/K)}
    (L : FiniteGaloisIntermediateField K K') (hU : IsOpen (U : Set Gal(K'/K))) :
    IsOpen (((C ⊔ L.fixingSubgroup) ⊓ U : Subgroup Gal(K'/K)) : Set Gal(K'/K)) := by
  have hN : IsOpen (L.fixingSubgroup : Set Gal(K'/K)) :=
    IntermediateField.fixingSubgroup_isOpen (L : IntermediateField K K')
  refine Subgroup.isOpen_of_mem_nhds ((C ⊔ L.fixingSubgroup) ⊓ U) (g := 1) ?_
  refine Filter.mem_of_superset
    ((hU.inter hN).mem_nhds (⟨U.one_mem, L.fixingSubgroup.one_mem⟩ :
      (1 : Gal(K'/K)) ∈ (U : Set Gal(K'/K)) ∩ (L.fixingSubgroup : Set Gal(K'/K)))) ?_
  intro x hx
  exact ⟨(le_sup_right : L.fixingSubgroup ≤ C ⊔ L.fixingSubgroup) hx.2, hx.1⟩

/-- **Route B, lemma (L1)(a) (continuity of `H²(·, Z/p)`).**

`NK.BrauerHasse.H2Profinite p C` is the filtered colimit of the finite level cohomologies
`H²(C/(C ∩ Gal(K'/L)), Z/p)` along the inflation maps, and `NK.NUV2.LC.RouteB.res` is the
restriction map.  Given `C ≤ U` with `U` open, every class of `H²(C, Z/p)` is the restriction of a
class of `H²(C', Z/p)` for some **open** `C'` with `C ≤ C' ≤ U`.

Proof sketch: write `x = ofLevel L a`; choose the open `C' = (C ⊔ Gal(K'/L)) ⊓ U`.  Then
`C' ∩ Gal(K'/L) = C ∩ Gal(K'/L)`-in-the-quotient, i.e. `levelInclHom (C ≤ C') L` is an isomorphism
of level groups (it is injective always and surjective because `C' ≤ C ⊔ Gal(K'/L)`), so `H2.map` of
it is an isomorphism and `a` has a preimage `b` at level `L` of `C'`; `res (ofLevel L b) = x` by
`NK.NUV2.LC.RouteB.res_ofLevel`. -/
theorem res_surjective_open (p : ℕ) {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {C U : Subgroup Gal(K'/K)}
    (hU : IsOpen (U : Set Gal(K'/K))) (hCU : C ≤ U) (x : NK.BrauerHasse.H2Profinite p C) :
    ∃ (C' : Subgroup Gal(K'/K)) (hopen : IsOpen (C' : Set Gal(K'/K))) (h1 : C ≤ C') (h2 : C' ≤ U),
      ∃ y : NK.BrauerHasse.H2Profinite p C',
        NK.NUV2.LC.RouteB.res (K := K) (K' := K') p h1 y = x := by
  -- every class is represented at a finite Galois level
  obtain ⟨L, a, rfl⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective x
  -- the level at which the lift is manufactured
  refine ⟨(C ⊔ L.fixingSubgroup) ⊓ U, isOpen_sup_fixingSubgroup_inf L hU,
    le_inf le_sup_left hCU, inf_le_right, ?_⟩
  -- the level-group inclusion is bijective: injective in general, surjective since
  -- `(C ⊔ Gal(K'/L)) ⊓ U ≤ C ⊔ Gal(K'/L)`
  have hbij : Function.Bijective
      (NK.BrauerHasse.levelInclHom (le_inf le_sup_left hCU :
        C ≤ (C ⊔ L.fixingSubgroup) ⊓ U) L) :=
    ⟨NK.HassePrinciple.levelInclHom_injective _ L,
      levelInclHom_surjective_of_le_sup_fixingSubgroup' _ L inf_le_left⟩
  -- hence `H2.map` of it is surjective, and `a` has a preimage `b` at the same level
  obtain ⟨b, hb⟩ := NK.HassePrinciple.h2Map_surjective_of_bijective (p := p) _ hbij a
  refine ⟨NK.BrauerHasse.H2Profinite.ofLevel L b, ?_⟩
  rw [res_ofLevel]
  exact congrArg (NK.BrauerHasse.H2Profinite.ofLevel L) hb

end NK.NUV2.LC.RouteB
