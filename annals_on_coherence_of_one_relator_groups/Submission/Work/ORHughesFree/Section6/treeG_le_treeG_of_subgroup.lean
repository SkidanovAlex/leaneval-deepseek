import Mathlib
import Submission.Work.ORHughesFree.Section6.SubgroupComplexity
import Submission.Work.ORHughesFree.Section6.TreeG
import Submission.Work.ORHughesFree.Section6.RatStruct
import Submission.Work.ORHughesFree.Section6.Phi_subgroup_mem
import Submission.Work.ORHughesFree.Section6.UnitsTimesEquiv
import Submission.Work.ORHughesFree.Rat.Restrict
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_mono

set_option autoImplicit false

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

/-! ### Two compatibilities of the group-like units

The two lemmas below identify, in `D_H = D_{K[↥H],U}`, the image of the group-like unit
`λ·h ∈ K[↥H]` with the image of the corresponding unit `λ·↑h ∈ K[G]`: this is what makes the
inclusion `D_H ↪ D_G` compatible with the two rational structures.  They are the only inputs of
`lift_ratStructSubgroup_ratUnitsTimesEquiv` besides `Rat.transport_*`.

Note the intentional use of `MonoidAlgebra.mapDomainRingHom K H.subtype` (rather than the
abbreviation `inducedMapRing H`) so that the type expressions agree with those of `DHU`,
`ratStructSubgroup`, `smulElem` and `toDG`. -/

/-- `inducedMapRing H` sends the group-like unit `λ·h` of `K[↥H]` to the group-like unit `λ·↑h`
of `K[G]`: `unitOf` is compatible with `unitsTimesMulEquiv`. -/
theorem inducedMapRing_unitOf {K : Type} [Field K] {G : Type} [Group G]
    (H : Subgroup G) (u : Kˣ × H) :
    inducedMapRing (K := K) H (unitOf u) =
      unitOf (unitsTimesMulEquiv (K := K) (G := G) H u) := by
  change MonoidAlgebra.mapDomain H.subtype (MonoidAlgebra.single u.2 (u.1 : K)) =
    MonoidAlgebra.single ((unitsTimesMulEquiv (K := K) (G := G) H u : Kˣ × G).2)
      (((unitsTimesMulEquiv (K := K) (G := G) H u : Kˣ × G).1 : K))
  rw [MonoidAlgebra.mapDomain_single, unitsTimesMulEquiv_apply]
  rfl

/-- The image of the group-like unit `λ·↑h ∈ K[G]` in `D_H` (via `smulElem`) agrees with the image
of `λ·h ∈ K[↥H]` computed in the rational `Kˣ × ↥H`-semiring structure `ratStruct` of `D_H`. -/
theorem smulElem_unitsTimesMulEquiv {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (u : Kˣ × H) :
    smulElem φ H (unitsTimesMulEquiv (K := K) (G := G) H u) =
      (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smul u 1 := by
  apply Subtype.ext
  rw [smulElem_coe, ratStruct_smul]
  simp only [RingHom.comp_apply, Subring.coe_one, mul_one]
  exact (congrArg φ (inducedMapRing_unitOf (K := K) H u)).symm

/-! ### The two halves of the compatibility square

`Phi φ ∘ ofSubgroup W = toDG φ H ∘ g` and `g ∘ ratUnitsTimesEquiv H = Phi (φ ∘ K[↥H] ↪ K[G])`,
where `W = unitsTimesSubgroup H` and `g = RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)`. -/

/-- `toDG φ H ∘ g = Phi φ ∘ ofSubgroup W`: the inclusion `D_H ↪ D_G` intertwines the universal
morphism of the subgroup `W = Kˣ × H` with the universal morphism of `Kˣ × G`. -/
theorem toDG_lift_ratStructSubgroup {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (β : RatU ↥(unitsTimesSubgroup (K := K) H)) :
    toDG φ H (RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) β)
      = Phi φ (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H) β) := by
  let W : Subgroup (Kˣ × G) := unitsTimesSubgroup (K := K) H
  let g : RatU ↥W →+* ↥(DHU φ H) := RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)
  have hhom : IsRationalUSemiringHom (RatU.rational)
      (RationalUSemiring.restrict W (ratStruct φ)) ((toDG φ H).comp g) :=
  { map_rat := fun x => by
      change toDG φ H (g (RatU.ratOp x)) =
        (RationalUSemiring.restrict W (ratStruct φ)).ratOp (toDG φ H (g x))
      rw [show g (RatU.ratOp x) = ratOpClosure (DHU φ H) (g x) from
        (RatU.lift_isHom (↥(DHU φ H)) (ratStructSubgroup φ H)).map_rat x]
      rw [toDG_ratOpClosure φ H (g x)]
      change ratOpClosure (DGU φ) (toDG φ H (g x)) =
        (ratStruct φ).ratOp (toDG φ H (g x))
      rw [ratStruct_ratOp]
    map_smul := fun u x => by
      change toDG φ H (g (RatU.smul u x)) =
        (RationalUSemiring.restrict W (ratStruct φ)).smul u (toDG φ H (g x))
      rw [show g (RatU.smul u x) = (ratStructSubgroup φ H).smul u (g x) from
        (RatU.lift_isHom (↥(DHU φ H)) (ratStructSubgroup φ H)).map_smul u x]
      change toDG φ H (smulElem φ H u * g x) =
        (RationalUSemiring.restrict W (ratStruct φ)).smul u (toDG φ H (g x))
      apply Subtype.ext
      simp only [Subring.coe_mul, toDG_coe, RationalUSemiring.restrict_smul, ratStruct_smul,
        smulElem_coe]
    map_smulRight := fun x u => by
      change toDG φ H (g (RatU.smulRight x u)) =
        (RationalUSemiring.restrict W (ratStruct φ)).smulRight (toDG φ H (g x)) u
      rw [show g (RatU.smulRight x u) = (ratStructSubgroup φ H).smulRight (g x) u from
        (RatU.lift_isHom (↥(DHU φ H)) (ratStructSubgroup φ H)).map_smulRight x u]
      change toDG φ H (g x * smulElem φ H u) =
        (RationalUSemiring.restrict W (ratStruct φ)).smulRight (toDG φ H (g x)) u
      apply Subtype.ext
      simp only [Subring.coe_mul, toDG_coe, RationalUSemiring.restrict_smulRight,
        ratStruct_smulRight, smulElem_coe] }
  have heq : (toDG φ H).comp g = (Phi φ).comp (RatU.ofSubgroup W) := by
    rw [RatU.lift_unique (↥(DGU φ)) (RationalUSemiring.restrict W (ratStruct φ)) _ hhom,
      Phi_comp_ofSubgroup φ W]
  have hb : toDG φ H (g β) = (Phi φ) (RatU.ofSubgroup W β) := by
    have h1 := congrFun (congrArg DFunLike.coe heq) β
    simpa using h1
  exact hb

/-- `g ∘ ratUnitsTimesEquiv H = Phi (φ ∘ K[↥H] ↪ K[G])`: the transport isomorphism
`Rat(Kˣ × H) ≃+* Rat(↥(Kˣ × H))` intertwines the two universal morphisms. -/
theorem lift_ratStructSubgroup_ratUnitsTimesEquiv {K : Type} [Field K] {G : Type} [Group G]
    {U : Type} [Ring U] (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (α : RatU (Kˣ × H)) :
    RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H α) =
      Phi (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype)) α := by
  have hB : IsRationalUSemiringHom (RatU.rational (U := Kˣ × H))
      (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype)))
      ((RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)).comp
        (ratUnitsTimesEquiv (K := K) H).toRingHom) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      change RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)
            (ratUnitsTimesEquiv (K := K) H (RatU.ratOp x)) =
          (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).ratOp
            (RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H x))
      have h1 : ratUnitsTimesEquiv (K := K) H (RatU.ratOp x) =
          RatU.ratOp (ratUnitsTimesEquiv (K := K) H x) :=
        Rat.transport_rat (unitsTimesMulEquiv (K := K) (G := G) H) x
      have h2 : RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)
            (RatU.ratOp (ratUnitsTimesEquiv (K := K) H x)) =
          (ratStructSubgroup φ H).ratOp
            (RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H x)) :=
        (RatU.lift_isHom (↥(DHU φ H)) (ratStructSubgroup φ H)).map_rat _
      rw [h1, h2]
      exact (ratStruct_ratOp (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype)) _).symm
    · intro u x
      change RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)
            (ratUnitsTimesEquiv (K := K) H (RatU.smul u x)) =
          (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smul u
            (RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H x))
      have h1 : ratUnitsTimesEquiv (K := K) H (RatU.smul u x) =
          RatU.smul (unitsTimesMulEquiv (K := K) (G := G) H u)
            (ratUnitsTimesEquiv (K := K) H x) :=
        Rat.transport_smul (unitsTimesMulEquiv (K := K) (G := G) H) u x
      have h2 : RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)
            (RatU.smul (unitsTimesMulEquiv (K := K) (G := G) H u)
              (ratUnitsTimesEquiv (K := K) H x)) =
          (ratStructSubgroup φ H).smul (unitsTimesMulEquiv (K := K) (G := G) H u)
            (RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H x)) :=
        (RatU.lift_isHom (↥(DHU φ H)) (ratStructSubgroup φ H)).map_smul _ _
      rw [h1, h2]
      rw [show (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smul u
            (RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H x)) =
          (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smul u 1 *
            RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H x) from
        (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smul_eq_mul u _]
      rw [← smulElem_unitsTimesMulEquiv φ H u]
      rfl
    · intro x u
      change RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)
            (ratUnitsTimesEquiv (K := K) H (RatU.smulRight x u)) =
          (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smulRight
            (RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H x)) u
      have h1 : ratUnitsTimesEquiv (K := K) H (RatU.smulRight x u) =
          RatU.smulRight (ratUnitsTimesEquiv (K := K) H x)
            (unitsTimesMulEquiv (K := K) (G := G) H u) :=
        Rat.transport_smulRight (unitsTimesMulEquiv (K := K) (G := G) H) x u
      have h2 : RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)
            (RatU.smulRight (ratUnitsTimesEquiv (K := K) H x)
              (unitsTimesMulEquiv (K := K) (G := G) H u)) =
          (ratStructSubgroup φ H).smulRight
            (RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H x))
            (unitsTimesMulEquiv (K := K) (G := G) H u) :=
        (RatU.lift_isHom (↥(DHU φ H)) (ratStructSubgroup φ H)).map_smulRight _ _
      rw [h1, h2]
      rw [show (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smulRight
            (RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H x)) u =
          RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H x) *
            (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smulRight 1 u from
        (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smulRight_eq_mul _ u]
      rw [show (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smulRight 1 u =
          (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smul u 1 from
        (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))).smulRight_one u]
      rw [← smulElem_unitsTimesMulEquiv φ H u]
      rfl
  calc RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H α)
      = ((RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)).comp
          (ratUnitsTimesEquiv (K := K) H).toRingHom) α := rfl
    _ = RatU.lift (↥(DHU φ H))
          (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))) α :=
        congrFun (congrArg DFunLike.coe
          (RatU.lift_unique (↥(DHU φ H))
            (ratStruct (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))) _ hB)) α
    _ = Phi (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype)) α := rfl

/-- **`Tree_G ≤ Tree_H`.**  For a subgroup `H ≤ G`, every `H`-realiser of `x` is a `G`-realiser
(via `RatU.ofSubgroup` and `Rat.treeOfRat_ofSubgroup`, which says that the complexity of an element
of `Rat(Kˣ × H)` is the same computed in `Rat(Kˣ × G)`), so the `G`-complexity of `x` is at most
its `H`-complexity.  (`range_inducedMapRing_le` says that the image of `K[↥H]` lies in the image of
`K[G]`, so that the division closure of `K[↥H]` is a subring of that of `K[G]`.  The two
presentations `Kˣ × H` and `↥(unitsTimesSubgroup H)` are related by
`UnitsTimesEquiv.ratUnitsTimesEquiv`, whose transport preserves `Rat.treeOfRat`.) -/
theorem treeG_le_treeG_of_subgroup {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (x : ↥(divisionClosure (Set.range (φ.comp (inducedMapRing (K := K) H))))) :
    Tree.le (treeG φ (⟨(x : U),
        Work.ORHughesFree.DivisionClosure.divisionClosure_mono (range_inducedMapRing_le φ H) x.2⟩ :
        ↥(divisionClosure (Set.range φ))))
      (treeG (φ.comp (inducedMapRing (K := K) H)) x) := by
  obtain ⟨⟨α, hα, hαtree⟩, _⟩ := treeG_spec (φ.comp (inducedMapRing (K := K) H)) x
  -- the `H`-realiser `α` gives the `G`-realiser `ofSubgroup (unitsTimesSubgroup H) (e α)`
  have hgα : RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H) (ratUnitsTimesEquiv (K := K) H α)
      = x := (lift_ratStructSubgroup_ratUnitsTimesEquiv φ H α).trans hα
  have hγ : Phi φ (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
        (ratUnitsTimesEquiv (K := K) H α))
      = (⟨(x : U), Work.ORHughesFree.DivisionClosure.divisionClosure_mono
          (range_inducedMapRing_le φ H) x.2⟩ : ↥(divisionClosure (Set.range φ))) := by
    rw [← toDG_lift_ratStructSubgroup φ H (ratUnitsTimesEquiv (K := K) H α)]
    rw [hgα]
    exact Subtype.ext (toDG_coe φ H x)
  -- hence `Tree_G x ≤ Tree (e α) = Tree α = Tree_H x`
  have hle := (treeG_spec φ (⟨(x : U),
      Work.ORHughesFree.DivisionClosure.divisionClosure_mono
        (range_inducedMapRing_le φ H) x.2⟩ : ↥(divisionClosure (Set.range φ)))).2
    (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H) (ratUnitsTimesEquiv (K := K) H α)) hγ
  rw [Rat.treeOfRat_ofSubgroup (unitsTimesSubgroup (K := K) H)
      (ratUnitsTimesEquiv (K := K) H α), treeOfRat_ratUnitsTimesEquiv (K := K) H α, hαtree] at hle
  exact hle

end Work.ORHughesFree.Section6
