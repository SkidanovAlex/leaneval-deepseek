import Mathlib
import Submission.NK.HassePrinciple.Obstruction
import Submission.NK.BrauerHasse.Profinite

namespace NK.HassePrinciple

open CategoryTheory

set_option autoImplicit false

universe u

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## Naturality of the level-wise localisation in the subgroup

For an inclusion `V ≤ U` of subgroups of `Gal(K'/K)` and a place `A` of `K'`, the local level
group `(V ⊓ D_A)/((V ⊓ D_A) ∩ Gal(K'/L))` maps to `(U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))`, and the
two ways round the square

```
(V ⊓ D_A)/(...)  --localInclHom-->  V/(V ∩ Gal(K'/L))
      |                                       |
localLevelInclHom                      levelInclHom
      v                                       v
(U ⊓ D_A)/(...)  --localInclHom-->  U/(U ∩ Gal(K'/L))
```

agree.  This is the level-wise form of the fact that the localisation is natural in the subgroup:
the level-wise restriction of global classes corresponds to the level-wise restriction, at each
place, of the local ones. -/

/-- The inclusion-induced quotient map on the *local* level groups
`(V ⊓ D_A)/((V ⊓ D_A) ∩ Gal(K'/L)) →* (U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))` for `V ≤ U`. -/
noncomputable def localLevelInclHom {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K') :
    LocalLevelGroup V A L →* LocalLevelGroup U A L :=
  QuotientGroup.map (L.fixingSubgroup.subgroupOf (V ⊓ stabSubgroup A))
    (L.fixingSubgroup.subgroupOf (U ⊓ stabSubgroup A))
    (Subgroup.inclusion (inf_le_inf_right (stabSubgroup A) hV))
    (fun x hx => by simpa using hx)

/-- The square expressing that the inclusion of the local level groups is compatible with the
inclusions of the local level groups in the global ones: restricting an element of an intermediate
subgroup and then passing to the global level agrees with passing to the global level of the larger
subgroup after including the local level groups. -/
lemma levelInclHom_comp_localInclHom {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K') :
    (levelInclHom hV L).comp (localInclHom V A L) =
      (localInclHom U A L).comp (localLevelInclHom hV A L) := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

/-- **Naturality of the level-wise localisation in the subgroup.**  For `V ≤ U` the restriction
`H2.map (levelInclHom hV L)` of the global level followed by the level-wise localisation at `A` is
the level-wise localisation at `A` of the larger subgroup followed by the map induced by the
inclusion of the local level groups. -/
lemma levelInclHom_locLevel (p : ℕ) {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K') :
    H2.map (levelInclHom hV L) ≫ locLevel p V A L =
      locLevel p U A L ≫ H2.map (localLevelInclHom hV A L) := by
  simp only [locLevel, ← H2.map_comp, levelInclHom_comp_localInclHom]

/-- Elementwise form of `levelInclHom_locLevel`. -/
lemma levelInclHom_locLevel_apply (p : ℕ) {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (a : LevelH2 p U L) :
    (locLevel p V A L) ((H2.map (levelInclHom hV L)).hom a) =
      (H2.map (localLevelInclHom hV A L)).hom ((locLevel p U A L) a) := by
  have hnat := congrArg
    (fun (k : H2 p (LevelGroup U L) ⟶ H2 p (LocalLevelGroup V A L)) => k.hom a)
    (levelInclHom_locLevel (K := K) (K' := K') p hV A L)
  simpa only [ModuleCat.comp_apply] using hnat

/-- The level obstruction is a subsystem with respect to restriction: the level-wise restriction
`H2.map (levelInclHom hV L)` along an inclusion `V ≤ U` carries the level obstruction of `(U,L)` into
the level obstruction of `(V,L)`.  (Naturality of the level-wise localisation `locLevel` in the
subgroup: `locLevel p V A L ∘ res = (localisation of the inclusion of local level groups) ∘ locLevel
p U A L`.) -/
theorem levelInclHom_mem_levelObstruction {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    {a : NK.BrauerHasse.LevelH2 p U L}
    (ha : a ∈ NK.HassePrinciple.levelObstruction p U L) :
    (NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom hV L)).hom a ∈
      NK.HassePrinciple.levelObstruction p V L := by
  rw [mem_levelObstruction_iff] at ha ⊢
  intro A
  rw [levelInclHom_locLevel_apply p hV A.1 L a, ha A, map_zero]

end NK.HassePrinciple
