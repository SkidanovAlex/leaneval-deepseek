import Mathlib
import Submission.NK.BrauerHasse.Profinite
import Submission.NK.BrauerHasse.All
import Submission.NK.HassePrinciple.finite_levelGroup

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

/-- Given a Sylow `p`-subgroup `Q` of the finite level group `U/(U ⊓ Gal(K'/L))`, there is a subgroup
`V ≤ U` whose level group `V/(V ⊓ Gal(K'/L))` is isomorphic to `Q`, namely the preimage of `Q` in `U`;
moreover the level-wise restriction `levelInclHom hV L : V/(V ⊓ Gal(K'/L)) →* U/(U ⊓ Gal(K'/L))` has
range exactly `Q`. -/
theorem exists_subgroup_levelGroup_equiv_sylow {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {p : ℕ} [Fact p.Prime]
    (U : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (Q : Sylow p (NK.BrauerHasse.LevelGroup U L)) :
    ∃ (V : Subgroup Gal(K'/K)) (hV : V ≤ U),
      Nonempty (NK.BrauerHasse.LevelGroup V L ≃* Q) ∧
        MonoidHom.range (NK.BrauerHasse.levelInclHom hV L) = Q.toSubgroup := by
  -- The quotient map `U → U/(U ∩ Gal(K'/L))` and the preimage `W ≤ U` of the Sylow subgroup `Q`.
  let φ : ↥U →* NK.BrauerHasse.LevelGroup U L :=
    QuotientGroup.mk' (L.fixingSubgroup.subgroupOf U)
  let W : Subgroup ↥U := Q.toSubgroup.comap φ
  -- `V` is the preimage of `Q` in `U`, viewed as a subgroup of `Gal(K'/K)`.
  let V : Subgroup Gal(K'/K) := W.map U.subtype
  have hV : V ≤ U := Subgroup.map_subtype_le W
  -- The composite `V → U → U/(U ∩ Gal(K'/L))`.
  let χ : ↥V →* NK.BrauerHasse.LevelGroup U L := φ.comp (Subgroup.inclusion hV)
  -- The image of `V` in `U` is exactly `W`.
  have hrange_incl : (Subgroup.inclusion hV).range = W := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp v.2
      have hthis : (Subgroup.inclusion hV) v = w := by
        apply Subtype.ext
        rw [Subgroup.coe_inclusion]
        exact hwv.symm
      rw [hthis]
      exact hw
    · intro hx
      refine ⟨⟨(x : Gal(K'/K)), Subgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
  -- The range of `χ` is exactly `Q`.
  have hrangeχ : χ.range = Q.toSubgroup := by
    rw [show χ = φ.comp (Subgroup.inclusion hV) from rfl, MonoidHom.range_comp, hrange_incl]
    exact Subgroup.map_comap_eq_self
      (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]; exact le_top)
  -- The kernel of `χ` is `Gal(K'/L) ∩ V`, so that `χ` descends to `V/(V ∩ Gal(K'/L))`.
  have hkerχ : χ.ker = L.fixingSubgroup.subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, show χ x = φ (Subgroup.inclusion hV x) from rfl, ← MonoidHom.mem_ker,
        QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Subgroup.coe_inclusion]
  -- The range of `levelInclHom` agrees with that of `χ` (both are images of `↥V`).
  have hrangeL : (NK.BrauerHasse.levelInclHom hV L).range = χ.range := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (L.fixingSubgroup.subgroupOf V) z
      exact ⟨v, by rw [NK.BrauerHasse.levelInclHom, QuotientGroup.map_mk']; rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨QuotientGroup.mk' _ v,
        by rw [NK.BrauerHasse.levelInclHom, QuotientGroup.map_mk']; rfl⟩
  refine ⟨V, hV, ⟨?_⟩, ?_⟩
  · -- Noether's first isomorphism theorem for `χ`, transported to `V/(V ∩ Gal(K'/L))`.
    exact (QuotientGroup.quotientMulEquivOfEq hkerχ.symm).trans
      ((QuotientGroup.quotientKerEquivRange χ).trans (MulEquiv.subgroupCongr hrangeχ))
  · rw [hrangeL, hrangeχ]

end NK.HassePrinciple
