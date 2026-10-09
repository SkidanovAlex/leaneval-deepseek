import Mathlib.RingTheory.Norm.Transitivity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Galois

/-- **Abstract group-theoretic bound.**  For group homomorphisms `f : G →* H` and `g : H →* J`
whose cokernels `H ⧸ f.range` and `J ⧸ g.range` are finite, the cokernel of the composite
`g ∘ f` has cardinal at most the product of those two cokernels:
`|J ⧸ (g ∘ f).range| ≤ |H ⧸ f.range| · |J ⧸ g.range|`.

Indeed `(g ∘ f).range = (f.range).map g ≤ g.range`, and the relative index of these two
subgroups of `J` is bounded by the index of `f.range`, i.e. by `|H ⧸ f.range|`; the remaining
factor is `|J ⧸ g.range|`. -/
theorem natCard_quotient_range_comp_le_mul {G H J : Type*} [Group G] [Group H] [Group J]
    (f : G →* H) (g : H →* J)
    (h1 : Finite (J ⧸ g.range)) (h2 : Finite (H ⧸ f.range)) :
    Nat.card (J ⧸ (g.comp f).range) ≤
      Nat.card (H ⧸ f.range) * Nat.card (J ⧸ g.range) := by
  let M : Subgroup H := f.range
  let NK : Subgroup J := g.range
  let NE : Subgroup J := (g.comp f).range
  have : Finite (H ⧸ M) := h2
  have : Finite (J ⧸ NK) := h1
  have hMfin : M.FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (Subgroup.index_ne_zero_of_finite (H := M))
  haveI : M.FiniteIndex := hMfin
  have hNE : NE = M.map g := MonoidHom.range_comp g f
  have hle : NE ≤ NK := by rw [hNE]; exact Subgroup.map_le_range g M
  have hrel : NE.relIndex NK ≤ M.index := by
    have hcomap : NE.relIndex NK = (Subgroup.comap g NE).index :=
      (Subgroup.index_comap NE g).symm
    rw [hcomap, hNE, Subgroup.comap_map_eq]
    exact Subgroup.index_antitone le_sup_left
  calc Nat.card (J ⧸ NE)
      = NE.index := (Subgroup.index_eq_card NE).symm
    _ = NE.relIndex NK * NK.index := (Subgroup.relIndex_mul_index hle).symm
    _ = NE.relIndex NK * Nat.card (J ⧸ NK) := by rw [Subgroup.index_eq_card NK]
    _ ≤ M.index * Nat.card (J ⧸ NK) := Nat.mul_le_mul_right _ hrel
    _ = Nat.card (H ⧸ M) * Nat.card (J ⧸ NK) := by rw [Subgroup.index_eq_card M]

/-- The norm maps of a tower of finite-dimensional field extensions `F ⊆ K ⊆ E` are
transitive on units, so the unit norm `Eˣ →* Fˣ` is the composite of the two intermediate ones. -/
theorem norm_unit_comp_norm_unit {F K E : Type*} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E] :
    (Units.map (Algebra.norm F : K →* F)).comp (Units.map (Algebra.norm K : E →* K)) =
      Units.map (Algebra.norm F : E →* F) := by
  have hcomp : (Algebra.norm F : E →* F) =
      (Algebra.norm F : K →* F).comp (Algebra.norm K : E →* K) := by
    ext x
    simp only [MonoidHom.comp_apply]
    exact (Algebra.norm_norm (a := x)).symm
  rw [← Units.map_comp, hcomp]

/-- For a tower of finite-dimensional field extensions `F ⊆ K ⊆ E`, if the two norm quotients
`Fˣ ⧸ N_{K/F}(Kˣ)` and `Kˣ ⧸ N_{E/K}(Eˣ)` are finite, then the norm quotient
`Fˣ ⧸ N_{E/F}(Eˣ)` of the big extension has cardinal at most the product:
`|Fˣ ⧸ N_{E/F}(Eˣ)| ≤ |Kˣ ⧸ N_{E/K}(Eˣ)| · |Fˣ ⧸ N_{K/F}(Kˣ)|`. -/
theorem natCard_quotient_units_range_norm_le_mul_tower {F K E : Type*} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [FiniteDimensional F K] [FiniteDimensional K E]
    (h1 : Finite (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : K →* F))))
    (h2 : Finite (Kˣ ⧸ MonoidHom.range (Units.map (Algebra.norm K : E →* K)))) :
    Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F))) ≤
      Nat.card (Kˣ ⧸ MonoidHom.range (Units.map (Algebra.norm K : E →* K))) *
      Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : K →* F))) := by
  have key := natCard_quotient_range_comp_le_mul
    (Units.map (Algebra.norm K : E →* K)) (Units.map (Algebra.norm F : K →* F)) h1 h2
  rwa [norm_unit_comp_norm_unit] at key

end Commons.FieldTheory.Galois