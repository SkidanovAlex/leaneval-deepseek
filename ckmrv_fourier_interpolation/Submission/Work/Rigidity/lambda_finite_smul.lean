import Mathlib
import Submission.Work.Rigidity.LambdaFiberDefs

/-!
# Finiteness of the `Γ(2)`-elements carrying one compact set into another

`Γ(2) = CongruenceSubgroup.Gamma 2` is a subgroup of finite index of `SL(2, ℤ)`, hence
its image in `GL(2, ℝ)` is an arithmetic subgroup, and arithmetic subgroups act properly
discontinuously on the upper half-plane.  Consequently only finitely many `γ ∈ Γ(2)` can
map a point of a compact set `K` into a compact set `K'`.

The proof goes through the arithmetic subgroup `𝒢 = Γ(2).map (mapGL ℝ)` of `GL(2, ℝ)`:
proper discontinuity of the action of `𝒢` gives finiteness of
`{g : GL(2,ℝ) | g ∈ 𝒢 ∧ (g • K ∩ K').Nonempty}`, and `SL(2,ℤ) → GL(2,ℝ)` is injective with
`γ • z = (mapGL ℝ γ) • z`, so the corresponding set of `γ ∈ Γ(2)` is its finite preimage.
-/

open scoped MatrixGroups Pointwise

namespace Work.Rigidity

/-- Only finitely many `γ ∈ Γ(2)` move a compact piece of `ℍ` onto another compact piece. -/
theorem lambda_finite_smul (K K' : Set UpperHalfPlane) (hK : IsCompact K) (hK' : IsCompact K') :
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ |
        γ ∈ CongruenceSubgroup.Gamma 2 ∧ ∃ z ∈ K, γ • z ∈ K'}.Finite := by
  -- Finiteness for the arithmetic group `𝒢 = Γ(2) ⊂ GL(2, ℝ)` acting on `ℍ`.
  have hfin : {g : GL (Fin 2) ℝ |
      g ∈ ((CongruenceSubgroup.Gamma 2) : Subgroup (GL (Fin 2) ℝ)) ∧
      (g • K ∩ K').Nonempty}.Finite :=
    (Subgroup.properlyDiscontinuousSMul_iff
      (((CongruenceSubgroup.Gamma 2) : Subgroup (GL (Fin 2) ℝ)))).mp
      inferInstance hK hK'
  -- Pull back along the injective map `SL(2, ℤ) → GL(2, ℝ)`.
  have hinj : Set.InjOn (Matrix.SpecialLinearGroup.mapGL ℝ)
      ((Matrix.SpecialLinearGroup.mapGL ℝ) ⁻¹' {g : GL (Fin 2) ℝ |
        g ∈ ((CongruenceSubgroup.Gamma 2) : Subgroup (GL (Fin 2) ℝ)) ∧
        (g • K ∩ K').Nonempty}) :=
    Set.injOn_of_injective (f := Matrix.SpecialLinearGroup.mapGL ℝ)
      (Matrix.SpecialLinearGroup.mapGL_injective (n := Fin 2) (R := ℤ) (S := ℝ))
  refine Set.Finite.subset (Set.Finite.preimage (f := Matrix.SpecialLinearGroup.mapGL ℝ) hinj hfin) ?_
  intro γ hγ
  obtain ⟨hγG, z, hzK, hzK'⟩ := hγ
  exact ⟨Subgroup.mem_map_of_mem _ hγG,
    ⟨(Matrix.SpecialLinearGroup.mapGL ℝ γ) • z, ⟨z, hzK, rfl⟩, hzK'⟩⟩

end Work.Rigidity
