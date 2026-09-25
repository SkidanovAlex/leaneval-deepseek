import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.RankTheoryDeep.All

/-!
# `NK.NUV2.ideleLeopoldt_two_of_halves`

The *two halves* of the idèle-side rank formula for `ℓ = 2`: the lower bound
`r_ℂ(K) + 1 ≤ rank_{ℤ_2} Hom_cts(C_K, ℤ_2)` (CoNF (10.3.20)) together with the monotonicity of the
defect `rank_{ℤ_2} Hom_cts(C_K, ℤ_2) - r_ℂ(K)` (CoNF (10.3.7) Cor.) produce a *single* monotone
function `δ` with

  `rank_{ℤ_2} Hom_cts(C_K, ℤ_2) = r_ℂ(K) + 1 + δ K`

for every number field `K ⊆ Ω`.  This is the *pinning* of the Leopoldt defect: the formula itself
forces

  `δ K = rank_{ℤ_2} Hom_cts(C_K, ℤ_2) - r_ℂ(K) - 1`   (`K` a number field),

and the two halves are exactly what is needed to see that this is a well-behaved `ℕ`-valued
function.

## Where the content is, and where it is not

Both hypotheses and the conclusion quantify over `K : IntermediateField ℚ Ω` carrying a
`NumberField ↥K` instance: they are statements about the *number subfields* of `Ω`.  The extension
of the pinned defect to a total function on all intermediate fields is therefore pure bookkeeping —
`δ` is set to `0` at the (infinitely many) intermediate fields that are not number fields, and
those values are never compared with anything.  The mathematical content of the lemma is fully
contained in its two hypotheses: subtracting the *same* `1` from both sides of the monotonicity
hypothesis `hmono` (Legendre/Leopoldt defect monotonicity) gives monotonicity of the pinned defect
on number fields, and `hbound` makes the truncated subtraction `rank - r_ℂ - 1` exact, so that the
rank formula holds with `δ` as pinned.
-/

namespace NK.NUV2

open Classical

/-- The Leopoldt defect at `ℓ = 2`, pinned by the rank formula (CoNF (10.3.20)):
`δ K = rank_{ℤ_2} Hom_cts(C_K, ℤ_2) - r_ℂ(K) - 1` for a number field `K`, and the junk value `0` at
an intermediate field that is not a number field. -/
noncomputable def ideleLeopoldtDelta (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (K : IntermediateField ℚ Ω) : ℕ :=
  if h : NumberField ↥K then
    (letI : NumberField ↥K := h
     Module.finrank (PadicInt 2)
         (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup ↥K) 2)
       - NK.Reconstruct.rComplex ↥K - 1)
  else 0

/-- The defining property of `ideleLeopoldtDelta` at a number field: it is the difference between
the `ℤ_2`-rank of the idèle class group and `r_ℂ(K) + 1`. -/
theorem ideleLeopoldtDelta_apply (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (K : IntermediateField ℚ Ω) [NumberField ↥K] :
    ideleLeopoldtDelta Ω K =
      Module.finrank (PadicInt 2)
          (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup ↥K) 2)
        - NK.Reconstruct.rComplex ↥K - 1 := by
  classical
  unfold ideleLeopoldtDelta
  simp only [dif_pos (inferInstance : NumberField ↥K)]

theorem ideleLeopoldt_two_of_halves (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (hbound : ∀ (K : IntermediateField ℚ Ω) [NumberField ↥K],
      NK.Reconstruct.rComplex ↥K + 1
        ≤ Module.finrank (PadicInt 2)
            (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup ↥K) 2))
    (hmono : ∀ (M N : IntermediateField ℚ Ω) [NumberField ↥M] [NumberField ↥N], M ≤ N →
      Module.finrank (PadicInt 2)
            (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup ↥M) 2)
          - NK.Reconstruct.rComplex ↥M
        ≤ Module.finrank (PadicInt 2)
            (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup ↥N) 2)
          - NK.Reconstruct.rComplex ↥N) :
    ∃ δ : IntermediateField ℚ Ω → ℕ,
      (∀ (M N : IntermediateField ℚ Ω) [NumberField ↥M] [NumberField ↥N], M ≤ N → δ M ≤ δ N) ∧
        ∀ (K : IntermediateField ℚ Ω) [NumberField ↥K],
          Module.finrank (PadicInt 2)
              (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup ↥K) 2)
            = NK.Reconstruct.rComplex ↥K + 1 + δ K := by
  classical
  refine ⟨ideleLeopoldtDelta Ω, ?_, ?_⟩
  · -- Monotonicity: subtract the same `1` from both sides of `hmono`.
    intro M N hM hN hMN
    rw [ideleLeopoldtDelta_apply Ω M, ideleLeopoldtDelta_apply Ω N]
    exact Nat.sub_le_sub_right (hmono M N hMN) 1
  · -- The rank formula: `hbound` makes the truncated subtraction exact.
    intro K hK
    rw [ideleLeopoldtDelta_apply Ω K]
    have hb := hbound K
    omega

end NK.NUV2
