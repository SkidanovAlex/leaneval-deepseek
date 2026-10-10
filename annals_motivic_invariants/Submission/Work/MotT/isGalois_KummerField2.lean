import Mathlib
import Submission.Work.MotT.T4Setup
import Submission.Work.MotT.isGalois_adjoin_root5

set_option linter.unusedVariables false -- v435-speed

set_option linter.style.haveILetI false

/-!
# The two-root Kummer field `L = K(ζ, w₁, w₂)` is finite Galois over `K`

Node T4 of the LAM route runs the descent argument over the field `L = K(ζ, w₁, w₂)`
(`Work.MotT.KummerField2 K h₁ h₂ hk`, with `ζ = zeta5K K hk` a primitive fifth root of unity in
`K̄ = AlgebraicClosure K` and `wᵢ = root5K hᵢ` a chosen fifth root of `hᵢ`), so that the point
produced over `L` is `K`-rational after the Galois descent `L^{Aut_K L} = K`.  This file supplies the
Galois layer: `L/K` is finite and Galois (i.e. finite, separable, normal).

The argument is the one already proved for the one-root field in
`Submission/Work/MotT/isGalois_adjoin_root5.lean`: `L` is the splitting field over `K` of a
separable polynomial whose roots generate it.

* If `hᵢ ≠ 0`, then `K(ζ, wᵢ)` is the splitting field over `K` of the separable polynomial
  `X ^ 5 - C hᵢ` (`isGalois_adjoin_root5`), whose roots in `K̄` are the `ζ ^ j * wᵢ` (`j < 5`).
* If `hᵢ = 0`, then `wᵢ = 0` and `K(ζ, wᵢ) = K(ζ)` is the splitting field over `K` of the
  separable polynomial `X ^ 5 - C 1`, whose roots are the fifth roots of unity, i.e. the powers of
  `ζ`; this is the `h = 0` case of `isGalois_adjoinZetaRoot5` below.

Both roots together are handled by a compositum: `L = K(ζ, w₁) ⊔ K(ζ, w₂)` is the compositum of two
finite Galois intermediate fields, and finite Galois intermediate fields are closed under `⊔`
(`Mathlib/FieldTheory/Galois/GaloisClosure.lean`, `FiniteGaloisIntermediateField`'s `IsGalois`
instance; finiteness is `IntermediateField.finiteDimensional_sup`).

Note that no hypothesis on `h₁`, `h₂` beyond `ringChar K ≠ 5` is needed: the degenerate cases
`hᵢ = 0` are handled by the second bullet above.
-/

namespace Work.MotT

noncomputable section

open Polynomial

/-- **`K(ζ, ⁵√h)`**: the one-root Kummer field inside `K̄`, with `ζ = zeta5K K hk` the chosen
primitive fifth root of unity.  (The two-root field `KummerField2` is the compositum of the two
one-root fields for `h₁` and `h₂`, see `KummerField2_eq_sup`.) -/
def adjoinZetaRoot5 (K : Type) [Field K] (h : K) (hk : ringChar K ≠ 5) :
    IntermediateField K (KbK K) :=
  IntermediateField.adjoin K ({zeta5K K hk, root5K h} : Set (KbK K))

/-- **`K(ζ, ⁵√h)/K` is finite and Galois** for every `h ∈ K`, as long as `ringChar K ≠ 5`.

For `h ≠ 0` this is `isGalois_adjoin_root5` (`X ^ 5 - C h` is separable and `ζ, ⁵√h` generate its
splitting field).  For `h = 0` we have `⁵√0 = 0`, so `K(ζ, 0) = K(ζ)`, which is the splitting field
of the separable polynomial `X ^ 5 - C 1`: its roots are the fifth roots of unity, and every fifth
root of unity is a power of the primitive root `ζ`. -/
theorem isGalois_adjoinZetaRoot5 (K : Type) [Field K] (hk : ringChar K ≠ 5) (h : K) :
    FiniteDimensional K ↥(adjoinZetaRoot5 K h hk) ∧ IsGalois K ↥(adjoinZetaRoot5 K h hk) := by
  have e0 : adjoinZetaRoot5 K 0 hk =
      IntermediateField.adjoin K ({zeta5K K hk, root5K (0 : K)} : Set (KbK K)) := rfl
  by_cases hh : h = 0
  · subst hh
    -- char `K ≠ 5` gives `5 ≠ 0` in `K`
    have h5K : (5 : K) ≠ 0 := by
      intro h0
      have hdvd : ringChar K ∣ 5 := (CharP.cast_eq_zero_iff K (ringChar K) 5).mp h0
      rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hz
      · rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd (ringChar K) hdvd with h' | h'
        · exact hp.ne_one h'
        · exact hk h'
      · haveI : CharZero K := (CharP.charP_zero_iff_charZero K).mp (ringChar.eq_iff.mp hz)
        exact (Nat.cast_ne_zero.mpr (by norm_num : (5 : ℕ) ≠ 0)) h0
    have hsep : (X ^ 5 - C (1 : K) : K[X]).Separable :=
      Polynomial.separable_X_pow_sub_C 1 h5K one_ne_zero
    have hsplit : ((X ^ 5 - C (1 : K) : K[X]).map (algebraMap K (KbK K))).Splits :=
      IsAlgClosed.splits _
    -- `⁵√0 = 0`
    have hroot0 : root5K (0 : K) = 0 := by
      have h := root5K_spec (0 : K)
      rw [map_zero] at h
      exact (pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp h
    -- `ζ` is a root of `X ^ 5 - C 1`
    have hζ_mem : zeta5K K hk ∈ (X ^ 5 - C (1 : K) : K[X]).rootSet (KbK K) := by
      rw [Polynomial.Monic.mem_rootSet (Polynomial.monic_X_pow_sub_C (1 : K) (by norm_num))]
      simp [(zeta5K_isPrimitiveRoot K hk).pow_eq_one]
    -- every root of `X ^ 5 - C 1` is a power of `ζ`, hence lies in `K(ζ, 0)`
    have hB : ∀ x ∈ (X ^ 5 - C (1 : K) : K[X]).rootSet (KbK K),
        x ∈ (adjoinZetaRoot5 K 0 hk : Set (KbK K)) := by
      intro x hx
      have hx5 : x ^ 5 = (1 : KbK K) := by
        have h := Polynomial.aeval_eq_zero_of_mem_rootSet hx
        simpa [Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] using h
      obtain ⟨i, -, hi⟩ := (zeta5K_isPrimitiveRoot K hk).eq_pow_of_pow_eq_one hx5
      rw [← hi]
      exact pow_mem (IntermediateField.subset_adjoin K _ (by simp)) i
    -- conversely `ζ` and `0` lie in the field generated by the roots
    have h1 : adjoinZetaRoot5 K 0 hk ≤
        IntermediateField.adjoin K ((X ^ 5 - C (1 : K) : K[X]).rootSet (KbK K)) := by
      rw [e0, IntermediateField.adjoin_le_iff]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact IntermediateField.subset_adjoin K _ hζ_mem
      · rw [hroot0]
        exact zero_mem _
    have h2 : IntermediateField.adjoin K ((X ^ 5 - C (1 : K) : K[X]).rootSet (KbK K)) ≤
        adjoinZetaRoot5 K 0 hk := by
      rw [e0, IntermediateField.adjoin_le_iff]
      exact hB
    have hEq := le_antisymm h1 h2
    -- `K(ζ, 0) = K(ζ)` is the splitting field of `X ^ 5 - C 1` over `K`
    haveI hsf : (X ^ 5 - C (1 : K) : K[X]).IsSplittingField K ↥(adjoinZetaRoot5 K 0 hk) := by
      rw [IntermediateField.isSplittingField_iff]
      exact ⟨IntermediateField.splits_of_splits hsplit hB, hEq⟩
    exact ⟨Polynomial.IsSplittingField.finiteDimensional _ (X ^ 5 - C (1 : K) : K[X]),
      IsGalois.of_separable_splitting_field hsep⟩
  · exact isGalois_adjoin_root5 K hk h hh (zeta5K K hk) (zeta5K_isPrimitiveRoot K hk)

/-- **The two-root Kummer field is the compositum of the two one-root Kummer fields**:
`K(ζ, w₁, w₂) = K(ζ, w₁) ⊔ K(ζ, w₂)`.  Both inclusions are immediate from the description of the
generators as elements of the respective fields. -/
theorem KummerField2_eq_sup (K : Type) [Field K] (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    KummerField2 K h₁ h₂ hk = adjoinZetaRoot5 K h₁ hk ⊔ adjoinZetaRoot5 K h₂ hk := by
  have e1 : adjoinZetaRoot5 K h₁ hk =
      IntermediateField.adjoin K ({zeta5K K hk, root5K h₁} : Set (KbK K)) := rfl
  have e2 : adjoinZetaRoot5 K h₂ hk =
      IntermediateField.adjoin K ({zeta5K K hk, root5K h₂} : Set (KbK K)) := rfl
  rw [show KummerField2 K h₁ h₂ hk = IntermediateField.adjoin K
      ({zeta5K K hk, root5K h₁, root5K h₂} : Set (KbK K)) from rfl, e1, e2]
  refine le_antisymm ?_ ?_
  · -- `K(ζ, w₁, w₂) ≤ K(ζ, w₁) ⊔ K(ζ, w₂)`
    rw [IntermediateField.adjoin_le_iff]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact SetLike.mem_coe.mpr (le_sup_left (a := IntermediateField.adjoin K
        ({zeta5K K hk, root5K h₁} : Set (KbK K))) (b := IntermediateField.adjoin K
        ({zeta5K K hk, root5K h₂} : Set (KbK K)))
        (IntermediateField.subset_adjoin K ({zeta5K K hk, root5K h₁} : Set (KbK K))
          (show zeta5K K hk ∈ ({zeta5K K hk, root5K h₁} : Set (KbK K)) by simp)))
    · exact SetLike.mem_coe.mpr (le_sup_left (a := IntermediateField.adjoin K
        ({zeta5K K hk, root5K h₁} : Set (KbK K))) (b := IntermediateField.adjoin K
        ({zeta5K K hk, root5K h₂} : Set (KbK K)))
        (IntermediateField.subset_adjoin K ({zeta5K K hk, root5K h₁} : Set (KbK K))
          (show root5K h₁ ∈ ({zeta5K K hk, root5K h₁} : Set (KbK K)) by simp)))
    · exact SetLike.mem_coe.mpr (le_sup_right (a := IntermediateField.adjoin K
        ({zeta5K K hk, root5K h₁} : Set (KbK K))) (b := IntermediateField.adjoin K
        ({zeta5K K hk, root5K h₂} : Set (KbK K)))
        (IntermediateField.subset_adjoin K ({zeta5K K hk, root5K h₂} : Set (KbK K))
          (show root5K h₂ ∈ ({zeta5K K hk, root5K h₂} : Set (KbK K)) by simp)))
  · -- `K(ζ, w₁) ⊔ K(ζ, w₂) ≤ K(ζ, w₁, w₂)`
    rw [sup_le_iff]
    constructor <;> rw [IntermediateField.adjoin_le_iff]
    · rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact IntermediateField.subset_adjoin K _ (by simp)
      · exact IntermediateField.subset_adjoin K _ (by simp)
    · rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact IntermediateField.subset_adjoin K _ (by simp)
      · exact IntermediateField.subset_adjoin K _ (by simp)

/-- **`L = K(ζ, w₁, w₂)/K` is finite and Galois** for `ringChar K ≠ 5`.

`L` is the compositum `K(ζ, w₁) ⊔ K(ζ, w₂)` of two finite Galois intermediate fields
(`KummerField2_eq_sup`, `isGalois_adjoinZetaRoot5`); finiteness is
`IntermediateField.finiteDimensional_sup` and the Galois property of a compositum of Galois
extensions is the `IsGalois` instance for `FiniteGaloisIntermediateField`. -/
theorem isGalois_KummerField2 (K : Type) [Field K] (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    FiniteDimensional K ↥(KummerField2 K h₁ h₂ hk) ∧ IsGalois K ↥(KummerField2 K h₁ h₂ hk) := by
  haveI := (isGalois_adjoinZetaRoot5 K hk h₁).1
  haveI := (isGalois_adjoinZetaRoot5 K hk h₁).2
  haveI := (isGalois_adjoinZetaRoot5 K hk h₂).1
  haveI := (isGalois_adjoinZetaRoot5 K hk h₂).2
  rw [KummerField2_eq_sup K h₁ h₂ hk]
  exact ⟨inferInstance, inferInstance⟩

end

end Work.MotT
