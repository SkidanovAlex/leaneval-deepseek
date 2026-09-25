/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cyclotomic (unramified) levels of `κ = K_𝔭` inside `κ(μ_{p'})`

For a number field `K`, a finite place `𝔭` and `κ = K_𝔭`, the maximal unramified extension
`κ^ur = κ(μ_{p'})` (realised in a separable closure `K'` as
`NK.LocalAnabelian.unramifiedClosure p`) is the union of the cyclotomic extensions
`κ(ζ_{q^d - 1})`, `q = NK.LocalStructure.residueCard K 𝔭`, which are unramified of degree `d`.

This file sets up that tower: the orders `levelN d = q ^ d - 1`, a chosen primitive root
`levelRoot d`, the level fields `levelField d = κ⟮levelRoot d⟯`, the containment
`levelField d ≤ unramifiedClosure p`, and the divisibility of the level orders.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Degree.zhatComponents
import Submission.NK.TameStructureDeep.Degree.Equality
import Submission.NK.TameStructureDeep.Degree.exists_algEquiv_adjoin_primitiveRoot_pow
import Submission.NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure
import Submission.NK.Mine.ResidueCharAutomatic

open scoped Classical NumberField
open IsDedekindDomain IntermediateField

namespace NK.TameStructureDeep.Degree

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
  [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']

noncomputable section

/-- The residue characteristic of `κ = K_𝔭`. -/
abbrev residueChar : ℕ := ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))

/-- The level order `q ^ d - 1` of the cyclotomic level of degree `d`. -/
def levelN (d : ℕ) : ℕ := NK.LocalStructure.residueCard K 𝔭 ^ d - 1

theorem two_le_residueCard : 2 ≤ NK.LocalStructure.residueCard K 𝔭 :=
  NK.LocalReciprocity.two_le_residueCard K 𝔭

omit [IsSepClosure (𝔭.adicCompletion K) K'] in
theorem levelN_pos (d : ℕ) (hd : d ≠ 0) : 0 < levelN 𝔭 d := by
  have hq2 : 2 ≤ NK.LocalStructure.residueCard K 𝔭 := two_le_residueCard 𝔭
  have h1 : 2 ≤ NK.LocalStructure.residueCard K 𝔭 ^ d :=
    le_trans hq2 (Nat.le_self_pow hd _)
  rw [levelN]
  omega

omit [IsSepClosure (𝔭.adicCompletion K) K'] in
theorem levelN_ne_zero (d : ℕ) (hd : d ≠ 0) : levelN 𝔭 d ≠ 0 := (levelN_pos 𝔭 d hd).ne'

/-- `p ∤ q ^ d - 1` for `d ≥ 1`: the level orders are prime to the residue characteristic. -/
theorem not_residueChar_dvd_levelN (d : ℕ) (hd : d ≠ 0) : ¬ residueChar 𝔭 ∣ levelN 𝔭 d := by
  have hp := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hpc := NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
  obtain ⟨f, hf, hqf⟩ := NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hp hpc
  show ¬ ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ∣ _
  rw [levelN, hqf, ← pow_mul]
  set p := ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) with hpdef
  have hfd : f * d ≠ 0 := Nat.mul_ne_zero (by omega) hd
  have hpdvd : p ∣ p ^ (f * d) := dvd_pow_self p hfd
  have hpos : 1 ≤ p ^ (f * d) := Nat.one_le_pow _ _ hp.pos
  intro hdiv
  have h1 : p ∣ p ^ (f * d) - (p ^ (f * d) - 1) := Nat.dvd_sub hpdvd hdiv
  rw [Nat.sub_sub_self hpos] at h1
  exact hp.not_dvd_one h1

omit [IsSepClosure (𝔭.adicCompletion K) K'] in
/-- `q ^ e - 1` divides `q ^ d - 1` when `e ∣ d`. -/
theorem levelN_dvd_levelN {e d : ℕ} (hed : e ∣ d) : levelN 𝔭 e ∣ levelN 𝔭 d := by
  obtain ⟨k, rfl⟩ := hed
  rw [levelN, levelN, pow_mul]
  simpa using Nat.sub_dvd_pow_sub_pow (NK.LocalStructure.residueCard K 𝔭 ^ e) 1 k

/-- There is a primitive `(q ^ d - 1)`-th root of unity in the separable closure `K'`. -/
theorem exists_levelRoot (d : ℕ) (hd : d ≠ 0) : ∃ ζ : K', IsPrimitiveRoot ζ (levelN 𝔭 d) := by
  haveI hcharκ : CharZero (𝔭.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
  haveI hchar : CharZero K' := charZero_of_injective_algebraMap
    (RingHom.injective (algebraMap (𝔭.adicCompletion K) K'))
  haveI : NeZero ((levelN 𝔭 d : ℕ) : K') := ⟨by
    rw [Nat.cast_ne_zero]; exact levelN_ne_zero 𝔭 d hd⟩
  haveI : IsSepClosed K' := (inferInstance : IsSepClosure (𝔭.adicCompletion K) K').sep_closed
  exact NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := K') (n := levelN 𝔭 d)

/-- A chosen primitive `(q ^ d - 1)`-th root of unity of `K'` (for `d = 0` this is `0`, an
irrelevant value). -/
noncomputable def levelRoot (d : ℕ) : K' :=
  if hd : d = 0 then 0 else Classical.choose (exists_levelRoot 𝔭 d hd)

theorem levelRoot_isPrimitiveRoot (d : ℕ) (hd : d ≠ 0) :
    IsPrimitiveRoot (levelRoot (K' := K') 𝔭 d) (levelN 𝔭 d) := by
  rw [levelRoot, dif_neg hd]
  exact Classical.choose_spec (exists_levelRoot 𝔭 d hd)

/-- The level field `κ⟮ζ_d⟯` of degree `d`. -/
noncomputable def levelField (d : ℕ) : IntermediateField (𝔭.adicCompletion K) K' :=
  IntermediateField.adjoin (𝔭.adicCompletion K) ({levelRoot (K' := K') 𝔭 d} : Set K')

theorem mem_levelField_root (d : ℕ) :
    levelRoot (K' := K') 𝔭 d ∈ levelField (K' := K') 𝔭 d :=
  IntermediateField.mem_adjoin_simple_self (𝔭.adicCompletion K) (levelRoot (K' := K') 𝔭 d)

theorem levelRoot_mem_unramifiedClosure (d : ℕ) :
    levelRoot (K' := K') 𝔭 d ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K)
      (K' := K') (residueChar 𝔭) := by
  rcases eq_or_ne d 0 with rfl | hd
  · rw [levelRoot, dif_pos rfl]
    exact zero_mem _
  · have hle : (𝔭.adicCompletion K)⟮levelRoot (K' := K') 𝔭 d⟯ ≤
        NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (residueChar 𝔭) :=
      le_iSup_of_le (⟨levelN 𝔭 d, not_residueChar_dvd_levelN 𝔭 d hd⟩)
        (le_iSup_of_le (levelRoot (K' := K') 𝔭 d)
          (le_iSup_of_le (levelRoot_isPrimitiveRoot 𝔭 d hd) (le_refl _)))
    exact hle (IntermediateField.mem_adjoin_simple_self (𝔭.adicCompletion K) _)

/-- Every level is contained in the maximal unramified extension `κ(μ_{p'})`. -/
theorem levelField_le_unramifiedClosure (d : ℕ) :
    levelField (K' := K') 𝔭 d ≤ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K)
      (K' := K') (residueChar 𝔭) := by
  rw [levelField]
  exact IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr (levelRoot_mem_unramifiedClosure 𝔭 d))

/-- The level field is the cyclotomic extension of level `levelN d`. -/
theorem isCyclotomicExtension_levelField (d : ℕ) (hd : d ≠ 0) :
    IsCyclotomicExtension {levelN 𝔭 d} (𝔭.adicCompletion K)
      ↥(levelField (K' := K') 𝔭 d) := by
  haveI : NeZero (levelN 𝔭 d) := ⟨levelN_ne_zero 𝔭 d hd⟩
  haveI hint : Algebra.IsIntegral (𝔭.adicCompletion K) K' := inferInstance
  rw [levelField]
  exact (levelRoot_isPrimitiveRoot 𝔭 d hd).intermediateField_adjoin_isCyclotomicExtension
    (𝔭.adicCompletion K)

instance isGalois_levelField (d : ℕ) [NeZero d] :
    IsGalois (𝔭.adicCompletion K) ↥(levelField (K' := K') 𝔭 d) := by
  haveI : IsCyclotomicExtension {levelN 𝔭 d} (𝔭.adicCompletion K)
      ↥(levelField (K' := K') 𝔭 d) := isCyclotomicExtension_levelField 𝔭 d (NeZero.ne d)
  exact IsCyclotomicExtension.isGalois {levelN 𝔭 d} (𝔭.adicCompletion K)
    ↥(levelField (K' := K') 𝔭 d)

instance normal_levelField (d : ℕ) [NeZero d] :
    Normal (𝔭.adicCompletion K) ↥(levelField (K' := K') 𝔭 d) :=
  IsGalois.to_normal

/-- **The Frobenius acts on the roots of unity of a level by `ζ ↦ ζ ^ q`**: the canonical
generator `levelFrob d` of `Gal(κ⟮ζ_d⟯/κ)`. -/
noncomputable def levelFrob (d : ℕ) (hd : d ≠ 0) :
    Gal(↥(levelField (K' := K') 𝔭 d) / 𝔭.adicCompletion K) :=
  Classical.choose (exists_algEquiv_adjoin_primitiveRoot_pow (K' := K') 𝔭
    (not_residueChar_dvd_levelN 𝔭 d hd) (levelRoot_isPrimitiveRoot 𝔭 d hd))

theorem levelFrob_apply (d : ℕ) (hd : d ≠ 0) :
    levelFrob (K' := K') 𝔭 d hd ⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root 𝔭 d⟩ =
      ⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root 𝔭 d⟩ ^
        NK.LocalStructure.residueCard K 𝔭 :=
  Classical.choose_spec (exists_algEquiv_adjoin_primitiveRoot_pow (K' := K') 𝔭
    (not_residueChar_dvd_levelN 𝔭 d hd) (levelRoot_isPrimitiveRoot 𝔭 d hd))

end

end NK.TameStructureDeep.Degree
