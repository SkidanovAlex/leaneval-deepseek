import Mathlib
import Submission.Work.TorsorExistence.Defs
import Submission.Work.TorsorExistence.nonempty_cyclicExtension_of_isGalois_finrank_five
import Submission.Work.TorsorExistence.finrank_cyclotomicField_dvd_totient
import Submission.Work.TorsorExistence.totient_le_finrank_rat_cyclotomicField
import Submission.Work.TorsorExistence.exists_index_five_of_five_dvd_card

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.TorsorExistence

open Polynomial IntermediateField

open scoped IsMulCommutative

noncomputable section

/-- Every number field has a cyclic extension of degree `5`.  (Route: for `k` with
`5 ^ (k - 1) > [𝕜 : ℚ]`, consider `M := 𝕜(ζ_{5 ^ k})`, the compositum of `𝕜` with the
cyclotomic field `ℚ(ζ_{5^k})`; `Gal(ℚ(ζ_{5^k})/ℚ) ≅ (ℤ/5^k)ˣ` is abelian of order `4 * 5^(k-1)`,
`K := 𝕜 ∩ ℚ(ζ_{5^k})` has `[K : ℚ] ∣ [𝕜 : ℚ]` and `[K : ℚ] < 5 ^ (k-1)`, so
`[M : 𝕜] = 4 * 5^(k-1) / [K : ℚ]` is divisible by `5`; a finite abelian group of order divisible
by `5` has a quotient of order `5`, and the fixed field of the kernel of that quotient is a
cyclic extension of degree `5` of `𝕜`.) -/
theorem existsCyclicExtension_numberField {𝕜 : Type} [Field 𝕜] [NumberField 𝕜] :
    Nonempty (CyclicExtension 𝕜 5) := by
  classical
  set d : ℕ := Module.finrank ℚ 𝕜 with hd
  set m : ℕ := 5 ^ (d + 1) with hm
  have hmpos : 0 < m := by rw [hm]; positivity
  haveI : NeZero m := ⟨hmpos.ne'⟩
  -- ## Step 1: `5` divides the degree `[𝕜(ζ_m) : 𝕜]`
  have htot : Nat.totient m = 4 * 5 ^ d := by
    rw [hm, Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by omega : 0 < d + 1),
      show d + 1 - 1 = d from by omega]
    omega
  have hle : 4 * 5 ^ d ≤ Module.finrank ℚ (CyclotomicField m 𝕜) := by
    have h := totient_le_finrank_rat_cyclotomicField (K := 𝕜) m
    rwa [htot] at h
  have hdvd : Module.finrank 𝕜 (CyclotomicField m 𝕜) ∣ 4 * 5 ^ d := by
    have h := finrank_cyclotomicField_dvd_totient (K := 𝕜) m
    rwa [htot] at h
  have htower : Module.finrank ℚ (CyclotomicField m 𝕜)
      = d * Module.finrank 𝕜 (CyclotomicField m 𝕜) := by
    have h := Module.finrank_mul_finrank ℚ 𝕜 (CyclotomicField m 𝕜)
    rw [← hd] at h
    exact h.symm
  have hfive : 5 ∣ Module.finrank 𝕜 (CyclotomicField m 𝕜) := by
    by_contra hcon
    have h4 : Module.finrank 𝕜 (CyclotomicField m 𝕜) ∣ 4 := by
      rcases Nat.eq_zero_or_pos d with h0 | hd''
      · simpa [h0] using hdvd
      · have hcop : Nat.Coprime (Module.finrank 𝕜 (CyclotomicField m 𝕜)) (5 ^ d) := by
          rw [Nat.coprime_pow_right_iff hd'']
          exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr hcon).symm
        exact hcop.dvd_of_dvd_mul_right hdvd
    have hle4 : Module.finrank 𝕜 (CyclotomicField m 𝕜) ≤ 4 := Nat.le_of_dvd (by norm_num) h4
    have hbig : 4 * 5 ^ d ≤ 4 * d := by
      calc 4 * 5 ^ d ≤ Module.finrank ℚ (CyclotomicField m 𝕜) := hle
        _ = d * Module.finrank 𝕜 (CyclotomicField m 𝕜) := htower
        _ ≤ d * 4 := Nat.mul_le_mul_left d hle4
        _ = 4 * d := by ring
    have h5d : 5 ^ d ≤ d := Nat.le_of_mul_le_mul_left hbig (by norm_num)
    have hlt : d < 5 ^ d := Nat.lt_pow_self (by norm_num : 1 < 5)
    omega
  -- ## Step 2: the Galois correspondence in the abelian extension `𝕜(ζ_m)/𝕜`
  haveI : IsAbelianGalois 𝕜 (CyclotomicField m 𝕜) :=
    IsCyclotomicExtension.isAbelianGalois {m} 𝕜 (CyclotomicField m 𝕜)
  haveI : IsGalois 𝕜 (CyclotomicField m 𝕜) := inferInstance
  haveI : Finite (CyclotomicField m 𝕜 ≃ₐ[𝕜] CyclotomicField m 𝕜) := inferInstance
  have hcard : Nat.card (CyclotomicField m 𝕜 ≃ₐ[𝕜] CyclotomicField m 𝕜)
      = Module.finrank 𝕜 (CyclotomicField m 𝕜) := IsGalois.card_aut_eq_finrank 𝕜 _
  have h5G : 5 ∣ Nat.card (CyclotomicField m 𝕜 ≃ₐ[𝕜] CyclotomicField m 𝕜) := by
    rw [hcard]; exact hfive
  obtain ⟨H, hH⟩ := exists_index_five_of_five_dvd_card h5G
  haveI : H.Normal := inferInstance
  haveI : FiniteDimensional 𝕜 ↥(IntermediateField.fixedField H) := inferInstance
  have hfin : Module.finrank 𝕜 ↥(IntermediateField.fixedField H) = 5 := by
    have e := IsGalois.normalAutEquivQuotient H
    have h1 : Nat.card ((CyclotomicField m 𝕜 ≃ₐ[𝕜] CyclotomicField m 𝕜) ⧸ H) = 5 := by
      rw [← Subgroup.index_eq_card, hH]
    have h2 : Nat.card (↥(IntermediateField.fixedField H) ≃ₐ[𝕜]
        ↥(IntermediateField.fixedField H)) = 5 := by
      rw [← Nat.card_congr e.toEquiv]; exact h1
    rw [← IsGalois.card_aut_eq_finrank 𝕜 ↥(IntermediateField.fixedField H)]
    exact h2
  exact nonempty_cyclicExtension_of_isGalois_finrank_five hfin

end

end Work.TorsorExistence
