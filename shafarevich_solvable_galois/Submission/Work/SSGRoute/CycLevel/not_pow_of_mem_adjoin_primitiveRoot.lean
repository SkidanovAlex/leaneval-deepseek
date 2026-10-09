import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CycLevel

open Polynomial IntermediateField

/-- If `m > 0` is not a `q`-th power in `ℚ` and `ζ` is a primitive `q ^ e`-th root of unity in
`Ω = AlgebraicClosure ℚ`, then no element of `ℚ⟮ζ⟯` has `q`-th power `m`.

Proof plan: given `β ∈ ℚ⟮ζ⟯` with `β ^ q = m`; write `K = ℚ⟮ζ⟯` and view `ζ` as a primitive
`q ^ e`-th root of unity of `K`.  Capelli's theorem shows `X ^ q - C m` is irreducible over `ℚ`,
so `minpoly ℚ β = X ^ q - C m` and `[ℚ⟮β⟯ : ℚ] = q`.  The conjugate `β * ζ ^ (q ^ (e - 1))` is a
root of `minpoly ℚ β` lying in the abelian (hence normal) extension `K / ℚ`, so it lies in
`ℚ⟮β⟯`; as `β ≠ 0` this gives `ζ ^ (q ^ (e - 1)) ∈ ℚ⟮β⟯`.  Hence `[ℚ⟮ζ ^ (q ^ (e - 1))⟯ : ℚ] =
q - 1` divides `[ℚ⟮β⟯ : ℚ] = q`, forcing `q = 2`, contrary to `2 < q`. -/
theorem not_pow_of_mem_adjoin_primitiveRoot (q e m : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (he : 0 < e) (hm : 0 < m) (hmℚ : ∀ y : ℚ, y ^ q ≠ (m : ℚ))
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (q ^ e)) :
    ∀ β ∈ IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)),
      β ^ q ≠ algebraMap ℚ (AlgebraicClosure ℚ) (m : ℚ) := by
  intro β hβ hβm
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isIntegral
  have hqpos : 0 < q := hq.pos
  have hqne : q ≠ 0 := hq.ne_zero
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hodd : Odd q := hq.odd_of_ne_two (by omega)
  -- Capelli: `X ^ q - C m` is irreducible over `ℚ`.
  have hirr : Irreducible (X ^ q - C (m : ℚ)) := by
    rw [X_pow_sub_C_irreducible_iff_of_odd hodd]
    intro d hdq hd1 b
    have hdq' : d = q := (hq.eq_one_or_self_of_dvd d hdq).resolve_left hd1
    rw [hdq']
    exact hmℚ b
  -- `K = ℚ⟮ζ⟯`, a cyclotomic (hence abelian) extension of `ℚ`.
  set K : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)) with hKdef
  have hζK : ζ ∈ K := by
    rw [hKdef]
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)
  haveI hne : NeZero (q ^ e) := ⟨pow_ne_zero e hqne⟩
  haveI hKcyc : IsCyclotomicExtension {q ^ e} ℚ K := by
    rw [hKdef]
    exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI hKabel : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q ^ e} ℚ K
  haveI hKgal : IsGalois ℚ K := hKabel.toIsGalois
  haveI hKint : Algebra.IsIntegral ℚ ↥K := Algebra.IsAlgebraic.isIntegral
  let ζK : ↥K := ⟨ζ, hζK⟩
  have hζK' : IsPrimitiveRoot ζK (q ^ e) := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff (N := K)]
    exact hζ
  have hηK : IsPrimitiveRoot (ζK ^ (q ^ (e - 1))) q :=
    hζK'.pow (pow_pos hqpos _) (by rw [← pow_succ, Nat.sub_add_cancel he])
  let βK : ↥K := ⟨β, hβ⟩
  have hβKq : βK ^ q = algebraMap ℚ ↥K (m : ℚ) := by
    apply Subtype.ext
    rw [IntermediateField.coe_pow]
    change (β : AlgebraicClosure ℚ) ^ q = algebraMap ℚ (AlgebraicClosure ℚ) (m : ℚ)
    rw [hβm]
  -- `F = ℚ⟮β⟯ ≤ K`, and `F / ℚ` is abelian Galois.
  set F : IntermediateField ℚ ↥K := IntermediateField.adjoin ℚ ({βK} : Set ↥K) with hFdef
  have hβKF : βK ∈ F := by
    rw [hFdef]
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton βK)
  haveI hFabel : IsAbelianGalois ℚ F :=
    IsAbelianGalois.of_algHom
      ({ toFun := fun x : ↥F => (x : ↥K)
         map_one' := rfl, map_mul' := fun x y => rfl, map_zero' := rfl, map_add' := fun x y => rfl
         commutes' := fun r => rfl } : ↥F →ₐ[ℚ] ↥K)
  haveI hFgal : IsGalois ℚ F := hFabel.toIsGalois
  haveI hFint : Algebra.IsIntegral ℚ ↥F := Algebra.IsAlgebraic.isIntegral
  -- `minpoly ℚ β = X ^ q - C m` (in `K`, and in `F`).
  have hminβK : minpoly ℚ βK = X ^ q - C (m : ℚ) := by
    symm
    refine minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C (m : ℚ) hqne)
    rw [map_sub, map_pow, aeval_X, aeval_C, hβKq, sub_self]
  have hminβKF : minpoly ℚ (⟨βK, hβKF⟩ : F) = X ^ q - C (m : ℚ) := by
    have heq : algebraMap ↥F ↥K (⟨βK, hβKF⟩ : F) = βK := Subtype.ext rfl
    have h2 : minpoly ℚ (algebraMap ↥F ↥K (⟨βK, hβKF⟩ : F))
        = minpoly ℚ (⟨βK, hβKF⟩ : F) :=
      minpoly.algebraMap_eq (A := ℚ) (B := ↥F) (B' := ↥K)
        (fun a b h => Subtype.ext h) (⟨βK, hβKF⟩ : F)
    rw [← h2, heq, hminβK]
  -- `minpoly ℚ β` splits over both `K` and `F`.
  have h1 : ((X ^ q - C (m : ℚ)).map (algebraMap ℚ ↥K)).Splits := by
    have := IsGalois.splits ℚ βK
    rwa [hminβK] at this
  have h2 : ((X ^ q - C (m : ℚ)).map (algebraMap ℚ ↥F)).Splits := by
    have := IsGalois.splits ℚ (⟨βK, hβKF⟩ : F)
    rwa [hminβKF] at this
  -- hence every root of `minpoly ℚ β` in `K` lies in `F`.
  have hroots : ∀ x ∈ (X ^ q - C (m : ℚ)).rootSet ↥K, x ∈ F :=
    (IntermediateField.splits_iff_mem h1).mp h2
  have hβKηK : βK * ζK ^ (q ^ (e - 1)) ∈ F := by
    apply hroots
    rw [Polynomial.mem_rootSet]
    refine ⟨(monic_X_pow_sub_C (m : ℚ) hqne).ne_zero, ?_⟩
    rw [map_sub, map_pow, aeval_X, aeval_C, mul_pow, hβKq, hηK.pow_eq_one, mul_one, sub_self]
  have hβKne : βK ≠ 0 := by
    intro h0
    have hzero : algebraMap ℚ ↥K (m : ℚ) = 0 := by rw [← hβKq, h0, zero_pow hqne]
    apply hmQ
    have : algebraMap ℚ ↥K (m : ℚ) = algebraMap ℚ ↥K (0 : ℚ) := by rw [map_zero]; exact hzero
    exact (algebraMap ℚ ↥K).injective this
  have hηKF : ζK ^ (q ^ (e - 1)) ∈ F := by
    have hmem : βK * ζK ^ (q ^ (e - 1)) * βK⁻¹ ∈ F := mul_mem hβKηK (inv_mem hβKF)
    have heq : βK * ζK ^ (q ^ (e - 1)) * βK⁻¹ = ζK ^ (q ^ (e - 1)) := by
      rw [mul_assoc, mul_comm (ζK ^ (q ^ (e - 1))) βK⁻¹, ← mul_assoc,
        mul_inv_cancel₀ hβKne, one_mul]
    rwa [heq] at hmem
  -- degrees: `[ℚ⟮η⟯ : ℚ] = q - 1` divides `[F : ℚ] = q`.
  have hle : IntermediateField.adjoin ℚ ({ζK ^ (q ^ (e - 1))} : Set ↥K) ≤ F := by
    rw [hFdef, IntermediateField.adjoin_le_iff]
    rintro x rfl
    exact hηKF
  have hfinF : Module.finrank ℚ F = q := by
    rw [hFdef, IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral βK),
      hminβK, natDegree_X_pow_sub_C]
  have hfinη : Module.finrank ℚ
      (IntermediateField.adjoin ℚ ({ζK ^ (q ^ (e - 1))} : Set ↥K)) = q - 1 := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (ζK ^ (q ^ (e - 1)))),
      ← cyclotomic_eq_minpoly_rat hηK hqpos, natDegree_cyclotomic, Nat.totient_prime hq]
  have hq2le : 2 ≤ q := hq.two_le
  have hdvd : Module.finrank ℚ
      (IntermediateField.adjoin ℚ ({ζK ^ (q ^ (e - 1))} : Set ↥K)) ∣ Module.finrank ℚ F :=
    IntermediateField.finrank_dvd_of_le_right hle
  rw [hfinη, hfinF] at hdvd
  rcases (Nat.dvd_prime hq).mp hdvd with h | h
  · omega
  · omega



end Work.SSGRoute.CycLevel
