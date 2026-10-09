import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTdualControl

/-- If `K / k` is a finite Galois extension of number fields and `ζ` is a primitive `p`-th root of
unity in a field `Ω` containing `K`, then `K⟮ζ⟯ / k` is Galois.

Mathematically this is the statement that `K⟮ζ⟯ = K · k⟮ζ⟯` is the compositum of the two Galois
extensions `K/k` and `k⟮ζ⟯/k` (the latter being cyclotomic, hence Galois).  The proof is carried out
in the lattice of intermediate fields of `k` in `Ω`: it identifies `K⟮ζ⟯` with
`Kk ⊔ Mk` where `Kk` is the image of `K` in `Ω` and `Mk = k⟮ζ⟯`, shows both are Galois over `k`,
and concludes with normality of a sup of normal extensions together with separability (automatic in
characteristic zero). -/
theorem isGalois_adjoin_isPrimitiveRoot (p : ℕ) [Fact p.Prime] {k K Ω : Type} [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) :
    IsGalois k ↥(IntermediateField.adjoin K {ζ} : IntermediateField K Ω) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- The image of `K` inside `Ω`, as an intermediate field of `k`.
  let Kk : IntermediateField k Ω := (IsScalarTower.toAlgHom k K Ω).fieldRange
  -- The cyclotomic field `k⟮ζ⟯`.
  let Mk : IntermediateField k Ω := IntermediateField.adjoin k {ζ}
  let L : IntermediateField K Ω := IntermediateField.adjoin K {ζ}
  -- `Kk ⊔ k⟮ζ⟯` is Galois over `k`.
  have hgal : IsGalois k ↥(Kk ⊔ Mk) := by
    rw [isGalois_iff]
    -- `Kk` is Galois over `k`, as it is the image of the Galois extension `K/k`.
    have hKk : IsGalois k ↥Kk :=
      IsGalois.of_algEquiv (IsScalarTower.toAlgHom k K Ω).equivFieldRange
    have : IsGalois k ↥Kk := hKk
    -- `ζ` is integral (hence algebraic) over `k`.
    have hζint : IsIntegral k ζ :=
      IsIntegral.of_pow (Fact.out : p.Prime).pos (by rw [hζ.pow_eq_one]; exact isIntegral_one)
    have hζalg : IsAlgebraic k ζ := hζint.isAlgebraic
    -- `k⟮ζ⟯` is a cyclotomic extension of `k`, hence Galois over `k`.
    have hcyc : IsCyclotomicExtension ({p} : Set ℕ) k Mk := by
      change IsCyclotomicExtension ({p} : Set ℕ) k
        (IntermediateField.adjoin k ({ζ} : Set Ω)).toSubalgebra
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg]
      exact hζ.adjoin_isCyclotomicExtension k
    have hMk : IsGalois k ↥Mk := IsCyclotomicExtension.isGalois ({p} : Set ℕ) k Mk
    have : IsGalois k ↥Mk := hMk
    -- Finiteness over `k`, then integrality and separability (characteristic zero).
    have hfinKk : FiniteDimensional k ↥Kk :=
      LinearEquiv.finiteDimensional (IsScalarTower.toAlgHom k K Ω).equivFieldRange.toLinearEquiv
    have hfinMk : FiniteDimensional k ↥Mk :=
      IntermediateField.finiteDimensional_adjoin (S := ({ζ} : Set Ω))
        (by intro x hx; rw [Set.mem_singleton_iff] at hx; rwa [hx])
    have hfin : FiniteDimensional k ↥(Kk ⊔ Mk) := IntermediateField.finiteDimensional_sup Kk Mk
    have hint : Algebra.IsIntegral k ↥(Kk ⊔ Mk) := Algebra.IsIntegral.of_finite k ↥(Kk ⊔ Mk)
    have : Algebra.IsIntegral k ↥(Kk ⊔ Mk) := hint
    refine ⟨Algebra.IsSeparable.of_integral k ↥(Kk ⊔ Mk), ?_⟩
    -- Normality is `IntermediateField.normal_sup`, using normality of each factor.
    exact inferInstance
  -- `K⟮ζ⟯`, viewed as an intermediate field of `k`, is exactly `Kk ⊔ Mk`.
  have hL : L.restrictScalars k = Kk ⊔ Mk := by
    have hKK : Kk ≤ IntermediateField.restrictScalars k L := by
      intro x hx
      rw [IntermediateField.mem_restrictScalars]
      rw [AlgHom.mem_fieldRange] at hx
      obtain ⟨y, rfl⟩ := hx
      exact IntermediateField.algebraMap_mem L y
    have hM : Mk ≤ IntermediateField.restrictScalars k L := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact IntermediateField.subset_adjoin K _ (by simp)
    have h1 : Kk ⊔ Mk ≤ IntermediateField.restrictScalars k L := sup_le hKK hM
    have h2 : IntermediateField.restrictScalars k L ≤ Kk ⊔ Mk := by
      intro x hx
      rw [IntermediateField.mem_restrictScalars] at hx
      have hgen : ∀ y ∈ (IntermediateField.adjoin K ({ζ} : Set Ω) : IntermediateField K Ω),
          y ∈ Kk ⊔ Mk := by
        intro y hy
        exact IntermediateField.adjoin_induction K (fun x hx => by
          rw [Set.mem_singleton_iff] at hx; subst hx
          exact le_sup_right (a := Kk) (b := Mk) (IntermediateField.subset_adjoin k _ (by simp)))
          (fun a => le_sup_left (a := Kk) (b := Mk) (by
            rw [AlgHom.mem_fieldRange]
            exact ⟨a, rfl⟩))
          (fun a b ha hb iha ihb => add_mem iha ihb)
          (fun a ha iha => inv_mem iha)
          (fun a b ha hb iha ihb => mul_mem iha ihb) hy
      exact hgen x hx
    exact le_antisymm h2 h1
  rw [← hL] at hgal
  exact hgal

end Work.SSGRoute.PTdualControl
