import Mathlib
import Submission.NK.Reconstruct.gammaBaseChange
import Submission.NK.Reconstruct.torsionFreeGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base-change map `π_{L/K} : Γ_L → Γ_K` preserves `ℤ_ℓ`-torsion

`NK.Reconstruct.gammaBaseChange_toAdditive_mem_torsion`: the additive homomorphism underlying
the base-change (norm/transfer) map `π_{L/K} : Γ_L → Γ_K` of
`NK.Reconstruct.gammaBaseChangeHom` carries the torsion submodule
`NK.Reconstruct.GammaTorsion` of the ℓ-adic abelianisation `Γ_L = G_L^{ab,(ℓ)}` into the torsion
submodule of `Γ_K`.

The mathematical content is that `Γ_L → Γ_K` is a homomorphism of `ℤ_ℓ`-modules, so that the
torsion submodule is mapped into the torsion submodule.  We avoid formalising the full
`ℤ_ℓ`-linearity of `gammaBaseChangeHom` and use only the *underlying additive* map together with the
elementary description of torsion in a module over the discrete valuation ring `ℤ_ℓ`: every non-zero
element of `ℤ_ℓ` is `unit * ℓ ^ n`, so an element killed by a non-zero scalar is killed by a natural
number, and `AddMonoidHom`s preserve the resulting natural-number multiples.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

section Torsion

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Torsion is annihilated by a natural number.**  For a `ℤ_ℓ`-module, an element killed by a
non-zero scalar of the discrete valuation ring `ℤ_ℓ` is annihilated by some non-zero natural
number: `ℤ_ℓ` is a DVR with uniformiser `ℓ`
(`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`), so a non-zero scalar is `unit * ℓ ^ n`. -/
theorem exists_nat_nsmul_eq_zero_of_mem_gammaTorsion {x : Additive (Gamma K K' ℓ)}
    (hx : x ∈ GammaTorsion (K := K) (K' := K') ℓ) :
    ∃ n : ℕ, n ≠ 0 ∧ n • x = 0 := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
  have ha' : (a : PadicInt ℓ) • x = 0 := ha
  have ha0 : (a : PadicInt ℓ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp a.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := PadicInt ℓ) ha0
    (PadicInt.irreducible_p (p := ℓ))
  refine ⟨ℓ ^ n, pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero, ?_⟩
  -- multiply `a • x = 0` by the inverse of the unit part of `a = u * ℓ ^ n`
  have h2 : (↑(u⁻¹) : PadicInt ℓ) • ((a : PadicInt ℓ) • x) = 0 := by rw [ha', smul_zero]
  rw [← mul_smul] at h2
  rw [hu] at h2
  have h3 : (↑(u⁻¹) : PadicInt ℓ) * (↑u * (ℓ : PadicInt ℓ) ^ n) = (ℓ : PadicInt ℓ) ^ n := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [h3] at h2
  -- `ℓ ^ n • x = 0` with the natural-number scalar `ℓ ^ n`
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at h2
  exact h2

/-- **A non-zero natural multiple of an element is torsion.**  Conversely to
`exists_nat_nsmul_eq_zero_of_mem_gammaTorsion`: an element of a `ℤ_ℓ`-module annihilated by a
non-zero natural number is `ℤ_ℓ`-torsion (the scalar `(n : ℤ_ℓ)` is a non-zero-divisor because
`ℤ_ℓ` has characteristic zero). -/
theorem mem_gammaTorsion_of_nat_smul_eq_zero {n : ℕ} (hn : n ≠ 0)
    {x : Additive (Gamma K K' ℓ)} (h : (n : PadicInt ℓ) • x = 0) :
    x ∈ GammaTorsion (K := K) (K' := K') ℓ :=
  (Submodule.mem_torsion_iff x).mpr
    ⟨⟨(n : PadicInt ℓ),
      mem_nonZeroDivisors_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)⟩, h⟩

end Torsion

theorem gammaBaseChange_toAdditive_mem_torsion {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] (L : FrobLevel K K')
    {x : Additive (Gamma ↥L.L K' ℓ)} (hx : x ∈ GammaTorsion (K := ↥L.L) (K' := K') ℓ) :
    MonoidHom.toAdditive (gammaBaseChangeHom (K := K) (K' := K') ℓ L) x ∈
      GammaTorsion (K := K) (K' := K') ℓ := by
  obtain ⟨n, hn, hzero⟩ :=
    exists_nat_nsmul_eq_zero_of_mem_gammaTorsion (K := ↥L.L) (K' := K') hx
  refine mem_gammaTorsion_of_nat_smul_eq_zero (K := K) (K' := K') hn ?_
  rw [Nat.cast_smul_eq_nsmul]
  have hmap : (MonoidHom.toAdditive (gammaBaseChangeHom (K := K) (K' := K') ℓ L)) (n • x)
      = n • (MonoidHom.toAdditive (gammaBaseChangeHom (K := K) (K' := K') ℓ L)) x :=
    AddMonoidHom.map_nsmul _ n x
  rw [← hmap, hzero, map_zero]

end NK.Reconstruct
