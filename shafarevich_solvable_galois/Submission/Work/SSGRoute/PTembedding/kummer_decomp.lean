import Mathlib
import Submission.Work.SSGRoute.PTembedding.KummerMuDefs
import Submission.Work.SSGRoute.PTembedding.hilbert90_decomp
import Submission.Work.SSGRoute.PTembedding.mup_kummer_defs
import Submission.Work.SSGRoute.LTDDefs.DecompAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Kummer theory over the decomposition group

`H¹(D_A, μ_p) ≅ Fˣ ⧸ (Fˣ)^p` for the decomposition field `F = Ω^{D_A}` of a finite place `A`.
-/

open SSGRoute
open Work.SSGRoute

namespace Work.SSGRoute.PTembedding.MupCard

noncomputable section

set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- The decomposition field is the fixed field of `decomp k A`. -/
theorem decompField_eq_fixedField (A : ValuationSubring Ω) :
    Work.SSGRoute.mup.decompField k Ω A = IntermediateField.fixedField (SSGRoute.decomp k A) :=
  rfl

/-- A `p`-th root of unity of `Ω` lies in `K` (since `ζ ∈ K` is primitive). -/
theorem mem_K_of_pow_eq_one {K : IntermediateField k Ω} {ζ : Ω} (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K) {x : Ω} (hx : x ^ p = 1) : x ∈ K := by
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [← hi]
  exact pow_mem hζK i

/-- The Galois action on the units intertwines with the Galois action on `Ω`. -/
@[simp] theorem algEquivUnitsMapOfField_smul_eq (σ : Ω ≃ₐ[k] Ω) (u : Units Ω) :
    ((Work.SSGRoute.PT.algEquivUnitsMapOfField k Ω σ u : Units Ω) : Ω) = σ (u : Ω) := rfl

section Cocycle

variable (A : ValuationSubring Ω)

/-- A `p`-th root in `Ω` of a unit of the decomposition field `F = Ω^{D_A}`. -/
theorem exists_pow_eq (a : (↥(Work.SSGRoute.mup.decompField k Ω A))ˣ) :
    ∃ α : Units Ω,
      α ^ p = Units.map (algebraMap ↥(Work.SSGRoute.mup.decompField k Ω A) Ω).toMonoidHom a := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (a : Ω) (Fact.out : p.Prime).pos
  have hy0 : y ≠ 0 := by
    intro hy0
    have h1 : ((a : ↥(Work.SSGRoute.mup.decompField k Ω A)) : Ω) = 0 := by
      rw [← hy, hy0, zero_pow (Fact.out : p.Prime).ne_zero]
    exact a.ne_zero (Subtype.ext (by simpa using h1))
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map]
  exact hy

end Cocycle




section Kummer

variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)

/-- The ratio `σ α / α` for `σ ∈ D_A`, as a unit of `Ω`. -/
noncomputable def kummerRatio (α : Units Ω) (σ : ↥(SSGRoute.decomp k A)) : Units Ω :=
  Work.SSGRoute.PT.algEquivUnitsMapOfField k Ω (σ : Ω ≃ₐ[k] Ω) α / α

theorem kummerRatio_coe (α : Units Ω) (σ : ↥(SSGRoute.decomp k A)) :
    ((kummerRatio A α σ : Units Ω) : Ω)
      = (σ : Ω ≃ₐ[k] Ω) (α : Ω) / (α : Ω) := by
  rw [kummerRatio, Units.val_div_eq_div_val]
  rfl

/-- If `α ^ p` is a unit of the decomposition field `F = Ω^{D_A}`, then `σ α / α` is a `p`-th
root of unity. -/
theorem kummerRatio_pow (a : (↥(Work.SSGRoute.mup.decompField k Ω A))ˣ) (α : Units Ω)
    (hα : α ^ p = Units.map (algebraMap ↥(Work.SSGRoute.mup.decompField k Ω A) Ω).toMonoidHom a)
    (σ : ↥(SSGRoute.decomp k A)) :
    ((kummerRatio A α σ : Units Ω) : Ω) ^ p = 1 := by
  have hfix : (σ : Ω ≃ₐ[k] Ω) ((α ^ p : Units Ω) : Ω) = ((α ^ p : Units Ω) : Ω) := by
    have h1 : ((α ^ p : Units Ω) : Ω)
        = ((a : ↥(Work.SSGRoute.mup.decompField k Ω A)) : Ω) := by
      rw [hα]
      rfl
    rw [h1]
    exact (IntermediateField.mem_fixedField_iff (SSGRoute.decomp k A) _).mp
      ((a : ↥(Work.SSGRoute.mup.decompField k Ω A))).2 (σ : Ω ≃ₐ[k] Ω) σ.2
  rw [kummerRatio_coe A α σ, div_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hfix]
  exact div_self (α ^ p).ne_zero

end Kummer

/-! ## The Kummer sequence over the decomposition group -/

section PowPi

/-- **The `p`-th power endomorphism of `Ωˣ`**, as an additive endomorphism of `Additive Ωˣ`. -/
noncomputable def powPi : Additive (Units Ω) →+ Additive (Units Ω) where
  toFun a := Additive.ofMul (Additive.toMul a ^ p)
  map_zero' := by
    apply Additive.toMul.injective
    show Additive.toMul (Additive.ofMul (Additive.toMul (0 : Additive (Units Ω)) ^ p))
      = Additive.toMul (0 : Additive (Units Ω))
    simp
  map_add' a b := by
    apply Additive.toMul.injective
    show Additive.toMul (Additive.ofMul (Additive.toMul (a + b) ^ p))
      = Additive.toMul (Additive.ofMul (Additive.toMul a ^ p)
          + Additive.ofMul (Additive.toMul b ^ p))
    simp [mul_pow]

@[simp] theorem powPi_apply (a : Additive (Units Ω)) :
    powPi (p := p) a = Additive.ofMul (Additive.toMul a ^ p) := rfl

/-- `powPi` is multiplication by `p` in the additive notation. -/
theorem powPi_eq_nsmul (a : Additive (Units Ω)) : powPi (p := p) a = p • a := by
  rw [powPi_apply]
  have h : (p • a) = Additive.ofMul (Additive.toMul a ^ p) := by
    rw [← ofMul_toMul a, ofMul_pow, toMul_ofMul]
  rw [h]

/-- `powPi` is equivariant for the natural action of any subgroup of `G_k`. -/
theorem powPi_equivariant (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Work.GroupCohomology.IsEquivariant ↥H (powPi (p := p) (Ω := Ω)) := by
  intro g a
  rw [powPi_eq_nsmul, powPi_eq_nsmul, smul_nsmul_comm]

end PowPi

section KummerSES

variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- The action of the decomposition group of `A` on `μ_p ⊆ K`, through the restriction `res k K`. -/
noncomputable instance instDistribMulActionDecompMuAdd (A : ValuationSubring Ω) :
    DistribMulAction ↥(SSGRoute.decomp k A) (MuAdd p K) :=
  SSGRoute.decompDistribMulAction K (MuAdd p K) A

/-- **The Kummer inclusion** `μ_p(K) ↪ Ωˣ`, induced by the inclusion `K ⊆ Ω`. -/
noncomputable def muIota : MuAdd p K →+ Additive (Units Ω) where
  toFun a := Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidHom
    ((Additive.toMul a : rootsOfUnity p K) : (↥K)ˣ))
  map_zero' := by
    apply Additive.toMul.injective
    show Additive.toMul (Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidHom
        ((Additive.toMul (0 : MuAdd p K) : rootsOfUnity p K) : (↥K)ˣ)))
      = Additive.toMul (0 : Additive (Units Ω))
    simp
  map_add' a b := by
    apply Additive.toMul.injective
    show Additive.toMul (Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidHom
        ((Additive.toMul (a + b) : rootsOfUnity p K) : (↥K)ˣ)))
      = Additive.toMul (Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidHom
            ((Additive.toMul a : rootsOfUnity p K) : (↥K)ˣ))
          + Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidHom
            ((Additive.toMul b : rootsOfUnity p K) : (↥K)ˣ)))
    simp [map_mul]

@[simp] theorem muIota_apply (a : MuAdd p K) :
    muIota (p := p) (K := K) a
      = Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidHom
          ((Additive.toMul a : rootsOfUnity p K) : (↥K)ˣ)) := rfl

end KummerSES

end

end Work.SSGRoute.PTembedding.MupCard
