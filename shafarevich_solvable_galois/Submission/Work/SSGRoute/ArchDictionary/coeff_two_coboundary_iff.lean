import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` coefficient computation behind `archDict_localZero_imp_coboundary`

For `p = 2` the canonical coefficient identification
`Φ = e1aCoeffNat 2 … E : E ≃+ Hom_ℤ(E', Ωˣ)` (`E' = DualMod 2 (E ⊗ T)`) takes values in the
`2`-torsion of `Ωˣ`, i.e. in `μ₂ = {±1}`, and every field automorphism fixes `μ₂`.  Hence the
`c`-equivariance of `Φ` reads, on generators, as

`Φ ((res c) • e) (ρ(res c) m) = Φ e m`,

and since `Φ` is injective the "cocycle identity" `Φ (x + e) (ρ(res c) m) = Φ e m` holds for all
`m` precisely when `x = (res c) • e - e`, i.e. precisely when `x` is the coboundary of `e` on the
involution group `⟨c⟩`.

This is the clean algebraic piece of the `p = 2` half of the archimedean comparison square (see
`ArchDictionary/NOTE_localZero_imp_coboundary_strategy.md`, §3).
-/

namespace Work.SSGRoute.ArchDictionary

set_option linter.unusedVariables false

/-- In a field `Ω`, an algebra automorphism `σ` fixes every element `a` of the additive group
`Additive Ωˣ` that is `2`-torsion (equivalently: every `u ∈ Ωˣ` with `u ^ 2 = 1`, i.e. `u = ±1`).

This is the only arithmetic input of the `p = 2` coefficient computation: the values of the
canonical Kummer dictionary lie in `μ₂`, and `μ₂` is fixed by every field automorphism. -/
lemma smul_addUnits_eq_self_of_two_nsmul_eq_zero (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (σ : Ω ≃ₐ[k] Ω) (a : Additive Ωˣ) (ha : (2 : ℕ) • a = 0) : σ • a = a := by
  have h2 : (Additive.toMul a) ^ 2 = 1 := by
    simpa using congrArg Additive.toMul ha
  apply Additive.toMul.injective
  rw [Work.SSGRoute.addUnits_smul_toMulΩ]
  apply Units.ext
  rw [Work.SSGRoute.algEquivUnitsMapΩ_coe]
  have hval : ((Additive.toMul a : Ωˣ) : Ω) ^ 2 = 1 := by
    have := congrArg (fun u : Ωˣ => (u : Ω)) h2
    simpa using this
  rcases sq_eq_one_iff.mp hval with h | h
  · rw [h, map_one]
  · rw [h, map_neg, map_one]

theorem coeff_two_coboundary_iff (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (x e : E) :
    (∀ m : Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T),
        (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K ζ hζ hζK T hT E (x + e))
            ((SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))).ρ (SSGRoute.res k K c) m)
          = (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K ζ hζ hζK T hT E e) m)
      ↔ x = (SSGRoute.res k K c) • e - e := by
  classical
  set Φ := Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K ζ hζ hζK T hT E with hΦdef
  -- `c`-equivariance of the canonical coefficient identification
  have hΦc : Φ ((SSGRoute.res k K c) • e) = c • Φ e :=
    Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant 2 k Ω K ζ hζ hζK T hT E c e
  -- the values of `Φ` are `2`-torsion, hence fixed by every automorphism of `Ω`
  have hfix : ∀ (e' : E) (m : Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T)),
      c • (Φ e' m) = Φ e' m := by
    intro e' m
    have hm2 : (2 : ℕ) • m = 0 := by
      have h : ((2 : ℕ) : ZMod 2) = 0 := by decide
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 m, h, zero_smul]
    have h2 : (2 : ℕ) • (Φ e' m) = 0 := by
      have hmap : (Φ e' : Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T) →+ Additive Ωˣ)
            ((2 : ℕ) • m)
          = (2 : ℕ) • ((Φ e' : Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T) →+ Additive Ωˣ) m) :=
        map_nsmul (Φ e' : Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T) →+ Additive Ωˣ) 2 m
      rw [← hmap, hm2]
      exact map_zero _
    exact smul_addUnits_eq_self_of_two_nsmul_eq_zero k Ω c _ h2
  constructor
  · -- `⟹`: the hypothesis forces `Φ x` and `Φ ((res c) • e - e)` to agree, hence `x` is the
    -- coboundary of `e`
    intro h
    apply Φ.injective
    refine AddMonoidHom.ext (fun n : ↑(SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))) => ?_)
    -- `ρ(res c)` is invertible (it is a `K`-algebra automorphism of the finite module `E'`)
    have hρρ : (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))).ρ (SSGRoute.res k K c)
        (((SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))).ρ
            ((SSGRoute.res k K c)⁻¹)) n) = n := by
      change ((SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))).ρ (SSGRoute.res k K c) ∘ₗ
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))).ρ ((SSGRoute.res k K c)⁻¹)) n = n
      rw [← Rep.ρ_mul]
      simp
    have h1 : Φ x n = Φ e (((SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))).ρ
            ((SSGRoute.res k K c)⁻¹)) n) - Φ e n := by
      have hh := h (((SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))).ρ ((SSGRoute.res k K c)⁻¹)) n)
      rw [hρρ] at hh
      have hsum : Φ (x + e) n = Φ x n + Φ e n := by rw [map_add]; rfl
      rw [hsum] at hh
      exact (eq_sub_iff_add_eq).mpr hh
    have h2 : Φ ((SSGRoute.res k K c) • e - e) n
        = Φ e (((SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))).ρ
            ((SSGRoute.res k K c)⁻¹)) n) - Φ e n := by
      have hsub : Φ ((SSGRoute.res k K c) • e - e) n
          = Φ ((SSGRoute.res k K c) • e) n - Φ e n := by rw [map_sub]; rfl
      rw [hsub, hΦc, Work.SSGRoute.homCoind.smul_apply]
      exact congrArg (fun z : Additive Ωˣ => z - Φ e n)
        (hfix e (((SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))).ρ
            ((SSGRoute.res k K c)⁻¹)) n))
    rw [h1, h2]
  · -- `⟸`: if `x` is the coboundary of `e`, then `x + e = (res c) • e` and equivariance plus
    -- `hfix` give the identity
    intro hx
    rw [hx]
    intro m
    have heq : (SSGRoute.res k K c) • e - e + e = (SSGRoute.res k K c) • e := by abel
    rw [heq, hΦc, Work.SSGRoute.homCoind.smul_apply]
    have hinner : ((SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))).ρ
                ((SSGRoute.res k K c)⁻¹))
            (((SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))).ρ
                (SSGRoute.res k K c)) m) = m := by
      rw [Rep.ofDistribMulAction_ρ_apply_apply, Rep.ofDistribMulAction_ρ_apply_apply,
        inv_smul_smul]
    rw [hinner]
    exact hfix e m

end Work.SSGRoute.ArchDictionary
