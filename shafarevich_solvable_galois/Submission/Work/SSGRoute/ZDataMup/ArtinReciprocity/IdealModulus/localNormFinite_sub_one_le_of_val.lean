import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Integral
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
import Submission.NK.CFTLib.Arl.val_norm_one_add_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped NumberField WithZero
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

/-- **The norm of a principal one-unit, relative to an arbitrary integral modulus element.**

Let `K ⊆ L` be a finite extension of number fields, `Q` a finite prime of `K`, `q` a prime of `L`
above `Q`, and `0 ≠ y` in the ring of integers `𝒪_Q` of the `Q`-adic completion of `K`.  For `z`
in the `q`-adic completion of `L` with `v_q z ≤ v_q y` (i.e. `z ≡ 0 mod y` in the `q`-adic
completion), the local norm satisfies

`v_Q (N_{L_q/K_Q} (1 + z) - 1) ≤ v_Q y`,

i.e. the norm of a principal unit congruent to `1` modulo `y` is congruent to `1` modulo `y`.

This is the exact generalisation of `NK.CFTLib.Arl.val_norm_one_add_le` from the case
`y = (m : ℕ)`, `m > 0`, to an arbitrary nonzero element of `Q.adicCompletionIntegers K`; the
proof of `val_norm_one_add_le` applies verbatim with `(m : ℕ)` replaced by `y`. -/
theorem val_norm_one_add_le_of_val {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (y : Q.adicCompletionIntegers K) (hy : y ≠ 0) (z : q.adicCompletion L)
    (hz : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) z ≤
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K))) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((Algebra.norm (Q.adicCompletion K) (1 + z)) - 1)
      ≤ Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (y : Q.adicCompletion K) := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- ## The algebra structure of `L_q` over `A := 𝓞_Q` and the scalar towers
  letI hAL : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  letI hstAL : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K)
      (q.adicCompletion L) := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  -- ## Structural instances for the local extension `L_q / K_Q`
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hczK : CharZero (Q.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (Q.adicCompletion K)).injective
  haveI hczL : CharZero (q.adicCompletion L) :=
    charZero_of_injective_algebraMap (algebraMap L (q.adicCompletion L)).injective
  haveI hInt : Algebra.IsIntegral (Q.adicCompletion K) (q.adicCompletion L) :=
    Algebra.IsIntegral.of_finite (Q.adicCompletion K) (q.adicCompletion L)
  haveI hsep : Algebra.IsSeparable (Q.adicCompletion K) (q.adicCompletion L) :=
    Algebra.IsSeparable.of_integral (Q.adicCompletion K) (q.adicCompletion L)
  letI hic : IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
      Q q hq
  -- ## Step 1: write `z = y * a` with `a` integral at `q`
  have hyK : (y : Q.adicCompletion K) ≠ 0 := fun h => hy (Subtype.ext h)
  have hyL : Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K) ≠ 0 :=
    fun h => hyK (RingHom.injective (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
      (by rw [h, map_zero]))
  have hyvL : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hyL
  have hyvL_pos : (0 : WithZero (Multiplicative ℤ)) <
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K)) :=
    pos_iff_ne_zero.mpr hyvL
  set a : q.adicCompletion L :=
    z / Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K) with ha_def
  have hz_eq : z = Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K)
      * a := by
    rw [ha_def]
    exact (mul_div_cancel₀ z hyL).symm
  have ha_val : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) a ≤ 1 := by
    have h1 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) a *
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K)) =
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) z := by
      rw [← Valuation.map_mul, ha_def, div_mul_cancel₀ z hyL]
    have h2 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) a *
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K)) ≤
        (1 : WithZero (Multiplicative ℤ)) *
          Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K)) := by
      rw [h1, one_mul]; exact hz
    exact (mul_le_mul_iff_left₀ hyvL_pos).mp h2
  have ha_mem : a ∈ q.adicCompletionIntegers L :=
    (mem_adicCompletionIntegers (R := 𝓞 L) L q).mpr ha_val
  have ha_int : IsIntegral (Q.adicCompletionIntegers K) a :=
    (IsIntegralClosure.isIntegral_iff (R := Q.adicCompletionIntegers K)
      (A := q.adicCompletionIntegers L) (B := q.adicCompletion L)).mpr ⟨⟨a, ha_mem⟩, rfl⟩
  -- ## Step 2: the algebraic closure and the product formula for the norm
  let Ω := AlgebraicClosure (q.adicCompletion L)
  letI hAO : Algebra (Q.adicCompletionIntegers K) Ω := inferInstance
  letI hstAO : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K) Ω := inferInstance
  have hnorm : algebraMap (Q.adicCompletion K) Ω
        (Algebra.norm (Q.adicCompletion K) (1 + z)) =
      ∏ σ : q.adicCompletion L →ₐ[Q.adicCompletion K] Ω, σ (1 + z) :=
    Algebra.norm_eq_prod_embeddings (Q.adicCompletion K) (E := Ω) (1 + z)
  -- ## Step 3: the factors lie in the integral closure of `A` in `Ω`
  let Acl := integralClosure (Q.adicCompletionIntegers K) Ω
  letI hAAcl : Algebra (Q.adicCompletionIntegers K) Acl := inferInstance
  letI hstAcl : IsScalarTower (Q.adicCompletionIntegers K) Acl Ω := inferInstance
  let xΩ : Acl := ⟨algebraMap (Q.adicCompletionIntegers K) Ω y,
    (mem_integralClosure_iff _ _).mpr isIntegral_algebraMap⟩
  have hxΩ : (xΩ : Ω) = algebraMap (Q.adicCompletion K) Ω (y : Q.adicCompletion K) := by
    show algebraMap (Q.adicCompletionIntegers K) Ω y =
      algebraMap (Q.adicCompletion K) Ω (y : Q.adicCompletion K)
    rw [IsScalarTower.algebraMap_apply (Q.adicCompletionIntegers K) (Q.adicCompletion K) Ω y]
    rfl
  let g : (q.adicCompletion L →ₐ[Q.adicCompletion K] Ω) → Acl :=
    fun σ => ⟨σ a, (mem_integralClosure_iff _ _).mpr (IsIntegral.map σ ha_int)⟩
  have hg : ∀ σ, (g σ : Ω) = σ a := fun σ => rfl
  have hpt : ∀ σ : q.adicCompletion L →ₐ[Q.adicCompletion K] Ω,
      ((1 + xΩ * g σ : Acl) : Ω) = σ (1 + z) := by
    intro σ
    have hmm : (xΩ : Ω) =
        σ (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K)) := by
      have hba : (algebraMap (Q.adicCompletion K) (q.adicCompletion L))
          = Commons.RingTheory.Henselian.adicCompletionMap Q q hq :=
        RingHom.algebraMap_toAlgebra _
      rw [hxΩ, ← hba]
      exact (AlgHom.commutes σ (y : Q.adicCompletion K)).symm
    have h1 : ((1 + xΩ * g σ : Acl) : Ω) = 1 + (xΩ : Ω) * σ a := by
      rw [Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_mul, hg]
    have h8 : σ (1 + Commons.RingTheory.Henselian.adicCompletionMap Q q hq
          (y : Q.adicCompletion K) * a) =
        1 + σ (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K))
          * σ a := by
      rw [map_add, map_one, map_mul]
    rw [h1, hmm, hz_eq, h8]
  -- ## Step 4: the product of the factors is `≡ 1` modulo `x`
  obtain ⟨C, hC⟩ := NK.CFTLib.Arl.exists_prod_sub_one_eq_mul xΩ Finset.univ g
  have hcoe_prod : ((∏ σ : q.adicCompletion L →ₐ[Q.adicCompletion K] Ω,
      (1 + xΩ * g σ) : Acl) : Ω) = ∏ σ, ((1 + xΩ * g σ : Acl) : Ω) :=
    map_prod (Subalgebra.val Acl) (fun σ => (1 + xΩ * g σ)) Finset.univ
  have hprod : (∏ σ : q.adicCompletion L →ₐ[Q.adicCompletion K] Ω,
      ((1 + xΩ * g σ : Acl) : Ω)) =
      ∏ σ : q.adicCompletion L →ₐ[Q.adicCompletion K] Ω, σ (1 + z) :=
    Finset.prod_congr rfl (fun σ _ => hpt σ)
  have h5 : (∏ σ : q.adicCompletion L →ₐ[Q.adicCompletion K] Ω, (1 + xΩ * g σ)) =
      1 + xΩ * C := by
    calc (∏ σ, (1 + xΩ * g σ)) = ((∏ σ, (1 + xΩ * g σ)) - 1) + 1 :=
          (sub_add_cancel _ _).symm
      _ = xΩ * C + 1 := by rw [hC]
      _ = 1 + xΩ * C := by ring
  have hCΩ : ((∏ σ : q.adicCompletion L →ₐ[Q.adicCompletion K] Ω, σ (1 + z)) - 1 : Ω) =
      algebraMap (Q.adicCompletion K) Ω (y : Q.adicCompletion K) * (C : Ω) := by
    have h6 : (∏ σ : q.adicCompletion L →ₐ[Q.adicCompletion K] Ω,
        ((1 + xΩ * g σ : Acl) : Ω)) =
        1 + algebraMap (Q.adicCompletion K) Ω (y : Q.adicCompletion K) * (C : Ω) := by
      have h7 : (∏ σ : q.adicCompletion L →ₐ[Q.adicCompletion K] Ω,
          ((1 + xΩ * g σ : Acl) : Ω)) = ((1 + xΩ * C : Acl) : Ω) := by
        rw [← hcoe_prod]
        exact congrArg (fun t : Acl => (t : Ω)) h5
      rw [h7, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_mul, hxΩ]
    rw [← hprod, h6]
    ring
  -- ## Step 5: division by `y` and integrality of the quotient
  set u : Q.adicCompletion K :=
    (Algebra.norm (Q.adicCompletion K) (1 + z) - 1) / (y : Q.adicCompletion K) with hu_def
  have hyΩ : algebraMap (Q.adicCompletion K) Ω (y : Q.adicCompletion K) ≠ 0 :=
    fun h => hyK (RingHom.injective (algebraMap (Q.adicCompletion K) Ω) (by rw [h, map_zero]))
  have hmap_u : algebraMap (Q.adicCompletion K) Ω u = (C : Ω) := by
    rw [hu_def, map_div₀, map_sub, map_one, hnorm, hCΩ]
    exact mul_div_cancel_left₀ (C : Ω) hyΩ
  have hu_int : IsIntegral (Q.adicCompletionIntegers K) u :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom _ (Q.adicCompletion K) Ω)
      (algebraMap (Q.adicCompletion K) Ω).injective).mp
      (by rw [IsScalarTower.coe_toAlgHom', hmap_u]; exact (mem_integralClosure_iff _ _).mp C.2)
  have hu_mem : u ∈ Q.adicCompletionIntegers K :=
    Valuation.Integers.mem_of_integral
      (v := (Valued.v : Valuation (Q.adicCompletion K) (WithZero (Multiplicative ℤ))))
      (Valuation.integer.integers
        (Valued.v : Valuation (Q.adicCompletion K) (WithZero (Multiplicative ℤ)))) hu_int
  have hu_val : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) u ≤ 1 :=
    (mem_adicCompletionIntegers (R := 𝓞 K) K Q).mp hu_mem
  -- ## Step 6: conclude
  have hu_eq : Algebra.norm (Q.adicCompletion K) (1 + z) - 1 =
      u * (y : Q.adicCompletion K) := by
    rw [hu_def]
    exact (div_mul_cancel₀ _ hyK).symm
  calc Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (Algebra.norm (Q.adicCompletion K) (1 + z) - 1)
      = Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (u * (y : Q.adicCompletion K)) := by rw [hu_eq]
    _ = Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) u *
          Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (y : Q.adicCompletion K) := Valuation.map_mul _ _ _
    _ ≤ (1 : WithZero (Multiplicative ℤ)) *
          Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (y : Q.adicCompletion K) := by gcongr
    _ = Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (y : Q.adicCompletion K) := one_mul _

/-- The local norm `N_{L_q/K_Q}` carries the principal units congruent to `1` modulo an integral
element `y` into the principal units congruent to `1` modulo `y`: if `u` is a unit of `L_q` with
`v_q (u - 1) ≤ v_q y`, then `v_Q (N_{L_q/K_Q}(u) - 1) ≤ v_Q y`.

This is the statement needed at level `𝔪` of the ideal-modulus congruence filtrations, where the
modulus at `𝔭` is an arbitrary ideal (so that the bound is `y ∈ 𝓞_Q`, not a natural number). -/
theorem localNormFinite_sub_one_le_of_val
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (y : Q.adicCompletionIntegers K) (hy : y ≠ 0)
    (u : (q.adicCompletion L)ˣ)
    (hu : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        ((u : q.adicCompletion L) - 1) ≤
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (y : Q.adicCompletion K))) :
    Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((NK.GlobalCFT.Place.localNormFinite q Q hq u : (Q.adicCompletion K)ˣ) :
          Q.adicCompletion K) - 1) ≤
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (y : Q.adicCompletion K) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  have hnorm : ((NK.GlobalCFT.Place.localNormFinite q Q hq u : (Q.adicCompletion K)ˣ) :
        Q.adicCompletion K)
      = Algebra.norm (Q.adicCompletion K) (1 + ((u : q.adicCompletion L) - 1)) := by
    rw [NK.GlobalCFT.Place.localNormFinite, Units.coe_map]
    congr 1
    ring
  rw [hnorm]
  exact val_norm_one_add_le_of_val Q q hq y hy _ hu

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
