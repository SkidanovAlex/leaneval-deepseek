import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Galois twist of the idèle of a prime is congruent to the idèle of the conjugate prime

For a Galois automorphism `ρ` of a number field `K` and a finite place `Q'` whose conjugates lie
outside the support of a modulus `𝔪`, the idèles `ρ • ideleOfIdeal K Q'.asIdeal` and
`ideleOfIdeal K (ρ Q').asIdeal` agree at every place except `ρ Q'`, and at `ρ Q'` they are both
uniformisers, so their quotient is a local unit there.  Since the modulus imposes no condition at
`ρ Q'`, the quotient lies in the congruence subgroup `U(𝔪)`.

The file develops the small amount of local arithmetic needed for this: the Galois action on idèles
is computed on `ideleOfFun` idèles, the local ring isomorphisms preserve the valuation, and the
congruence condition at exponent `0` is automatic for a local unit.
-/

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors Pointwise Classical

namespace Work.SSGRoute.ZDataTwo.TwoRec

/-! ## Elementary places of the height-one spectrum -/

/-- The `q`-adic count of the height-one prime `q₀` is `1` at `q = q₀` and `0` elsewhere. -/
theorem fractionalIdeal_count_asIdeal_self {K : Type} [Field K] [NumberField K]
    (q q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FractionalIdeal.count K q
        (q₀.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
      (if q = q₀ then 1 else 0) := by
  classical
  by_cases h : q = q₀
  · subst h
    rw [if_pos rfl]
    exact FractionalIdeal.count_self K q
  · rw [if_neg h]
    rw [FractionalIdeal.count_coe K q (show q₀.asIdeal ≠ 0 from fun hh => q₀.ne_bot hh)]
    rw [Nat.cast_eq_zero, ← not_ne_iff]
    intro hne
    rw [Associates.count_ne_zero_iff_dvd
      (show q₀.asIdeal ≠ 0 from fun hh => q₀.ne_bot hh) q.irreducible] at hne
    have hle : q₀.asIdeal ≤ q.asIdeal := Ideal.dvd_iff_le.mp hne
    have hmax : q₀.asIdeal = q.asIdeal :=
      Ideal.IsMaximal.eq_of_le q₀.isMaximal q.isPrime.ne_top hle
    exact h (by apply IsDedekindDomain.HeightOneSpectrum.ext; exact hmax.symm)

/-! ## The Galois action on finite places -/

section Smul

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The Galois action on finite places is a group action: undoing `ρ` with `ρ⁻¹` returns the
place. -/
theorem smulHeightOneSpectrum_inv_smul (ρ : K ≃ₐ[k] K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.GlobalCFT.Place.smulHeightOneSpectrum ρ
        (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q) = q := by
  have h : ρ • (ρ⁻¹ • NK.GlobalCFT.Place.ofFinite q) = NK.GlobalCFT.Place.ofFinite q :=
    smul_inv_smul ρ (NK.GlobalCFT.Place.ofFinite q)
  simp only [NK.GlobalCFT.Place.smul_ofFinite] at h
  exact NK.GlobalCFT.Place.ofFinite_inj.mp h

end Smul

/-! ## The local ring isomorphism preserves the valuation, in the inverse direction -/

section Valued

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The inverse of the canonical local field isomorphism `K_q ≃+* K_{ρ⁻¹ q}` preserves the
valuation. -/
theorem localRingEquiv_symm_valued_apply (ρ : K ≃ₐ[k] K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (y : NK.GlobalCFT.Place.localField K
      (NK.GlobalCFT.Place.ofFinite (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q))) :
    Valued.v ((NK.GlobalCFT.Place.localRingEquiv ρ⁻¹ (NK.GlobalCFT.Place.ofFinite q)).symm y) =
      Valued.v y := by
  have h := NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_valued (K := k) (L := K) ρ⁻¹ q
    ((NK.GlobalCFT.Place.localRingEquiv ρ⁻¹ (NK.GlobalCFT.Place.ofFinite q)).symm y)
  rw [show NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv ρ⁻¹ q
        ((NK.GlobalCFT.Place.localRingEquiv ρ⁻¹ (NK.GlobalCFT.Place.ofFinite q)).symm y) = y from
      RingEquiv.apply_symm_apply _ _] at h
  exact h.symm

/-- The unit form of `localRingEquiv_symm_valued_apply`. -/
theorem localRingEquiv_symm_valued (ρ : K ≃ₐ[k] K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (NK.GlobalCFT.Place.localField K
      (NK.GlobalCFT.Place.ofFinite (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)))ˣ) :
    Valued.v ((Units.map (NK.GlobalCFT.Place.localRingEquiv ρ⁻¹
        (NK.GlobalCFT.Place.ofFinite q)).symm.toMonoidHom u :
        (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q))ˣ) :
        NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)) =
      Valued.v ((u : NK.GlobalCFT.Place.localField K
        (NK.GlobalCFT.Place.ofFinite (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)))) := by
  rw [Units.coe_map]
  exact localRingEquiv_symm_valued_apply ρ q (u : _)

end Valued

/-! ## The value of the Galois twist of `ideleOfIdeal` -/

section Apply

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The value of `ρ • ideleOfIdeal K Q'.asIdeal` at the finite place `q`: it is the image under
the local isomorphism of the idèle of `Q'` evaluated at `ρ⁻¹ q`. -/
theorem smul_ideleOfIdeal_apply_finite (ρ : K ≃ₐ[k] K)
    (Q' q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) (NK.GlobalCFT.Place.ofFinite q) =
      Units.map (NK.GlobalCFT.Place.localRingEquiv ρ⁻¹
        (NK.GlobalCFT.Place.ofFinite q)).symm.toMonoidHom
        (NK.GlobalCFT.IdeleClassGroup.unifUnit K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q) ^
          FractionalIdeal.count K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q)
            (Q'.asIdeal : FractionalIdeal
              (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) := rfl

/-- The value of `ρ • ideleOfIdeal K Q'.asIdeal` at an infinite place is `1`. -/
theorem smul_ideleOfIdeal_apply_infinite (ρ : K ≃ₐ[k] K)
    (Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : NumberField.InfinitePlace K) :
    (ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) (NK.GlobalCFT.Place.ofInfinite w) = 1 := by
  rw [NK.GlobalCFT.Idele.smul_apply]
  have h1 : (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)
      (ρ⁻¹ • NK.GlobalCFT.Place.ofInfinite w) = 1 := rfl
  rw [h1]
  exact map_one _

end Apply

/-! ## The congruence condition at exponent zero -/

section Cong

variable {K : Type} [Field K] [NumberField K]

/-- The trivial idèle is congruent to `1` modulo every modulus. -/
theorem isCongAt_one
    (m : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.NUV2.RouteB.IsCongAt K m q 1 := by
  rw [NK.NUV2.RouteB.IsCongAt]
  rw [show ((1 : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K q)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion K q) - 1 = 0 from by simp]
  rw [show Valued.v (0 : IsDedekindDomain.HeightOneSpectrum.adicCompletion K q) = 0 from
    map_zero _]
  exact WithZero.zero_le _

/-- A local unit is congruent to `1` modulo a modulus of exponent `0` at that place. -/
theorem isCongAt_of_valued_eq_one
    (m : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K q)ˣ)
    (hq : m q = 0)
    (hx : Valued.v ((x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K q)) = 1) :
    NK.NUV2.RouteB.IsCongAt K m q x := by
  have hneg : Valued.v (-1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion K q) = 1 := by
    rw [show (-1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion K q) =
          -(1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion K q) from by simp,
      Valuation.map_neg, Valuation.map_one]
  rw [NK.NUV2.RouteB.IsCongAt, hq, Nat.cast_zero, neg_zero]
  calc Valued.v ((x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K q) - 1)
      = Valued.v ((x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K q) +
          (-1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion K q)) := by
        rw [sub_eq_add_neg]
    _ ≤ max (Valued.v ((x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K q)))
          (Valued.v (-1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion K q)) :=
        Valuation.map_add _ _ _
    _ = WithZero.exp (0 : ℤ) := by
        rw [hx, hneg, max_self]
        exact WithZero.exp_zero.symm

end Cong

/-! ## The main congruence -/

theorem smul_ideleOfIdeal_cong {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (𝔪 : NK.NUV2.RouteB.Modulus K)
    (Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : 𝔪.exps Q' = 0)
    (hQ' : 𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q') = 0) :
    (ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) *
        (NK.HeckeL.ideleOfIdeal K
          (Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q').asIdeal)⁻¹
      ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
  classical
  have hplace : Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' =
      NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q' :=
    (NK.GlobalCFT.Inclusion.smulHeightOneSpectrum_eq_placeSmul (K := k) (L := K) ρ Q').symm
  rw [hplace]
  set q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q' with hq₀def
  have hbridge : NK.GlobalCFT.Place.smulHeightOneSpectrum ρ Q' =
      Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' := hq₀def.symm.trans hplace.symm
  have hexp : 𝔪.exps q₀ = 0 := by
    rw [hq₀def, hbridge]
    exact hQ'
  -- The Galois twist vanishes at every finite place other than `q₀`.
  have hxq : ∀ q, q ≠ q₀ →
      (ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) (NK.GlobalCFT.Place.ofFinite q) = 1 := by
    intro q hq
    rw [smul_ideleOfIdeal_apply_finite]
    have hq'' : NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q ≠ Q' := by
      intro h
      apply hq
      rw [hq₀def]
      have h2 := congrArg (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ) h
      rw [smulHeightOneSpectrum_inv_smul] at h2
      exact h2
    rw [fractionalIdeal_count_asIdeal_self, if_neg hq'', zpow_zero]
    exact map_one _
  -- The idèle of `q₀` vanishes at every finite place other than `q₀`.
  have hyq : ∀ q, q ≠ q₀ →
      NK.HeckeL.ideleOfIdeal K q₀.asIdeal (NK.GlobalCFT.Place.ofFinite q) = 1 := by
    intro q hq
    show NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^
      FractionalIdeal.count K q
        (q₀.asIdeal : FractionalIdeal
          (nonZeroDivisors (NumberField.RingOfIntegers K)) K) = 1
    rw [fractionalIdeal_count_asIdeal_self, if_neg hq, zpow_zero]
  -- Both are `1` at the infinite places.
  have hxinf : ∀ w : NumberField.InfinitePlace K,
      (ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) (NK.GlobalCFT.Place.ofInfinite w) = 1 :=
    fun w => smul_ideleOfIdeal_apply_infinite ρ Q' w
  have hyinf : ∀ w : NumberField.InfinitePlace K,
      NK.HeckeL.ideleOfIdeal K q₀.asIdeal (NK.GlobalCFT.Place.ofInfinite w) = 1 := by
    intro w
    show (1 : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ) = 1
    rfl
  -- At `q₀` both are uniformisers, hence of equal valuation.
  have hsmul : NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q₀ = Q' := by
    have hq₀smul : NK.GlobalCFT.Place.ofFinite q₀ = ρ • NK.GlobalCFT.Place.ofFinite Q' :=
      (congrArg NK.GlobalCFT.Place.ofFinite hq₀def).trans
        (NK.GlobalCFT.Place.smul_ofFinite ρ Q').symm
    have h : ρ⁻¹ • (ρ • NK.GlobalCFT.Place.ofFinite Q') = NK.GlobalCFT.Place.ofFinite Q' :=
      inv_smul_smul ρ (NK.GlobalCFT.Place.ofFinite Q')
    rw [← hq₀smul] at h
    rw [NK.GlobalCFT.Place.smul_ofFinite] at h
    exact NK.GlobalCFT.Place.ofFinite_inj.mp h
  have hcount : FractionalIdeal.count K (NK.GlobalCFT.Place.smulHeightOneSpectrum ρ⁻¹ q₀)
      (Q'.asIdeal : FractionalIdeal
        (nonZeroDivisors (NumberField.RingOfIntegers K)) K) = 1 := by
    rw [fractionalIdeal_count_asIdeal_self, if_pos hsmul]
  have hx_val : Valued.v (((ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal)
        (NK.GlobalCFT.Place.ofFinite q₀) :
        (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q₀))ˣ) :
        NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q₀)) =
      WithZero.exp (-1 : ℤ) := by
    rw [smul_ideleOfIdeal_apply_finite]
    rw [localRingEquiv_symm_valued]
    rw [NK.GlobalCFT.IdeleClassGroup.valued_unifUnit_zpow]
    rw [hcount]
  have hy_val : Valued.v ((NK.HeckeL.ideleOfIdeal K q₀.asIdeal
        (NK.GlobalCFT.Place.ofFinite q₀) :
        (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q₀))ˣ) :
        NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q₀)) =
      WithZero.exp (-1 : ℤ) := by
    show Valued.v (((NK.GlobalCFT.IdeleClassGroup.unifUnit K q₀ ^
        FractionalIdeal.count K q₀
          (q₀.asIdeal : FractionalIdeal
            (nonZeroDivisors (NumberField.RingOfIntegers K)) K) :
        (q₀.adicCompletion K)ˣ) : q₀.adicCompletion K)) = WithZero.exp (-1 : ℤ)
    rw [FractionalIdeal.count_self, zpow_one]
    exact NK.GlobalCFT.IdeleClassGroup.valued_unifUnit q₀
  rw [NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff]
  refine ⟨fun q => ?_, fun w hw hpos => ?_⟩
  · by_cases hq : q = q₀
    · subst hq
      have hzv : Valued.v (((((ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) *
            (NK.HeckeL.ideleOfIdeal K q₀.asIdeal)⁻¹) (NK.GlobalCFT.Place.ofFinite q₀)) :
            (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q₀))ˣ) :
            NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q₀)) = 1 := by
        rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, Units.val_mul,
          Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx_val, hy_val]
        exact mul_inv_cancel₀ WithZero.exp_ne_zero
      exact ⟨hzv, isCongAt_of_valued_eq_one (𝔪.exps) q₀ _ hexp hzv⟩
    · have hz1 : (((ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) *
            (NK.HeckeL.ideleOfIdeal K q₀.asIdeal)⁻¹)
            (NK.GlobalCFT.Place.ofFinite q)) = 1 := by
        rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, hxq q hq, hyq q hq]
        simp
      refine ⟨?_, ?_⟩
      · rw [hz1]
        simp
      · rw [hz1]
        exact isCongAt_one (𝔪.exps) q
  · have hz1 : (((ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) *
          (NK.HeckeL.ideleOfIdeal K q₀.asIdeal)⁻¹)
          (NK.GlobalCFT.Place.ofInfinite w)) = 1 := by
      rw [NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, hxinf w, hyinf w]
      simp
    rw [hz1]
    simp

end Work.SSGRoute.ZDataTwo.TwoRec
