import Mathlib
import Submission.Work.SSGRoute.CycLevel.routeA_defs
import Submission.NK.Chebotarev.FrobeniusGenerateTop
import Submission.Work.SSGRoute.CycLevel.cyclic_qpart_orderOf
import Submission.Work.SSGRoute.CycLevel.div_dvd_of_qpow_mul_dvd
import Submission.NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree
import Submission.NK.CFTLib.ArtinReciprocityIdeal.exists_algEquiv_zeta_pow
import Submission.Work.SSGRoute.ramificationIdx_mul_inertiaDeg_dvd_finrank
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped NumberField Pointwise
open NumberField IsDedekindDomain

namespace Work.SSGRoute.CycLevel

/-- **The cyclotomic character of `k⟮ζ_ℓ⟯/k` is bijective.**  For a number field `k`, a prime `ℓ`
with `ℓ ∤ disc k` and a primitive `ℓ`-th root of unity `ζ` in `AlgebraicClosure k`, the Galois
group of `k⟮ζ_ℓ⟯ / k` has cardinality `ℓ - 1`.

(This is the fragment of `cycM_structure_aux` computing the order of the cyclotomic level; it is
recorded separately since the main argument needs it for the degree `[k⟮ζ⟯ : k]`.) -/
theorem cycL_card_aut {k : Type} [Field k] [NumberField k] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hdisc : ¬ (ℓ : ℤ) ∣ NumberField.discr k) (ζ : AlgebraicClosure k)
    (hζ : IsPrimitiveRoot ζ ℓ) :
    Nat.card (↥(cycL ℓ ζ) ≃ₐ[k] ↥(cycL ℓ ζ)) = ℓ - 1 := by
  haveI hne : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI hfact : Fact ℓ.Prime := ⟨hℓ⟩
  have hζLmem : ζ ∈ cycL ℓ ζ := IntermediateField.mem_adjoin_simple_self k ζ
  have hζL : IsPrimitiveRoot (⟨ζ, hζLmem⟩ : ↥(cycL ℓ ζ)) ℓ :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp (by
      rw [show ((⟨ζ, hζLmem⟩ : ↥(cycL ℓ ζ)) : AlgebraicClosure k) = ζ from rfl]
      exact hζ)
  haveI hcyc : IsCyclotomicExtension {ℓ} k ↥(cycL ℓ ζ) :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin ℓ k (AlgebraicClosure k)
      (cycL ℓ ζ) hζ).mpr rfl
  have hθinj : Function.Injective (IsPrimitiveRoot.autToPow k hζL) :=
    IsPrimitiveRoot.autToPow_injective k hζL
  have hθsurj : Function.Surjective (IsPrimitiveRoot.autToPow k hζL) := by
    intro τ
    obtain ⟨σ, hσ⟩ :=
      NK.CFTLib.ArtinReciprocityIdeal.exists_algEquiv_zeta_pow ℓ hℓ hdisc ζ hζ τ
    refine ⟨σ, ?_⟩
    have h1 : (⟨ζ, hζLmem⟩ : ↥(cycL ℓ ζ))
          ^ (((IsPrimitiveRoot.autToPow k hζL σ : (ZMod ℓ)ˣ) : ZMod ℓ)).val
        = (⟨ζ, hζLmem⟩ : ↥(cycL ℓ ζ)) ^ ((τ : ZMod ℓ)).val :=
      (IsPrimitiveRoot.autToPow_spec k hζL σ).trans hσ
    exact Units.ext (ZMod.val_injective ℓ
      (pow_val_eq_of_lt hℓ hζL (ZMod.val_lt _) (ZMod.val_lt _) h1))
  have hbij : Function.Bijective (IsPrimitiveRoot.autToPow k hζL) := ⟨hθinj, hθsurj⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, ZMod.card_units]

/-- **`cycM_fullLocal`.**  Every finite place of `↥(cycM q e ℓ ζ)` above `v₀` has full local
degree: its stabiliser in `Gal(cycM/k)` is the whole group. -/
theorem cycM_fullLocal (k : Type) [Field k] [NumberField k] (q e ℓ : ℕ) (hq : q.Prime)
    (hℓ : ℓ.Prime) (he : 0 < e) (hdisc : ¬ (ℓ : ℤ) ∣ NumberField.discr k)
    (hdvd : q ^ e ∣ ℓ - 1) (ζ : AlgebraicClosure k) (hζ : IsPrimitiveRoot ζ ℓ)
    [NumberField ↥(cycM q e ℓ ζ)]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hres : (ℓ : NumberField.RingOfIntegers k) ∉ v₀.asIdeal)
    (hnotpow : ¬ ∃ x : (ZMod ℓ)ˣ,
      (x : ZMod ℓ) ^ q = ((Nat.card (NumberField.RingOfIntegers k ⧸ v₀.asIdeal) : ℕ) : ZMod ℓ)) :
    ∀ w : NK.GlobalCFT.Place ↥(cycM q e ℓ ζ),
      NK.GlobalCFT.Place.LiesOver w (NK.GlobalCFT.Place.ofFinite v₀) →
        Nat.card (MulAction.stabilizer (↥(cycM q e ℓ ζ) ≃ₐ[k] ↥(cycM q e ℓ ζ)) w) =
          Nat.card (↥(cycM q e ℓ ζ) ≃ₐ[k] ↥(cycM q e ℓ ζ)) := by
  classical
  haveI hℓne : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI hℓfact : Fact ℓ.Prime := ⟨hℓ⟩
  -- ## 1. the structural data of `M := cycM q e ℓ ζ`
  obtain ⟨hfdM, _hnfM, hgalM, _hcycMinst, hcardM⟩ :=
    cycM_structure_aux k q e ℓ hq hℓ he hdisc hdvd ζ hζ
  haveI : FiniteDimensional k ↥(cycM q e ℓ ζ) := hfdM
  haveI : IsGalois k ↥(cycM q e ℓ ζ) := hgalM
  have hfinM : Module.finrank k ↥(cycM q e ℓ ζ) = q ^ e := by
    rw [← IsGalois.card_aut_eq_finrank k ↥(cycM q e ℓ ζ)]
    exact hcardM
  -- ## 2. the structural data of `L := cycL ℓ ζ`
  have hML : cycM q e ℓ ζ ≤ cycL ℓ ζ := IntermediateField.lift_le _
  haveI hcycL : IsCyclotomicExtension {ℓ} k ↥(cycL ℓ ζ) :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin ℓ k (AlgebraicClosure k)
      (cycL ℓ ζ) hζ).mpr rfl
  haveI hfdL : FiniteDimensional k ↥(cycL ℓ ζ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} k ↥(cycL ℓ ζ)
  haveI hgalL : IsGalois k ↥(cycL ℓ ζ) := IsCyclotomicExtension.isGalois {ℓ} k ↥(cycL ℓ ζ)
  haveI hnfL : NumberField ↥(cycL ℓ ζ) := NumberField.of_module_finite k ↥(cycL ℓ ζ)
  have hcardL : Nat.card (↥(cycL ℓ ζ) ≃ₐ[k] ↥(cycL ℓ ζ)) = ℓ - 1 :=
    cycL_card_aut ℓ hℓ hdisc ζ hζ
  have hfinL : Module.finrank k ↥(cycL ℓ ζ) = ℓ - 1 := by
    rw [← IsGalois.card_aut_eq_finrank k ↥(cycL ℓ ζ)]
    exact hcardL
  -- ## 3. the tower `M ⊆ L`
  letI : Algebra ↥(cycM q e ℓ ζ) ↥(cycL ℓ ζ) :=
    (IntermediateField.inclusion hML).toRingHom.toAlgebra
  haveI : IsScalarTower k ↥(cycM q e ℓ ζ) ↥(cycL ℓ ζ) :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  haveI : FiniteDimensional ↥(cycM q e ℓ ζ) ↥(cycL ℓ ζ) :=
    FiniteDimensional.right k ↥(cycM q e ℓ ζ) ↥(cycL ℓ ζ)
  haveI : IsGalois ↥(cycM q e ℓ ζ) ↥(cycL ℓ ζ) :=
    IsGalois.tower_top_of_isGalois k ↥(cycM q e ℓ ζ) ↥(cycL ℓ ζ)
  haveI : Module.Free ↥(cycM q e ℓ ζ) ↥(cycL ℓ ζ) := Module.Free.of_divisionRing _ _
  have hfinML : Module.finrank ↥(cycM q e ℓ ζ) ↥(cycL ℓ ζ) = (ℓ - 1) / q ^ e := by
    have h1 : q ^ e * Module.finrank ↥(cycM q e ℓ ζ) ↥(cycL ℓ ζ) = ℓ - 1 := by
      rw [← hfinM, ← hfinL]
      exact Module.finrank_mul_finrank k ↥(cycM q e ℓ ζ) ↥(cycL ℓ ζ)
    have h2 : q ^ e * ((ℓ - 1) / q ^ e) = ℓ - 1 := Nat.mul_div_cancel' hdvd
    rw [← h2] at h1
    exact mul_left_cancel₀ (pow_pos hq.pos e).ne' h1
  -- ## 4. the conclusion, place by place
  intro w hw
  rcases (NK.GlobalCFT.Place.liesOver_iff w (NK.GlobalCFT.Place.ofFinite v₀)).mp hw with
    ⟨_, v', -, hv', -⟩ | ⟨P, Q, hwP, hvQ, hPQ⟩
  · exact absurd hv'.symm (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite v' v₀)
  · rw [hwP]
    have hvQ' : Q = v₀ := (NK.GlobalCFT.Place.ofFinite_inj.mp hvQ).symm
    rw [hvQ'] at hPQ
    haveI hPv : P.asIdeal.LiesOver v₀.asIdeal := hPQ
    -- the stabiliser of the place is the stabiliser of the prime
    have hplace : MulAction.stabilizer (↥(cycM q e ℓ ζ) ≃ₐ[k] ↥(cycM q e ℓ ζ))
          (NK.GlobalCFT.Place.ofFinite P)
        = MulAction.stabilizer (↥(cycM q e ℓ ζ) ≃ₐ[k] ↥(cycM q e ℓ ζ)) (P.asIdeal) := by
      ext σ
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
        NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj,
        IsDedekindDomain.HeightOneSpectrum.ext_iff,
        NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
      rw [Ideal.pointwise_smul_def]
      exact Iff.rfl
    rw [hplace]
    -- ## 5. a prime `W` of `𝓞 L` above `P`
    obtain ⟨W, hWP⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
        (K := ↥(cycM q e ℓ ζ)) (L := ↥(cycL ℓ ζ)) P
    have hWv : W.asIdeal.LiesOver v₀.asIdeal := NK.Chebotarev.liesOver_trans hWP hPv
    -- ## 6. the cyclotomic local degree at the level of `L`
    have hcycW : W.asIdeal.ramificationIdx (𝓞 k) = 1 ∧
        W.asIdeal.inertiaDeg (𝓞 k) =
          orderOf ((Ideal.absNorm v₀.asIdeal : ℕ) : ZMod ℓ) :=
      NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree (K := k) v₀ ℓ hℓ hres W hWv
    have habs : Nat.card (𝓞 k ⧸ v₀.asIdeal) = Ideal.absNorm v₀.asIdeal := by
      rw [Ideal.absNorm_apply]
      rfl
    -- ## 7. the tower multiplicativity of the inertia degree
    have htower_f : W.asIdeal.inertiaDeg (𝓞 k)
        = P.asIdeal.inertiaDeg (𝓞 k) * W.asIdeal.inertiaDeg (𝓞 ↥(cycM q e ℓ ζ)) := by
      haveI : W.asIdeal.LiesOver P.asIdeal := hWP
      exact Ideal.inertiaDeg_tower (R := 𝓞 k) P.asIdeal W.asIdeal
    -- ## 8. the residue cardinality `n` is not divisible by `ℓ`
    have hn : ¬ ℓ ∣ Nat.card (𝓞 k ⧸ v₀.asIdeal) := by
      intro hdvd'
      letI : Field (𝓞 k ⧸ v₀.asIdeal) := Ideal.Quotient.field v₀.asIdeal
      haveI : Finite (𝓞 k ⧸ v₀.asIdeal) :=
        Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum v₀
      haveI : Fintype (𝓞 k ⧸ v₀.asIdeal) := Fintype.ofFinite _
      obtain ⟨p, hcharp, m, hp, hcard⟩ := FiniteField.card' (𝓞 k ⧸ v₀.asIdeal)
      have hcard' : Nat.card (𝓞 k ⧸ v₀.asIdeal) = p ^ ((m : ℕ)) := by
        rw [Nat.card_eq_fintype_card]
        exact hcard
      have hℓp : ℓ ∣ p := by
        rw [hcard'] at hdvd'
        exact hℓ.dvd_of_dvd_pow hdvd'
      have hℓeq : ℓ = p := by
        rcases hp.eq_one_or_self_of_dvd ℓ hℓp with h1 | h1
        · exact absurd h1 hℓ.ne_one
        · exact h1
      have hcharℓ : CharP (𝓞 k ⧸ v₀.asIdeal) ℓ := hℓeq.symm ▸ hcharp
      have hzero : ((ℓ : ℕ) : 𝓞 k ⧸ v₀.asIdeal) = 0 :=
        (CharP.charP_iff_prime_eq_zero hℓ).mp hcharℓ
      apply hres
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      show Ideal.Quotient.mk v₀.asIdeal ((ℓ : ℕ) : 𝓞 k) = 0
      rw [map_natCast]
      exact hzero
    -- ## 9. the unit `u` with `u = n mod ℓ`
    have hcop : Nat.Coprime (Nat.card (𝓞 k ⧸ v₀.asIdeal)) ℓ :=
      ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hn).symm
    let u : (ZMod ℓ)ˣ := ZMod.unitOfCoprime (Nat.card (𝓞 k ⧸ v₀.asIdeal)) hcop
    have hu : (u : ZMod ℓ) = ((Nat.card (𝓞 k ⧸ v₀.asIdeal) : ℕ) : ZMod ℓ) :=
      ZMod.coe_unitOfCoprime _ _
    have hval : ((Ideal.absNorm v₀.asIdeal : ℕ) : ZMod ℓ) = (u : ZMod ℓ) := by
      rw [← habs, hu]
    have hord : W.asIdeal.inertiaDeg (𝓞 k) = orderOf u := by
      rw [hcycW.2, hval]
      exact orderOf_units (y := u)
    -- ## 10. the group-theoretic input
    have hnotpow' : u ∉ (powMonoidHom q).range := by
      rintro ⟨y, hy⟩
      apply hnotpow
      have hy' : y ^ q = u := hy
      refine ⟨y, ?_⟩
      rw [← Units.val_pow_eq_pow_val y q, hy']
      exact hu
    have hcardG : Nat.card (ZMod ℓ)ˣ = ℓ - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units]
    have hfull : ∀ j : ℕ, q ^ j ∣ ℓ - 1 → q ^ j ∣ orderOf u := by
      intro j hj
      exact cyclic_qpart_orderOf q hq u hnotpow' j (by rwa [hcardG])
    -- ## 11. the local degree at the level of `M` divides `(ℓ-1)/q^e`
    have hdivH : W.asIdeal.ramificationIdx (𝓞 ↥(cycM q e ℓ ζ))
          * W.asIdeal.inertiaDeg (𝓞 ↥(cycM q e ℓ ζ)) ∣ (ℓ - 1) / q ^ e := by
      have h1 := Work.SSGRoute.ramificationIdx_mul_inertiaDeg_dvd_finrank
        ↥(cycM q e ℓ ζ) ↥(cycL ℓ ζ) P W hWP
      rwa [hfinML] at h1
    -- ## 12. the crucial divisibility `q ^ e ∣ f(P|v₀)`
    have hOeq : orderOf u
        = P.asIdeal.inertiaDeg (𝓞 k) * W.asIdeal.inertiaDeg (𝓞 ↥(cycM q e ℓ ζ)) := by
      rw [← hord, htower_f]
    have hfW : 0 < W.asIdeal.inertiaDeg (𝓞 ↥(cycM q e ℓ ζ)) := by
      rcases Nat.eq_zero_or_pos (W.asIdeal.inertiaDeg (𝓞 ↥(cycM q e ℓ ζ))) with h0 | hpos
      · rw [h0, mul_zero] at hOeq
        exact absurd hOeq (orderOf_pos u).ne'
      · exact hpos
    have hdivf : q ^ e ∣ P.asIdeal.inertiaDeg (𝓞 k) := by
      have hH : q ^ e * (W.asIdeal.ramificationIdx (𝓞 ↥(cycM q e ℓ ζ))
            * W.asIdeal.inertiaDeg (𝓞 ↥(cycM q e ℓ ζ))) ∣ ℓ - 1 := by
        have h := Nat.mul_dvd_mul_left (q ^ e) hdivH
        rwa [Nat.mul_div_cancel' hdvd] at h
      have hmain := div_dvd_of_qpow_mul_dvd hq he (orderOf_pos u) hfW
        ⟨P.asIdeal.inertiaDeg (𝓞 k), by rw [hOeq, mul_comm]⟩
        ⟨W.asIdeal.ramificationIdx (𝓞 ↥(cycM q e ℓ ζ)), by rw [mul_comm]⟩ hH hfull
      rwa [hOeq, Nat.mul_div_cancel _ hfW] at hmain
    -- ## 13. the stabiliser at the level of `M`
    haveI : IsGaloisGroup (↥(cycM q e ℓ ζ) ≃ₐ[k] ↥(cycM q e ℓ ζ))
        (𝓞 k) (𝓞 ↥(cycM q e ℓ ζ)) := inferInstance
    have hstabP : Nat.card (MulAction.stabilizer (↥(cycM q e ℓ ζ) ≃ₐ[k] ↥(cycM q e ℓ ζ))
          P.asIdeal)
        = P.asIdeal.ramificationIdx (𝓞 k) * P.asIdeal.inertiaDeg (𝓞 k) := by
      have h1 : Nat.card (MulAction.stabilizer (↥(cycM q e ℓ ζ) ≃ₐ[k] ↥(cycM q e ℓ ζ))
            P.asIdeal)
          = v₀.asIdeal.ramificationIdxIn (𝓞 ↥(cycM q e ℓ ζ))
            * v₀.asIdeal.inertiaDegIn (𝓞 ↥(cycM q e ℓ ζ)) :=
        Ideal.card_stabilizer_eq v₀.asIdeal P.asIdeal
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx v₀.asIdeal P.asIdeal
            (↥(cycM q e ℓ ζ) ≃ₐ[k] ↥(cycM q e ℓ ζ)),
        Ideal.inertiaDegIn_eq_inertiaDeg v₀.asIdeal P.asIdeal
            (↥(cycM q e ℓ ζ) ≃ₐ[k] ↥(cycM q e ℓ ζ))] at h1
      exact h1
    have hprod_dvd : P.asIdeal.ramificationIdx (𝓞 k) * P.asIdeal.inertiaDeg (𝓞 k) ∣ q ^ e := by
      rw [← hstabP, ← hcardM]
      exact Subgroup.card_subgroup_dvd_card _
    have hfeq : P.asIdeal.inertiaDeg (𝓞 k) = q ^ e :=
      Nat.dvd_antisymm ((dvd_mul_left _ _).trans hprod_dvd) hdivf
    have heq1 : P.asIdeal.ramificationIdx (𝓞 k) = 1 := by
      have h2 : P.asIdeal.ramificationIdx (𝓞 k) * q ^ e ∣ q ^ e := by
        rwa [hfeq] at hprod_dvd
      have h3 : P.asIdeal.ramificationIdx (𝓞 k) * q ^ e ∣ 1 * q ^ e := by
        rwa [one_mul]
      exact Nat.dvd_one.mp
        ((Nat.mul_dvd_mul_iff_right (pow_pos hq.pos e)).mp h3)
    rw [hstabP, hfeq, heq1, one_mul, hcardM]

end Work.SSGRoute.CycLevel
