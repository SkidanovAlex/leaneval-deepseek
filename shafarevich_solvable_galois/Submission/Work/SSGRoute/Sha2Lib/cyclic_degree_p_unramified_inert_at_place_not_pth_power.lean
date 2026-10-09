import Mathlib
import Submission.Work.SSGRoute.CycLevel.routeA_level
import Submission.Work.SSGRoute.CycLevel.cyclic_qpart_orderOf
import Submission.Work.SSGRoute.CycLevel.div_dvd_of_qpow_mul_dvd
import Submission.Work.SSGRoute.ramificationIdx_mul_inertiaDeg_dvd_finrank
import Submission.NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree
import Submission.NK.CFTLib.ArtinReciprocityIdeal.exists_algEquiv_zeta_pow
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.Sha2Lib

open scoped NumberField

/-!
# The cyclotomic level: a cyclic degree-`p` level which is unramified and inert at `Q`

This file proves `Work.SSGRoute.Sha2Lib.cyclic_degree_p_unramified_inert_at_place_not_pth_power`:
if `p` is an odd prime and `Q` is a finite place of the number field `k` whose residue cardinality
is not a `p`-th power, then `k` has a cyclic degree-`p` extension (inside any algebraically closed
overfield `Ω`) in which `Q` is unramified with residue degree `p`.

The construction is the "route A" cyclotomic level: a rational prime `ℓ` with `p ∣ ℓ - 1`,
`ℓ ∤ disc k`, `ℓ ∤ N Q` and `N Q ∉ ((ZMod ℓ)ˣ)^p` produces `k⟮ζ_ℓ⟯ ⊇ k`, whose Galois group is
cyclic of order `ℓ - 1`; the level `M` is the fixed field of the subgroup of `p`-th powers, of
degree `p` over `k`.  `k⟮ζ_ℓ⟯/k` is unramified at `Q`, and its Frobenius at `Q` is not a `p`-th
power, which forces `Q` to be inert in `M`.
-/

noncomputable section

/-! ## The Chebotarev/Kummer input: the prime `ℓ` -/

/-- **The Chebotarev/Kummer input.**  Let `p` be an odd prime, `k` a number field and `Q` a finite
place of `k` whose residue cardinality `NQ` is not a `p`-th power of a positive integer.  Then there
is a rational prime `ℓ` with `p ∣ ℓ - 1`, `ℓ ∤ disc k`, `ℓ ∤ NQ`, and `NQ` *not* a `p`-th power in
`(ZMod ℓ)ˣ`.

This is the first half of `Work.SSGRoute.CycLevel.routeA_level`: the Kummer field
`N = ℚ(ζ_p, NQ^{1/p})` (`Work.SSGRoute.CycLevel.kummerCyc_data`) together with the Chebotarev-type
existence of primes with a prescribed Frobenius
(`Work.SSGRoute.CycLevel.exists_prime_notPower_mod`). -/
theorem exists_prime_not_pthPower_mod_of_place (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k : Type)
    [Field k] [NumberField k] (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hN : ¬ ∃ m : ℕ, 0 < m ∧ Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) = m ^ p) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ p ∣ ℓ - 1 ∧ ¬ (ℓ : ℤ) ∣ NumberField.discr k ∧
      ¬ ℓ ∣ Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) ∧
      (¬ ∃ x : (ZMod ℓ)ˣ, (x : ZMod ℓ) ^ p
        = ((Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) : ℕ) : ZMod ℓ)) := by
  classical
  have hp' : p.Prime := Fact.out
  have hp2 : 2 < p := by
    have h2 := hp'.two_le
    omega
  set m : ℕ := Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) with hm
  haveI hfin : Finite (NumberField.RingOfIntegers k ⧸ Q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q
  haveI : Nonempty (NumberField.RingOfIntegers k ⧸ Q.asIdeal) :=
    ⟨Ideal.Quotient.mk Q.asIdeal 0⟩
  have hmpos : 0 < m := by rw [hm]; exact Nat.card_pos
  have hmq : ¬ ∃ m' : ℕ, 0 < m' ∧ m = m' ^ p := by rw [hm]; exact hN
  obtain ⟨N, hFN, hNF, hAlgN, hFDiN, hGalN, ζ, α, σ, hζ, hα, hσζ, hσα⟩ :=
    Work.SSGRoute.CycLevel.kummerCyc_data p 1 m hp' hp2 (by norm_num) hmpos hmq
  letI : Field N := hFN
  letI : NumberField N := hNF
  letI : Algebra ℚ N := hAlgN
  letI : FiniteDimensional ℚ N := hFDiN
  letI : IsGalois ℚ N := hGalN
  obtain ⟨ℓ, hℓprime, hℓdvd, hℓnotD, hℓnotmZ, hℓnotpow⟩ :=
    Work.SSGRoute.CycLevel.exists_prime_notPower_mod p 1 m hp' hp2 (by norm_num) hmpos hmq
      (NumberField.discr k) (NumberField.discr_ne_zero k) N ζ α σ hζ hα hσζ hσα
  refine ⟨ℓ, hℓprime, by simpa using hℓdvd, hℓnotD, ?_, ?_⟩
  · exact fun hdiv => hℓnotmZ (by exact_mod_cast hdiv)
  · exact hℓnotpow

/-! ## The cardinality of `Gal(k⟮ζ_ℓ⟯/k)` -/

/-- **The Galois group of `k⟮ζ_ℓ⟯/k` has order `ℓ - 1`.**  Let `k` be a number field, `ℓ` a
rational prime not dividing `disc k`, `Ω` any field with an algebra structure over `k` (e.g. an
algebraically closed overfield), and `ζ ∈ Ω` a primitive `ℓ`-th root of unity.  Then
`Gal(k⟮ζ⟯/k)` has cardinality `ℓ - 1`.

The cyclotomic character `IsPrimitiveRoot.autToPow k hζ` is injective
(`IsPrimitiveRoot.autToPow_injective`) and surjective by
`NK.CFTLib.ArtinReciprocityIdeal.exists_algEquiv_zeta_pow` (this is where `ℓ ∤ disc k` is used), so
it is a bijection onto `(ZMod ℓ)ˣ`, of cardinality `ℓ - 1` (`ZMod.card_units`).  This is the
general-`Ω` version of `Work.SSGRoute.CycLevel.cycL_card_aut`. -/
theorem card_aut_adjoin_primitiveRoot_eq_sub_one (ℓ : ℕ) (hℓ : ℓ.Prime) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] (hdisc : ¬ (ℓ : ℤ) ∣ NumberField.discr k)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ ℓ) :
    Nat.card (↥(IntermediateField.adjoin k ({ζ} : Set Ω)) ≃ₐ[k]
      ↥(IntermediateField.adjoin k ({ζ} : Set Ω))) = ℓ - 1 := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set L : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω) with hL
  have hζLmem : ζ ∈ L := IntermediateField.mem_adjoin_simple_self k ζ
  have hζL : IsPrimitiveRoot (⟨ζ, hζLmem⟩ : ↥L) ℓ :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp (by
      rw [show ((⟨ζ, hζLmem⟩ : ↥L) : Ω) = ζ from rfl]
      exact hζ)
  haveI hcycL : IsCyclotomicExtension {ℓ} k ↥L :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin ℓ k Ω L hζ).mpr rfl
  have hθinj : Function.Injective (IsPrimitiveRoot.autToPow k hζL) :=
    IsPrimitiveRoot.autToPow_injective k hζL
  have hθsurj : Function.Surjective (IsPrimitiveRoot.autToPow k hζL) := by
    intro τ
    obtain ⟨σ, hσ⟩ :=
      NK.CFTLib.ArtinReciprocityIdeal.exists_algEquiv_zeta_pow ℓ hℓ hdisc ζ hζ τ
    refine ⟨σ, ?_⟩
    have h1 : (⟨ζ, hζLmem⟩ : ↥L)
          ^ (((IsPrimitiveRoot.autToPow k hζL σ : (ZMod ℓ)ˣ) : ZMod ℓ)).val
        = (⟨ζ, hζLmem⟩ : ↥L) ^ ((τ : ZMod ℓ)).val :=
      (IsPrimitiveRoot.autToPow_spec k hζL σ).trans hσ
    exact Units.ext (ZMod.val_injective ℓ
      (Work.SSGRoute.CycLevel.pow_val_eq_of_lt hℓ hζL (ZMod.val_lt _) (ZMod.val_lt _) h1))
  have hbij : Function.Bijective (IsPrimitiveRoot.autToPow k hζL) := ⟨hθinj, hθsurj⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, ZMod.card_units]

/-! ## The cyclic degree-`p` sublevel of `k⟮ζ_ℓ⟯` -/

/-- **A cyclic degree-`p` sublevel of `k⟮ζ_ℓ⟯`.**  Let `p` be a prime, `ℓ` a prime with `p ∣ ℓ - 1`,
`k` a number field with `ℓ ∤ disc k`, `Ω` a field over `k` and `ζ ∈ Ω` a primitive `ℓ`-th root of
unity.  Then there is an intermediate field `M ⊆ k⟮ζ⟯ ⊆ Ω` which is a number field, finite and
Galois over `k`, with cyclic Galois group `Gal(M/k)` of order `p`.

`M` is the fixed field of the subgroup of `p`-th powers of `Gal(k⟮ζ⟯/k)`, a cyclic group of order
`ℓ - 1` (via the cyclotomic character, `card_aut_adjoin_primitiveRoot_eq_sub_one`). -/
theorem exists_cyclic_p_level_le_adjoin_primitiveRoot (p ℓ : ℕ) [Fact p.Prime] (hℓ : ℓ.Prime)
    (hdvd : p ∣ ℓ - 1) (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (hdisc : ¬ (ℓ : ℤ) ∣ NumberField.discr k) (ζ : Ω) (hζ : IsPrimitiveRoot ζ ℓ) :
    ∃ (M : IntermediateField k Ω) (_ : NumberField ↥M) (_ : FiniteDimensional k ↥M)
      (_ : IsGalois k ↥M),
      IsCyclic (↥M ≃ₐ[k] ↥M) ∧ Nat.card (↥M ≃ₐ[k] ↥M) = p ∧
      M ≤ IntermediateField.adjoin k ({ζ} : Set Ω) := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set L : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω) with hL
  have hζLmem : ζ ∈ L := IntermediateField.mem_adjoin_simple_self k ζ
  have hζL : IsPrimitiveRoot (⟨ζ, hζLmem⟩ : ↥L) ℓ :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp (by
      rw [show ((⟨ζ, hζLmem⟩ : ↥L) : Ω) = ζ from rfl]
      exact hζ)
  haveI hcycL : IsCyclotomicExtension {ℓ} k ↥L :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin ℓ k Ω L hζ).mpr rfl
  haveI hfdL : FiniteDimensional k ↥L := IsCyclotomicExtension.finiteDimensional {ℓ} k ↥L
  haveI hgalL : IsGalois k ↥L := IsCyclotomicExtension.isGalois {ℓ} k ↥L
  have hcardL : Nat.card (↥L ≃ₐ[k] ↥L) = ℓ - 1 :=
    card_aut_adjoin_primitiveRoot_eq_sub_one ℓ hℓ k Ω hdisc ζ hζ
  have hθinj : Function.Injective (IsPrimitiveRoot.autToPow k hζL) :=
    IsPrimitiveRoot.autToPow_injective k hζL
  haveI hcycG : IsCyclic (↥L ≃ₐ[k] ↥L) := isCyclic_of_injective _ hθinj
  haveI : Finite (↥L ≃ₐ[k] ↥L) := Finite.of_injective _ hθinj
  letI : CommGroup (↥L ≃ₐ[k] ↥L) := IsCyclic.commGroup
  set H : Subgroup (↥L ≃ₐ[k] ↥L) :=
    Subgroup.closure (Set.range fun y : ↥L ≃ₐ[k] ↥L => y ^ p) with hHdef
  have hHrange : H = (powMonoidHom p).range := by
    rw [hHdef]
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ ⟨y, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
    · rintro _ ⟨y, rfl⟩
      exact Subgroup.subset_closure ⟨y, rfl⟩
  have hHindex : H.index = p := by
    rw [hHrange, IsCyclic.index_powMonoidHom_range, hcardL]
    exact Nat.gcd_eq_right hdvd
  haveI hHnorm : H.Normal := Subgroup.normal_of_isMulCommutative H
  have hcardM0 : Nat.card (↥(IntermediateField.fixedField H) ≃ₐ[k]
      ↥(IntermediateField.fixedField H)) = p := by
    rw [← Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv, ← Subgroup.index_eq_card]
    exact hHindex
  haveI hgalM0 : IsGalois k ↥(IntermediateField.fixedField H) :=
    IsGalois.of_fixedField_normal_subgroup H
  haveI hcycM0 : IsCyclic (↥(IntermediateField.fixedField H) ≃ₐ[k]
      ↥(IntermediateField.fixedField H)) :=
    isCyclic_of_surjective _ (IsGalois.normalAutEquivQuotient H).surjective
  let M : IntermediateField k Ω := IntermediateField.lift (IntermediateField.fixedField H)
  have hle : M ≤ L := IntermediateField.lift_le (IntermediateField.fixedField H)
  have e_al : ↥(IntermediateField.fixedField H) ≃ₐ[k] ↥M :=
    IntermediateField.liftAlgEquiv (E := L) (IntermediateField.fixedField H)
  haveI hfdM : FiniteDimensional k ↥M :=
    FiniteDimensional.of_surjective e_al.toLinearMap e_al.surjective
  haveI hgalM : IsGalois k ↥M := IsGalois.of_algEquiv e_al
  have hcycM : IsCyclic (↥M ≃ₐ[k] ↥M) := (MulEquiv.isCyclic (AlgEquiv.autCongr e_al)).mp hcycM0
  have hcardM : Nat.card (↥M ≃ₐ[k] ↥M) = p := by
    rw [← Nat.card_congr (AlgEquiv.autCongr e_al).toEquiv]
    exact hcardM0
  exact ⟨M, NumberField.of_module_finite k ↥M, hfdM, hgalM, hcycM, hcardM, hle⟩

/-! ## The local computation at `Q` -/

/-- **Local behaviour at a place of the base field.**  Let `p` be a prime, `ℓ` a prime with
`p ∣ ℓ - 1`, and `k ⊆ M ⊆ L` a tower of number fields with `L/k` a cyclotomic extension of
conductor `ℓ` (i.e. `IsCyclotomicExtension {ℓ} k L`), `[M : k] = p` and `[L : k] = ℓ - 1`.  Let `Q`
be a finite place of `k` with `(ℓ) ∉ Q`, with `ℓ ∤ NQ` (`NQ` the residue cardinality) and with `NQ`
*not* a `p`-th power in `(ZMod ℓ)ˣ`.  Then every place `w` of `M` above `Q` has `e(w|Q) = 1`
(unramified) and `f(w|Q) = p` (inert).

(Note that `ℓ ∤ NQ` is *not* implied by the "not a `p`-th power" condition: if `ℓ ∣ NQ` then `NQ`
reduces to `0`, which is not a `p`-th power of a unit; both conditions are supplied by
`exists_prime_not_pthPower_mod_of_place`.)

Proof: `e(P|Q) = 1` and `f(P|Q) = orderOf(NQ mod ℓ)` for `P | w` in `L`
(`NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree`).  Multiplicativity in towers gives `e(w|Q) = 1`
and `f(P|Q) = f(w|Q) · f(P|w)`; since `NQ` is not a `p`-th power, the `p`-part of `f(P|Q)` is the
full `p`-part of `ℓ - 1` (`Work.SSGRoute.CycLevel.cyclic_qpart_orderOf`), so the `p`-part of
`f(P|Q) / f(P|w) = f(w|Q)` survives the division by `f(P|w) ∣ (ℓ-1)/p`
(`Work.SSGRoute.CycLevel.div_dvd_of_qpow_mul_dvd`).  Hence `p ∣ f(w|Q)`, while
`e(w|Q) · f(w|Q) ∣ [M:k] = p` (`Work.SSGRoute.ramificationIdx_mul_inertiaDeg_dvd_finrank`), so
`f(w|Q) = p`. -/
theorem ramificationIdx_inertiaDeg_of_cyclotomic_p_level (p ℓ : ℕ) [Fact p.Prime] (hℓ : ℓ.Prime)
    (hdvd : p ∣ ℓ - 1) (k M L : Type) [Field k] [NumberField k] [Field M] [NumberField M]
    [Field L] [NumberField L] [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L]
    [IsGalois k M] [IsGalois k L] [IsCyclotomicExtension {ℓ} k L]
    (hfinM : Module.finrank k M = p) (hfinL : Module.finrank k L = ℓ - 1)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hres : (ℓ : NumberField.RingOfIntegers k) ∉ Q.asIdeal)
    (hℓN : ¬ ℓ ∣ Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal))
    (hnotpow : ¬ ∃ x : (ZMod ℓ)ˣ, (x : ZMod ℓ) ^ p
      = ((Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) : ℕ) : ZMod ℓ))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hw : w.asIdeal.LiesOver Q.asIdeal) :
    w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
      w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = p := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI hgalML : IsGalois M L := IsGalois.tower_top_of_isGalois k M L
  -- ## the relative degree `[L : M] = (ℓ - 1) / p`
  have hfinML : Module.finrank M L = (ℓ - 1) / p := by
    have h1 : p * Module.finrank M L = ℓ - 1 := by
      rw [← hfinM, ← hfinL]
      exact Module.finrank_mul_finrank k M L
    have h2 : p * ((ℓ - 1) / p) = ℓ - 1 := Nat.mul_div_cancel' hdvd
    rw [← h2] at h1
    exact mul_left_cancel₀ hp.pos.ne' h1
  -- ## a place `P` of `L` above `w`
  obtain ⟨P, hPw⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := M) (L := L) w
  haveI hPw' : P.asIdeal.LiesOver w.asIdeal := hPw
  have hPQ : P.asIdeal.LiesOver Q.asIdeal := NK.Chebotarev.liesOver_trans hPw hw
  -- ## the cyclotomic local degree at `P`
  have hcycP := NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree (K := k) Q ℓ hℓ hres P hPQ
  -- ## the unit `u` with `u = NQ mod ℓ`
  have hcop : Nat.Coprime (Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal)) ℓ :=
    ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
  let u : (ZMod ℓ)ˣ := ZMod.unitOfCoprime (Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal)) hcop
  have hu : (u : ZMod ℓ) = ((Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) : ℕ) : ZMod ℓ) :=
    ZMod.coe_unitOfCoprime _ _
  have habs : Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) = Ideal.absNorm Q.asIdeal := by
    rw [Ideal.absNorm_apply]; rfl
  have hval : ((Ideal.absNorm Q.asIdeal : ℕ) : ZMod ℓ) = (u : ZMod ℓ) := by
    rw [← habs, hu]
  have hord : P.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = orderOf u := by
    rw [hcycP.2, hval]
    exact orderOf_units (y := u)
  have hnotpow' : u ∉ (powMonoidHom p).range := by
    rintro ⟨y, hy⟩
    apply hnotpow
    refine ⟨y, ?_⟩
    have hy' : y ^ p = u := hy
    calc (y : ZMod ℓ) ^ p = ((y ^ p : (ZMod ℓ)ˣ) : ZMod ℓ) :=
          (Units.val_pow_eq_pow_val y p).symm
      _ = (u : ZMod ℓ) := by rw [hy']
      _ = ((Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) : ℕ) : ZMod ℓ) := hu
  have hcardG : Nat.card (ZMod ℓ)ˣ = ℓ - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hfull : ∀ j : ℕ, p ^ j ∣ ℓ - 1 → p ^ j ∣ orderOf u := fun j hj =>
    Work.SSGRoute.CycLevel.cyclic_qpart_orderOf p hp u hnotpow' j (by rwa [hcardG])
  -- ## the local degree at the level of `M` divides `(ℓ-1)/p`
  have hdivH : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers M)
        * P.asIdeal.inertiaDeg (NumberField.RingOfIntegers M) ∣ (ℓ - 1) / p := by
    have h1 := Work.SSGRoute.ramificationIdx_mul_inertiaDeg_dvd_finrank M L w P hPw
    rwa [hfinML] at h1
  -- ## `e(w|Q) = 1`
  have heq1 : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    have h1 : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k)
        = w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k)
          * P.asIdeal.ramificationIdx (NumberField.RingOfIntegers M) :=
      Ideal.ramificationIdx_tower (R := NumberField.RingOfIntegers k) w.asIdeal P.asIdeal
    rw [hcycP.1] at h1
    exact Nat.dvd_one.mp ⟨P.asIdeal.ramificationIdx (NumberField.RingOfIntegers M), h1⟩
  -- ## the tower relation for the inertia degree
  have hOeq : orderOf u = w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k)
      * P.asIdeal.inertiaDeg (NumberField.RingOfIntegers M) :=
    hord.symm.trans (Ideal.inertiaDeg_tower (R := NumberField.RingOfIntegers k) w.asIdeal P.asIdeal)
  have hfW : 0 < P.asIdeal.inertiaDeg (NumberField.RingOfIntegers M) := by
    rcases Nat.eq_zero_or_pos (P.asIdeal.inertiaDeg (NumberField.RingOfIntegers M)) with h0 | hpos
    · rw [h0, mul_zero] at hOeq
      exact absurd hOeq (orderOf_pos u).ne'
    · exact hpos
  -- ## `p ∣ f(w|Q)`
  have hH : p ^ 1 * (P.asIdeal.ramificationIdx (NumberField.RingOfIntegers M)
      * P.asIdeal.inertiaDeg (NumberField.RingOfIntegers M)) ∣ ℓ - 1 := by
    have h := Nat.mul_dvd_mul_left p hdivH
    rw [Nat.mul_div_cancel' hdvd] at h
    simpa using h
  have hmain : p ^ 1 ∣ orderOf u / P.asIdeal.inertiaDeg (NumberField.RingOfIntegers M) :=
    Work.SSGRoute.CycLevel.div_dvd_of_qpow_mul_dvd (q := p) (e := 1) (O := orderOf u)
      (f := P.asIdeal.inertiaDeg (NumberField.RingOfIntegers M))
      (H := P.asIdeal.ramificationIdx (NumberField.RingOfIntegers M)
        * P.asIdeal.inertiaDeg (NumberField.RingOfIntegers M)) (m := ℓ - 1)
      hp (by norm_num) (orderOf_pos u) hfW
      ⟨w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k), hOeq.trans (Nat.mul_comm _ _)⟩
      ⟨P.asIdeal.ramificationIdx (NumberField.RingOfIntegers M), Nat.mul_comm _ _⟩ hH hfull
  have hpdvdf : p ∣ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    rw [hOeq, Nat.mul_div_cancel _ hfW] at hmain
    simpa using hmain
  -- ## `f(w|Q) ∣ p`
  have hfdiv : w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) ∣ p := by
    have h1 := Work.SSGRoute.ramificationIdx_mul_inertiaDeg_dvd_finrank k M Q w hw
    rw [hfinM, heq1, one_mul] at h1
    exact h1
  exact ⟨heq1, Nat.dvd_antisymm hfdiv hpdvdf⟩

/-- **Cyclotomic case: residue cardinality not a `p`-th power.**

`p` is an odd prime, `Q` a finite place of the number field `k` whose residue cardinality
`N := Nat.card (𝓞 k ⧸ Q.asIdeal)` is *not* a `p`-th power of a positive integer (`hN`).  Then there is
a cyclic degree-`p` level `M ⊆ Ω` over `k` which is unramified at `Q` (every `w | Q`: `e(w|Q) = 1`)
and in which `Q` is inert (every `w | Q`: `f(w|Q) = p`).

Route (ingredients on disk and proved):
* by `Work.SSGRoute.CycLevel.exists_prime_notPower_mod`
  (`Submission/Work/SSGRoute/CycLevel/routeA_level.lean`, proved via Čebotarev) there is a rational
  prime `ℓ` with `p ∣ ℓ - 1`, `ℓ ∤ N`, `ℓ ∤ disc k`, and `N` *not* a `p`-th power in `(ZMod ℓ)ˣ`;
* `ℓ ∤ N` means `ℓ` is not the residue characteristic of `Q`, so `(ℓ : 𝓞 k) ∉ Q.asIdeal`;
* let `ζ` be a primitive `ℓ`-th root of unity in `Ω` and consider `k(ζ) ≤ Ω`: the extension
  `k(ζ)/k` is Galois with `Gal(k(ζ)/k) ⊆ (ZMod ℓ)ˣ ≅ ℤ/(ℓ-1)`, hence *cyclic*; the Frobenius of `Q`
  acts on `ζ` as `ζ ↦ ζ^N`, so its image is the class of `N`; since `N` is not a `p`-th power in the
  cyclic group `(ZMod ℓ)ˣ`, it is not a `p`-th power in the subgroup `Gal(k(ζ)/k)` either
  (`G^p = G ∩ ((ZMod ℓ)ˣ)^p` for a subgroup `G` of a cyclic group), so there is a surjection
  `ψ : Gal(k(ζ)/k) ↠ ZMod p` with `ψ(Frob_Q) ≠ 0`; take `M := k(ζ)^{ker ψ}`;
* `k(ζ)/k` is unramified at `Q` (the residue characteristic of `Q` does not divide `ℓ`; on disk
  `NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension`), hence so is `M`;
* `ψ(Frob_Q) ≠ 0` means the decomposition group of every `w | Q` in `Gal(M/k)` is non-trivial, so `Q`
  is not split in `M`; with `e = 1` and `[M:k] = p` this forces `f(w|Q) = p`.

(`Work.SSGRoute.CycLevel.routeA_level` contains the same construction in `LevelData` form and is the
right place to crib the formalisation of the `ℓ`, `ζ`, `k(ζ)` steps.) -/
theorem cyclic_degree_p_unramified_inert_at_place_not_pth_power (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hN : ¬ ∃ m : ℕ, 0 < m ∧ Nat.card (NumberField.RingOfIntegers k ⧸ Q.asIdeal) = m ^ p) :
    ∃ (M : IntermediateField k Ω) (_ : NumberField ↥M) (_ : FiniteDimensional k ↥M)
      (_ : IsGalois k ↥M),
      IsCyclic (↥M ≃ₐ[k] ↥M) ∧ Nat.card (↥M ≃ₐ[k] ↥M) = p ∧
      ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M),
        w.asIdeal.LiesOver Q.asIdeal →
          w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
          w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = p := by
  classical
  -- ## the prime `ℓ` and a primitive `ℓ`-th root of unity `ζ ∈ Ω`
  obtain ⟨ℓ, hℓprime, hℓdvd, hℓdisc, hℓN, hℓnotpow⟩ :=
    exists_prime_not_pthPower_mod_of_place p hp k Q hN
  haveI : NeZero ℓ := ⟨hℓprime.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓprime⟩
  haveI hcharΩ : CharZero Ω :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  haveI hNeℓΩ : NeZero ((ℓ : ℕ) : Ω) := ⟨(Nat.cast_ne_zero).mpr hℓprime.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := Ω) (n := ℓ)
  -- ## the cyclic degree-`p` level `M ⊆ k⟮ζ⟯`
  obtain ⟨M, hnfM, hfdM, hgalM, hcycM, hcardM, hle⟩ :=
    exists_cyclic_p_level_le_adjoin_primitiveRoot p ℓ hℓprime hℓdvd k Ω hℓdisc ζ hζ
  letI : NumberField ↥M := hnfM
  letI : FiniteDimensional k ↥M := hfdM
  letI : IsGalois k ↥M := hgalM
  -- ## the cyclotomic level `L = k⟮ζ⟯` and the tower `k ⊆ M ⊆ L`
  let L : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω)
  have hle' : M ≤ L := hle
  haveI hcycL : IsCyclotomicExtension ({ℓ} : Set ℕ) k ↥L :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin ℓ k Ω L hζ).mpr rfl
  haveI hfdL : FiniteDimensional k ↥L := IsCyclotomicExtension.finiteDimensional {ℓ} k ↥L
  haveI hgalL : IsGalois k ↥L := IsCyclotomicExtension.isGalois {ℓ} k ↥L
  haveI hnfL : NumberField ↥L := NumberField.of_module_finite k ↥L
  letI : Algebra ↥M ↥L := (IntermediateField.inclusion hle').toRingHom.toAlgebra
  haveI : IsScalarTower k ↥M ↥L := IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  haveI : FiniteDimensional ↥M ↥L := FiniteDimensional.right k ↥M ↥L
  haveI : IsGalois ↥M ↥L := IsGalois.tower_top_of_isGalois k ↥M ↥L
  -- ## the degrees `[M : k] = p` and `[L : k] = ℓ - 1`
  have hfinM : Module.finrank k ↥M = p := by
    rw [← IsGalois.card_aut_eq_finrank k ↥M]
    exact hcardM
  have hfinL : Module.finrank k ↥L = ℓ - 1 := by
    rw [← IsGalois.card_aut_eq_finrank k ↥L]
    exact card_aut_adjoin_primitiveRoot_eq_sub_one ℓ hℓprime k Ω hℓdisc ζ hζ
  -- ## `ℓ` is not the residue characteristic of `Q`
  have hres : (ℓ : NumberField.RingOfIntegers k) ∉ Q.asIdeal :=
    Work.SSGRoute.CycLevel.cast_notMem_of_not_dvd_natCard k Q ℓ hℓprime hℓN
  refine ⟨M, hnfM, hfdM, hgalM, hcycM, hcardM, ?_⟩
  intro w hw
  exact ramificationIdx_inertiaDeg_of_cyclotomic_p_level p ℓ hℓprime hℓdvd k ↥M ↥L hfinM hfinL
    Q hres hℓN hℓnotpow w hw

end

end Work.SSGRoute.Sha2Lib
