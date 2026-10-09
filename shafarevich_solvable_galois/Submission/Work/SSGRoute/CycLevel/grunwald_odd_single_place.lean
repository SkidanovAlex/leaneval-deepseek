import Mathlib
import Submission.Work.SSGRoute.CycLevel.KummerBundle
import Submission.Work.SSGRoute.CycLevel.kummer_pow_of_isPow_almostAll
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The odd Grünwald–Wang step at a single place

The target `grunwald_odd_single_place` is deduced from the following ingredients:

* `kummer_pow_of_isPow_almostAll` (the `\v{C}ebotarev`/Kummer step over a number field containing
  `μ_q`);
* `norm_descent_aux` (the descent along `k(ζ_q) / k`, using that `[k(ζ_q) : k] ∣ q - 1`);
* `hasse_principle_single` (the Hasse principle for `q`-th powers at all places `≠ v₀`);
* `not_pow_onePlace_unifUnit` and the `p`-power criterion in the idèle class group
  (`Work.SSGRoute.PTW.mem_pthPower_of_all_open_index_p_subgroups`), together with the group-theory
  lemma `Work.SSGRoute.PT.exists_surjective_hom_zmod_of_cyclic`.
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

open scoped NumberField
open IsDedekindDomain

namespace Work.SSGRoute.CycLevel

noncomputable section

/-! ## The norm descent from `k(ζ_q)` to `k` -/

/-- **Norm descent.**  Let `k` be a number field, `q` an odd prime, `K ⊇ k` a cyclotomic extension
of `k` containing a primitive `q`-th root of unity `ζ`, and `b ∈ K` with `b ^ q = a ∈ k`.  Then `a`
is already a `q`-th power in `k`.

Since `[K : k] ∣ q - 1` and `N(b) ^ q = a ^ [K : k]`, writing `q - 1 = [K : k] * t` gives
`(N(b) ^ t) ^ q = a ^ (q - 1)`, so that `a / N(b) ^ t` is a `q`-th root of `a` in `k`. -/
theorem norm_descent_aux {k : Type} [Field k] [NumberField k]
    (q : ℕ) (hq : q.Prime)
    (K : Type) [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [IsCyclotomicExtension {q} k K] (ζ : K) (hζ : IsPrimitiveRoot ζ q)
    (a : kˣ) (b : K) (hb : b ^ q = algebraMap k K (a : k)) :
    ∃ b' : kˣ, (b' : k) ^ q = (a : k) := by
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd : Module.finrank k K ∣ q - 1 := by
    have hinj : Function.Injective (IsPrimitiveRoot.autToPow k hζ) :=
      IsPrimitiveRoot.autToPow_injective k hζ
    have h2 : Nat.card (K ≃ₐ[k] K) = Nat.card ((IsPrimitiveRoot.autToPow k hζ).range) :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have h3 : Nat.card ((IsPrimitiveRoot.autToPow k hζ).range) ∣ Nat.card (ZMod q)ˣ :=
      Subgroup.card_subgroup_dvd_card _
    have h5 : Nat.card (ZMod q)ˣ = q - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units]
    have h4 : Nat.card (K ≃ₐ[k] K) = Module.finrank k K := IsGalois.card_aut_eq_finrank k K
    rw [← h4, h2, ← h5]
    exact h3
  have hb0 : b ≠ 0 := by
    intro h0
    have h1 : (algebraMap k K) (a : k) = 0 := by rw [← hb, h0, zero_pow hq.ne_zero]
    exact (Units.ne_zero a) ((algebraMap k K).injective (by rw [h1, map_zero]))
  haveI : Module.Free k K := Module.Free.of_divisionRing k K
  have hnorm : (Algebra.norm k b) ^ q = (a : k) ^ Module.finrank k K := by
    have h1 : Algebra.norm k (b ^ q) = Algebra.norm k (algebraMap k K (a : k)) := by rw [hb]
    rwa [map_pow, Algebra.norm_algebraMap] at h1
  have hN0 : Algebra.norm k b ≠ 0 := (Algebra.norm_ne_zero_iff (R := k) (S := K)).mpr hb0
  set c : kˣ := Units.mk0 (Algebra.norm k b) hN0 with hc
  have hcd : c ^ q = a ^ (Module.finrank k K) := by
    apply Units.ext
    push_cast
    simp only [hc, Units.val_mk0]
    exact hnorm
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨a / c ^ t, ?_⟩
  have hc' : (c ^ t) ^ q = a ^ (q - 1) := by
    calc (c ^ t) ^ q = c ^ (t * q) := by rw [pow_mul]
      _ = c ^ (q * t) := by rw [mul_comm]
      _ = (c ^ q) ^ t := by rw [pow_mul]
      _ = (a ^ Module.finrank k K) ^ t := by rw [hcd]
      _ = a ^ (Module.finrank k K * t) := by rw [pow_mul]
      _ = a ^ (q - 1) := by rw [ht]
  have hb'' : (a / c ^ t) ^ q = a := by
    rw [div_pow, hc', div_eq_mul_inv]
    have h2 : a ^ q = a * a ^ (q - 1) := by
      conv_lhs => rw [show q = (q - 1) + 1 from (Nat.sub_add_cancel hq.one_le).symm]
      rw [pow_succ']
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
  have h3 := congrArg (fun z : kˣ => (z : k)) hb''
  simp only [Units.val_pow_eq_pow_val] at h3
  exact h3

/-- **Norm descent, in the shape needed below.** -/
theorem norm_descent_cyclotomic {k : Type} [Field k] [NumberField k]
    (q : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (ζ : Ω) (hζ : IsPrimitiveRoot ζ q)
    (a : kˣ) (b : ↥(IntermediateField.adjoin k ({ζ} : Set Ω)))
    (hb : b ^ q = algebraMap k (IntermediateField.adjoin k ({ζ} : Set Ω)) (a : k)) :
    ∃ b' : kˣ, (b' : k) ^ q = (a : k) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hζmem : ζ ∈ IntermediateField.adjoin k ({ζ} : Set Ω) :=
    IntermediateField.subset_adjoin k _ (Set.mem_singleton ζ)
  have hζK : IsPrimitiveRoot
      (⟨ζ, hζmem⟩ : ↥(IntermediateField.adjoin k ({ζ} : Set Ω))) q :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp
      (by rw [show ((⟨ζ, hζmem⟩ : ↥(IntermediateField.adjoin k ({ζ} : Set Ω))) : Ω) = ζ from rfl]
          exact hζ)
  haveI hcyc : IsCyclotomicExtension {q} k ↥(IntermediateField.adjoin k ({ζ} : Set Ω)) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension k
  haveI hfd : FiniteDimensional k ↥(IntermediateField.adjoin k ({ζ} : Set Ω)) :=
    IsCyclotomicExtension.finiteDimensional {q} k ↥(IntermediateField.adjoin k ({ζ} : Set Ω))
  haveI hgal : IsGalois k ↥(IntermediateField.adjoin k ({ζ} : Set Ω)) :=
    IsCyclotomicExtension.isGalois {q} k ↥(IntermediateField.adjoin k ({ζ} : Set Ω))
  exact norm_descent_aux q hq _ ⟨ζ, hζmem⟩ hζK a b hb

/-! ## The Hasse principle at a single place -/

/-- **Local transfer of the `q`-th power condition to a finite extension.** -/
theorem exists_pow_adicCompletion_of_liesOver' {k K : Type} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hv : 𝔭.asIdeal.LiesOver v.asIdeal) (q : ℕ) (x : kˣ)
    (hx : ∃ y : v.adicCompletion k, y ^ q = algebraMap k (v.adicCompletion k) (x : k)) :
    ∃ z : 𝔭.adicCompletion K,
      z ^ q = algebraMap K (𝔭.adicCompletion K) (algebraMap k K (x : k)) := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨φ, hφ⟩ := Commons.RingTheory.Henselian.adicCompletionMap_liesOver v 𝔭 hv
  have hx1 : algebraMap k (v.adicCompletion k) (x : k) = ((x : k) : v.adicCompletion k) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  have hx2 : algebraMap K (𝔭.adicCompletion K) (algebraMap k K (x : k)) =
      ((algebraMap k K (x : k)) : 𝔭.adicCompletion K) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  refine ⟨φ y, ?_⟩
  rw [← map_pow, hy, hx1, hφ (x : k), hx2]

/-- **The Hasse principle for `q`-th powers over a base containing `μ_q`.** -/
theorem hasse_principle_of_mu {k : Type} [Field k] [NumberField k]
    (q : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (K : Type) [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [IsCyclotomicExtension {q} k K]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) (a : kˣ)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k), v ≠ v₀ →
      ∃ b : v.adicCompletion k, b ^ q = algebraMap k (v.adicCompletion k) (a : k)) :
    ∃ b : kˣ, (b : k) ^ q = (a : k) := by
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NumberField K := NumberField.of_module_finite k K
  have hfin : (v₀.asIdeal.primesOver (NumberField.RingOfIntegers K)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver (K := k) (L := K) v₀.asIdeal
      v₀.isPrime v₀.ne_bot
  let T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    hfin.toFinset.attach.image fun P =>
      (⟨P.1, ((Set.Finite.mem_toFinset hfin).mp P.2).1,
        Ideal.ne_bot_of_mem_primesOver v₀.ne_bot ((Set.Finite.mem_toFinset hfin).mp P.2)⟩ :
        IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  have hTmem : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔭 ∈ T ↔ 𝔭.asIdeal ∈ v₀.asIdeal.primesOver (NumberField.RingOfIntegers K) := by
    intro 𝔭
    constructor
    · intro h
      obtain ⟨P, _, hP⟩ := Finset.mem_image.mp h
      rw [← hP]
      exact (Set.Finite.mem_toFinset hfin).mp P.2
    · intro h
      refine Finset.mem_image.mpr ⟨⟨𝔭.asIdeal, (Set.Finite.mem_toFinset hfin).mpr h⟩,
        Finset.mem_attach _ _, ?_⟩
      exact HeightOneSpectrum.ext rfl
  have hloc : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), 𝔭 ∉ T →
      ∃ b : (𝔭.adicCompletion K)ˣ,
        algebraMap K (𝔭.adicCompletion K)
            ((Units.map (algebraMap k K).toMonoidHom a : Kˣ) : K) =
          (b : 𝔭.adicCompletion K) ^ q := by
    intro 𝔭 h𝔭
    have hPrimes : 𝔭.asIdeal ∉ v₀.asIdeal.primesOver (NumberField.RingOfIntegers K) :=
      fun h => h𝔭 ((hTmem 𝔭).mpr h)
    have hLiesNot : ¬ 𝔭.asIdeal.LiesOver v₀.asIdeal := fun h => hPrimes ⟨𝔭.isPrime, h⟩
    let v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
      IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers k) 𝔭
    have hv_asIdeal : v.asIdeal = 𝔭.asIdeal.under (NumberField.RingOfIntegers k) :=
      IsDedekindDomain.HeightOneSpectrum.under_asIdeal _ 𝔭
    have hlies : 𝔭.asIdeal.LiesOver v.asIdeal := by
      rw [hv_asIdeal]; exact Ideal.over_under _
    have hne : v ≠ v₀ := by
      intro hcon
      exact hLiesNot (by rw [← hcon]; exact hlies)
    obtain ⟨z, hz⟩ := exists_pow_adicCompletion_of_liesOver' v 𝔭 hlies q a (h v hne)
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, zero_pow hq.ne_zero] at hz
      have h1 : algebraMap k K (a : k) = 0 :=
        (algebraMap K (𝔭.adicCompletion K)).injective (by rw [map_zero]; exact hz.symm)
      exact (Units.ne_zero a) ((algebraMap k K).injective (by rw [h1, map_zero]))
    refine ⟨Units.mk0 z hz0, ?_⟩
    have hcoe : ((Units.map (algebraMap k K).toMonoidHom a : Kˣ) : K) = algebraMap k K (a : k) :=
      rfl
    rw [Units.val_mk0, hcoe]
    exact hz.symm
  obtain ⟨ζK, hζK⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot k K (Set.mem_singleton q) hq.ne_zero
  obtain ⟨b, hb⟩ := kummer_pow_of_isPow_almostAll (AlgebraicClosure K) q hq ⟨ζK, hζK⟩
    (Units.map (algebraMap k K).toMonoidHom a) T hloc
  have hb' : ((b : K) : K) ^ q = algebraMap k K (a : k) := by
    rw [hb]
    rfl
  exact norm_descent_aux q hq K ζK hζK a (b : K) hb'

/-- **The Hasse principle for `q`-th powers at a single place.** -/
theorem hasse_principle_single (k : Type) [Field k] [NumberField k]
    (q : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) (a : kˣ)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k), v ≠ v₀ →
      ∃ b : v.adicCompletion k, b ^ q = algebraMap k (v.adicCompletion k) (a : k)) :
    ∃ b : kˣ, (b : k) ^ q = (a : k) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure k) q
  have hζmem : ζ ∈ IntermediateField.adjoin k ({ζ} : Set (AlgebraicClosure k)) :=
    IntermediateField.subset_adjoin k _ (Set.mem_singleton ζ)
  haveI hcyc : IsCyclotomicExtension {q} k
      ↥(IntermediateField.adjoin k ({ζ} : Set (AlgebraicClosure k))) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension k
  haveI hfd : FiniteDimensional k ↥(IntermediateField.adjoin k ({ζ} : Set (AlgebraicClosure k))) :=
    IsCyclotomicExtension.finiteDimensional {q} k
      ↥(IntermediateField.adjoin k ({ζ} : Set (AlgebraicClosure k)))
  haveI hgal : IsGalois k ↥(IntermediateField.adjoin k ({ζ} : Set (AlgebraicClosure k))) :=
    IsCyclotomicExtension.isGalois {q} k
      ↥(IntermediateField.adjoin k ({ζ} : Set (AlgebraicClosure k)))
  exact hasse_principle_of_mu q hq hq2
    ↥(IntermediateField.adjoin k ({ζ} : Set (AlgebraicClosure k))) v₀ a h

/-! ## The uniformiser at `v₀` is not a `q`-th power in the idèle class group -/

/-- The local uniformiser of the completion `k_{v₀}`, as a unit of the local field, is not a
`q`-th power. -/
theorem unifUnit_not_pow (k : Type) [Field k] [NumberField k]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : ℕ) (hq : q.Prime) (hq2 : 2 < q) :
    ¬ ∃ x : (v₀.adicCompletion k)ˣ, x ^ q = NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀ := by
  rintro ⟨x, hx⟩
  have h1 : Valued.v (((x ^ q : (v₀.adicCompletion k)ˣ) : v₀.adicCompletion k)) =
      Valued.v ((NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀ :
        (v₀.adicCompletion k)ˣ) : v₀.adicCompletion k) := by rw [hx]
  rw [Units.val_pow_eq_pow_val, map_pow, NK.GlobalCFT.IdeleClassGroup.valued_unifUnit] at h1
  have h2 : (q : ℤ) * WithZero.log (Valued.v ((x : (v₀.adicCompletion k)ˣ) : v₀.adicCompletion k))
      = -1 := by
    have h0 := congrArg (WithZero.log (M := ℤ)) h1
    rw [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at h0
    exact h0
  have hdvd : (q : ℤ) ∣ 1 :=
    ⟨-WithZero.log (Valued.v ((x : (v₀.adicCompletion k)ˣ) : v₀.adicCompletion k)),
      by linarith⟩
  have hdvd' : q ∣ 1 := by exact_mod_cast hdvd
  have := Nat.le_of_dvd one_pos hdvd'
  omega

/-- **The one-place idèle class of a non-`q`-th-power local unit is not a `q`-th power in `C_k`.**

This is the contrapositive of the Hasse principle `hasse_principle_single`. -/
theorem not_pow_onePlace_of_not_pow (k : Type) [Field k] [NumberField k]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (a : (v₀.adicCompletion k)ˣ)
    (ha : ¬ ∃ x : (v₀.adicCompletion k)ˣ, x ^ q = a) :
    ¬ ∃ y : NK.GlobalCFT.IdeleClassGroup k,
      y ^ q = NK.GlobalCFT.IdeleClassGroup.mk k
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀) a) := by
  classical
  rintro ⟨y, hy⟩
  obtain ⟨η, rfl⟩ := NK.GlobalCFT.IdeleClassGroup.mk_surjective k y
  have hmk : NK.GlobalCFT.IdeleClassGroup.mk k (η ^ q) =
      NK.GlobalCFT.IdeleClassGroup.mk k
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀) a) := by
    rw [map_pow]; exact hy
  obtain ⟨c, hc⟩ : ∃ c : kˣ, NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀) a =
      η ^ q * NK.GlobalCFT.Idele.principalIdele k c := by
    have hmem : (η ^ q)⁻¹ * NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀) a ∈
        NK.GlobalCFT.Idele.principalSubgroup k :=
      (NK.GlobalCFT.IdeleClassGroup.mk_eq_mk_iff).mp hmk
    obtain ⟨c, hc⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hmem
    refine ⟨c, ?_⟩
    calc NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀) a
        = η ^ q * ((η ^ q)⁻¹ * NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀) a) := by
          rw [← mul_assoc, mul_inv_cancel, one_mul]
      _ = η ^ q * NK.GlobalCFT.Idele.principalIdele k c := by rw [hc]
  have hloc : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k), v ≠ v₀ →
      ∃ b : NK.GlobalCFT.Place.localField k (NK.GlobalCFT.Place.ofFinite v),
        b ^ q = algebraMap k (NK.GlobalCFT.Place.localField k (NK.GlobalCFT.Place.ofFinite v))
          (c : k) := by
    intro v hv
    have hcomp := congrArg (fun z : NK.GlobalCFT.Idele k =>
      z (NK.GlobalCFT.Place.ofFinite v)) hc
    have hpow : (η ^ q) (NK.GlobalCFT.Place.ofFinite v) =
        (η (NK.GlobalCFT.Place.ofFinite v)) ^ q :=
      map_pow (NK.GlobalCFT.Idele.eval (NK.GlobalCFT.Place.ofFinite v)) η q
    rw [NK.HassePrinciple.onePlace_apply_ne (by simpa using hv),
      NK.GlobalCFT.Idele.mul_apply, hpow,
      NK.GlobalCFT.Idele.principalIdele_apply] at hcomp
    have hB : Units.map (algebraMap k (NK.GlobalCFT.Place.localField k
          (NK.GlobalCFT.Place.ofFinite v))) c
        = ((η (NK.GlobalCFT.Place.ofFinite v))⁻¹) ^ q := by
      rw [inv_pow]
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hcomp.symm)
    refine ⟨((η (NK.GlobalCFT.Place.ofFinite v))⁻¹ :
      (NK.GlobalCFT.Place.localField k (NK.GlobalCFT.Place.ofFinite v))ˣ), ?_⟩
    have hval := congrArg (fun u : (NK.GlobalCFT.Place.localField k
        (NK.GlobalCFT.Place.ofFinite v))ˣ =>
        (u : NK.GlobalCFT.Place.localField k (NK.GlobalCFT.Place.ofFinite v))) hB
    simpa [Units.coe_map] using hval.symm
  obtain ⟨d, hd⟩ := hasse_principle_single k q hq hq2 v₀ c hloc
  have hd' : d ^ q = c := by
    apply Units.ext
    simpa using hd
  have hcomp₀ := congrArg (fun z : NK.GlobalCFT.Idele k =>
    z (NK.GlobalCFT.Place.ofFinite v₀)) hc
  have hpow₀ : (η ^ q) (NK.GlobalCFT.Place.ofFinite v₀) =
      (η (NK.GlobalCFT.Place.ofFinite v₀)) ^ q :=
    map_pow (NK.GlobalCFT.Idele.eval (NK.GlobalCFT.Place.ofFinite v₀)) η q
  rw [NK.HassePrinciple.onePlace_apply_self, NK.GlobalCFT.Idele.mul_apply, hpow₀,
    NK.GlobalCFT.Idele.principalIdele_apply] at hcomp₀
  refine ha ⟨η (NK.GlobalCFT.Place.ofFinite v₀) *
    Units.map (algebraMap k (NK.GlobalCFT.Place.localField k
      (NK.GlobalCFT.Place.ofFinite v₀))) d, ?_⟩
  rw [mul_pow, ← map_pow, hd']
  exact hcomp₀.symm

end

open NK.GlobalCFT

/-- **The odd Grünwald–Wang step at a single place, in class-field-theoretic form.**

For a number field `k`, a finite place `v₀` and an odd prime `q` there is a *surjective* character
`χ : C_k → Multiplicative (ZMod q)` (the additive group `ZMod q` written multiplicatively, so that
`χ` is the Artin character of a cyclic extension of degree `q`) which is non-trivial on the image of
the local group `k_{v₀}ˣ`.

This is the `S = {v₀}` case of Grünwald's result for odd `q` (Milne, *Class Field Theory*,
VIII.2.4; Artin–Tate, *Class Field Theory*, Ch. X Thm. 5): for odd `q` there is *no* Grünwald–Wang
exceptional case, so local data of order `q` at `v₀` is realised by a global character. -/
theorem grunwald_odd_single_place (k : Type) [Field k] [NumberField k]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : ℕ) (hq : q.Prime) (hq2 : 2 < q) :
    ∃ χ : NK.GlobalCFT.IdeleClassGroup k →* Multiplicative (ZMod q),
      Function.Surjective χ ∧
      ∃ a : (NK.GlobalCFT.Place.localField k (NK.GlobalCFT.Place.ofFinite v₀))ˣ,
        χ (NK.GlobalCFT.IdeleClassGroup.mk k
            (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀) a)) ≠ 1 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hnot : ¬ ∃ y : NK.GlobalCFT.IdeleClassGroup k,
      y ^ q = NK.GlobalCFT.IdeleClassGroup.mk k
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀)
          (NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀)) :=
    not_pow_onePlace_of_not_pow k v₀ q hq hq2 (NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀)
      (unifUnit_not_pow k v₀ q hq hq2)
  have hV : ∃ V : Subgroup (NK.GlobalCFT.IdeleClassGroup k), V.FiniteIndex ∧
      IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup k)) ∧ V.index = q ∧
      NK.GlobalCFT.IdeleClassGroup.mk k
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀)
          (NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀)) ∉ V := by
    by_contra hcon
    obtain ⟨y, hy⟩ := Work.SSGRoute.PTW.mem_pthPower_of_all_open_index_p_subgroups k q
      (NK.GlobalCFT.IdeleClassGroup.mk k
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀)
          (NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀)))
      (fun V h1 h2 h3 => by
        by_contra hmem
        exact hcon ⟨V, h1, h2, h3, hmem⟩)
    exact hnot ⟨y, hy⟩
  obtain ⟨V, hVfin, hVopen, hVidx, hVnot⟩ := hV
  haveI : V.Normal := Subgroup.normal_of_isMulCommutative V
  have hGcard : Nat.card (NK.GlobalCFT.IdeleClassGroup k ⧸ V) = q := by
    rw [← Subgroup.index_eq_card, hVidx]
  haveI : IsCyclic (NK.GlobalCFT.IdeleClassGroup k ⧸ V) := isCyclic_of_prime_card hGcard
  have he : (NK.GlobalCFT.IdeleClassGroup k ⧸ V) ≃* Multiplicative (ZMod q) := by
    have h1 := zmodCyclicMulEquiv (inferInstance :
      IsCyclic (NK.GlobalCFT.IdeleClassGroup k ⧸ V))
    rw [hGcard] at h1
    exact h1.symm
  have hg : (QuotientGroup.mk' V) (NK.GlobalCFT.IdeleClassGroup.mk k
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀)
        (NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀))) ≠ 1 := by
    intro h1
    exact hVnot ((QuotientGroup.eq_one_iff _).mp h1)
  refine ⟨he.toMonoidHom.comp (QuotientGroup.mk' V), ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := he.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V z
    exact ⟨x, hz⟩
  · refine ⟨NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀, ?_⟩
    intro h1
    exact hg (he.injective (by rw [map_one]; exact h1))

end Work.SSGRoute.CycLevel
