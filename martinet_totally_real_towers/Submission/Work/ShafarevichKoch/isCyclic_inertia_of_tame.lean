import Mathlib
import Submission.Commons.NumberTheory.NumberField.tame_totallyRamified_different_not_pow_dvd

/-!
# Tamely ramified inertia is cyclic

This is the local-field input `(D)` of the Shafarevich--Koch chapter: for a Galois extension of
number fields `L/F` and a prime `P` of `𝒪_L` above a rational prime `q` which is tame at `P`
(`q ∤ e(P/P ∩ 𝒪_F)`), the inertia group `I_P` is cyclic.

The proof is the classical one, in the "global" (uncompleted) form:

* let `T = L^{I_P}` be the inertia field; then `L/T` is totally ramified of degree `e = |I_P|`
  and tame, and the Galois group of `L/T` *is* `I_P`;
* pick a uniformizer `π ∈ P ∖ P²`; then `L = T(π)` and, writing `f = minpoly T π`,
  `f'(π) = ∏_{σ ≠ 1} (π - σ π)`;
* every `σ ∈ I_P` satisfies `σ π - π ∈ P`, so `v_P(f'(π)) = ∑_{σ≠1} v_P(π - σπ) ≥ e - 1`;
* the tame different bound `f'(π) ∉ P^e` gives `v_P(f'(π)) < e`, so `v_P(π - σπ) = 1` for all
  `σ ≠ 1`, i.e. no element of `I_P` acts trivially on `P/P²`;
* hence `I_P ↪ (𝒪_L/P)ˣ`, the units of a finite field, which are cyclic.
-/

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-! ## Two general lemmas -/

section Minpoly

theorem aeval_derivative_minpoly_eq_prod {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)] [DecidableEq (L ≃ₐ[K] L)]
    (α : L) (hα : IntermediateField.adjoin K {α} = ⊤) :
    Polynomial.aeval α (Polynomial.derivative (minpoly K α)) =
      ∏ σ ∈ (Finset.univ.erase (1 : L ≃ₐ[K] L)), (α - σ α) := by
  classical
  set F : Polynomial L := ∏ σ : L ≃ₐ[K] L, (Polynomial.X - Polynomial.C (σ α)) with hF
  have hFmonic : F.Monic := by
    rw [hF]; exact Polynomial.monic_prod_of_monic _ _ (fun σ _ => Polynomial.monic_X_sub_C _)
  have hFdeg : F.natDegree = Fintype.card (L ≃ₐ[K] L) := by
    rw [hF, Polynomial.natDegree_prod_of_monic _ _ (fun σ _ => Polynomial.monic_X_sub_C _)]
    simp
  have hFroot : Polynomial.aeval α F = 0 := by
    rw [hF, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (1 : L ≃ₐ[K] L)) (by simp)
  have hfix : ∀ τ : L ≃ₐ[K] L,
      Polynomial.map (τ : L →+* L) F = F := by
    intro τ
    rw [hF, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact Finset.prod_equiv (Equiv.mulLeft τ) (by intro i; simp)
      (by intro i _; simp [AlgEquiv.mul_apply])
  have hlifts : F ∈ Polynomial.lifts (algebraMap K L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [← IntermediateField.mem_bot, IsGalois.mem_bot_iff_fixed]
    intro τ
    have h := congrArg (fun p : Polynomial L => p.coeff n) (hfix τ)
    rw [Polynomial.coeff_map] at h
    exact h
  obtain ⟨Q, hQmap, hQdeg, hQmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hFmonic
  have hQroot : Polynomial.aeval α Q = 0 := by
    have h : Polynomial.aeval α Q = Polynomial.aeval α F := by
      rw [← hQmap, Polynomial.aeval_map_algebraMap]
    rw [h, hFroot]
  have hdvd : minpoly K α ∣ Q := minpoly.dvd K α hQroot
  have htop : Module.finrank K ↥(⊤ : IntermediateField K L) = Module.finrank K L :=
    (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finrank_eq
  have hQdegK : Q.natDegree = (minpoly K α).natDegree := by
    rw [hQdeg, hFdeg, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank K L,
      ← IntermediateField.adjoin.finrank (IsGalois.integral K α), hα, htop]
  have hQeq : Q = minpoly K α :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsGalois.integral K α)) hQmonic
      hdvd (le_of_eq hQdegK)
  have hderiv : Polynomial.aeval α (Polynomial.derivative (minpoly K α)) =
      Polynomial.aeval α (Polynomial.derivative F) := by
    rw [← hQeq, ← hQmap, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
  set G : Polynomial L :=
    ∏ σ ∈ (Finset.univ.erase (1 : L ≃ₐ[K] L)), (Polynomial.X - Polynomial.C (σ α)) with hG
  have hFG : F = (Polynomial.X - Polynomial.C α) * G := by
    rw [hG, hF, ← Finset.prod_erase_mul (Finset.univ)
      (fun σ => Polynomial.X - Polynomial.C (σ α)) (Finset.mem_univ (1 : L ≃ₐ[K] L))]
    simp only [AlgEquiv.one_apply]
    exact mul_comm _ _
  rw [hderiv, hFG, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C]
  rw [map_add, map_mul, map_one, one_mul]
  have hz : Polynomial.aeval α (Polynomial.X - Polynomial.C α) = 0 := by simp
  rw [map_mul, hz, zero_mul, add_zero]
  rw [hG, map_prod]
  exact Finset.prod_congr rfl (fun σ _ => by simp)


end Minpoly

section Embedding

theorem isCyclic_of_acts_trivially_mod_maximalIdeal {R : Type*} [CommRing R]
    [IsDedekindDomain R] (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)] (hPne : P ≠ ⊥)
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G R]
    (htriv : ∀ g : G, ∀ x : R, g • x - x ∈ P)
    (π : R) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2)
    (hsep : ∀ g : G, g ≠ 1 → π - g • π ∉ P ^ 2) :
    IsCyclic G := by
  classical
  haveI hfield : Field (R ⧸ P) := Ideal.Quotient.field P
  haveI hPprime : P.IsPrime := Ideal.IsMaximal.isPrime (show P.IsMaximal from inferInstance)
  let v : IsDedekindDomain.HeightOneSpectrum R :=
    { asIdeal := P, isPrime := hPprime, ne_bot := hPne }
  have hπ0 : π ≠ 0 := fun h => hπ2 (by rw [h]; exact Submodule.zero_mem _)
  have hvπ : v.intValuation π = WithZero.exp (-1 : ℤ) := by
    have hle : v.intValuation π ≤ WithZero.exp (-(1 : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v π 1).mpr (by simpa using hπ)
    have hlt : WithZero.exp (-(2 : ℤ)) < v.intValuation π := by
      rw [lt_iff_not_ge]
      intro hc
      exact hπ2 ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v π 2).mp hc)
    obtain ⟨n, hn⟩ : ∃ n : ℤ, v.intValuation π = WithZero.exp n :=
      ⟨WithZero.log (v.intValuation π),
        (WithZero.exp_log (IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v π hπ0)).symm⟩
    rw [hn] at hle hlt
    rw [WithZero.exp_le_exp] at hle
    rw [WithZero.exp_lt_exp] at hlt
    rw [hn, show n = -1 by omega]
  have hgP : ∀ g : G, g • π ∈ P := by
    intro g
    have h := htriv g π
    have heq : g • π = (g • π - π) + π := by abel
    rw [heq]
    exact P.add_mem h hπ
  have hmapP : ∀ g : G, ∀ x ∈ P, g • x ∈ P := by
    intro g x hx
    have h := htriv g x
    have heq : g • x = (g • x - x) + x := by abel
    rw [heq]
    exact P.add_mem h hx
  have hmapP2 : ∀ g : G, ∀ x ∈ P ^ 2, g • x ∈ P ^ 2 := by
    intro g x hx
    rw [pow_two] at hx ⊢
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [smul_mul']
      exact Ideal.mul_mem_mul (hmapP g a ha) (hmapP g b hb)
    · intro u w hu hw
      rw [smul_add]
      exact add_mem hu hw
  have hexists : ∀ g : G, ∃ c : R, g • π - c * π ∈ P ^ 2 := by
    intro g
    have hle : v.intValuation (g • π) ≤ v.intValuation π := by
      rw [hvπ]
      exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v (g • π) 1).mpr
        (by simpa using hgP g)
    obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.exists_intValuation_mul_sub_lt v hle
      (Multiplicative.ofAdd (-2))
    refine ⟨y, ?_⟩
    rw [← WithZero.exp_eq_coe_ofAdd (-2)] at hy
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v _ 2).mp (le_of_lt hy)
  choose lam hlam using hexists
  have hkey : ∀ {a b : R}, (a - b) * π ∈ P ^ 2 → a - b ∈ P := by
    intro a b hab
    have h1 : v.intValuation (a - b) ≤ WithZero.exp (-(1 : ℤ)) := by
      by_cases hx : v.intValuation (a - b) = 0
      · rw [hx]; exact zero_le
      · have h2 : v.intValuation ((a - b) * π) ≤ WithZero.exp (-(2 : ℤ)) :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v _ 2).mpr hab
        rw [Valuation.map_mul, hvπ] at h2
        rw [← WithZero.exp_log hx] at h2
        rw [← WithZero.exp_add, WithZero.exp_le_exp] at h2
        rw [← WithZero.exp_log hx]
        exact WithZero.exp_le_exp.mpr (by omega)
    simpa using (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v (a - b) 1).mp
      (by simpa using h1)
  have hlamgπ : ∀ g : G, lam g * π ∈ P := by
    intro g
    have h := P.sub_mem (hgP g) (P.pow_le_self (by norm_num : (2:ℕ) ≠ 0) (hlam g))
    rwa [show g • π - (g • π - lam g * π) = lam g * π by ring] at h
  have huniq : ∀ {g : G} {c : R}, g • π - c * π ∈ P ^ 2 → lam g - c ∈ P := by
    intro g c h
    refine hkey ?_
    have h1 : (g • π - lam g * π) - (g • π - c * π) ∈ P ^ 2 :=
      Submodule.sub_mem (P ^ 2) (hlam g) h
    have heq : (g • π - lam g * π) - (g • π - c * π) = (c - lam g) * π := by ring
    rw [heq] at h1
    have : (lam g - c) * π = -((c - lam g) * π) := by ring
    rw [this]
    exact neg_mem h1
  have hmul : ∀ g h : G, lam (g * h) - lam h * lam g ∈ P := by
    intro g h
    refine hkey ?_
    have hpP : g • lam h - lam h ∈ P := htriv g (lam h)
    have hmain : (g * h) • π - lam h * lam g * π ∈ P ^ 2 := by
      have key : (g * h) • π - lam h * lam g * π
          = lam h * (g • π - lam g * π) + (g • lam h - lam h) * (lam g * π)
            + (g • lam h - lam h) * (g • π - lam g * π) + g • (h • π - lam h * π) := by
        have e1 : (g * h) • π = g • (h • π) := by rw [mul_smul]
        have e2 : h • π = lam h * π + (h • π - lam h * π) := by ring
        have e3 : g • π = lam g * π + (g • π - lam g * π) := by ring
        have e6 : g • lam h = lam h + (g • lam h - lam h) := by ring
        rw [e1, e2, smul_add, smul_mul', e6, e3]
        ring
      rw [key]
      have hA : lam h * (g • π - lam g * π) ∈ P ^ 2 := Ideal.mul_mem_left _ _ (hlam g)
      have hB : (g • lam h - lam h) * (lam g * π) ∈ P ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul hpP (hlamgπ g)
      have hC : (g • lam h - lam h) * (g • π - lam g * π) ∈ P ^ 2 :=
        Ideal.mul_mem_left _ _ (hlam g)
      have hD : g • (h • π - lam h * π) ∈ P ^ 2 := hmapP2 g _ (hlam h)
      exact add_mem (add_mem (add_mem hA hB) hC) hD
    have hsub : lam (g * h) * π - (g * h) • π ∈ P ^ 2 := by
      have := neg_mem (hlam (g * h))
      rwa [show -((g * h) • π - lam (g * h) * π) = lam (g * h) * π - (g * h) • π by ring] at this
    have heq : (lam (g * h) - lam h * lam g) * π
        = (lam (g * h) * π - (g * h) • π) + ((g * h) • π - lam h * lam g * π) := by ring
    rw [heq]
    exact add_mem hsub hmain
  have hval : ∀ g : G, lam g ∉ P := by
    intro g hg
    have h : lam g * π ∈ P ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hg hπ
    have h2 : g • π ∈ P ^ 2 := by
      have := add_mem (hlam g) h
      rwa [show (g • π - lam g * π) + lam g * π = g • π by ring] at this
    refine hπ2 ?_
    have := hmapP2 g⁻¹ (g • π) h2
    rwa [show g⁻¹ • (g • π) = π by rw [← mul_smul]; simp] at this
  have hunit : ∀ g : G, IsUnit (Ideal.Quotient.mk P (lam g)) := fun g => by
    have h := Ideal.Quotient.isUnit_mk_pow_of_notMem P (n := 1) (hval g)
    rwa [pow_one] at h
  let f : G → (R ⧸ P)ˣ := fun g => (hunit g).unit
  have hfval : ∀ g : G, ((f g : (R ⧸ P)ˣ) : R ⧸ P) = Ideal.Quotient.mk P (lam g) :=
    fun g => (hunit g).unit_spec
  have hf : ∀ g h : G, f (g * h) = f g * f h := by
    intro g h
    apply Units.ext
    rw [hfval, Units.val_mul, hfval, hfval, ← map_mul]
    rw [Ideal.Quotient.eq]
    have := hmul g h
    rwa [← show lam (g * h) - lam g * lam h = lam (g * h) - lam h * lam g by ring] at this
  let θ : G →* (R ⧸ P)ˣ := MonoidHom.mk' f hf
  have hθ : ∀ g : G, ((θ g : (R ⧸ P)ˣ) : R ⧸ P) = Ideal.Quotient.mk P (lam g) := fun g => hfval g
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : lam g - 1 ∈ P := by
      refine (Ideal.Quotient.eq).mp ?_
      rw [← hθ g, hg]
      simp
    by_contra hg1
    refine hsep g hg1 ?_
    have h4 : lam g * π - π ∈ P ^ 2 := by
      have h2 : (lam g - 1) * π ∈ P ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul h1 hπ
      rwa [show (lam g - 1) * π = lam g * π - π by ring] at h2
    have h3 : g • π - π ∈ P ^ 2 := by
      have := add_mem (hlam g) h4
      rwa [show (g • π - lam g * π) + (lam g * π - π) = g • π - π by ring] at this
    have := neg_mem h3
    rwa [show -(g • π - π) = π - g • π by ring] at this
  exact isCyclic_of_injective θ hinj


end Embedding

/-! ## The main theorem -/

theorem isCyclic_inertia_of_tame {F L : Type} [Field F] [Field L] [Algebra F L]
    [NumberField F] [NumberField L] [FiniteDimensional F L] [IsGalois F L]
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime]
    (q : ℕ) (hq : Nat.Prime q)
    (hover : P.under ℤ = Ideal.span ({(q : ℤ)} : Set ℤ))
    (htame : ¬ (q : ℤ) ∣ (P.ramificationIdx (NumberField.RingOfIntegers F) : ℤ)) :
    IsCyclic ↥(Ideal.inertia (L ≃ₐ[F] L) P) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  -- ## P is nonzero and maximal
  have hqP : (q : 𝓞 L) ∈ P := by
    have h1 : (q : ℤ) ∈ Ideal.span ({(q : ℤ)} : Set ℤ) := Ideal.subset_span (by simp)
    rw [← hover] at h1
    simpa using h1
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot] at hqP
    have h0 : (q : 𝓞 L) = 0 := Ideal.mem_bot.mp hqP
    exact hq.ne_zero (Nat.cast_eq_zero.mp h0)
  haveI hPmax : P.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot P hPne
  -- ## the inertia field
  let I : Subgroup (L ≃ₐ[F] L) := Ideal.inertia (L ≃ₐ[F] L) P
  let T : IntermediateField F L := IntermediateField.fixedField I
  have hfin : Module.finrank ↥T L = Nat.card ↥I := IntermediateField.finrank_fixedField_eq_card I
  have hram : Nat.card ↥I = P.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (P.under (𝓞 F)) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[F] L)]
  -- ## `L/T` is totally ramified
  have htop : Ideal.inertia (L ≃ₐ[↥T] L) P = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    rw [Ideal.mem_inertia]
    intro x
    have hτmem : (((IntermediateField.subgroupEquivAlgEquiv I).symm σ : ↥I) : L ≃ₐ[F] L) ∈
        Ideal.inertia (L ≃ₐ[F] L) P := ((IntermediateField.subgroupEquivAlgEquiv I).symm σ).2
    have hx := (Ideal.mem_inertia).mp hτmem x
    have h1 : σ • x =
        (((IntermediateField.subgroupEquivAlgEquiv I).symm σ : ↥I) : L ≃ₐ[F] L) • x := by
      apply FaithfulSMul.algebraMap_injective (𝓞 L) L
      have e1 : algebraMap (𝓞 L) L (σ • x) = σ (algebraMap (𝓞 L) L x) := by
        rw [algebraMap.smul']
        rfl
      have e2 : algebraMap (𝓞 L) L
            ((((IntermediateField.subgroupEquivAlgEquiv I).symm σ : ↥I) : L ≃ₐ[F] L) • x) =
          ((((IntermediateField.subgroupEquivAlgEquiv I).symm σ : ↥I) : L ≃ₐ[F] L))
            (algebraMap (𝓞 L) L x) := by
        rw [algebraMap.smul']
        rfl
      have hfun : ∀ y : L,
          ((((IntermediateField.subgroupEquivAlgEquiv I).symm σ : ↥I) : L ≃ₐ[F] L)) y = σ y :=
        fun y => congrFun (congrArg (fun f : L ≃ₐ[↥T] L => (f : L → L))
          ((IntermediateField.subgroupEquivAlgEquiv I).apply_symm_apply σ)).symm y
      rw [e1, e2, hfun]
    rw [h1]
    exact hx
  have he : Module.finrank ↥T L = P.ramificationIdx (𝓞 ↥T) := by
    have hcard : Nat.card ↥(Ideal.inertia (L ≃ₐ[↥T] L) P) = P.ramificationIdx (𝓞 ↥T) := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (P.under (𝓞 ↥T)) P,
        Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[↥T] L)]
    rw [htop, Subgroup.card_top, IsGalois.card_aut_eq_finrank] at hcard
    exact hcard
  have htameT : ¬ q ∣ P.ramificationIdx (𝓞 ↥T) := by
    rw [← he, hfin, hram]
    intro h
    exact htame (Int.ofNat_dvd.mpr h)
  -- ## `P₀ = P ∩ 𝓞 T` lies over `q`
  have hP0lies : (P.under (𝓞 ↥T)).LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
    ⟨by rw [Ideal.under_under, hover]⟩
  have hP0max : (P.under (𝓞 ↥T)).IsMaximal := by
    refine Ideal.isMaximal_of_isPrime_of_ne_bot (P.under (𝓞 ↥T)) ?_
    intro hbot
    have hqmem : (q : ℤ) ∈ (P.under (𝓞 ↥T)).under ℤ := by
      rw [← hP0lies.over]
      exact Ideal.subset_span (by simp)
    rw [hbot, Ideal.under_bot] at hqmem
    exact hq.ne_zero (Int.natCast_eq_zero.mp (Ideal.mem_bot.mp hqmem))
  have hmap : Ideal.map (algebraMap (𝓞 ↥T) (𝓞 L)) (P.under (𝓞 ↥T)) =
      P ^ P.ramificationIdx (𝓞 ↥T) :=
    (Commons.NumberTheory.NumberField.totallyRamified_structure q (P.under (𝓞 ↥T)) P he).2.2
  -- ## a uniformizer
  obtain ⟨π, hπ, hπ2⟩ := Commons.NumberTheory.NumberField.exists_uniformizer P
  have hgen : Algebra.adjoin ↥T ({algebraMap (𝓞 L) L π} : Set L) = ⊤ :=
    Commons.NumberTheory.NumberField.uniformizer_generates q (P.under (𝓞 ↥T)) P he π hπ hπ2
  have hα : IntermediateField.adjoin ↥T {algebraMap (𝓞 L) L π} = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj]
    rw [IntermediateField.adjoin_toSubalgebra ({algebraMap (𝓞 L) L π} : Set L), hgen]
    rfl
  -- ## the derivative formula
  set g : 𝓞 L := Polynomial.aeval π (Polynomial.derivative (minpoly (𝓞 ↥T) π)) with hgdef
  set s : Finset (L ≃ₐ[↥T] L) := Finset.univ.erase (1 : L ≃ₐ[↥T] L) with hsdef
  have hg_eq : g = ∏ σ ∈ s, (π - σ • π) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    have hder := aeval_derivative_minpoly_eq_prod (K := ↥T) (L := L) (algebraMap (𝓞 L) L π) hα
    rw [← hsdef] at hder
    calc algebraMap (𝓞 L) L g
        = Polynomial.aeval (algebraMap (𝓞 L) L π)
            (Polynomial.derivative ((minpoly (𝓞 ↥T) π).map (algebraMap (𝓞 ↥T) ↥T))) := by
          rw [hgdef, Polynomial.derivative_map]
          refine Polynomial.map_aeval_eq_aeval_map (R := 𝓞 ↥T) (S := 𝓞 L) (T := ↥T) (U := L)
            (φ := algebraMap (𝓞 ↥T) ↥T) (ψ := algebraMap (𝓞 L) L)
            (p := Polynomial.derivative (minpoly (𝓞 ↥T) π)) (a := π) ?_
          ext x
          rw [RingHom.comp_apply, RingHom.comp_apply,
            ← IsScalarTower.algebraMap_apply (𝓞 ↥T) ↥T L,
            ← IsScalarTower.algebraMap_apply (𝓞 ↥T) (𝓞 L) L]
      _ = Polynomial.aeval (algebraMap (𝓞 L) L π)
            (Polynomial.derivative (minpoly ↥T (algebraMap (𝓞 L) L π))) := by
          congr 2
          exact (minpoly.isIntegrallyClosed_eq_field_fractions ↥T L
            (IsIntegralClosure.isIntegral (R := 𝓞 ↥T) (A := 𝓞 L) (B := L) π)).symm
      _ = ∏ σ ∈ s, (algebraMap (𝓞 L) L π - σ (algebraMap (𝓞 L) L π)) := hder
      _ = algebraMap (𝓞 L) L (∏ σ ∈ s, (π - σ • π)) := by
          rw [map_prod]
          refine Finset.prod_congr rfl (fun σ _ => ?_)
          rw [map_sub, algebraMap.smul', AlgEquiv.smul_def]
  -- ## the tame different bound
  have hg_notmem : g ∉ P ^ Module.finrank ↥T L := by
    have h := Commons.NumberTheory.NumberField.derivative_uniformizer_tame_not_mem_pow q
      (P.under (𝓞 ↥T)) P hmap π hπ hπ2 he htameT
    rwa [← he] at h
  have hg_ne : g ≠ 0 := fun h => hg_notmem (by rw [h]; exact Submodule.zero_mem _)
  -- ## counting
  have hprod_ne : ∏ σ ∈ s, (π - σ • π) ≠ 0 := by rw [← hg_eq]; exact hg_ne
  have hfac_ne : ∀ σ ∈ s, (π - σ • π) ≠ 0 := Finset.prod_ne_zero_iff.mp hprod_ne
  have htriv : ∀ (σ : L ≃ₐ[↥T] L), ∀ x : 𝓞 L, σ • x - x ∈ P := by
    intro σ x
    exact (Ideal.mem_inertia).mp (by rw [htop]; trivial) x
  have hfac_ge : ∀ σ ∈ s, 1 ≤ Commons.NumberTheory.NumberField.orderCount P (π - σ • π) := by
    intro σ hσ
    refine Commons.NumberTheory.NumberField.orderCount_ge_of_mem_pow P (hfac_ne σ hσ) 1 ?_
    have h1 : σ • π ∈ P := by
      have h2 := htriv σ π
      rw [show σ • π = (σ • π - π) + π by ring]
      exact P.add_mem h2 hπ
    simpa [pow_one] using P.sub_mem hπ h1
  have hcount_prod : ∀ (t : Finset (L ≃ₐ[↥T] L)),
      (∀ σ ∈ t, (π - σ • π) ≠ 0) →
      Commons.NumberTheory.NumberField.orderCount P (∏ σ ∈ t, (π - σ • π)) =
        ∑ σ ∈ t, Commons.NumberTheory.NumberField.orderCount P (π - σ • π) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.prod_empty, Finset.sum_empty]
      have h1P : (1 : 𝓞 L) ∉ P := by
        intro hmem
        have : (⊤ : Ideal (𝓞 L)) ≤ P := by
          rw [← Ideal.span_singleton_one]
          exact (Ideal.span_singleton_le_iff_mem P).mpr hmem
        exact hPmax.ne_top (top_unique this)
      exact Commons.NumberTheory.NumberField.orderCount_eq_zero_of_not_mem (P := P) h1P
    | insert a t ha ih =>
      intro ht
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        Commons.NumberTheory.NumberField.orderCount_mul P (ht a (Finset.mem_insert_self a t))
          (Finset.prod_ne_zero_iff.mpr (fun σ hσ => ht σ (Finset.mem_insert_of_mem hσ))),
        ih (fun σ hσ => ht σ (Finset.mem_insert_of_mem hσ))]
  have hcount : Commons.NumberTheory.NumberField.orderCount P g =
      ∑ σ ∈ s, Commons.NumberTheory.NumberField.orderCount P (π - σ • π) := by
    rw [hg_eq]
    exact hcount_prod s hfac_ne
  have hup : Commons.NumberTheory.NumberField.orderCount P g < P.ramificationIdx (𝓞 ↥T) := by
    rw [← he]
    by_contra hcon
    push_neg at hcon
    exact hg_notmem (Commons.NumberTheory.NumberField.mem_pow_of_orderCount_ge P hg_ne hcon)
  have hcard_s : s.card = P.ramificationIdx (𝓞 ↥T) - 1 := by
    rw [hsdef, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, he]
  have hocc : ∀ σ ∈ s, Commons.NumberTheory.NumberField.orderCount P (π - σ • π) = 1 := by
    intro σ hσ
    by_contra hne
    have hge : 2 ≤ Commons.NumberTheory.NumberField.orderCount P (π - σ • π) := by
      have := hfac_ge σ hσ; omega
    have hsum_ge : P.ramificationIdx (𝓞 ↥T) ≤
        ∑ τ ∈ s, Commons.NumberTheory.NumberField.orderCount P (π - τ • π) := by
      rw [← Finset.sum_erase_add s (fun τ => Commons.NumberTheory.NumberField.orderCount P (π - τ • π)) hσ]
      have hrest : (s.erase σ).card ≤ ∑ τ ∈ s.erase σ,
          Commons.NumberTheory.NumberField.orderCount P (π - τ • π) := by
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum (fun τ hτ => hfac_ge τ (Finset.mem_of_mem_erase hτ))
      have hc : (s.erase σ).card = s.card - 1 := Finset.card_erase_of_mem hσ
      omega
    omega
  -- ## no nontrivial element acts trivially
  have hsep : ∀ σ : L ≃ₐ[↥T] L, σ ≠ 1 → π - σ • π ∉ P ^ 2 := by
    intro σ hσ1 hcon
    have hmem : σ ∈ s := by rw [hsdef]; exact Finset.mem_erase.mpr ⟨hσ1, Finset.mem_univ _⟩
    have := Commons.NumberTheory.NumberField.orderCount_ge_of_mem_pow P (hfac_ne σ hmem) 2 hcon
    have := hocc σ hmem
    omega
  -- ## conclusion
  have hcyc : IsCyclic (L ≃ₐ[↥T] L) :=
    isCyclic_of_acts_trivially_mod_maximalIdeal P hPne (L ≃ₐ[↥T] L) htriv π hπ hπ2 hsep
  exact (IntermediateField.subgroupEquivAlgEquiv I).isCyclic.mpr hcyc

end Work.ShafarevichKoch
