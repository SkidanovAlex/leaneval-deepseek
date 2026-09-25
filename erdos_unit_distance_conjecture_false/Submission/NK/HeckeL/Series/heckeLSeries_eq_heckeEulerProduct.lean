/-
The Hecke `L`-series of a ray class character, written as a Dirichlet series over the ideals
coprime to the modulus, equals its Euler product over the primes outside the modulus.
-/
import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.NK.HeckeL.Basic.rayChar_atIdeal_mul
import Submission.NK.HeckeL.Basic.ideal_eq_prod_finsupp
import Submission.NK.HeckeL.Series.tsum_finsupp_support_subset_prod
import Submission.NK.HeckeL.Series.summable_finsupp_prod_pow
import Submission.NK.HeckeL.Series.tendsto_tsum_subtype_of_cofinal

set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain Filter
open scoped BigOperators Classical nonZeroDivisors Topology

open NK.GlobalCFT (Idele IdeleClassGroup)

noncomputable section

namespace NK.HeckeL.Series

variable {K : Type*} [Field K] [NumberField K]


/-! ## The building blocks -/

/-- The argument of the Euler factor at `𝔭`. -/
noncomputable def aCoeff {U : Subgroup (Idele K)} (χ : RayChar K U)
    (S : Finset (PrimeIdeal K)) (s : ℝ) (𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}) : ℂ :=
  χ.atPrime 𝔭.1 * (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)

/-- The ideal attached to a vector of exponents on the primes outside `S`. -/
noncomputable def idealOfCoeff (S : Finset (PrimeIdeal K))
    (c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ) : Ideal (𝓞 K) :=
  ∏ 𝔭 ∈ c.support, (𝔭.1.asIdeal) ^ (c 𝔭)

/-- The summand of the Euler product, expanded. -/
noncomputable def hCoeff {U : Subgroup (Idele K)} (χ : RayChar K U)
    (S : Finset (PrimeIdeal K)) (s : ℝ) (c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ) : ℂ :=
  ∏ 𝔭 ∈ c.support, (aCoeff χ S s 𝔭) ^ (c 𝔭)

/-- The summand of the Hecke `L`-series. -/
noncomputable def gCoeff {U : Subgroup (Idele K)} (χ : RayChar K U)
    (S : Finset (PrimeIdeal K)) (s : ℝ)
    (𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞}) : ℂ :=
  χ.atIdeal 𝔞.1 * (((Ideal.absNorm 𝔞.1 : ℝ) ^ (-s) : ℝ) : ℂ)

/-! ## Multiplicativity of `atIdeal` -/

theorem atPrime_eq_atIdeal {U : Subgroup (Idele K)} (χ : RayChar K U) (𝔭 : PrimeIdeal K) :
    χ.atPrime 𝔭 = χ.atIdeal 𝔭.asIdeal := rfl

theorem atIdeal_one {U : Subgroup (Idele K)} (χ : RayChar K U) :
    χ.atIdeal (1 : Ideal (𝓞 K)) = 1 := by
  have h := NK.HeckeL.Basic.rayChar_atIdeal_mul U χ (1 : Ideal (𝓞 K)) (1 : Ideal (𝓞 K))
    one_ne_zero one_ne_zero
  rw [mul_one] at h
  have hne : χ.atIdeal (1 : Ideal (𝓞 K)) ≠ 0 := by
    show (χ (classOfIdeal K U 1) : ℂ) ≠ 0
    exact Units.ne_zero _
  have h' : χ.atIdeal (1 : Ideal (𝓞 K)) * 1
      = χ.atIdeal (1 : Ideal (𝓞 K)) * χ.atIdeal (1 : Ideal (𝓞 K)) := by
    rw [mul_one]; exact h
  exact (mul_left_cancel₀ hne h').symm

theorem atIdeal_pow {U : Subgroup (Idele K)} (χ : RayChar K U) (I : Ideal (𝓞 K)) (e : ℕ)
    (hI : I ≠ 0) : χ.atIdeal (I ^ e) = χ.atIdeal I ^ e := by
  induction e with
  | zero => rw [pow_zero, pow_zero]; exact atIdeal_one χ
  | succ n ih =>
      rw [pow_succ, NK.HeckeL.Basic.rayChar_atIdeal_mul U χ (I ^ n) I
        (pow_ne_zero n hI) hI, ih, pow_succ]

theorem atIdeal_finset_prod {U : Subgroup (Idele K)} (χ : RayChar K U) {ι : Type*}
    (t : Finset ι) (f : ι → Ideal (𝓞 K)) (hf : ∀ i ∈ t, f i ≠ 0) :
    χ.atIdeal (∏ i ∈ t, f i) = ∏ i ∈ t, χ.atIdeal (f i) := by
  classical
  induction t using Finset.induction with
  | empty =>
      rw [Finset.prod_empty, Finset.prod_empty]
      exact atIdeal_one χ
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [NK.HeckeL.Basic.rayChar_atIdeal_mul U χ (f a) (∏ i ∈ s, f i) hfa
        (Finset.prod_ne_zero_iff.mpr hfs), ih hfs]

/-! ## The exponent-vector description of the ideals coprime to `S` -/

theorem idealOfCoeff_ne_zero (S : Finset (PrimeIdeal K))
    (c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ) : idealOfCoeff S c ≠ 0 := by
  rw [idealOfCoeff, Finset.prod_ne_zero_iff]
  intro 𝔭 _
  exact pow_ne_zero _ 𝔭.1.ne_bot

theorem idealOfCoeff_coprime (S : Finset (PrimeIdeal K))
    (c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ) :
    ∀ 𝔮 ∈ S, ¬ 𝔮.asIdeal ∣ idealOfCoeff S c := by
  intro 𝔮 h𝔮S hdvd
  rw [idealOfCoeff] at hdvd
  have hp𝔮 : Prime 𝔮.asIdeal := Ideal.prime_of_isPrime 𝔮.ne_bot 𝔮.isPrime
  obtain ⟨𝔭, _h𝔭mem, h𝔭dvd⟩ := (hp𝔮.dvd_finset_prod_iff
    (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => 𝔭.1.asIdeal ^ (c 𝔭))).mp hdvd
  have hpdvd : 𝔮.asIdeal ∣ 𝔭.1.asIdeal := hp𝔮.dvd_of_dvd_pow h𝔭dvd
  have hle : 𝔭.1.asIdeal ≤ 𝔮.asIdeal := Ideal.dvd_iff_le.mp hpdvd
  have heq : 𝔭.1.asIdeal = 𝔮.asIdeal :=
    (IsDedekindDomain.HeightOneSpectrum.isMaximal 𝔭.1).eq_of_le 𝔮.isPrime.ne_top hle
  have : 𝔮 = 𝔭.1 := IsDedekindDomain.HeightOneSpectrum.asIdeal_injective heq.symm
  exact 𝔭.2 (this ▸ h𝔮S)

theorem idealOfCoeff_injective (S : Finset (PrimeIdeal K)) :
    Function.Injective (idealOfCoeff (K := K) S) := by
  intro c d h
  obtain ⟨w, _hw, huniq⟩ := NK.HeckeL.Basic.ideal_eq_prod_finsupp (K := K) S (idealOfCoeff S c)
    (idealOfCoeff_ne_zero S c) (idealOfCoeff_coprime S c)
  exact (huniq c rfl).trans (huniq d h.symm).symm

theorem idealOfCoeff_surjective (S : Finset (PrimeIdeal K)) :
    ∀ I : {I : Ideal (𝓞 K) // I ≠ 0 ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I},
      ∃ c, idealOfCoeff S c = I.1 := by
  rintro ⟨I, hI, hcop⟩
  obtain ⟨c, hc, -⟩ := NK.HeckeL.Basic.ideal_eq_prod_finsupp (K := K) S I hI hcop
  exact ⟨c, hc⟩

/-- Bijection between exponent vectors on the primes outside `S` and the nonzero ideals of `𝓞 K`
coprime to `S`. -/
noncomputable def coeffEquiv (S : Finset (PrimeIdeal K)) :
    ({𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ) ≃
      {I : Ideal (𝓞 K) // I ≠ 0 ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I} :=
  Equiv.ofBijective
    (fun c => ⟨idealOfCoeff S c, idealOfCoeff_ne_zero S c, idealOfCoeff_coprime S c⟩)
    ⟨fun _ _ h => idealOfCoeff_injective S (Subtype.ext_iff.mp h),
     fun I => (idealOfCoeff_surjective S I).imp fun c hc => Subtype.ext hc⟩

/-! ## The computation of the character and the norm -/

theorem absNorm_idealOfCoeff (S : Finset (PrimeIdeal K))
    (c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ) :
    Ideal.absNorm (idealOfCoeff S c)
      = ∏ 𝔭 ∈ c.support, (Ideal.absNorm 𝔭.1.asIdeal) ^ (c 𝔭) := by
  have h : Ideal.absNorm (∏ 𝔭 ∈ c.support, (𝔭.1.asIdeal) ^ (c 𝔭))
      = ∏ 𝔭 ∈ c.support, Ideal.absNorm ((𝔭.1.asIdeal) ^ (c 𝔭)) :=
    map_prod (Ideal.absNorm (S := 𝓞 K)) _ _
  rw [idealOfCoeff, h]
  exact Finset.prod_congr rfl (fun 𝔭 _ => map_pow (Ideal.absNorm (S := 𝓞 K)) _ _)

/-- Splitting a real power of a finite product of nonnegative reals. -/
theorem rpow_natCast_pow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (z : ℝ) :
    (x ^ n) ^ z = (x ^ z) ^ n := by
  rw [← Real.rpow_natCast_mul hx n z, ← Real.rpow_natCast (x ^ z) n,
    ← Real.rpow_mul hx z ((n : ℕ) : ℝ)]
  congr 1
  ring

theorem absNorm_idealOfCoeff_rpow (S : Finset (PrimeIdeal K)) (s : ℝ)
    (c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ) :
    ((Ideal.absNorm (idealOfCoeff S c) : ℝ) ^ (-s))
      = ∏ 𝔭 ∈ c.support, ((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) ^ (c 𝔭) := by
  have hcast : ((∏ 𝔭 ∈ c.support, (Ideal.absNorm 𝔭.1.asIdeal) ^ (c 𝔭) : ℕ) : ℝ)
      = ∏ 𝔭 ∈ c.support, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (c 𝔭) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl (fun 𝔭 _ => Nat.cast_pow _ _)
  rw [absNorm_idealOfCoeff, hcast]
  rw [← Real.finsetProd_rpow c.support
    (fun 𝔭 => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (c 𝔭))
    (fun 𝔭 _ => pow_nonneg (Nat.cast_nonneg _) _) (-s)]
  exact Finset.prod_congr rfl (fun 𝔭 _ =>
    rpow_natCast_pow_eq (Nat.cast_nonneg _) (c 𝔭) (-s))

theorem gCoeff_coeffEquiv {U : Subgroup (Idele K)} (χ : RayChar K U)
    (S : Finset (PrimeIdeal K)) (s : ℝ) (c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ) :
    gCoeff χ S s (coeffEquiv S c) = hCoeff χ S s c := by
  have hcoe : (coeffEquiv S c).1 = idealOfCoeff S c := rfl
  have h1 : χ.atIdeal (idealOfCoeff S c)
      = ∏ 𝔭 ∈ c.support, (χ.atPrime 𝔭.1) ^ (c 𝔭) := by
    rw [idealOfCoeff, atIdeal_finset_prod χ c.support (fun 𝔭 => 𝔭.1.asIdeal ^ (c 𝔭))
      (fun 𝔭 _ => pow_ne_zero _ 𝔭.1.ne_bot)]
    exact Finset.prod_congr rfl (fun 𝔭 _ => by
      rw [atIdeal_pow χ 𝔭.1.asIdeal (c 𝔭) 𝔭.1.ne_bot, atPrime_eq_atIdeal])
  have h2 : (((Ideal.absNorm (idealOfCoeff S c) : ℝ) ^ (-s) : ℝ) : ℂ)
      = ∏ 𝔭 ∈ c.support,
          ((((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) ^ (c 𝔭) : ℝ) : ℂ) := by
    rw [absNorm_idealOfCoeff_rpow, Complex.ofReal_prod]
  rw [gCoeff, hCoeff, hcoe, h1, h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun 𝔭 _ => by rw [aCoeff, mul_pow, Complex.ofReal_pow])

/-! ## Sizes and summability -/

theorem norm_aCoeff {U : Subgroup (Idele K)} (χ : RayChar K U)
    [Finite (IdeleClassGroup.rayClassGroup K U)] (S : Finset (PrimeIdeal K))
    (s : ℝ) (𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}) :
    ‖aCoeff χ S s 𝔭‖ = (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by
  rw [aCoeff, norm_mul, RayChar.norm_atPrime_eq_one, one_mul]
  exact (RCLike.norm_ofReal _).trans
    (abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem two_le_absNorm_primeIdeal_hecke (𝔭 : PrimeIdeal K) :
    2 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
  have hne : Ideal.absNorm 𝔭.asIdeal ≠ 1 := fun h =>
    𝔭.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hpos : 1 ≤ Ideal.absNorm 𝔭.asIdeal := by
    rcases Nat.eq_zero_or_pos (Ideal.absNorm 𝔭.asIdeal) with h | h
    · exact absurd h (fun h0 => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
    · exact h
  exact_mod_cast (by omega : 2 ≤ Ideal.absNorm 𝔭.asIdeal)

theorem norm_aCoeff_lt_one {U : Subgroup (Idele K)} (χ : RayChar K U)
    [Finite (IdeleClassGroup.rayClassGroup K U)] (S : Finset (PrimeIdeal K))
    {s : ℝ} (hs : 1 < s) (𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}) :
    ‖aCoeff χ S s 𝔭‖ < 1 := by
  rw [norm_aCoeff χ S s]
  refine (Real.rpow_lt_one_iff_of_pos (Nat.cast_pos.mpr ?_)).mpr
    (Or.inl ⟨by linarith [two_le_absNorm_primeIdeal_hecke 𝔭.1], by linarith⟩)
  exact Nat.pos_of_ne_zero fun h => 𝔭.1.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

theorem summable_norm_aCoeff {U : Subgroup (Idele K)} (χ : RayChar K U)
    [Finite (IdeleClassGroup.rayClassGroup K U)] (S : Finset (PrimeIdeal K))
    {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => ‖aCoeff χ S s 𝔭‖) := by
  have hbase : Summable (fun 𝔭 : PrimeIdeal K => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :=
    Commons.NumberTheory.NumberField.Set.summable_primeIdealNorm K hs
  have hsub : Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) := hbase.subtype _
  exact hsub.congr (fun 𝔭 => (norm_aCoeff χ S s 𝔭).symm)

theorem norm_hCoeff {U : Subgroup (Idele K)} (χ : RayChar K U) (S : Finset (PrimeIdeal K))
    (s : ℝ) (c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ) :
    ‖hCoeff χ S s c‖ = ∏ 𝔭 ∈ c.support, (‖aCoeff χ S s 𝔭‖) ^ (c 𝔭) := by
  rw [hCoeff, norm_prod]
  exact Finset.prod_congr rfl (fun 𝔭 _ => norm_pow _ _)

theorem summable_norm_hCoeff {U : Subgroup (Idele K)} (χ : RayChar K U)
    [Finite (IdeleClassGroup.rayClassGroup K U)] (S : Finset (PrimeIdeal K))
    {s : ℝ} (hs : 1 < s) :
    Summable (fun c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ => ‖hCoeff χ S s c‖) := by
  have h := summable_finsupp_prod_pow
    (x := fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => ‖aCoeff χ S s 𝔭‖)
    (fun 𝔭 => norm_nonneg _) (fun 𝔭 => norm_aCoeff_lt_one χ S hs 𝔭)
    (summable_norm_aCoeff χ S hs)
  exact h.congr (fun c => (norm_hCoeff χ S s c).symm)

theorem summable_hCoeff {U : Subgroup (Idele K)} (χ : RayChar K U)
    [Finite (IdeleClassGroup.rayClassGroup K U)] (S : Finset (PrimeIdeal K))
    {s : ℝ} (hs : 1 < s) :
    Summable (fun c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ => hCoeff χ S s c) :=
  (summable_norm_hCoeff χ S hs).of_norm

/-! ## The Euler product -/

theorem heckeEulerProduct_eq_tprod {U : Subgroup (Idele K)} (χ : RayChar K U)
    (S : Finset (PrimeIdeal K)) (s : ℝ) :
    heckeEulerProduct K U S χ s
      = ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, (1 - aCoeff χ S s 𝔭)⁻¹ := rfl

theorem multipliable_eulerFactor {U : Subgroup (Idele K)} (χ : RayChar K U)
    [Finite (IdeleClassGroup.rayClassGroup K U)] (S : Finset (PrimeIdeal K))
    {s : ℝ} (hs : 1 < s) :
    Multipliable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => (1 - aCoeff χ S s 𝔭)⁻¹) := by
  have hsum : Summable (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => ‖-aCoeff χ S s 𝔭‖) := by
    simpa only [norm_neg] using summable_norm_aCoeff χ S hs
  have hne : ∀ 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, (1 : ℂ) + -aCoeff χ S s 𝔭 ≠ 0 := by
    intro 𝔭 h
    have h1 : (1 : ℂ) = aCoeff χ S s 𝔭 := by
      have := congrArg (fun z : ℂ => z + aCoeff χ S s 𝔭) h
      simpa using this
    have h2 : ‖aCoeff χ S s 𝔭‖ = 1 := by rw [← h1, norm_one]
    linarith [norm_aCoeff_lt_one χ S hs 𝔭]
  have hP : HasProd (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => (1 : ℂ) + -aCoeff χ S s 𝔭)
      (∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, ((1 : ℂ) + -aCoeff χ S s 𝔭)) :=
    (multipliable_one_add_of_summable hsum).hasProd
  have hne0 : (∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}, ((1 : ℂ) + -aCoeff χ S s 𝔭)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable hne hsum
  exact ((hP.inv₀ hne0).multipliable).congr (fun 𝔭 => rfl)

/-! ## The main theorem -/

theorem heckeLSeries_eq_heckeEulerProduct {K : Type*} [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : NK.HeckeL.RayChar K U) {s : ℝ} (hs : 1 < s) :
    NK.HeckeL.heckeLSeries K U S χ s = NK.HeckeL.heckeEulerProduct K U S χ s := by
  -- the truncated product is the sum over exponent vectors supported on `T`
  have hsum_prod : ∀ T : Finset {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
      ∑' (c : {c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ // c.support ⊆ T}), hCoeff χ S s c.1
        = ∏ 𝔭 ∈ T, (1 - aCoeff χ S s 𝔭)⁻¹ := by
    intro T
    have h := tsum_finsupp_support_subset_prod T (aCoeff χ S s)
      (fun i _ => norm_aCoeff_lt_one χ S hs i)
    simpa only [hCoeff] using h
  -- the sum over the supported vectors converges to the full sum
  have hmono : Tendsto (fun T : Finset {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
      ∑' (c : {c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ // c.support ⊆ T}), hCoeff χ S s c.1)
      atTop (𝓝 (∑' c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ, hCoeff χ S s c)) :=
    tendsto_tsum_subtype_of_cofinal
      (f := fun c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ => hCoeff χ S s c)
      (summable_hCoeff χ S hs)
      (fun T : Finset {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
        {c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ | c.support ⊆ T})
      (fun t => ⟨t.biUnion (fun c => c.support), fun b hb c hc =>
        (Finset.subset_biUnion_of_mem
          (fun c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ => c.support) hc).trans hb⟩)
  -- the truncated products converge to the Euler product
  have hprod : Tendsto (fun T : Finset {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
      ∏ 𝔭 ∈ T, (1 - aCoeff χ S s 𝔭)⁻¹) atTop (𝓝 (heckeEulerProduct K U S χ s)) := by
    rw [heckeEulerProduct_eq_tprod χ S s]
    exact (multipliable_eulerFactor χ S hs).hasProd
  have hEq : (∑' c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ, hCoeff χ S s c)
      = heckeEulerProduct K U S χ s :=
    tendsto_nhds_unique hmono
      (hprod.congr' (Filter.Eventually.of_forall fun T => (hsum_prod T).symm))
  calc heckeLSeries K U S χ s
      = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞}, gCoeff χ S s 𝔞 := rfl
    _ = ∑' c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ, gCoeff χ S s (coeffEquiv S c) :=
        (Equiv.tsum_eq (coeffEquiv S) (gCoeff χ S s)).symm
    _ = ∑' c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ, hCoeff χ S s c :=
        tsum_congr (fun c => gCoeff_coeffEquiv χ S s c)
    _ = heckeEulerProduct K U S χ s := hEq

end NK.HeckeL.Series
