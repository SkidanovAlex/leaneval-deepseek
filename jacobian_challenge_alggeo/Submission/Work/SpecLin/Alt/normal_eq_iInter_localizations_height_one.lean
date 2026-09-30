import Mathlib
import Submission.Work.SpecLin.Alt.denomIdeal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.SpecLin.Alt

universe u v

/-- **The local core of the main theorem.**

Let `R` be a Noetherian local domain which is integrally closed in its fraction field `K`
(normality), let `x : K` and let `D = denomIdeal x` be its denominator ideal
(`Submission/Work/SpecLin/Alt/denomIdeal.lean`).  If the radical of `D` is the maximal ideal of
`R` -- equivalently, if `x ∉ R` but `x` is in the localisation `R_q` at every prime `q ≠ m` --
then the maximal ideal of `R` is principal, so `R` has dimension at most one (Krull's principal
ideal theorem).

The proof is elementary and uses no form of Serre's criterion: pick `n` minimal with
`m ^ n ≤ D`, an element `c ∈ m ^ (n-1)`, `c ∉ D`, and put `y = c * x`.  Then
`m ⊆ {a | y * a ∈ R}`, and if all these elements even lie in `m` the determinant trick
(`isIntegral_of_smul_mem_submodule`) makes `y` integral over `R`, a contradiction; otherwise
`y * a = b` with `b` a unit of `R`, which forces `m = Ideal.span {a}`. -/
theorem isPrincipal_maximalIdeal_of_denomIdeal_radical {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [IsIntegrallyClosedIn R K] {x : K}
    (hrad : (denomIdeal x).radical = IsLocalRing.maximalIdeal R) :
    Submodule.IsPrincipal (IsLocalRing.maximalIdeal R) := by
  classical
  obtain ⟨n, hn, hmin⟩ : ∃ n, IsLocalRing.maximalIdeal R ^ n ≤ denomIdeal x ∧
      ∀ k < n, ¬ (IsLocalRing.maximalIdeal R ^ k ≤ denomIdeal x) := by
    have hex : ∃ n, IsLocalRing.maximalIdeal R ^ n ≤ denomIdeal x :=
      Ideal.exists_pow_le_of_le_radical_of_fg
        (I := IsLocalRing.maximalIdeal R) (J := denomIdeal x)
        (by rw [hrad]) (IsNoetherian.noetherian _)
    exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have htop : (⊤ : Ideal R) ≤ denomIdeal x := by simpa [h] using hn
      have hDtop : (denomIdeal x : Ideal R) = ⊤ := top_le_iff.mp htop
      have hrad_top : (⊤ : Ideal R).radical = IsLocalRing.maximalIdeal R := by
        rw [← hDtop]; exact hrad
      rw [Ideal.radical_top] at hrad_top
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hrad_top.symm
    · exact h
  obtain ⟨c, hc_mem, hc_notmem⟩ :
      ∃ c ∈ IsLocalRing.maximalIdeal R ^ (n - 1), c ∉ denomIdeal x := by
    by_contra hcon
    push Not at hcon
    exact hmin (n - 1) (by omega) (fun z hz => hcon z hz)
  set y : K := algebraMap R K c * x with hy
  have hy_mem : ∀ a ∈ IsLocalRing.maximalIdeal R,
      ∃ b : R, y * algebraMap R K a = algebraMap R K b := by
    intro a ha
    have hac : a * c ∈ denomIdeal x := by
      have h1 : a * c ∈ IsLocalRing.maximalIdeal R ^ (n - 1) * IsLocalRing.maximalIdeal R := by
        rw [Ideal.mul_comm]
        exact Ideal.mul_mem_mul ha hc_mem
      rw [← pow_succ, Nat.sub_one_add_one hn0.ne'] at h1
      exact hn h1
    obtain ⟨b, hb⟩ := (mem_denomIdeal x (a * c)).1 hac
    refine ⟨b, ?_⟩
    rw [hy]
    calc (algebraMap R K c * x) * algebraMap R K a
        = x * (algebraMap R K a * algebraMap R K c) := by ring
      _ = x * algebraMap R K (a * c) := by rw [map_mul]
      _ = algebraMap R K b := hb
  by_cases hcase : ∀ a ∈ IsLocalRing.maximalIdeal R, ∃ b ∈ IsLocalRing.maximalIdeal R,
      y * algebraMap R K a = algebraMap R K b
  · exfalso
    have hD_ne_bot : (denomIdeal x : Ideal R) ≠ ⊥ := denomIdeal_ne_bot (A := R) (K := K) x
    have hm_ne_bot : IsLocalRing.maximalIdeal R ≠ ⊥ := by
      intro hbot
      refine hD_ne_bot (le_bot_iff.mp ?_)
      have h1 : (denomIdeal x : Ideal R) ≤ IsLocalRing.maximalIdeal R := by
        rw [← hrad]; exact Ideal.le_radical
      exact hbot ▸ h1
    obtain ⟨a₀, ha₀m, ha₀ne⟩ : ∃ a ∈ IsLocalRing.maximalIdeal R, a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hm_ne_bot (le_bot_iff.mp fun z hz => hcon z hz)
    let N : Submodule R K := Submodule.map (Algebra.linearMap R K) (IsLocalRing.maximalIdeal R)
    have hmemN : algebraMap R K a₀ ∈ N := by
      show algebraMap R K a₀ ∈
        Submodule.map (Algebra.linearMap R K) (IsLocalRing.maximalIdeal R)
      rw [Submodule.mem_map]
      exact ⟨a₀, ha₀m, by simp [Algebra.linearMap_apply]⟩
    have hN0 : N ≠ ⊥ := by
      intro hbot
      rw [hbot] at hmemN
      have haz : algebraMap R K a₀ = 0 := by simpa using hmemN
      exact ha₀ne (IsFractionRing.injective R K (by simpa using haz))
    have hNfg : N.FG := by
      show (Submodule.map (Algebra.linearMap R K) (IsLocalRing.maximalIdeal R)).FG
      exact Submodule.FG.map (Algebra.linearMap R K) (IsNoetherian.noetherian _)
    have hstab : ∀ z ∈ N, y • z ∈ N := by
      intro z hz
      show y • z ∈ Submodule.map (Algebra.linearMap R K) (IsLocalRing.maximalIdeal R)
      rw [Submodule.mem_map] at hz ⊢
      obtain ⟨a, ha, rfl⟩ := hz
      obtain ⟨b, hb, hb_eq⟩ := hcase a ha
      exact ⟨b, hb, by
        show algebraMap R K b = y • algebraMap R K a
        rw [← hb_eq, smul_eq_mul]⟩
    have hint : IsIntegral R y :=
      isIntegral_of_smul_mem_submodule N hN0 hNfg y hstab
    obtain ⟨r, hr⟩ := (IsIntegrallyClosedIn.isIntegral_iff).1 hint
    exact hc_notmem ((mem_denomIdeal x c).2 ⟨r, by rw [hr, hy]; ring⟩)
  · push Not at hcase
    obtain ⟨a, ha_m, ha_not⟩ := hcase
    obtain ⟨b, hb_eq⟩ := hy_mem a ha_m
    have hb_notm : b ∉ IsLocalRing.maximalIdeal R := fun hbm => ha_not b hbm hb_eq
    have hbunit : IsUnit b := (IsLocalRing.notMem_maximalIdeal).1 hb_notm
    obtain ⟨u, hu⟩ : ∃ u : Rˣ, (↑u : R) = b := ⟨hbunit.unit, hbunit.unit_spec⟩
    have hm_le_span : IsLocalRing.maximalIdeal R ≤ Ideal.span {a} := by
      intro d hd
      obtain ⟨e, he⟩ := hy_mem d hd
      have h1 : algebraMap R K b * algebraMap R K d = algebraMap R K e * algebraMap R K a := by
        rw [← hb_eq, ← he]; ring
      have h2 : b * d = e * a :=
        IsFractionRing.injective R K (by rw [map_mul, map_mul]; exact h1)
      rw [Ideal.mem_span_singleton]
      refine ⟨(↑(u⁻¹) : R) * e, ?_⟩
      have h3 : (↑u : R) * d = e * a := by rw [hu]; exact h2
      calc d = ((↑(u⁻¹) : R) * ↑u) * d := by rw [Units.inv_mul, one_mul]
        _ = (↑(u⁻¹) : R) * ((↑u : R) * d) := by rw [mul_assoc]
        _ = (↑(u⁻¹) : R) * (e * a) := by rw [h3]
        _ = a * ((↑(u⁻¹) : R) * e) := by ring
    have hspan_le_m : Ideal.span {a} ≤ IsLocalRing.maximalIdeal R := by
      rw [Ideal.span_le]
      simpa using ha_m
    exact ⟨a, le_antisymm hm_le_span hspan_le_m⟩

/-- Krull's principal ideal theorem applied to the localisation at a prime: if the maximal ideal
of a localisation `R` of `A` at the prime `P` is principal, then `P` has height at most one. -/
theorem localization_height_le_one_of_isPrincipal_maximalIdeal {A : Type*} [CommRing A] {R : Type*}
    [CommRing R] [Algebra A R] [IsNoetherianRing R] (P : Ideal A) [P.IsPrime]
    [IsLocalization.AtPrime R P] [IsLocalRing R]
    (h : Submodule.IsPrincipal (IsLocalRing.maximalIdeal R)) : P.height ≤ 1 := by
  have hm : (IsLocalRing.maximalIdeal R).height ≤ 1 := by
    obtain ⟨a, ha⟩ := h.principal
    have hprime : (Ideal.span {a}).IsPrime := by
      rw [show Ideal.span {a} = IsLocalRing.maximalIdeal R from ha.symm]
      exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime
    haveI := hprime
    have hmem : IsLocalRing.maximalIdeal R ∈ (Ideal.span {a}).minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton_iff.mpr ha
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) _ hmem
  have h1 : ringKrullDim R = (P.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height P R
  have h2 : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) = ringKrullDim R :=
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  have hcoele : (P.height : WithBot ℕ∞) ≤ (1 : ℕ∞) := by
    rw [← h1, ← h2]
    exact WithBot.coe_le_coe.mpr hm
  exact WithBot.coe_le_coe.mp hcoele

-- Serre/Krull input for `Work.SpecLin.Alt.conservationNumber_unit` (see
-- `Submission/Work/SpecLin/Alt/conservationNumber.lean` and `Alt/NOTES_chartCore.md`):
-- a Noetherian NORMAL domain is the intersection, inside its fraction field, of its
-- localisations at its height-one primes.  This is the "S2 / second Serre condition" half of
-- Serre's criterion: a rational function which is regular at every height-one prime is
-- regular.  Mathlib has the Krull half (`Ideal.height_span_singleton_le_one`,
-- `Ideal.exists_isPrime_height_eq`) but not this one.  Instantiated at the normal Noetherian
-- local ring `A = B_𝔫` it is exactly the hypothesis `hnormal` of `conservationNumber_unit`.
-- Suggested route: reduce to `x` integral over `A` by the "regular at height one" condition
-- plus `IsIntegrallyClosed`, using that `A = ⋂_{ht p = 1} A_p` for Noetherian normal `A`
-- (Serre); the Krull PIT identifies the height-one primes and their localisations as the
-- discrete valuation rings of `A`.
theorem normal_eq_iInter_localizations_height_one {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] {K : Type*} [Field K] [Algebra A K]
    [IsFractionRing A K] (x : K)
    (h : ∀ p : Ideal A, p.IsPrime → p.height = 1 →
      ∃ b s : A, s ∉ p ∧ x * algebraMap A K s = algebraMap A K b) :
    ∃ a : A, x = algebraMap A K a := by
  by_contra hx
  -- `x` is not in the image of `A`; its denominator ideal is a proper ideal.
  have hDtop : (denomIdeal x : Ideal A) ≠ ⊤ :=
    fun htop => hx ((denomIdeal_eq_top_iff x).1 htop)
  -- Choose a minimal prime `P` over `D = denomIdeal x`.
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hDtop
  have hP' : (denomIdeal x).IsMinimalPrime P := hP
  have hPprime : P.IsPrime := hP'.isPrime
  have hDP : (denomIdeal x : Ideal A) ≤ P := hP'.le
  -- The localisation `R = A_P`, realised inside `K`.
  let S : Submonoid A := P.primeCompl
  have hS : S ≤ nonZeroDivisors A := P.primeCompl_le_nonZeroDivisors
  let R : Subalgebra A K := Localization.subalgebra.ofField K S hS
  haveI hRloc : IsLocalization S R := Localization.subalgebra.isLocalization_ofField K S hS
  haveI : IsLocalization.AtPrime R P := hRloc
  haveI : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R P
  haveI : IsNoetherianRing R := IsLocalization.isNoetherianRing S R inferInstance
  haveI : IsIntegrallyClosed R := isIntegrallyClosed_of_isLocalization R S hS
  haveI : IsIntegrallyClosedIn R K := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).1 inferInstance
  -- `denomIdeal x` (in `A`) maps into the denominator ideal of `x` in `R`.
  have hmap_le : (denomIdeal x : Ideal A).map (algebraMap A R) ≤ (denomIdeal x : Ideal R) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change algebraMap A R a ∈ (denomIdeal x : Ideal R)
    rw [mem_denomIdeal] at ha ⊢
    obtain ⟨b, hb⟩ := ha
    exact ⟨algebraMap A R b, by
      rw [show algebraMap R K (algebraMap A R a) = algebraMap A K a from rfl,
        show algebraMap R K (algebraMap A R b) = algebraMap A K b from rfl]
      exact hb⟩
  -- `x` is not in `R`, i.e. the denominator ideal of `x` in `R` is proper.
  have hDne' : (denomIdeal x : Ideal R) ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ (denomIdeal x : Ideal R) := by rw [htop]; trivial
    rw [one_mem_denomIdeal_iff] at h1
    obtain ⟨r, hr⟩ := h1
    obtain ⟨a, s, hs, hrs⟩ :
        ∃ a s : A, ∃ (_ : s ∈ S), (↑r : K) = algebraMap A K a * (algebraMap A K s)⁻¹ :=
      (mem_subalgebra_ofField_iff (A := A) (K := K) S hS (↑r)).1 r.2
    have hxs : x = algebraMap A K a * (algebraMap A K s)⁻¹ := by
      rw [hr]
      exact hrs
    have hsP : s ∉ P := hs
    have hsD : s ∈ (denomIdeal x : Ideal A) := by
      rw [mem_denomIdeal]
      refine ⟨a, ?_⟩
      have hs0 : algebraMap A K s ≠ 0 := by
        intro h0
        refine hsP ?_
        have : s = 0 := (IsFractionRing.injective A K) (by rw [h0]; simp)
        rw [this]
        exact P.zero_mem
      rw [hxs, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    exact hsP (hDP hsD)
  -- The radical of the denominator ideal of `x` in `R` is the maximal ideal.
  have hrad' : (denomIdeal x : Ideal R).radical = IsLocalRing.maximalIdeal R := by
    have hradmap : ((denomIdeal x : Ideal A).map (algebraMap A R)).radical =
        P.map (algebraMap A R) :=
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (R := A) (A := ↥R)
        (q := P) (I := (denomIdeal x : Ideal A)) hP
    have hPmap : P.map (algebraMap A R) = IsLocalRing.maximalIdeal R :=
      IsLocalization.AtPrime.map_eq_maximalIdeal P R
    refine le_antisymm ?_ ?_
    · have h1 : (denomIdeal x : Ideal R).radical ≤ IsLocalRing.maximalIdeal R :=
        (Ideal.IsPrime.radical_le_iff (IsLocalRing.maximalIdeal.isMaximal R).isPrime).mpr
          (IsLocalRing.le_maximalIdeal hDne')
      simpa only [hPmap] using h1
    · rw [← hPmap, ← hradmap]
      exact Ideal.radical_mono hmap_le
  -- Hence the maximal ideal of `R` is principal and `P` has height at most one.
  have hprincipal : Submodule.IsPrincipal (IsLocalRing.maximalIdeal R) :=
    isPrincipal_maximalIdeal_of_denomIdeal_radical hrad'
  have hheight : P.height ≤ 1 :=
    localization_height_le_one_of_isPrincipal_maximalIdeal (A := A) (R := R) P hprincipal
  -- Since `denomIdeal x ≠ ⊥`, the height of `P` is not zero, so it is one.
  have hge : (1 : ℕ∞) ≤ P.height := by
    obtain ⟨a, s, hs, hxs⟩ := IsFractionRing.div_surjective A x
    have hsD : s ∈ (denomIdeal x : Ideal A) := by
      rw [mem_denomIdeal]
      refine ⟨a, ?_⟩
      rw [← hxs, div_mul_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)]
    have hle : Ideal.span {s} ≤ P := by
      rw [Ideal.span_le]
      simpa using hDP hsD
    exact le_trans (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hs)
      (Ideal.height_mono hle)
  have hPht : P.height = 1 := le_antisymm hheight hge
  -- Now the hypothesis at `P` gives an element of `denomIdeal x` outside `P`.
  obtain ⟨b, s, hs, hxs⟩ := h P hPprime hPht
  exact hs (hDP ((mem_denomIdeal x s).2 ⟨b, hxs⟩))

end Work.SpecLin.Alt
