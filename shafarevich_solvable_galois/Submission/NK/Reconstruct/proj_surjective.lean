import Mathlib
import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.GammaSup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Surjectivity of the projections `Γ_K → Γ_{L,ℓ}`

`NK.Reconstruct.Gamma K K' ℓ` is the projective limit of the finite ℓ-primary parts
`Γ_{L,ℓ} = LevelEllPart L.L ℓ` of the abelianisations `Gal(L/K)^{ab}` over the finite normal
number-field levels `L/K` of `K'` (`NK.Reconstruct.FrobLevel`), with the transition maps
`ellRestrict ℓ L M h : Γ_{M,ℓ} → Γ_{L,ℓ}`.

This file proves that the projection `Gamma.proj L : Γ_K → Γ_{L,ℓ}` onto a single level is
**surjective**.

The mathematical content is the classical statement that an inverse limit of *finite* sets with
surjective transition maps over a *directed* index set has surjective projections onto its factors
(Mittag-Leffler).  Concretely, given `x ∈ Γ_{L,ℓ}` one has to build a coherent family
`f ∈ Γ_K` with `f L = x`; by compactness of the product of the finite level groups it suffices to
satisfy any *finite* set of coherence constraints, and for finitely many levels one can use a common
upper bound `T = sup` of the finite levels in play (`FrobLevel.sup`), choosing any preimage
`y ∈ Γ_{T,ℓ}` of `x` under `ellRestrict ℓ L T` and then restricting `y` down to all levels below `T`.

Two facts about the transition maps are needed:

* `ellRestrict ℓ L M h` is surjective for `L.L ≤ M.L` (`projSurj_ellRestrict_surj`) — this follows
  from the surjectivity of the restriction of Galois groups, the fact that abelianisation is right
  exact, and the elementary fact that a surjection of finite abelian groups maps the ℓ-primary part
  onto the ℓ-primary part;
* the transition maps are functorial in the level: `ellRestrict ℓ L M h ∘ ellRestrict ℓ M N h' =
  ellRestrict ℓ L N (h.trans h')` (`projSurj_ellRestrict_comp`), which is the coherence of the
  restriction maps of the projective system.

The auxiliary "primary decomposition" of an element of a finite abelian group — every element is a
product of an element of order a power of `ℓ` and an element of order coprime to `ℓ` — is proved
here as `projSurj_exists_pow_ellPart_split`; it is what makes the ℓ-primary part a direct summand of
a finite abelian group and hence the ℓ-primary-part functor right exact.
-/

namespace NK.Reconstruct

set_option linter.style.haveILetI false

open scoped Pointwise

/-! ## Two arithmetic lemmas

For `0 < n` and any `m`, the part `n / gcd(n, m ^ n)` of `n` left after removing the primes shared
with `m` is coprime to `m`, and also to `gcd(n, m ^ n)`.  These are the two coprimality statements
behind the primary decomposition of an element of a finite abelian group of order `n` relative to
`ℓ = m`. -/

/-- **The `ℓ`-free part of `n` is coprime to `ℓ`.**  Concretely: if `0 < n` then
`n / gcd(n, ℓ^n)` is coprime to `ℓ`.

Indeed, if a prime `p` divided both `n / gcd(n, ℓ^n)` and `ℓ`, then `p ^ (n.factorization p)` would
divide both `n` and `ℓ ^ n` (the latter because `n.factorization p < n`) hence `gcd(n, ℓ ^ n)`, so
`p ^ (n.factorization p + 1) ∣ n`, contradicting the definition of `n.factorization p`. -/
theorem projSurj_coprime_div_gcd_pow {n m : ℕ} (hn : 0 < n) :
    Nat.Coprime (n / n.gcd (m ^ n)) m := by
  rcases lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [zero_pow hn.ne', Nat.gcd_zero_right, Nat.div_self hn]
      exact Nat.coprime_one_left 0
    · simp
  · rw [Nat.coprime_iff_gcd_eq_one]
    by_contra h1
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    have hpd1 : p ∣ n / n.gcd (m ^ n) := hpd.trans (Nat.gcd_dvd_left _ _)
    have hpd2 : p ∣ m := hpd.trans (Nat.gcd_dvd_right _ _)
    set v := n.factorization p with hv
    have hpv_n : p ^ v ∣ n := (hp.pow_dvd_iff_le_factorization hn.ne').mpr le_rfl
    have hmne : m ≠ 0 := by omega
    have hpv_pow : p ^ v ∣ m ^ n := by
      rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero n hmne), Nat.factorization_pow]
      simp only [Finsupp.smul_apply, smul_eq_mul]
      have hv_lt : v < n := Nat.factorization_lt p hn.ne'
      have h1 : 1 ≤ m.factorization p := (hp.dvd_iff_one_le_factorization hmne).mp hpd2
      calc v ≤ n := le_of_lt hv_lt
        _ ≤ n * m.factorization p := by simpa using Nat.mul_le_mul_left n h1
    have hpv_g : p ^ v ∣ n.gcd (m ^ n) := Nat.dvd_gcd hpv_n hpv_pow
    have key : n.gcd (m ^ n) * (n / n.gcd (m ^ n)) = n :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left n (m ^ n))
    have hle : v + 1 ≤ v := by
      apply (hp.pow_dvd_iff_le_factorization hn.ne').mp
      rw [pow_succ, ← key]
      exact mul_dvd_mul hpv_g hpd1
    omega

/-- **The two parts of the decomposition are coprime.**  If `0 < n`, then `n / gcd(n, ℓ^n)` is
coprime to `gcd(n, ℓ^n)`: a common prime `p` would divide `ℓ`, `n` and `n / gcd(n, ℓ^n)`, and then
`p ^ (n.factorization p + 1)` would divide `n`. -/
theorem projSurj_coprime_div_gcd_gcd {n m : ℕ} (hn : 0 < n) :
    Nat.Coprime (n / n.gcd (m ^ n)) (n.gcd (m ^ n)) := by
  rcases lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [zero_pow hn.ne', Nat.gcd_zero_right, Nat.div_self hn]
      exact Nat.coprime_one_left n
    · simp
  · rw [Nat.coprime_iff_gcd_eq_one]
    by_contra h1
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    have hpd1 : p ∣ n / n.gcd (m ^ n) := hpd.trans (Nat.gcd_dvd_left _ _)
    have hpd2 : p ∣ n.gcd (m ^ n) := hpd.trans (Nat.gcd_dvd_right _ _)
    have hpm : p ∣ m := hp.dvd_of_dvd_pow (hpd2.trans (Nat.gcd_dvd_right n (m^n)))
    have hmne : m ≠ 0 := by omega
    set v := n.factorization p with hv
    have hpv_n : p ^ v ∣ n := (hp.pow_dvd_iff_le_factorization hn.ne').mpr le_rfl
    have hpv_pow : p ^ v ∣ m ^ n := by
      rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero n hmne), Nat.factorization_pow]
      simp only [Finsupp.smul_apply, smul_eq_mul]
      have hv_lt : v < n := Nat.factorization_lt p hn.ne'
      have h1 : 1 ≤ m.factorization p := (hp.dvd_iff_one_le_factorization hmne).mp hpm
      calc v ≤ n := le_of_lt hv_lt
        _ ≤ n * m.factorization p := by simpa using Nat.mul_le_mul_left n h1
    have hpv_d : p ^ v ∣ n.gcd (m ^ n) := Nat.dvd_gcd hpv_n hpv_pow
    have key : n.gcd (m ^ n) * (n / n.gcd (m ^ n)) = n :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left n (m ^ n))
    have hle : v + 1 ≤ v := by
      apply (hp.pow_dvd_iff_le_factorization hn.ne').mp
      rw [pow_succ, ← key]
      exact mul_dvd_mul hpv_d hpd1
    omega

/-! ## The primary decomposition of an element of a finite abelian group -/

/-- **The ℓ-primary/ℓ-coprime splitting of an element of a finite abelian group.**

For a finite abelian group `A` and any `ℓ` there are `c m : ℕ` with `m` coprime to `ℓ` and, for
*every* `x : A`,

* `x ^ c ∈ ellPart A ℓ`, i.e. `x ^ c` has order a power of `ℓ`, and
* `(x * (x ^ c)⁻¹) ^ m = 1`, i.e. the complementary factor has order coprime to `ℓ`.

Equivalently, every `x` is the product of an element of the ℓ-primary part and an element whose
order is coprime to `ℓ`, so that `ellPart A ℓ` is a direct summand of `A`.

The proof removes from `e = Nat.card A` the part `d = gcd(e, ℓ^e)` supported on the primes of `ℓ`
and puts `m = e / d` (coprime to `ℓ`); `x ^ m ∈ ellPart A ℓ` because `(x ^ m) ^ (ℓ ^ e) =
x ^ (e * (ℓ ^ e / d)) = 1`.  The further power `c = m ^ φ(d)` is chosen so that
`m ^ φ(d) ≡ 1 (mod d)` (Euler), which makes the order of `x ^ m` (dividing `d`) divide
`m ^ φ(d) - 1`, whence `x * (x ^ c)⁻¹` is fixed by the `m`-th power map, i.e. `(x (x ^ c)⁻¹) ^ m = 1`. -/
theorem projSurj_exists_pow_ellPart_split (A : Type*) [CommGroup A] [Finite A] (ℓ : ℕ) :
    ∃ c m : ℕ, Nat.Coprime m ℓ ∧
      ∀ x : A, x ^ c ∈ ellPart A ℓ ∧ (x * (x ^ c)⁻¹) ^ m = 1 := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  haveI : Nonempty A := ⟨1⟩
  set e := Nat.card A with he
  have hepos : 0 < e := Nat.card_pos
  have hxpow : ∀ x : A, x ^ e = 1 := fun x => by
    rw [he, Nat.card_eq_fintype_card]; exact pow_card_eq_one
  set d := e.gcd (ℓ ^ e) with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hepos
  have hde : d ∣ e := Nat.gcd_dvd_left e (ℓ ^ e)
  have hdℓ : d ∣ ℓ ^ e := Nat.gcd_dvd_right e (ℓ ^ e)
  set m := e / d with hm
  have hedm : d * m = e := Nat.mul_div_cancel' hde
  have hmℓ : Nat.Coprime m ℓ := projSurj_coprime_div_gcd_pow hepos
  have hmd : Nat.Coprime m d := projSurj_coprime_div_gcd_gcd hepos
  have hφpos : 0 < Nat.totient d := Nat.totient_pos.mpr hdpos
  refine ⟨m ^ Nat.totient d, m, hmℓ, fun x => ?_⟩
  have hxe : x ^ e = 1 := hxpow x
  constructor
  · have hdvd : e ∣ (m ^ Nat.totient d) * ℓ ^ e := by
      have hpow : m ^ Nat.totient d = m * m ^ (Nat.totient d - 1) := by
        conv_lhs =>
          rw [← Nat.succ_pred_eq_of_pos hφpos]
          rw [pow_succ']
        rw [Nat.pred_eq_sub_one]
      have hcomm : m * d = e := by rw [mul_comm, hedm]
      refine ⟨m ^ (Nat.totient d - 1) * (ℓ ^ e / d), ?_⟩
      calc (m ^ Nat.totient d) * ℓ ^ e
          = (m * m ^ (Nat.totient d - 1)) * ℓ ^ e := by rw [hpow]
        _ = (m * m ^ (Nat.totient d - 1)) * (d * (ℓ ^ e / d)) := by
              rw [Nat.mul_div_cancel' hdℓ]
        _ = (m * d) * (m ^ (Nat.totient d - 1) * (ℓ ^ e / d)) := by ring
        _ = e * (m ^ (Nat.totient d - 1) * (ℓ ^ e / d)) := by rw [hcomm]
    refine ⟨e, ?_⟩
    rw [← pow_mul]
    obtain ⟨t, ht⟩ := hdvd
    rw [ht, pow_mul, hxe, one_pow]
  · have hE : (x ^ m) ^ d = 1 := by
      rw [← pow_mul, mul_comm m d, hedm, hxe]
    have hmod : m ^ Nat.totient d ≡ 1 [MOD orderOf (x ^ m)] :=
      (Nat.ModEq.pow_totient hmd).of_dvd (orderOf_dvd_iff_pow_eq_one.mpr hE)
    have hEpow : (x ^ m) ^ (m ^ Nat.totient d) = (x ^ m) ^ 1 := by
      rw [pow_eq_pow_iff_modEq]
      exact hmod
    have h1 : (x ^ (m ^ Nat.totient d)) ^ m = (x ^ m) ^ (m ^ Nat.totient d) := by
      rw [← pow_mul, ← pow_mul', mul_comm]
    rw [mul_pow, inv_pow, h1, hEpow, pow_one, mul_inv_cancel]

/-- **An element of the ℓ-primary part of order coprime to `ℓ` is trivial.**  This is the
complementary statement that makes the ℓ-primary part a direct summand. -/
theorem projSurj_eq_one_of_mem_ellPart_of_coprime {A : Type*} [CommGroup A] {ℓ m : ℕ} {z : A}
    (hz : z ∈ ellPart A ℓ) (hm : Nat.Coprime m ℓ) (hz1 : z ^ m = 1) : z = 1 := by
  obtain ⟨N, hN⟩ := hz
  have h1 : orderOf z ∣ ℓ ^ N := orderOf_dvd_iff_pow_eq_one.mpr hN
  have h2 : orderOf z ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hz1
  have h3 : orderOf z ∣ 1 := by
    rw [← (hm.pow_right N).gcd_eq_one]
    exact Nat.dvd_gcd h2 h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

/-- **A surjection of finite abelian groups maps the ℓ-primary part onto the ℓ-primary part.**

Given `f : A →* B` surjective with `A` finite, every `y ∈ ellPart B ℓ` has a preimage in
`ellPart A ℓ`: write `y = f x` and use the ℓ-primary splitting `x = x' · x''` of `x`
(`projSurj_exists_pow_ellPart_split`); then `f x'' = y · (f x')⁻¹` lies in `ellPart B ℓ` and has
order coprime to `ℓ`, hence is `1`, so `y = f x'`. -/
theorem projSurj_ellPart_map_surj {A B : Type*} [CommGroup A] [CommGroup B] [Finite A]
    (ℓ : ℕ) (f : A →* B) (hf : Function.Surjective f) :
    ∀ y ∈ ellPart B ℓ, ∃ a ∈ ellPart A ℓ, f a = y := by
  intro y hy
  obtain ⟨c, m, hcop, hsplit⟩ := projSurj_exists_pow_ellPart_split A ℓ
  obtain ⟨a, ha⟩ := hf y
  have hmem1 : f (a ^ c) ∈ ellPart B ℓ :=
    ellPart_map_le ℓ f (Subgroup.mem_map_of_mem f (hsplit a).1)
  have h1 : f (a * (a ^ c)⁻¹) = y * (f (a ^ c))⁻¹ := by rw [map_mul, map_inv, ha]
  have hmem : f (a * (a ^ c)⁻¹) ∈ ellPart B ℓ := by
    rw [h1]
    exact Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hmem1)
  have hpow : (f (a * (a ^ c)⁻¹)) ^ m = 1 := by rw [← map_pow, (hsplit a).2, map_one]
  have hone := projSurj_eq_one_of_mem_ellPart_of_coprime hmem hcop hpow
  rw [h1] at hone
  exact ⟨a ^ c, (hsplit a).1, (mul_inv_eq_one.mp hone).symm⟩

/-! ## The transition maps of the projective system

The restriction maps of the ℓ-primary parts, `ellRestrict ℓ L M h`, are surjective and
functorial.  Functoriality is proved on the level of Galois groups, where the restriction maps
`levelRestrictHom` become the naive restrictions (`projSurj_levelRestrictHom_apply`), which
compose (`projSurj_levelRestrictHom_comp`, an instance of the composition of restrictions through a
tower of normal subfields). -/

/-- Abelianisation is right exact: the abelianisation of a surjective homomorphism is surjective. -/
theorem projSurj_abelianization_map_surj {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : Function.Surjective (Abelianization.map f) := by
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨Abelianization.of a, rfl⟩

/-- **The restriction map on Galois groups is the naive restriction.**  For `L ⊆ M` and
`σ : Gal(M/K)`, the underlying element of `σ|_L ∈ Gal(L/K)` is the image under `σ` of `x` viewed in
`M`. -/
theorem projSurj_levelRestrictHom_apply {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {L M : FrobLevel K K'} (h : L.L ≤ M.L)
    (σ : Gal(↥M.L/K)) (x : ↥L.L) :
    (levelRestrictHom L M h σ x : ↥L.L).1 = (σ ⟨x.1, h x.2⟩ : ↥M.L).1 := by
  haveI : Normal K ↥(levelTo L M h) := normal_levelTo L M h
  have hkey : levelRestrictHom L M h σ x
      = (levelToEquiv L M h) (σ.restrictNormal (levelTo L M h) ⟨⟨x.1, h x.2⟩, x.2⟩) := rfl
  have hval : ((levelToEquiv L M h)
      (σ.restrictNormal (levelTo L M h) ⟨⟨x.1, h x.2⟩, x.2⟩) : ↥L.L).1
      = ((σ.restrictNormal (levelTo L M h) ⟨⟨x.1, h x.2⟩, x.2⟩ : ↥(levelTo L M h)) : ↥M.L).1 :=
    rfl
  have h3 : ((σ.restrictNormal (levelTo L M h) ⟨⟨x.1, h x.2⟩, x.2⟩ : ↥(levelTo L M h)) : ↥M.L)
      = σ ⟨x.1, h x.2⟩ :=
    AlgEquiv.restrictNormal_commutes σ (levelTo L M h) ⟨⟨x.1, h x.2⟩, x.2⟩
  rw [hkey, hval, h3]

/-- **Coherence of the restriction maps of Galois groups**: restricting first from `N` to `M` and
then from `M` to `L` is restricting from `N` to `L`. -/
theorem projSurj_levelRestrictHom_comp {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {L M N : FrobLevel K K'} (h : L.L ≤ M.L)
    (h' : M.L ≤ N.L) :
    (levelRestrictHom L M h).comp (levelRestrictHom M N h') = levelRestrictHom L N (h.trans h') := by
  ext σ x
  show ((levelRestrictHom L M h) ((levelRestrictHom M N h') σ) x : ↥L.L).1
      = ((levelRestrictHom L N (h.trans h')) σ x : ↥L.L).1
  rw [projSurj_levelRestrictHom_apply, projSurj_levelRestrictHom_apply,
    projSurj_levelRestrictHom_apply]

/-- **Surjectivity of the restriction map of Galois groups.**  For `L ⊆ M` normal over `K`, every
automorphism of `L` extends to `M`. -/
theorem projSurj_levelRestrictHom_surj {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {L M : FrobLevel K K'} (h : L.L ≤ M.L) :
    Function.Surjective (levelRestrictHom L M h) := by
  haveI : Normal K ↥(levelTo L M h) := normal_levelTo L M h
  intro σ
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := levelTo L M h)
    (E := ↥M.L) (algEquivConjHom (F := K) (levelToEquiv L M h).symm σ)
  refine ⟨τ, ?_⟩
  show algEquivConjHom (levelToEquiv L M h)
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M.L) (levelTo L M h) τ) = σ
  rw [hτ]
  ext x
  simp [algEquivConjHom, AlgEquiv.trans_apply]

/-- **Surjectivity of the restriction map on abelianisations.** -/
theorem projSurj_levelRestrict_surj {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {L M : FrobLevel K K'} (h : L.L ≤ M.L) :
    Function.Surjective (levelRestrict L M h) :=
  projSurj_abelianization_map_surj (levelRestrictHom L M h) (projSurj_levelRestrictHom_surj h)

/-- **Coherence of the restriction maps on abelianisations.** -/
theorem projSurj_levelRestrict_comp {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] {L M N : FrobLevel K K'} (h : L.L ≤ M.L) (h' : M.L ≤ N.L) :
    (levelRestrict L M h).comp (levelRestrict M N h') = levelRestrict L N (h.trans h') := by
  rw [levelRestrict, levelRestrict, levelRestrict, Abelianization.map_comp,
    projSurj_levelRestrictHom_comp]

/-- **Surjectivity of the transition maps of the projective system of ℓ-primary parts**: for
`L.L ≤ M.L` the map `ellRestrict ℓ L M h : Γ_{M,ℓ} → Γ_{L,ℓ}` is surjective.  This is
`projSurj_ellPart_map_surj` applied to the surjective restriction of abelianisations. -/
theorem projSurj_ellRestrict_surj {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] {L M : FrobLevel K K'} (ℓ : ℕ) (h : L.L ≤ M.L) :
    Function.Surjective (ellRestrict ℓ L M h) := by
  classical
  intro y
  obtain ⟨a, ha, hfa⟩ := projSurj_ellPart_map_surj (A := LevelAbelianization M.L)
    (B := LevelAbelianization L.L) ℓ (levelRestrict L M h) (projSurj_levelRestrict_surj h) y y.2
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  exact hfa

/-- **Coherence of the transition maps of the projective system of ℓ-primary parts**:
`ellRestrict ℓ L M h ∘ ellRestrict ℓ M N h' = ellRestrict ℓ L N (h.trans h')`. -/
theorem projSurj_ellRestrict_comp {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] {L M N : FrobLevel K K'} (ℓ : ℕ) (h : L.L ≤ M.L)
    (h' : M.L ≤ N.L) :
    (ellRestrict ℓ L M h).comp (ellRestrict ℓ M N h') = ellRestrict ℓ L N (h.trans h') := by
  ext x
  simp only [MonoidHom.comp_apply, ellRestrict_coe]
  rw [← MonoidHom.comp_apply, projSurj_levelRestrict_comp]

/-! ## A common upper bound for finitely many levels -/

/-- **Finitely many levels of the projective system have a common upper bound.**  The index system
`FrobLevel K K'` is directed by the compositum (`FrobLevel.sup`), so every finite set of levels is
bounded above by a level, and one may take that level above `L` as well. -/
theorem projSurj_finset_exists_upper_bound {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] (L : FrobLevel K K')
    (s : Finset (FrobLevel K K')) :
    ∃ T : FrobLevel K K', (∀ M ∈ s, M.L ≤ T.L) ∧ L.L ≤ T.L := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨L, by simp⟩
  | insert a s ha ih =>
      obtain ⟨T, hT, hLT⟩ := ih
      refine ⟨a.sup T, ?_, ?_⟩
      · intro N hN
        rcases Finset.mem_insert.mp hN with hNa | hN
        · rw [hNa]
          exact FrobLevel.le_sup_left a T
        · exact le_trans (hT N hN) (FrobLevel.le_sup_right a T)
      · exact le_trans hLT (FrobLevel.le_sup_right a T)

/-! ## Surjectivity of the projections of `Γ_K` -/

/-- **The projection `Γ_K → Γ_{L,ℓ}` is surjective.**

Given `x ∈ Γ_{L,ℓ}` we build a coherent family `f` of ℓ-primary elements with `f L = x`.  The space
`∏_M Γ_{M,ℓ}` is compact (a product of finite discrete groups) and the coherence conditions are
closed, so by finite intersection it suffices to satisfy finitely many of them.  For finitely many
constraints one takes a common upper bound `T` of the levels involved
(`projSurj_finset_exists_upper_bound`), a preimage `y` of `x` under `ellRestrict ℓ L T`
(`projSurj_ellRestrict_surj`), and defines `f M := ellRestrict ℓ M T (fM) y` for `M` below `T`; the
constraints hold by coherence of the transition maps (`projSurj_ellRestrict_comp`). -/
theorem proj_surjective {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) (L : FrobLevel K K') :
    Function.Surjective (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L) := by
  classical
  intro x
  let X := ∀ M : FrobLevel K K', LevelEllPart M.L ℓ
  let t : FrobLevel K K' × FrobLevel K K' → Set X := fun p =>
    if h : p.1.L ≤ p.2.L then {f : X | ellRestrict ℓ p.1 p.2 h (f p.2) = f p.1} else Set.univ
  have htclosed : ∀ p : FrobLevel K K' × FrobLevel K K', IsClosed (t p) := by
    rintro ⟨M, N⟩
    by_cases h : M.L ≤ N.L
    · have ht : t (M, N) = {f : X | ellRestrict ℓ M N h (f N) = f M} := dif_pos h
      rw [ht]
      exact isClosed_eq ((continuous_of_discreteTopology).comp (continuous_apply N))
        (continuous_apply M)
    · have ht : t (M, N) = Set.univ := dif_neg h
      rw [ht]
      exact isClosed_univ
  have hFIP : ∀ u : Finset (FrobLevel K K' × FrobLevel K K'), ∃ f : X,
      f L = x ∧ ∀ p ∈ u, f ∈ t p := by
    intro u
    obtain ⟨T, hT, hLT⟩ :=
      projSurj_finset_exists_upper_bound L ((u.image Prod.fst) ∪ (u.image Prod.snd))
    obtain ⟨y, hy⟩ := projSurj_ellRestrict_surj (K := K) (K' := K') ℓ hLT x
    let f : X := fun Q => if h : Q.L ≤ T.L then ellRestrict ℓ Q T h y else 1
    have hfL : f L = x := by
      show (if h : L.L ≤ T.L then ellRestrict ℓ L T h y else 1) = x
      rw [dif_pos hLT]
      exact hy
    refine ⟨f, hfL, ?_⟩
    intro p hp
    obtain ⟨M, N⟩ := p
    have hM : M.L ≤ T.L := hT M (by
      simp only [Finset.mem_union, Finset.mem_image]
      exact Or.inl ⟨(M, N), hp, rfl⟩)
    have hN : N.L ≤ T.L := hT N (by
      simp only [Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨(M, N), hp, rfl⟩)
    by_cases hMN : M.L ≤ N.L
    · have ht : t (M, N) = {g : X | ellRestrict ℓ M N hMN (g N) = g M} := dif_pos hMN
      rw [ht]
      show ellRestrict ℓ M N hMN (f N) = f M
      have hfM : f M = ellRestrict ℓ M T (hMN.trans hN) y := by
        show (if h : M.L ≤ T.L then ellRestrict ℓ M T h y else 1) = _
        rw [dif_pos (hMN.trans hN)]
      have hfN : f N = ellRestrict ℓ N T hN y := by
        show (if h : N.L ≤ T.L then ellRestrict ℓ N T h y else 1) = _
        rw [dif_pos hN]
      rw [hfM, hfN, ← MonoidHom.comp_apply, projSurj_ellRestrict_comp]
    · have ht : t (M, N) = Set.univ := dif_neg hMN
      rw [ht]
      exact Set.mem_univ _
  have hsclosed : IsClosed {f : X | f L = x} :=
    isClosed_eq (continuous_apply L) continuous_const
  have hnonempty : ({f : X | f L = x} ∩ ⋂ p, t p).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨u, hu⟩ := hsclosed.isCompact.elim_finite_subfamily_closed t htclosed
      (Set.disjoint_iff_inter_eq_empty.mpr hne)
    obtain ⟨f, hfL, hf⟩ := hFIP u
    have hmem : f ∈ ({f : X | f L = x} ∩ ⋂ p ∈ u, t p) := by
      refine ⟨hfL, ?_⟩
      simp only [Set.mem_iInter]
      exact hf
    exact Set.disjoint_left.mp hu hmem.1 hmem.2
  obtain ⟨f, hfL, hfall⟩ := hnonempty
  have hcompat : Compatible ℓ f := by
    intro M N h
    have hmem := Set.mem_iInter.mp hfall (M, N)
    rw [show t (M, N) = {g : X | ellRestrict ℓ M N h (g N) = g M} from dif_pos h] at hmem
    exact hmem
  exact ⟨⟨f, hcompat⟩, hfL⟩

end NK.Reconstruct
