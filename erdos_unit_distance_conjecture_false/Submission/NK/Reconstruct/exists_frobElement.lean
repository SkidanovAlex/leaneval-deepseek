import Mathlib
import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.GammaSup
import Submission.NK.Reconstruct.Gamma
import Submission.NK.Reconstruct.exists_pow_projection_ellPart
import Submission.NK.Chebotarev.All
import Submission.NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase

/-!
# Frobenius elements of the ℓ-adic abelianisation of an absolute Galois group

For a number field `K` and a Galois extension `K'` of `K`, the ℓ-adic abelianisation
`Γ_K = Γ_{K,ℓ}` (`NK.Reconstruct.Gamma`) is the projective limit of the ℓ-parts
`Γ_{L,ℓ} = ℓ-part(Gal(L/K)^{ab})` over the finite normal levels `L/K` inside `K'`.

This file proves that the Frobenius elements at a fixed prime `𝔭` of `K` glue to a single element
`F ∈ Γ_K`: **the Frobenius element of `Γ_K` at `𝔭`**.  Since the primes of the various levels above
`𝔭` are not canonically coherent, the glueing can only be performed on the ℓ-primary part; the
hypothesis `hw` is exactly the statement that, at every level and every prime above `𝔭`, all the
Frobenius elements have the *same ℓ-primary component* in `Gal(L/K)^{ab}` (this is the statement
that the ℓ-part of the Frobenius is well defined even at ramified primes).

The mathematical content:

* `EllCoprimeRel ℓ x y` — the relation "`x` and `y` have the same ℓ-primary component", expressed
  without choosing the component: `(x * y⁻¹) ^ m = 1` for some `m` coprime to `ℓ`.  It is an
  equivalence relation (`ellCoprimeRel_refl/symm/trans`), preserved by homomorphisms
  (`ellCoprimeRel_map`), and on the ℓ-primary part it is equality
  (`eq_of_mem_ellPart_of_ellCoprimeRel`).
* `ellComp ℓ x` — a canonical choice of an element of the ℓ-primary part congruent to `x`
  (`NK.Reconstruct.exists_pow_projection_ellPart` provides the exponent); by the previous point it
  is determined by `x` (`ellComp_eq_of_ellCoprimeRel`).
* `exists_smul_eq_of_liesOver` — the Galois group acts transitively on the primes of a finite
  Galois level above a fixed prime of the base (from `Ideal.isPretransitive_of_isGaloisGroup`).
  Consequently two Frobenius elements at primes above `𝔭` are conjugate, hence have equal images in
  the abelianisation (`frobenius_ellCoprimeRel`).
* `exists_level_frobElem` — at every finite level there is an ℓ-primary element congruent to the
  image of *every* Frobenius element at *every* prime above `𝔭`.
* `exists_frobElement` — those elements are compatible with the restriction maps `ellRestrict`, so
  they glue into an element `F ∈ Γ_K`.

-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

open scoped Pointwise

/-! ## The relation "same ℓ-primary component" -/

section GroupRel

variable {A : Type*} [CommGroup A]

/-- **`x` and `y` have the same ℓ-primary component.**  This is expressed without choosing the
component: the "ℓ-prime part" of `x * y⁻¹` is trivial, i.e. `(x * y⁻¹) ^ m = 1` for some `m`
coprime to `ℓ`. -/
def EllCoprimeRel (ℓ : ℕ) (x y : A) : Prop :=
  ∃ m : ℕ, Nat.Coprime m ℓ ∧ (x * y⁻¹) ^ m = 1

@[refl] theorem ellCoprimeRel_refl (ℓ : ℕ) (x : A) : EllCoprimeRel ℓ x x :=
  ⟨1, Nat.coprime_one_left ℓ, by simp⟩

theorem ellCoprimeRel_symm {ℓ : ℕ} {x y : A} (h : EllCoprimeRel ℓ x y) :
    EllCoprimeRel ℓ y x := by
  obtain ⟨m, hm, hpow⟩ := h
  refine ⟨m, hm, ?_⟩
  have h1 : y * x⁻¹ = (x * y⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
  rw [h1, inv_pow, hpow, inv_one]

theorem ellCoprimeRel_trans {ℓ : ℕ} {x y z : A} (h1 : EllCoprimeRel ℓ x y)
    (h2 : EllCoprimeRel ℓ y z) : EllCoprimeRel ℓ x z := by
  obtain ⟨m, hm, hp1⟩ := h1
  obtain ⟨n, hn, hp2⟩ := h2
  refine ⟨m * n, Nat.Coprime.mul_left hm hn, ?_⟩
  have hxy : (x * y⁻¹) ^ (m * n) = 1 := by rw [pow_mul, hp1, one_pow]
  have hyz : (y * z⁻¹) ^ (m * n) = 1 := by rw [mul_comm m n, pow_mul, hp2, one_pow]
  have hdecomp : x * z⁻¹ = (x * y⁻¹) * (y * z⁻¹) := by group
  rw [hdecomp, mul_pow, hxy, hyz, one_mul]

theorem ellCoprimeRel_map {B : Type*} [CommGroup B] (f : A →* B) {ℓ : ℕ} {x y : A}
    (h : EllCoprimeRel ℓ x y) : EllCoprimeRel ℓ (f x) (f y) := by
  obtain ⟨m, hm, hpow⟩ := h
  refine ⟨m, hm, ?_⟩
  rw [← map_inv, ← map_mul, ← map_pow, hpow, map_one]

end GroupRel

/-! ## The ℓ-primary component -/

section EqMem

variable {A : Type*} [CommGroup A]

/-- **Two elements of the ℓ-primary part with the same ℓ-primary component are equal.**  Both have
ℓ-power order, while their quotient is killed by an integer coprime to `ℓ`; the order of the
quotient divides the gcd of the two, which is `1`. -/
theorem eq_of_mem_ellPart_of_ellCoprimeRel {ℓ : ℕ} {x y : A}
    (hx : x ∈ ellPart A ℓ) (hy : y ∈ ellPart A ℓ) (h : EllCoprimeRel ℓ x y) : x = y := by
  obtain ⟨m, hm, hpow⟩ := h
  obtain ⟨n, hn⟩ := (mem_ellPart_iff ℓ x).mp hx
  obtain ⟨n', hn'⟩ := (mem_ellPart_iff ℓ y).mp hy
  have hxk : x ^ (ℓ ^ (n + n')) = 1 := by
    rw [pow_add, pow_mul, hn, one_pow]
  have hyk : y ^ (ℓ ^ (n + n')) = 1 := by
    rw [pow_add, mul_comm (ℓ ^ n) (ℓ ^ n'), pow_mul, hn', one_pow]
  have hpow2 : (x * y⁻¹) ^ (ℓ ^ (n + n')) = 1 := by
    rw [mul_pow, inv_pow, hxk, hyk, inv_one, one_mul]
  have hdvd : orderOf (x * y⁻¹) ∣ Nat.gcd m (ℓ ^ (n + n')) :=
    Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hpow) (orderOf_dvd_iff_pow_eq_one.mpr hpow2)
  have hgcd : Nat.gcd m (ℓ ^ (n + n')) = 1 := (hm.pow_right (n + n')).gcd_eq_one
  have hone : orderOf (x * y⁻¹) = 1 := Nat.dvd_one.mp (hgcd ▸ hdvd)
  have h2 : x * y⁻¹ = 1 := orderOf_eq_one_iff.mp hone
  exact mul_inv_eq_one.mp h2

end EqMem

section EllComp

variable {A : Type*} [CommGroup A] [Finite A]

/-- **A canonical element of the ℓ-primary part congruent to `x`**, built from the uniform exponent
of `NK.Reconstruct.exists_pow_projection_ellPart`. -/
noncomputable def ellComp (ℓ : ℕ) (x : A) : ellPart A ℓ :=
  ⟨x ^ Classical.choose (exists_pow_projection_ellPart (A := A) ℓ),
    ((Classical.choose_spec (exists_pow_projection_ellPart (A := A) ℓ)) x).1⟩

/-- `ellComp ℓ x` has the same ℓ-primary component as `x`. -/
theorem ellCoprimeRel_ellComp (ℓ : ℕ) (x : A) : EllCoprimeRel ℓ x (ellComp ℓ x) := by
  obtain ⟨m, hm, hpow⟩ :=
    ((Classical.choose_spec (exists_pow_projection_ellPart (A := A) ℓ)) x).2
  exact ⟨m, hm, hpow⟩

/-- **The ℓ-primary component of `x` is determined by `x`**: this is
`ellComp_eq_of_ellCoprimeRel`'s content, via the following uniqueness statement. -/
theorem ellComp_eq_of_ellCoprimeRel {ℓ : ℕ} {x y : A} (h : EllCoprimeRel ℓ x y) :
    ellComp ℓ x = ellComp ℓ y := by
  refine Subtype.ext (eq_of_mem_ellPart_of_ellCoprimeRel (ellComp ℓ x).2 (ellComp ℓ y).2 ?_)
  exact ellCoprimeRel_trans
    (ellCoprimeRel_trans (ellCoprimeRel_symm (ellCoprimeRel_ellComp ℓ x)) h)
    (ellCoprimeRel_ellComp ℓ y)

end EllComp



/-! ## The Galois group acts transitively on the primes above a fixed prime -/

section Transitive

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Transitivity of the Galois action on the primes of a finite Galois level above a fixed prime
of the base.**  This is the number-field case of `Ideal.exists_smul_eq_of_isGaloisGroup`. -/
theorem exists_smul_eq_of_liesOver {𝔭 : NK.Chebotarev.PrimeIdeal K}
    {P Q : NK.Chebotarev.PrimeIdeal L} (hP : P.asIdeal.LiesOver 𝔭.asIdeal)
    (hQ : Q.asIdeal.LiesOver 𝔭.asIdeal) : ∃ σ : Gal(L/K), σ • P = Q := by
  classical
  letI : MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  haveI : IsGaloisGroup Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) K L
  haveI : MulAction.IsPretransitive Gal(L/K)
      ↥(𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)) :=
    Ideal.isPretransitive_of_isGaloisGroup 𝔭.asIdeal Gal(L/K)
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq Gal(L/K)
    (show ↥(𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L))
      from ⟨P.asIdeal, P.isPrime, hP⟩)
    (show ↥(𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L))
      from ⟨Q.asIdeal, Q.isPrime, hQ⟩)
  refine ⟨σ, ?_⟩
  have h2 : Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ) P.asIdeal = Q.asIdeal := by
    have h3 := congrArg Subtype.val hσ
    rwa [Ideal.coe_smul_primesOver_mk_eq_map_galRestrict K L σ P.asIdeal] at h3
  exact IsDedekindDomain.HeightOneSpectrum.ext
    (by rw [NK.Chebotarev.smul_primeIdeal_asIdeal]; exact h2)

end Transitive

/-! ## Frobenius elements at the primes above `𝔭` -/

section Main

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-- **The image in the abelianisation of a Frobenius element at a prime above `𝔭` is the same for
all primes above `𝔭`** (up to the ℓ-primary component fixed by `hw`).  Two primes above `𝔭` are
conjugate, so their Frobenius elements are conjugate, and conjugation is trivial in the
abelianisation; the hypothesis `hw` then takes care of the ambiguity of a Frobenius element at a
single ramified prime. -/
theorem frobenius_ellCoprimeRel (ℓ : ℕ) (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (hw : ∀ (L : FrobLevel K K') (P : NK.Chebotarev.PrimeIdeal ↥L.L),
      P.asIdeal.LiesOver 𝔭.asIdeal →
        ∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ σ τ : Gal(↥L.L/K),
          NK.Chebotarev.IsFrobAt P σ → NK.Chebotarev.IsFrobAt P τ →
            (Abelianization.of σ * (Abelianization.of τ)⁻¹) ^ m = 1)
    (L : FrobLevel K K') {P P' : NK.Chebotarev.PrimeIdeal ↥L.L}
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) (hP' : P'.asIdeal.LiesOver 𝔭.asIdeal)
    {σ σ' : Gal(↥L.L/K)} (hσ : NK.Chebotarev.IsFrobAt P σ)
    (hσ' : NK.Chebotarev.IsFrobAt P' σ') :
    EllCoprimeRel ℓ (Abelianization.of σ) (Abelianization.of σ') := by
  haveI : IsGalois K ↥L.L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  obtain ⟨g, hg⟩ := exists_smul_eq_of_liesOver (K := K) (L := ↥L.L) hP hP'
  have hconj : NK.Chebotarev.IsFrobAt P' (g * σ * g⁻¹) := by
    have h := NK.Chebotarev.IsFrobAtConj (K := K) (L := ↥L.L) hσ (τ := g)
    rwa [hg] at h
  have hconjof : Abelianization.of (g * σ * g⁻¹) = Abelianization.of σ := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
  obtain ⟨m, hm, hrel⟩ := hw L P' hP'
  refine ⟨m, hm, ?_⟩
  rw [← hconjof]
  exact hrel (g * σ * g⁻¹) σ' hconj hσ'

/-- **At every finite level, the Frobenius elements at the primes above `𝔭` have a common
ℓ-primary component**, giving an element of `Γ_{L,ℓ}` congruent to the image of every Frobenius
element at every prime above `𝔭`. -/
theorem exists_level_frobElem (ℓ : ℕ) (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (hw : ∀ (L : FrobLevel K K') (P : NK.Chebotarev.PrimeIdeal ↥L.L),
      P.asIdeal.LiesOver 𝔭.asIdeal →
        ∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ σ τ : Gal(↥L.L/K),
          NK.Chebotarev.IsFrobAt P σ → NK.Chebotarev.IsFrobAt P τ →
            (Abelianization.of σ * (Abelianization.of τ)⁻¹) ^ m = 1)
    (L : FrobLevel K K') :
    ∃ x : LevelEllPart L.L ℓ, ∀ (P : NK.Chebotarev.PrimeIdeal ↥L.L)
      (hP : P.asIdeal.LiesOver 𝔭.asIdeal) (σ : Gal(↥L.L/K)),
      NK.Chebotarev.IsFrobAt P σ →
        EllCoprimeRel ℓ (x : LevelAbelianization L.L) (Abelianization.of σ) := by
  haveI : IsGalois K ↥L.L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  obtain ⟨P₀, hP₀⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := ↥L.L) 𝔭
  obtain ⟨σ₀, hσ₀⟩ := NK.Chebotarev.exists_isFrobAt (K := K) (L := ↥L.L) 𝔭 P₀ hP₀
  refine ⟨ellComp ℓ (Abelianization.of σ₀), ?_⟩
  intro P hP σ hσ
  exact ellCoprimeRel_trans
    (ellCoprimeRel_symm (ellCoprimeRel_ellComp ℓ (Abelianization.of σ₀)))
    (ellCoprimeRel_symm (frobenius_ellCoprimeRel ℓ 𝔭 hw L hP hP₀ hσ hσ₀))

end Main

/-! ## The Frobenius element of `Γ_K` at `𝔭` -/

theorem exists_frobElement {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (hw : ∀ (L : FrobLevel K K') (P : NK.Chebotarev.PrimeIdeal ↥L.L),
      P.asIdeal.LiesOver 𝔭.asIdeal →
        ∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ σ τ : Gal(↥L.L/K),
          NK.Chebotarev.IsFrobAt P σ → NK.Chebotarev.IsFrobAt P τ →
            (Abelianization.of σ * (Abelianization.of τ)⁻¹) ^ m = 1) :
    ∃ F : Gamma K K' ℓ, ∀ (L : FrobLevel K K') (P : NK.Chebotarev.PrimeIdeal ↥L.L)
      (hP : P.asIdeal.LiesOver 𝔭.asIdeal) (σ : Gal(↥L.L/K)),
      NK.Chebotarev.IsFrobAt P σ →
        ∃ m : ℕ, Nat.Coprime m ℓ ∧
          (((Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L F : LevelEllPart L.L ℓ) :
              LevelAbelianization L.L) * (Abelianization.of σ)⁻¹) ^ m = 1 := by
  classical
  have key : ∀ L : FrobLevel K K', ∃ x : LevelEllPart L.L ℓ,
      ∀ (P : NK.Chebotarev.PrimeIdeal ↥L.L) (hP : P.asIdeal.LiesOver 𝔭.asIdeal)
        (σ : Gal(↥L.L/K)), NK.Chebotarev.IsFrobAt P σ →
        EllCoprimeRel ℓ (x : LevelAbelianization L.L) (Abelianization.of σ) :=
    fun L => exists_level_frobElem ℓ 𝔭 hw L
  let f : ∀ L : FrobLevel K K', LevelEllPart L.L ℓ := fun L => Classical.choose (key L)
  have hf : Compatible ℓ f := by
    intro L M h
    -- a Frobenius element at a prime of the level `M` above `𝔭`
    haveI hLgal : IsGalois K ↥L.L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    haveI hMgal : IsGalois K ↥M.L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    obtain ⟨PM, hPM⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := ↥M.L) 𝔭
    obtain ⟨σM, hσM⟩ := NK.Chebotarev.exists_isFrobAt (K := K) (L := ↥M.L) 𝔭 PM hPM
    have hMspec : EllCoprimeRel ℓ (f M : LevelAbelianization M.L)
        (Abelianization.of σM) :=
      Classical.choose_spec (key M) PM hPM σM hσM
    -- its restriction to `L` is a Frobenius element at a prime above `𝔭`
    haveI hnorm : Normal K ↥(levelTo L M h) := normal_levelTo L M h
    haveI hEgal : IsGalois K ↥(levelTo L M h) :=
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    have hρ : NK.Chebotarev.IsFrobAt (PM.under (NumberField.RingOfIntegers ↥(levelTo L M h)))
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M.L) ↥(levelTo L M h) σM) :=
      NK.Chebotarev.IsFrobAtRestrictNormalHom (K := K) (M := ↥M.L)
        (levelTo L M h) hPM hσM
    have hliesE : (PM.under (NumberField.RingOfIntegers ↥(levelTo L M h))).asIdeal.LiesOver
        𝔭.asIdeal := by
      rw [NK.Chebotarev.under_asIdeal (levelTo L M h) PM]
      haveI := hPM
      exact inferInstance
    have hprimeE : NK.Chebotarev.IsFrobAtPrime 𝔭
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M.L) ↥(levelTo L M h) σM) :=
      ⟨PM.under (NumberField.RingOfIntegers ↥(levelTo L M h)), hliesE, hρ⟩
    have hkey : (levelToEquiv L M h).symm.trans
        ((AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M.L) ↥(levelTo L M h) σM).trans
          (levelToEquiv L M h)) = levelRestrictHom L M h σM := rfl
    have hprime : NK.Chebotarev.IsFrobAtPrime 𝔭 (levelRestrictHom L M h σM) := by
      rw [← hkey]
      exact (NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase (levelToEquiv L M h)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M.L) ↥(levelTo L M h) σM) 𝔭).mp hprimeE
    obtain ⟨P', hP', hfrob'⟩ :=
      (NK.Chebotarev.isFrobAtPrime_iff (K := K) (L := ↥L.L) 𝔭
        (levelRestrictHom L M h σM)).mp hprime
    have hLspec : EllCoprimeRel ℓ (f L : LevelAbelianization L.L)
        (Abelianization.of (levelRestrictHom L M h σM)) :=
      Classical.choose_spec (key L) P' hP' (levelRestrictHom L M h σM) hfrob'
    have hmap : EllCoprimeRel ℓ (levelRestrict L M h (f M : LevelAbelianization M.L))
        (Abelianization.of (levelRestrictHom L M h σM)) := by
      have h := ellCoprimeRel_map (levelRestrict L M h) hMspec
      simpa only [levelRestrict, Abelianization.map_of] using h
    refine Subtype.ext ?_
    rw [ellRestrict_coe]
    exact eq_of_mem_ellPart_of_ellCoprimeRel
      (ellPart_map_le ℓ (levelRestrict L M h)
        (Subgroup.mem_map_of_mem (levelRestrict L M h) (f M).2))
      (f L).2
      (ellCoprimeRel_trans hmap (ellCoprimeRel_symm hLspec))
  refine ⟨Gamma.mk f hf, ?_⟩
  intro L P hP σ hσ
  simpa only [EllCoprimeRel, Gamma.proj_mk, f] using Classical.choose_spec (key L) P hP σ hσ

end NK.Reconstruct
