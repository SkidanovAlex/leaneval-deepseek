import Mathlib
import Submission.NK.Chebotarev.LFunctions
import Submission.NK.Chebotarev.Density
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.NK.Chebotarev.charPrimeSum_one_eq
import Submission.NK.Chebotarev.HasDirichletDensitySensitivity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Čebotarev in the abelian case from the analytic input

This file proves `NK.Chebotarev.AbelianChebotarevOfLFunctions`: the Hecke `L`-function input
`NK.Chebotarev.AbelianLFunctions` implies the Čebotarev density theorem for an abelian
extension, in the form that the set of primes of `K` whose Frobenius is a prescribed element `σ`
of the (abelian) Galois group has Dirichlet density `1/|Gal(L/K)|`.

The argument is the standard one.  Write `G = Gal(L/K)`, `n = |G|`.  For an unramified prime `p`
the Frobenius element is well defined, and the orthogonality of the characters of `G` gives the
pointwise identity `[Frob_p = σ] = n⁻¹ * ∑_φ φ(σ)⁻¹ * φ(Frob_p)`.  Multiplying by `Np^{-s}`,
summing over `p` and exchanging the finite character sum with the infinite prime sum expresses the
partial Dirichlet series of the Frobenius set as `n⁻¹ * ∑_φ φ(σ)⁻¹ * L(χ_φ, s)`.  The trivial
character contributes `n⁻¹ * log (1/(s-1)) + O(1)` (the pole of the Dedekind zeta function) and
each non-trivial character contributes `O(1)` by `AbelianLFunctions`.  The finitely many ramified
primes are harmless.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace NK.Chebotarev

open Filter IsDedekindDomain Asymptotics
open scoped BigOperators Classical

/-! ## Characters of a finite group -/

section CharOrth

variable (G : Type*) [Group G] [Fintype G]

/-- The (finite) type of multiplicative characters of a finite group with values in `ℂˣ`.

Every such character takes values in roots of unity (of order dividing the order of its
argument), hence is determined by an element of a finite product of finite groups. -/
noncomputable instance instFintypeMonoidHomUnitsComplex : Fintype (G →* ℂˣ) := by
  classical
  haveI : ∀ g : G, Fintype (rootsOfUnity (orderOf g) ℂ) := fun g => by
    haveI : NeZero (orderOf g) := ⟨(orderOf_pos g).ne'⟩
    exact Fintype.ofFinite _
  refine Fintype.ofInjective
    (fun φ : G →* ℂˣ => fun g : G =>
      (⟨φ g, ?_⟩ : rootsOfUnity (orderOf g) ℂ)) ?_
  · rw [mem_rootsOfUnity]
    exact (by rw [← map_pow, pow_orderOf_eq_one, map_one] : φ g ^ orderOf g = 1)
  · intro φ ψ h
    refine MonoidHom.ext fun g => ?_
    exact Subtype.ext_iff.mp (congrFun h g)

/-- Every value of a multiplicative character of a finite group has norm `1`. -/
lemma norm_monoidHom_units_apply_eq_one {G : Type*} [Group G] [Finite G]
    (φ : G →* ℂˣ) (g : G) : ‖((φ g : ℂˣ) : ℂ)‖ = 1 := by
  have hk : (φ g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have h1 : ‖((φ g : ℂˣ) : ℂ)‖ ^ orderOf g = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, hk, Units.val_one, norm_one]
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  rcases (pow_eq_one_iff_of_ne_zero hn).mp h1 with h | ⟨h, -⟩
  · exact h
  · linarith [norm_nonneg ((φ g : ℂˣ) : ℂ)]

end CharOrth

section CharOrthComm

variable (G : Type*) [CommGroup G] [Fintype G]

instance instHasEnoughRootsOfUnityComplexExponent : HasEnoughRootsOfUnity ℂ (Monoid.exponent G) := by
  have he : Monoid.exponent G ≠ 0 :=
    (Monoid.exponent_pos_of_exists (Nat.card G) Nat.card_pos fun g => by
      simpa using pow_card_eq_one (x := g)).ne'
  haveI : NeZero (Monoid.exponent G) := ⟨he⟩
  exact ⟨⟨Complex.exp (2 * Real.pi * Complex.I / Monoid.exponent G),
    Complex.isPrimitiveRoot_exp _ he⟩, rootsOfUnity.isCyclic ℂ (Monoid.exponent G)⟩

/-- **Column orthogonality at the identity.** -/
theorem sum_monoidHom_apply_one :
    (∑ φ : G →* ℂˣ, ((φ 1 : ℂˣ) : ℂ)) = (Nat.card G : ℂ) := by
  have hcard : Fintype.card (G →* ℂˣ) = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ
  rw [Finset.sum_congr rfl (fun φ _ => by simp : ∀ _ ∈ Finset.univ, _ = (1 : ℂ))]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard, Nat.card_eq_fintype_card]

/-- **Column orthogonality away from the identity.**  The sum of the values at `g ≠ 1` of all
characters of a finite abelian group vanishes. -/
theorem sum_monoidHom_apply_eq_zero {g : G} (hg : g ≠ 1) :
    (∑ φ : G →* ℂˣ, ((φ g : ℂˣ) : ℂ)) = 0 := by
  obtain ⟨φ₀, hφ₀⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg
  have hfix : (∑ φ : G →* ℂˣ, ((φ g : ℂˣ) : ℂ)) =
      ((φ₀ g : ℂˣ) : ℂ) * (∑ φ : G →* ℂˣ, ((φ g : ℂˣ) : ℂ)) := by
    rw [Finset.mul_sum]
    refine (Fintype.sum_bijective (fun φ : G →* ℂˣ => φ₀ * φ)
      (Group.mulLeft_bijective φ₀)
      (fun φ : G →* ℂˣ => ((φ₀ g : ℂˣ) : ℂ) * ((φ g : ℂˣ) : ℂ))
      (fun φ : G →* ℂˣ => ((φ g : ℂˣ) : ℂ)) ?_).symm
    intro φ
    simp [MonoidHom.mul_apply]
  have hc : ((φ₀ g : ℂˣ) : ℂ) ≠ 1 := by
    simpa using hφ₀
  have h1 : (1 - ((φ₀ g : ℂˣ) : ℂ)) * (∑ φ : G →* ℂˣ, ((φ g : ℂˣ) : ℂ)) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]
    exact hfix
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc
  · exact h

/-- **Row orthogonality, diagonal case.** -/
theorem sum_monoidHom_inv_mul_self (a : G) :
    (∑ φ : G →* ℂˣ, (((φ a)⁻¹ : ℂˣ) : ℂ) * ((φ a : ℂˣ) : ℂ)) = (Nat.card G : ℂ) := by
  have h : ∀ φ : G →* ℂˣ, (((φ a)⁻¹ : ℂˣ) : ℂ) * ((φ a : ℂˣ) : ℂ) = 1 := by
    intro φ
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : (∑ φ : G →* ℂˣ, (1 : ℂ)) = (∑ φ : G →* ℂˣ, ((φ 1 : ℂˣ) : ℂ)) :=
    Finset.sum_congr rfl (fun φ _ => by simp)
  rw [Finset.sum_congr rfl (fun φ _ => h φ), h1, sum_monoidHom_apply_one]

/-- **Row orthogonality, off-diagonal case.** -/
theorem sum_monoidHom_inv_mul_eq_zero {a b : G} (h : a ≠ b) :
    (∑ φ : G →* ℂˣ, (((φ a)⁻¹ : ℂˣ) : ℂ) * ((φ b : ℂˣ) : ℂ)) = 0 := by
  have hpt : ∀ φ : G →* ℂˣ,
      (((φ a)⁻¹ : ℂˣ) : ℂ) * ((φ b : ℂˣ) : ℂ) = ((φ (a⁻¹ * b) : ℂˣ) : ℂ) := by
    intro φ
    rw [← Units.val_mul, ← map_inv, ← map_mul]
  rw [Finset.sum_congr rfl (fun φ _ => hpt φ)]
  exact sum_monoidHom_apply_eq_zero G (g := a⁻¹ * b) (by
    intro hh
    exact h (inv_mul_eq_one.mp hh))

/-- The composite of a `ℂˣ`-valued character with the inclusion `ℂˣ → ℂ` is trivial only if the
character is. -/
theorem units_coeHom_comp_eq_one_iff {G : Type*} [Group G] (φ : G →* ℂˣ) :
    (Units.coeHom ℂ).comp φ = 1 ↔ φ = 1 := by
  constructor
  · intro h
    refine MonoidHom.ext fun g => ?_
    have hg := DFunLike.congr_fun h g
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.one_apply] at hg
    exact Units.ext hg
  · rintro rfl
    exact MonoidHom.comp_one _

end CharOrthComm

/-! ## The main section -/

section Main

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The set of primes of `K` that ramify in the extension `L/K`. -/
def ramifiedPrimes : Set (PrimeIdeal K) :=
  {p | ¬ ∀ P : PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
    P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1}

theorem finite_ramifiedPrimes :
    (ramifiedPrimes (K := K) (L := L)).Finite := by
  have hQ : {q : PrimeIdeal L |
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}.Finite :=
    Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
  refine Set.Finite.of_injOn (f := fun p : PrimeIdeal K => p.asIdeal) ?_ ?_
    (hQ.image (fun q : PrimeIdeal L =>
      q.asIdeal.under (NumberField.RingOfIntegers K)))
  · intro p hp
    simp only [ramifiedPrimes, Set.mem_setOf_eq] at hp
    push_neg at hp
    obtain ⟨P, hP, hram⟩ := hp
    exact ⟨P, hram, hP.over.symm⟩
  · intro p _ p' _ h
    exact HeightOneSpectrum.ext h

lemma not_mem_ramifiedPrimes_iff (p : PrimeIdeal K) :
    p ∉ ramifiedPrimes (K := K) (L := L) ↔
      ∀ P : PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
  simp [ramifiedPrimes]

/-- The set of primes of `K` at which the chosen Frobenius element is `σ`. -/
def frobAtPrimeSet (σ : Gal(L/K)) : Set (PrimeIdeal K) :=
  {p | frobAtPrime (K := K) (L := L) p = σ}

lemma isFrobAtPrime_iff_frobAtPrime_eq_of_notMem_ramified
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) {p : PrimeIdeal K}
    (hp : p ∉ ramifiedPrimes (K := K) (L := L)) (σ : Gal(L/K)) :
    IsFrobAtPrime (K := K) (L := L) p σ ↔
      frobAtPrime (K := K) (L := L) p = σ :=
  isFrobAtPrime_iff_frobAtPrime_eq hcomm p
    ((not_mem_ramifiedPrimes_iff (K := K) (L := L) p).mp hp) σ

/-- The Frobenius set and the set of primes where the chosen Frobenius equals `σ` differ only at
ramified primes. -/
theorem finite_symmDiff_frobAtPrime (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (σ : Gal(L/K)) :
    (({p : PrimeIdeal K | IsFrobAtPrime (K := K) (L := L) p σ} \
        frobAtPrimeSet (K := K) (L := L) σ) ∪
      (frobAtPrimeSet (K := K) (L := L) σ \
        {p : PrimeIdeal K | IsFrobAtPrime (K := K) (L := L) p σ})).Finite := by
  refine (finite_ramifiedPrimes (K := K) (L := L)).subset ?_
  rintro p (hp | hp)
  · intro hcon
    exact hp.2 ((isFrobAtPrime_iff_frobAtPrime_eq_of_notMem_ramified hcomm
      (fun hc => hc hcon) σ).mp hp.1)
  · intro hcon
    exact hp.2 ((isFrobAtPrime_iff_frobAtPrime_eq_of_notMem_ramified hcomm
      (fun hc => hc hcon) σ).mpr hp.1)

/-- The weight `Np^{-s}` of a prime, as a complex number. -/
noncomputable def zetaWeight (s : ℝ) (p : PrimeIdeal K) : ℂ :=
  ((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ)

/-- The character coefficient `φ(σ)⁻¹`. -/
noncomputable def charCoeff (σ : Gal(L/K)) (φ : Gal(L/K) →* ℂˣ) : ℂ :=
  (((φ σ)⁻¹ : ℂˣ) : ℂ)

/-- The value `φ(Frob_p)` of a character at the Frobenius element. -/
noncomputable def frobCharAt (φ : Gal(L/K) →* ℂˣ) (p : PrimeIdeal K) : ℂ :=
  ((φ (frobAtPrime (K := K) (L := L) p) : ℂˣ) : ℂ)

/-- The character-theoretic transform of the Frobenius indicator: the complex number
`n⁻¹ * ∑_φ φ(σ)⁻¹ * L(χ_φ, s)`. -/
noncomputable def charFrobSum (σ : Gal(L/K)) (s : ℝ) : ℂ :=
  (Nat.card (Gal(L/K)) : ℂ)⁻¹ *
    ∑ φ : Gal(L/K) →* ℂˣ,
      charCoeff σ φ *
        charPrimeSum (K := K) (L := L) ((Units.coeHom ℂ).comp φ) s

lemma card_gal_ne_zero : (Nat.card (Gal(L/K)) : ℂ) ≠ 0 := by
  have hpos : 0 < Nat.card (Gal(L/K)) := by
    rw [IsGalois.card_aut_eq_finrank K L]
    exact Module.finrank_pos
  exact_mod_cast hpos.ne'

/-- The norm of the coercion of a real number to `ℂ` is its norm in `ℝ`. -/
lemma norm_ofReal_eq (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = ‖r‖ :=
  (RCLike.norm_ofReal (K := ℂ) r).trans (Real.norm_eq_abs r).symm

lemma zetaWeight_norm (s : ℝ) (p : PrimeIdeal K) :
    ‖zetaWeight s p‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) := by
  rw [zetaWeight]
  have h : ‖(((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)‖
      = |(Ideal.absNorm p.asIdeal : ℝ) ^ (-s)| := RCLike.norm_ofReal _
  rw [h, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

lemma charCoeff_norm_eq_one (σ : Gal(L/K)) (φ : Gal(L/K) →* ℂˣ) :
    ‖charCoeff σ φ‖ = 1 := by
  rw [charCoeff, ← map_inv]
  exact norm_monoidHom_units_apply_eq_one φ σ⁻¹

lemma frobCharAt_norm_eq_one (φ : Gal(L/K) →* ℂˣ) (p : PrimeIdeal K) :
    ‖frobCharAt φ p‖ = 1 :=
  norm_monoidHom_units_apply_eq_one φ _

lemma norm_charWeight_eq_one (φ : Gal(L/K) →* ℂˣ) (σ x : Gal(L/K)) :
    ‖charCoeff σ φ * ((φ x : ℂˣ) : ℂ)‖ = 1 := by
  rw [norm_mul, charCoeff_norm_eq_one, norm_monoidHom_units_apply_eq_one φ x, one_mul]

lemma charPrimeSum_eq_tsum (φ : Gal(L/K) →* ℂˣ) (s : ℝ) :
    charPrimeSum (K := K) (L := L) ((Units.coeHom ℂ).comp φ) s =
      ∑' p : PrimeIdeal K, frobCharAt φ p * zetaWeight s p := by
  simp only [charPrimeSum, frobCharAt, zetaWeight, MonoidHom.comp_apply, Units.coeHom_apply]

/-- The prime-ideal zeta sum of a set, written as a `tsum` over the whole spectrum of the
indicator function of the set. -/
lemma primeIdealZetaSum_eq_tsum_indicator (T : Set (PrimeIdeal K)) (s : ℝ) :
    NumberField.Set.primeIdealZetaSum T s =
      ∑' p : PrimeIdeal K,
        T.indicator (fun p => (Ideal.absNorm p.asIdeal : ℝ) ^ (-s)) p := by
  rw [NumberField.Set.primeIdealZetaSum_def]
  exact tsum_subtype T (fun p => (Ideal.absNorm p.asIdeal : ℝ) ^ (-s))

/-- **The character sum at `σ` itself equals `1`.** -/
lemma charSum_self (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (σ : Gal(L/K)) :
    (Nat.card (Gal(L/K)) : ℂ)⁻¹ *
      (∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * ((φ σ : ℂˣ) : ℂ)) = 1 := by
  letI : CommGroup (Gal(L/K)) :=
    { (inferInstance : Group (Gal(L/K))) with mul_comm := hcomm }
  rw [show (∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * ((φ σ : ℂˣ) : ℂ)) =
      (∑ φ : Gal(L/K) →* ℂˣ, (((φ σ)⁻¹ : ℂˣ) : ℂ) * ((φ σ : ℂˣ) : ℂ)) from
    Finset.sum_congr rfl (fun φ _ => by rw [charCoeff])]
  rw [sum_monoidHom_inv_mul_self (Gal(L/K)) σ,
    inv_mul_cancel₀ (card_gal_ne_zero (K := K) (L := L))]

/-- **The character sum at `x ≠ σ` vanishes.** -/
lemma charSum_of_ne (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    {σ x : Gal(L/K)} (h : x ≠ σ) :
    (Nat.card (Gal(L/K)) : ℂ)⁻¹ *
      (∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * ((φ x : ℂˣ) : ℂ)) = 0 := by
  letI : CommGroup (Gal(L/K)) :=
    { (inferInstance : Group (Gal(L/K))) with mul_comm := hcomm }
  rw [show (∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * ((φ x : ℂˣ) : ℂ)) =
      (∑ φ : Gal(L/K) →* ℂˣ, (((φ σ)⁻¹ : ℂˣ) : ℂ) * ((φ x : ℂˣ) : ℂ)) from
    Finset.sum_congr rfl (fun φ _ => by rw [charCoeff])]
  rw [sum_monoidHom_inv_mul_eq_zero (Gal(L/K)) (a := σ) (b := x) (Ne.symm h), mul_zero]

/-- The indicator of the set of primes whose Frobenius is `σ`, expanded in characters. -/
lemma indicator_frobAtPrimeSet (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (σ : Gal(L/K)) (p : PrimeIdeal K) :
    (((frobAtPrimeSet (K := K) (L := L) σ).indicator (fun _ => (1 : ℝ)) p : ℝ) : ℂ)
      = (Nat.card (Gal(L/K)) : ℂ)⁻¹ *
          ∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * frobCharAt φ p := by
  classical
  by_cases hp : p ∈ frobAtPrimeSet (K := K) (L := L) σ
  · rw [Set.indicator_of_mem hp]
    have hp' : frobAtPrime (K := K) (L := L) p = σ := hp
    simp only [frobCharAt]
    rw [hp']
    exact (charSum_self hcomm σ).symm
  · rw [Set.indicator_of_notMem hp]
    have hp' : frobAtPrime (K := K) (L := L) p ≠ σ := hp
    rw [show (((0 : ℝ)) : ℂ) = (0 : ℂ) by norm_num]
    exact (charSum_of_ne hcomm hp').symm

/-- Summability of the weighted prime-ideal zeta sum, the weight being bounded by `1`. -/
lemma summable_zetaSum_weighted {s : ℝ} (hs : 1 < s)
    (w : PrimeIdeal K → ℂ) (hw : ∀ p, ‖w p‖ ≤ 1) :
    Summable (fun p : PrimeIdeal K =>
      (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) * w p) := by
  refine Summable.of_norm_bounded
    (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hs) ?_
  intro p
  rw [norm_mul]
  have h1 : ‖(((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)‖
      = (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) := by
    have h2 : ‖(((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)‖
        = |(Ideal.absNorm p.asIdeal : ℝ) ^ (-s)| := RCLike.norm_ofReal _
    rw [h2, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  rw [h1]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hw p)

/-- **The Fourier identity for the Frobenius set.**  For `s > 1` the partial Dirichlet series of
the primes whose chosen Frobenius element is `σ` equals the character transform
`charFrobSum σ s = n⁻¹ * ∑_φ φ(σ)⁻¹ * (∑' p, φ(Frob_p) Np^{-s})`. -/
theorem primeIdealZetaSum_frobAtPrimeSet_eq
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (σ : Gal(L/K)) {s : ℝ} (hs : 1 < s) :
    ((NumberField.Set.primeIdealZetaSum (frobAtPrimeSet (K := K) (L := L) σ) s : ℝ) : ℂ)
      = charFrobSum (K := K) (L := L) σ s := by
  classical
  letI : CommGroup (Gal(L/K)) :=
    { (inferInstance : Group (Gal(L/K))) with mul_comm := hcomm }
  have hsm : ∀ φ : Gal(L/K) →* ℂˣ,
      Summable (fun p : PrimeIdeal K => zetaWeight s p * frobCharAt φ p) := by
    intro φ
    exact Summable.congr
      (f := fun p : PrimeIdeal K => (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) *
        ((φ (frobAtPrime (K := K) (L := L) p) : ℂˣ) : ℂ))
      (summable_zetaSum_weighted (K := K) hs _
        (fun p => (norm_monoidHom_units_apply_eq_one φ _).le))
      (fun p => by simp only [zetaWeight, frobCharAt])
  have hsm2 : ∀ φ : Gal(L/K) →* ℂˣ,
      Summable (fun p : PrimeIdeal K => zetaWeight s p * (charCoeff σ φ * frobCharAt φ p)) := by
    intro φ
    exact Summable.congr
      (f := fun p : PrimeIdeal K => (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) *
        ((((φ σ)⁻¹ : ℂˣ) : ℂ) * ((φ (frobAtPrime (K := K) (L := L) p) : ℂˣ) : ℂ)))
      (summable_zetaSum_weighted (K := K) hs _
        (fun p => (norm_charWeight_eq_one φ σ _).le))
      (fun p => by simp only [zetaWeight, charCoeff, frobCharAt])
  have hcard : (0 : ℝ) ≤ (Fintype.card (Gal(L/K) →* ℂˣ) : ℝ) := Nat.cast_nonneg _
  have hsum : Summable (fun p : PrimeIdeal K =>
      zetaWeight s p * ∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * frobCharAt φ p) := by
    have hg : Summable (fun p : PrimeIdeal K =>
        (Fintype.card (Gal(L/K) →* ℂˣ) : ℝ) * ((Ideal.absNorm p.asIdeal : ℝ) ^ (-s))) :=
      (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hs).mul_left _
    refine Summable.of_norm_bounded hg ?_
    intro p
    rw [norm_mul, zetaWeight_norm]
    have h2 : ‖∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * frobCharAt φ p‖
        ≤ (Fintype.card (Gal(L/K) →* ℂˣ) : ℝ) := by
      calc ‖∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * frobCharAt φ p‖
          ≤ ∑ φ : Gal(L/K) →* ℂˣ, ‖charCoeff σ φ * frobCharAt φ p‖ := norm_sum_le _ _
        _ = ∑ _φ : Gal(L/K) →* ℂˣ, (1 : ℝ) :=
            Finset.sum_congr rfl (fun φ _ => by
              rw [norm_mul, charCoeff_norm_eq_one, frobCharAt_norm_eq_one, one_mul])
        _ = (Fintype.card (Gal(L/K) →* ℂˣ) : ℝ) := by simp
    calc (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) *
          ‖∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * frobCharAt φ p‖
        ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) * (Fintype.card (Gal(L/K) →* ℂˣ) : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (Fintype.card (Gal(L/K) →* ℂˣ) : ℝ) * (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) := by ring
  have e1 : (∑' p : PrimeIdeal K,
        zetaWeight s p * ((Nat.card (Gal(L/K)) : ℂ)⁻¹ *
          ∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * frobCharAt φ p))
      = ∑' p : PrimeIdeal K, (Nat.card (Gal(L/K)) : ℂ)⁻¹ *
          (zetaWeight s p * ∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * frobCharAt φ p) :=
    tsum_congr (fun p => by ring)
  have e2 : (∑' p : PrimeIdeal K, (Nat.card (Gal(L/K)) : ℂ)⁻¹ *
        (zetaWeight s p * ∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * frobCharAt φ p))
      = (Nat.card (Gal(L/K)) : ℂ)⁻¹ *
          ∑' p : PrimeIdeal K, zetaWeight s p * ∑ φ : Gal(L/K) →* ℂˣ,
            charCoeff σ φ * frobCharAt φ p :=
    Summable.tsum_mul_left _ hsum
  have e3 : (∑' p : PrimeIdeal K, zetaWeight s p *
        ∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * frobCharAt φ p)
      = ∑' p : PrimeIdeal K, ∑ φ ∈ (Finset.univ : Finset (Gal(L/K) →* ℂˣ)),
          zetaWeight s p * (charCoeff σ φ * frobCharAt φ p) :=
    tsum_congr (fun p => by rw [Finset.mul_sum])
  have e4 : (∑' p : PrimeIdeal K, ∑ φ ∈ (Finset.univ : Finset (Gal(L/K) →* ℂˣ)),
        zetaWeight s p * (charCoeff σ φ * frobCharAt φ p))
      = ∑ φ ∈ (Finset.univ : Finset (Gal(L/K) →* ℂˣ)), ∑' p : PrimeIdeal K,
          zetaWeight s p * (charCoeff σ φ * frobCharAt φ p) :=
    Summable.tsum_finsetSum (fun φ _ => hsm2 φ)
  have e5 : ∀ φ : Gal(L/K) →* ℂˣ,
      (∑' p : PrimeIdeal K, zetaWeight s p * (charCoeff σ φ * frobCharAt φ p))
        = charCoeff σ φ * (∑' p : PrimeIdeal K, frobCharAt φ p * zetaWeight s p) := by
    intro φ
    have e5a : (∑' p : PrimeIdeal K, zetaWeight s p * (charCoeff σ φ * frobCharAt φ p))
        = ∑' p : PrimeIdeal K, charCoeff σ φ * (zetaWeight s p * frobCharAt φ p) :=
      tsum_congr (fun p => by ring)
    have e5b : (∑' p : PrimeIdeal K, charCoeff σ φ * (zetaWeight s p * frobCharAt φ p))
        = charCoeff σ φ * ∑' p : PrimeIdeal K, zetaWeight s p * frobCharAt φ p :=
      Summable.tsum_mul_left _ (hsm φ)
    have e5c : (∑' p : PrimeIdeal K, zetaWeight s p * frobCharAt φ p)
        = ∑' p : PrimeIdeal K, frobCharAt φ p * zetaWeight s p :=
      tsum_congr (fun p => by ring)
    rw [e5a, e5b, e5c]
  have e6 : (∑ φ ∈ (Finset.univ : Finset (Gal(L/K) →* ℂˣ)), ∑' p : PrimeIdeal K,
        zetaWeight s p * (charCoeff σ φ * frobCharAt φ p))
      = ∑ φ ∈ (Finset.univ : Finset (Gal(L/K) →* ℂˣ)),
          charCoeff σ φ * (∑' p : PrimeIdeal K, frobCharAt φ p * zetaWeight s p) :=
    Finset.sum_congr rfl (fun φ _ => e5 φ)
  have hmain : (∑' p : PrimeIdeal K,
        zetaWeight s p * ((Nat.card (Gal(L/K)) : ℂ)⁻¹ *
          ∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * frobCharAt φ p))
      = (Nat.card (Gal(L/K)) : ℂ)⁻¹ * (∑ φ ∈ (Finset.univ : Finset (Gal(L/K) →* ℂˣ)),
          charCoeff σ φ * (∑' p : PrimeIdeal K, frobCharAt φ p * zetaWeight s p)) := by
    rw [e1, e2, e3, e4, e6]
  have hs1 : NumberField.Set.primeIdealZetaSum (frobAtPrimeSet (K := K) (L := L) σ) s =
      ∑' p : PrimeIdeal K, (frobAtPrimeSet (K := K) (L := L) σ).indicator
        (fun p => (Ideal.absNorm p.asIdeal : ℝ) ^ (-s)) p :=
    primeIdealZetaSum_eq_tsum_indicator _ _
  have hs2 : ((∑' p : PrimeIdeal K, (frobAtPrimeSet (K := K) (L := L) σ).indicator
        (fun p => (Ideal.absNorm p.asIdeal : ℝ) ^ (-s)) p : ℝ) : ℂ)
      = ∑' p : PrimeIdeal K, (((frobAtPrimeSet (K := K) (L := L) σ).indicator
          (fun p => (Ideal.absNorm p.asIdeal : ℝ) ^ (-s)) p : ℝ) : ℂ) :=
    Complex.ofReal_tsum _
  have hs3 : (∑' p : PrimeIdeal K, (((frobAtPrimeSet (K := K) (L := L) σ).indicator
          (fun p => (Ideal.absNorm p.asIdeal : ℝ) ^ (-s)) p : ℝ) : ℂ))
      = ∑' p : PrimeIdeal K, zetaWeight s p *
          (((frobAtPrimeSet (K := K) (L := L) σ).indicator (fun _ => (1 : ℝ)) p : ℝ) : ℂ) :=
    tsum_congr (fun p => by
      by_cases hp : p ∈ frobAtPrimeSet (K := K) (L := L) σ
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; simp [zetaWeight]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; simp)
  have hs4 : (∑' p : PrimeIdeal K, zetaWeight s p *
        (((frobAtPrimeSet (K := K) (L := L) σ).indicator (fun _ => (1 : ℝ)) p : ℝ) : ℂ))
      = ∑' p : PrimeIdeal K, zetaWeight s p *
          ((Nat.card (Gal(L/K)) : ℂ)⁻¹ *
            ∑ φ : Gal(L/K) →* ℂˣ, charCoeff σ φ * frobCharAt φ p) :=
    tsum_congr (fun p => by rw [indicator_frobAtPrimeSet hcomm σ p])
  rw [hs1, hs2, hs3, hs4, charFrobSum]
  simp only [charPrimeSum_eq_tsum]
  exact hmain

/-- **The asymptotics of the character transform.**  The contribution of the trivial character is
the pole of the Dedekind zeta function, and every non-trivial character contributes `O(1)` by
`AbelianLFunctions`. -/
theorem charFrobSum_isBigO (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (h : AbelianLFunctions K L) (σ : Gal(L/K)) :
    (fun s : ℝ => charFrobSum (K := K) (L := L) σ s -
      (Nat.card (Gal(L/K)) : ℂ)⁻¹ * ((Real.log (1 / (s - 1)) : ℝ) : ℂ))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  classical
  letI : CommGroup (Gal(L/K)) :=
    { (inferInstance : Group (Gal(L/K))) with mul_comm := hcomm }
  have htriv : (fun s : ℝ => charPrimeSum (K := K) (L := L) (1 : Gal(L/K) →* ℂ) s -
      ((Real.log (1 / (s - 1)) : ℝ) : ℂ)) =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
    have hreal : (fun s : ℝ =>
        NumberField.Set.primeIdealZetaSum (Set.univ : Set (PrimeIdeal K)) s -
          Real.log (1 / (s - 1))) =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℝ)) :=
      Commons.NumberTheory.NumberField.Set.isBigO_primeIdealZetaSum_sub_log K
    have hcomplex : (fun s : ℝ =>
        (((NumberField.Set.primeIdealZetaSum (Set.univ : Set (PrimeIdeal K)) s -
          Real.log (1 / (s - 1))) : ℝ) : ℂ)) =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
        (fun _ : ℝ => (1 : ℂ)) := by
      obtain ⟨C, hC⟩ := hreal.bound
      refine Asymptotics.IsBigO.of_bound (max C 0) ?_
      filter_upwards [hC] with s hs
      rw [norm_one, mul_one] at hs
      rw [norm_one, mul_one]
      calc ‖((((NumberField.Set.primeIdealZetaSum (Set.univ : Set (PrimeIdeal K)) s -
              Real.log (1 / (s - 1))) : ℝ) : ℂ))‖
          = ‖(NumberField.Set.primeIdealZetaSum (Set.univ : Set (PrimeIdeal K)) s -
              Real.log (1 / (s - 1)))‖ := norm_ofReal_eq _
        _ ≤ max C 0 := hs.trans (le_max_left C 0)
    refine Asymptotics.IsBigO.congr' hcomplex ?_
      (Filter.Eventually.of_forall (fun _ => rfl))
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [charPrimeSum_one_eq (K := K) (L := L) hs]
    push_cast
    ring
  have hnon : ∀ φ ∈ (Finset.univ.erase (1 : Gal(L/K) →* ℂˣ)),
      (fun s : ℝ => charCoeff σ φ * charPrimeSum (K := K) (L := L)
        ((Units.coeHom ℂ).comp φ) s) =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
    intro φ hφ
    have hne : φ ≠ 1 := Finset.ne_of_mem_erase hφ
    have hχ : (Units.coeHom ℂ).comp φ ≠ 1 := fun hc =>
      hne ((units_coeHom_comp_eq_one_iff φ).mp hc)
    exact (h ((Units.coeHom ℂ).comp φ) hχ).const_mul_left _
  have hsum : (fun s : ℝ => ∑ φ ∈ (Finset.univ.erase (1 : Gal(L/K) →* ℂˣ)),
        charCoeff σ φ * charPrimeSum (K := K) (L := L) ((Units.coeHom ℂ).comp φ) s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
    refine Asymptotics.IsBigO.congr' (Asymptotics.IsBigO.sum hnon) ?_
      (Filter.Eventually.of_forall (fun _ => rfl))
    filter_upwards with s
    simp only [Finset.sum_apply]
  have hdec : (fun s : ℝ => charFrobSum (K := K) (L := L) σ s -
        (Nat.card (Gal(L/K)) : ℂ)⁻¹ * ((Real.log (1 / (s - 1)) : ℝ) : ℂ))
      = (fun s : ℝ => (Nat.card (Gal(L/K)) : ℂ)⁻¹ *
          ((charPrimeSum (K := K) (L := L) (1 : Gal(L/K) →* ℂ) s -
              ((Real.log (1 / (s - 1)) : ℝ) : ℂ)) +
            ∑ φ ∈ (Finset.univ.erase (1 : Gal(L/K) →* ℂˣ)),
              charCoeff σ φ * charPrimeSum (K := K) (L := L)
                ((Units.coeHom ℂ).comp φ) s)) := by
    funext s
    rw [charFrobSum]
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Gal(L/K) →* ℂˣ)) _ (Finset.mem_univ _)]
    have h1c : charCoeff σ (1 : Gal(L/K) →* ℂˣ) = 1 := rfl
    have h1s : ((Units.coeHom ℂ).comp (1 : Gal(L/K) →* ℂˣ)) = 1 := MonoidHom.comp_one _
    rw [h1c, h1s, one_mul]
    ring
  rw [hdec]
  exact (htriv.add hsum).const_mul_left _

/-- **Čebotarev's density theorem for a finite abelian extension, from the analytic input.** -/
theorem AbelianChebotarevOfLFunctions {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (h : NK.Chebotarev.AbelianLFunctions K L) (σ : Gal(L/K)) :
    NumberField.Set.HasDirichletDensity
      {p : NK.Chebotarev.PrimeIdeal K |
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ}
      (1 / (Nat.card (Gal(L/K)) : ℝ)) := by
  classical
  have hdiff : (frobAtPrimeSet (K := K) (L := L) σ \
        {p : PrimeIdeal K | IsFrobAtPrime (K := K) (L := L) p σ} ∪
        ({p : PrimeIdeal K | IsFrobAtPrime (K := K) (L := L) p σ} \
          frobAtPrimeSet (K := K) (L := L) σ)).Finite := by
    rw [Set.union_comm]
    exact finite_symmDiff_frobAtPrime hcomm σ
  refine HasDirichletDensitySensitivity
    (S := frobAtPrimeSet (K := K) (L := L) σ)
    (T := {p : PrimeIdeal K | IsFrobAtPrime (K := K) (L := L) p σ})
    (δ := 1 / (Nat.card (Gal(L/K)) : ℝ)) hdiff ?_
  refine Commons.NumberTheory.NumberField.Set.hasDirichletDensity_of_isBigO_primeIdealZetaSum_sub_log ?_
  have hO : (fun s : ℝ => ((NumberField.Set.primeIdealZetaSum
        (frobAtPrimeSet (K := K) (L := L) σ) s : ℝ) : ℂ) -
      (Nat.card (Gal(L/K)) : ℂ)⁻¹ * ((Real.log (1 / (s - 1)) : ℝ) : ℂ))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
    have hA : (fun s : ℝ => ((NumberField.Set.primeIdealZetaSum
          (frobAtPrimeSet (K := K) (L := L) σ) s : ℝ) : ℂ) -
        charFrobSum (K := K) (L := L) σ s)
        =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
      refine Asymptotics.IsBigO.of_bound 0 ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [primeIdealZetaSum_frobAtPrimeSet_eq hcomm σ hs, sub_self, norm_zero, zero_mul]
    have hB := charFrobSum_isBigO hcomm h σ
    refine Asymptotics.IsBigO.congr' (hA.add hB) ?_
      (Filter.Eventually.of_forall (fun _ => rfl))
    filter_upwards with s
    ring
  obtain ⟨C, hC⟩ := hO.bound
  refine Asymptotics.IsBigO.of_bound (max C 0) ?_
  filter_upwards [hC] with s hs
  rw [norm_one, mul_one] at hs
  rw [norm_one, mul_one]
  have key : (((NumberField.Set.primeIdealZetaSum (frobAtPrimeSet (K := K) (L := L) σ) s -
      (1 / (Nat.card (Gal(L/K)) : ℝ)) * Real.log (1 / (s - 1)) : ℝ)) : ℂ)
      = ((NumberField.Set.primeIdealZetaSum (frobAtPrimeSet (K := K) (L := L) σ) s : ℝ) : ℂ) -
        (Nat.card (Gal(L/K)) : ℂ)⁻¹ * ((Real.log (1 / (s - 1)) : ℝ) : ℂ) := by
    rw [one_div]
    push_cast <;> ring
  have hnorm : ‖NumberField.Set.primeIdealZetaSum (frobAtPrimeSet (K := K) (L := L) σ) s -
        (1 / (Nat.card (Gal(L/K)) : ℝ)) * Real.log (1 / (s - 1))‖
      = ‖((NumberField.Set.primeIdealZetaSum (frobAtPrimeSet (K := K) (L := L) σ) s : ℝ) : ℂ) -
        (Nat.card (Gal(L/K)) : ℂ)⁻¹ * ((Real.log (1 / (s - 1)) : ℝ) : ℂ)‖ := by
    rw [← key]
    exact (norm_ofReal_eq _).symm
  rw [hnorm]
  exact hs.trans (le_max_left C 0)

end Main

end NK.Chebotarev
