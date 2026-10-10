import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalInputs.Instantiation
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.NK.Mine.index_powSub_units_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local power-class count `|κˣ / (κˣ)^p| = p²` for `p` prime to the residue characteristic

Let `K` be a number field, `𝔮` a finite prime of `K` and `p` a prime which is *not* the residue
characteristic of `𝔮` (i.e. `p ∉ 𝔮`).  Then `p` is a unit of the ring of integers
`𝒪_κ = 𝔮.adicCompletionIntegers K` of the local field `κ = K_𝔮`, and the classical structure of
`κˣ` gives

  `|κˣ / (κˣ)^p| = p * |𝒪_κˣ / (𝒪_κˣ)^p| = p * |μ(F_qˣ / (F_qˣ)^p)|`

where the last factor is the `p`-power quotient of the units of the residue field.  Since `κ`
contains a primitive `p`-th root of unity `ζ_p` (hypothesis `hζ`), the reduction `ζ̄_p` of `ζ_p`
to the residue field is a *non-trivial* `p`-th root of unity — non-trivial because a `p`-th root
of unity congruent to `1` modulo the maximal ideal would force `p` itself into the maximal ideal
(geometric-sum argument), contradicting that `p` is a unit.  Hence `p ∣ #(F_qˣ)` and

  `|F_qˣ / (F_qˣ)^p| = gcd p #(F_qˣ) = p`,

so that `|κˣ / (κˣ)^p| = p²`.

This is the "`p ∉ 𝔮`" companion of `localIndex_finite_mem` (there `p` is the residue
characteristic, so the answer is `p ^ ([κ:ℚ_p] + 1 + δ)`; here the residue characteristic is
prime to `p` and the answer is `p²`).
-/

open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators

set_option linter.style.haveILetI false

namespace NK.GlobalCFTdeep.SecondInequality

noncomputable section

variable {K : Type} [Field K] [NumberField K]

/-! ## Some elementary lemmas about local rings -/

/-- **A non-trivial `p`-th root of unity cannot be congruent to `1` modulo `𝔪` when `p` is a
unit.**  In a local domain, if `x ^ p = 1`, `x ≠ 1` and `x ≡ 1 (mod 𝔪)`, the geometric-sum
identity `(x - 1) * ∑_{i<p} x^i = x^p - 1 = 0` forces `∑_{i<p} x^i = 0`; but that sum is
congruent to `p` modulo `𝔪`, so `p ≡ 0 (mod 𝔪)`, contradicting that `p` is a unit. -/
lemma residue_ne_one_of_pow_eq_one {R : Type*} [CommRing R] [IsLocalRing R] [IsDomain R]
    {p : ℕ} (hun : IsUnit (p : R)) {x : R} (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    IsLocalRing.residue R x ≠ 1 := by
  intro hres
  have hmem : x - 1 ∈ IsLocalRing.maximalIdeal R := by
    refine (IsLocalRing.residue_eq_zero_iff (x - 1)).mp ?_
    rw [map_sub, hres, map_one, sub_self]
  have hgeom : (x - 1) * (∑ i ∈ Finset.range p, x ^ i) = x ^ p - 1 := mul_geom_sum x p
  rw [hx, sub_self] at hgeom
  have hS : (∑ i ∈ Finset.range p, x ^ i) = 0 := by
    rcases mul_eq_zero.mp hgeom with h | h
    · exact absurd (sub_eq_zero.mp h) hx1
    · exact h
  have hSp : (∑ i ∈ Finset.range p, x ^ i) - (p : R) ∈ IsLocalRing.maximalIdeal R := by
    have hsplit : (∑ i ∈ Finset.range p, x ^ i) - (p : R) = ∑ i ∈ Finset.range p, (x ^ i - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [hsplit]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    have h1 : x ^ i - 1 = (x - 1) * (∑ j ∈ Finset.range i, x ^ j) := (mul_geom_sum x i).symm
    rw [h1]
    exact Ideal.mul_mem_right _ _ hmem
  have hp_mem : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    have h2 : (p : R) =
        (∑ i ∈ Finset.range p, x ^ i) - ((∑ i ∈ Finset.range p, x ^ i) - (p : R)) := by ring
    rw [h2]
    refine (IsLocalRing.maximalIdeal R).sub_mem ?_ hSp
    rw [hS]
    exact Submodule.zero_mem _
  exact (IsLocalRing.notMem_maximalIdeal.mpr hun) hp_mem

/-- **`p ∉ 𝔮` makes `p` a unit of the ring of integers of `K_𝔮`.**  The residue field of
`𝔮.adicCompletionIntegers K` is `𝓞 K ⧸ 𝔮`, so `p` dies in the residue field only if `p ∈ 𝔮`. -/
lemma isUnit_natCast_adicCompletionIntegers_of_notMem
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hnot : (p : NumberField.RingOfIntegers K) ∉ 𝔮.asIdeal) :
    IsUnit (p : 𝔮.adicCompletionIntegers K) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
  intro h0
  obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists 𝔮
  have h1 : e (p : IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) =
      (p : NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) := map_natCast e.toRingHom p
  have h2 : (p : NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) = 0 := by
    rw [← h1, h0]
    exact map_zero e
  exact hnot (Ideal.Quotient.eq_zero_iff_mem.mp h2)

/-- **A primitive `p`-th root of unity in `K_𝔮` forces `p` to divide the number of units of the
residue field**, provided `p` is a unit of `𝒪_κ`.  Indeed the reduction of `ζ_p` is a non-trivial
`p`-th root of unity of the (finite) residue field. -/
lemma dvd_natCard_residueUnits_of_exists_isPrimitiveRoot
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hnot : (p : NumberField.RingOfIntegers K) ∉ 𝔮.asIdeal)
    (hζ : ∃ ζ : 𝔮.adicCompletion K, IsPrimitiveRoot ζ p) :
    p ∣ Nat.card (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := hζ
  have hmem : ζ ∈ 𝔮.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers]
    exact NK.LocalInputs.PowerQuotient.val_le_one_of_pow_eq_one hp.ne_zero hζ.pow_eq_one
  have hpow : (⟨ζ, hmem⟩ : 𝔮.adicCompletionIntegers K) ^ p = 1 := by
    apply Subtype.ext; push_cast; exact hζ.pow_eq_one
  have hne : (⟨ζ, hmem⟩ : 𝔮.adicCompletionIntegers K) ≠ 1 := by
    intro h; exact hζ.ne_one hp.one_lt (Subtype.ext_iff.mp h)
  have hunit : IsUnit ((p : ℕ) : 𝔮.adicCompletionIntegers K) :=
    isUnit_natCast_adicCompletionIntegers_of_notMem 𝔮 hnot
  have hres : IsLocalRing.residue (𝔮.adicCompletionIntegers K)
      (⟨ζ, hmem⟩ : 𝔮.adicCompletionIntegers K) ≠ 1 :=
    residue_ne_one_of_pow_eq_one hunit hpow hne
  have hζunit : IsUnit (⟨ζ, hmem⟩ : 𝔮.adicCompletionIntegers K) := by
    refine isUnit_iff_exists.mpr
      ⟨(⟨ζ, hmem⟩ : 𝔮.adicCompletionIntegers K) ^ (p - 1), ?_, ?_⟩
    · rw [← pow_succ', Nat.sub_add_cancel hp.one_le]
      exact hpow
    · rw [mul_comm, ← pow_succ', Nat.sub_add_cancel hp.one_le]
      exact hpow
  set u : (𝔮.adicCompletionIntegers K)ˣ := hζunit.unit
  have huval : (u : 𝔮.adicCompletionIntegers K) = ⟨ζ, hmem⟩ := IsUnit.unit_spec hζunit
  have hup : u ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, huval, Units.val_one]
    exact hpow
  set y : (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ :=
    Units.map (IsLocalRing.residue (𝔮.adicCompletionIntegers K)).toMonoidHom u
  have hyp : y ^ p = 1 := by
    have h := congrArg
      (Units.map (IsLocalRing.residue (𝔮.adicCompletionIntegers K)).toMonoidHom) hup
    simpa [y] using h
  have hyne : y ≠ 1 := by
    intro h
    have h2 : IsLocalRing.residue (𝔮.adicCompletionIntegers K)
        (u : 𝔮.adicCompletionIntegers K) = 1 := by
      have hh := congrArg
        (fun z : (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ =>
          (z : IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))) h
      simpa [y] using hh
    rw [huval] at h2
    exact hres h2
  have hord : orderOf y = p := orderOf_eq_prime hyp hyne
  rw [← hord]
  exact orderOf_dvd_natCard y

/-! ## The three pieces of the cardinality computation -/

/-- **The principal units `U¹ = 1 + 𝔪` are `p`-divisible when `p` is a unit of `𝒪_κ`.**
Hensel's lemma applied to `X ^ p - u` at the simple root `1` (the derivative there is `p`, a
unit) lifts `1` modulo `𝔪` to a genuine `p`-th root of `u`. -/
lemma principalUnits_le_pow_range (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    {p : ℕ} (hp : p.Prime) (hunit : IsUnit (p : 𝔮.adicCompletionIntegers K)) :
    NK.LocalInputs.principalUnits K 𝔮 ≤
      (powMonoidHom p : (𝔮.adicCompletionIntegers K)ˣ →*
        (𝔮.adicCompletionIntegers K)ˣ).range := by
  letI : HenselianLocalRing (𝔮.adicCompletionIntegers K) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
      (R := NumberField.RingOfIntegers K) (K := K) 𝔮
  intro u hu
  have hu1 : ((u : 𝔮.adicCompletionIntegers K) - 1) ∈
      IsLocalRing.maximalIdeal (𝔮.adicCompletionIntegers K) :=
    (NK.LocalInputs.mem_principalUnits_iff K 𝔮 u).mp hu
  have hresu : IsLocalRing.residue (𝔮.adicCompletionIntegers K)
      (u : 𝔮.adicCompletionIntegers K) = 1 := by
    have h0 := (IsLocalRing.residue_eq_zero_iff ((u : 𝔮.adicCompletionIntegers K) - 1)).mpr hu1
    rw [map_sub, map_one] at h0
    exact sub_eq_zero.mp h0
  obtain ⟨b, hbpow, hbres⟩ :=
    Commons.RingTheory.Henselian.kummer_root_lift (R := 𝔮.adicCompletionIntegers K) p
      u.isUnit hunit 1 (by rw [one_pow]; exact hresu.symm)
  have hbunit : IsUnit b := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hbres]
    exact one_ne_zero
  refine MonoidHom.mem_range.mpr ⟨hbunit.unit, ?_⟩
  rw [powMonoidHom_apply]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  exact hbpow

/-- **The `p`-power quotient of `κˣ` is `p` times that of `𝒪_κˣ`** (the valuation is `ℤ`, which
has no `p`-torsion). -/
lemma natCard_kummerQuot_eq_mul_units (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    {p : ℕ} (hp : p.Prime) :
    Nat.card ((𝔮.adicCompletion K)ˣ ⧸
        (powMonoidHom p : (𝔮.adicCompletion K)ˣ →* (𝔮.adicCompletion K)ˣ).range) =
      p * Nat.card ((𝔮.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom p : (𝔮.adicCompletionIntegers K)ˣ →*
          (𝔮.adicCompletionIntegers K)ˣ).range) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have htor : ∀ h : Multiplicative ℤ, h ^ p = 1 → h = 1 := fun h hh =>
    Commons.NumberTheory.NumberField.Completion.pow_right_injective_zint hp.ne_zero
      (by rw [hh, one_pow])
  have hmain := Commons.NumberTheory.NumberField.Completion.natCard_quot_powMonoidHom_eq_mul
    (Commons.NumberTheory.NumberField.Completion.unitsValLog (𝔮.adicCompletion K))
    (Commons.NumberTheory.NumberField.Completion.unitsValLog_adicCompletion_surjective K 𝔮)
    p htor
  rw [hmain, Commons.NumberTheory.NumberField.Completion.natCard_multiplicative_int_quot_pow]
  congr 1
  have hker : (Commons.NumberTheory.NumberField.Completion.unitsValLog
      (𝔮.adicCompletion K)).ker = (𝔮.adicCompletionIntegers K).unitGroup :=
    Commons.NumberTheory.NumberField.Completion.adicUnitsVal_eq_unitGroup K 𝔮
  rw [hker]
  exact NK.LocalInputs.PowerQuotient.natCard_quot_powMonoidHom_eq_of_mulEquiv p
    (ValuationSubring.unitGroupMulEquiv (𝔮.adicCompletionIntegers K))

/-- **The `p`-power quotient of `𝒪_κˣ` is that of the units of the residue field**, because the
kernel `U¹` of the reduction consists of `p`-th powers (`principalUnits_le_pow_range`). -/
lemma natCard_units_quot_eq_residueUnits (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    {p : ℕ} (hp : p.Prime) (hunit : IsUnit (p : 𝔮.adicCompletionIntegers K)) :
    Nat.card ((𝔮.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom p : (𝔮.adicCompletionIntegers K)ˣ →*
          (𝔮.adicCompletionIntegers K)ˣ).range) =
      Nat.card ((IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ ⧸
        (powMonoidHom p : (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ →*
          (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ).range) :=
  NK.Mine.natCard_quot_powMonoidHom_eq_of_ker_le_pow
    (Units.map (IsLocalRing.residue (𝔮.adicCompletionIntegers K)).toMonoidHom)
    (Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion 𝔮)
    p (principalUnits_le_pow_range 𝔮 hp hunit)

/-- **The `p`-power quotient of the residue field units is `p`**, since `p` divides their
cardinality: the units of a finite field form a finite cyclic group, and the cokernel of the
`p`-th power map on a finite cyclic group is the explicitly computed `Nat.gcd p #G`. -/
lemma natCard_residueUnits_quot_pow_of_dvd (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ) :
    Nat.card ((IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ ⧸
        (powMonoidHom p : (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ →*
          (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ).range) = p := by
  haveI hfin : Finite (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔮
  haveI : Fintype (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) := Fintype.ofFinite _
  haveI : Fintype ((IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ) := Fintype.ofFinite _
  haveI : IsCyclic ((IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ) := inferInstance
  rw [Commons.GroupTheory.SpecificGroups.Cyclic.card_quotient_powMonoidHom
    (G := (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ),
    ← Nat.card_eq_fintype_card, Nat.card_units]
  exact Nat.gcd_eq_left (by rwa [Nat.card_units] at hdvd)

/-! ## The main statement -/

theorem localIndex_finite_notMem {K : Type} [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hnot : (p : NumberField.RingOfIntegers K) ∉ 𝔮.asIdeal)
    (hζ : ∃ ζ : 𝔮.adicCompletion K, IsPrimitiveRoot ζ p) :
    Nat.card ((𝔮.adicCompletion K)ˣ ⧸
      (powMonoidHom p : (𝔮.adicCompletion K)ˣ →* (𝔮.adicCompletion K)ˣ).range)
      = p ^ 2 := by
  have hunit : IsUnit (p : 𝔮.adicCompletionIntegers K) :=
    isUnit_natCast_adicCompletionIntegers_of_notMem 𝔮 hnot
  have hdvd : p ∣ Nat.card (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ :=
    dvd_natCard_residueUnits_of_exists_isPrimitiveRoot 𝔮 hp hnot hζ
  calc Nat.card ((𝔮.adicCompletion K)ˣ ⧸
        (powMonoidHom p : (𝔮.adicCompletion K)ˣ →* (𝔮.adicCompletion K)ˣ).range)
      = p * Nat.card ((𝔮.adicCompletionIntegers K)ˣ ⧸
          (powMonoidHom p : (𝔮.adicCompletionIntegers K)ˣ →*
            (𝔮.adicCompletionIntegers K)ˣ).range) :=
        natCard_kummerQuot_eq_mul_units 𝔮 hp
    _ = p * Nat.card ((IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ ⧸
          (powMonoidHom p : (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ →*
            (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K))ˣ).range) := by
        rw [natCard_units_quot_eq_residueUnits 𝔮 hp hunit]
    _ = p * p := by rw [natCard_residueUnits_quot_pow_of_dvd 𝔮 hp hdvd]
    _ = p ^ 2 := by rw [pow_two]

end

end NK.GlobalCFTdeep.SecondInequality
