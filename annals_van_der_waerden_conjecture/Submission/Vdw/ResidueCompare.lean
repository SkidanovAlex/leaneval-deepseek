import Mathlib
import Submission.Vdw.PolyIndex
import Submission.Vdw.TameExponent
import Submission.Vdw.DifferentChar
import Submission.Vdw.DedekindIndex
import Submission.Commons.NumberTheory.NumberField.residue_rad_degree_le_inertia_sum

open scoped BigOperators NumberField Classical
open Polynomial UniqueFactorizationMonoid

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Residue comparison (Bhargava's Lemma 24, step iii) — the residue-side bridge

**Mathematical content.**  For a number field `K`, an integral generator `θ`
(with `f := minpoly ℤ θ` of degree `m = [K : ℚ]`) and a prime `p`, the
*finiteness algebra* `A := F_p[x]/(f̄)` (where `f̄ := f mod p`) has
`dim_{F_p}(A/rad A) = deg rad(f̄)`, while `C := 𝒪_K/(p𝒪_K)` has
`dim_{F_p}(C/rad C) = Σ_{P|p} f_P` (inertia degrees).  The inclusion of the
order `ℤ[θ] ⊆ 𝒪_K` (lying over + residue-degree monotonicity on maximal
ideals over `p`) yields the **unconditional core inequality**
`deg rad(f̄) ≤ Σ_{P|p} f_P` (shared-commons theorem
`Commons.NumberTheory.NumberField.residue_rad_degree_le_inertia_sum`,
proved via quotient-cardinalities `p^deg-rad ≤ |(𝒪_K/(p))/rad|`), and hence
the **residue comparison**

    polyIndex(f̄)  ≥  Σ_{P|p} f_P·(e_P − 1)          (unconditional, all p)

via the fundamental identity `Σ e_P·f_P = [K : ℚ]`.  For tame primes
(`p ∤ e_P` for all `P | p`, automatic when `p > [K : ℚ]`) the tame different
theorem (`discr_val_tame_of_gt_degree`) identifies the right-hand sum with
`v_p(|disc K|)`, giving **Lemma 24 (field version)**:

    p > [K : ℚ]  ⟹  polyIndex(f̄) ≥ v_p(|Disc K|).

These are the residue-side facts that Case I's per-discriminant sieve (the
`indexClass` congruence conditions) consumes.

All theorems are proven (0 sorries).
-/

namespace Submission.Vdw

noncomputable section

/-- The prime ideal `(p)` of `ℤ`. -/
abbrev pZ (p : ℕ) : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)

/-- Finset-sum of `φ` over `primesOverFinset` equals the type-sum over
`pZ.primesOver (𝓞 K)`. -/
theorem sum_primesOverFinset_eq_sum_type {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)] (φ : Ideal (𝓞 K) → ℕ) :
    (∑ P ∈ IsDedekindDomain.primesOverFinset (pZ p) (𝓞 K), φ P) =
      ∑ q : (pZ p).primesOver (𝓞 K), φ q.1 := by
  classical
  have hp0 : (pZ p) ≠ ⊥ := by
    dsimp [pZ]
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (Nat.Prime.ne_zero (Fact.out (p := Nat.Prime p)))
  symm
  refine Finset.sum_bij (fun q _ => (q.1 : Ideal (𝓞 K))) ?_ ?_ ?_ ?_
  · intro q hq
    exact (IsDedekindDomain.mem_primesOverFinset_iff (p := pZ p) (B := 𝓞 K) hp0).mpr q.2
  · intro q hq r hr hqr
    apply Subtype.ext
    exact hqr
  · intro P hP
    have hP' : P ∈ (pZ p).primesOver (𝓞 K) :=
      (IsDedekindDomain.mem_primesOverFinset_iff (p := pZ p) (B := 𝓞 K) hp0).mp hP
    refine ⟨⟨P, hP'⟩, Finset.mem_univ _, rfl⟩
  · intro q hq
    rfl

/-- The core residue comparison in type-sum form:
`deg rad(f̄) ≤ Σ_{q | p} f_q` where `f̄ = minpoly θ mod p`. -/
theorem residue_rad_degree_le_inertia_sum_type {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact (Nat.Prime p)]
    (hdeg : 1 ≤ (minpoly ℤ θ).natDegree)
    (hgen : (minpoly ℤ θ).natDegree = Module.finrank ℚ K) :
    (UniqueFactorizationMonoid.radical ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))).natDegree ≤
      ∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ := by
  classical
  rw [← sum_primesOverFinset_eq_sum_type (K := K) p (fun P : Ideal (𝓞 K) => P.inertiaDeg ℤ)]
  exact Commons.NumberTheory.NumberField.residue_rad_degree_le_inertia_sum (K := K) θ p hdeg hgen

/-- Fundamental identity (type-sum form): `Σ_{q|p} e_q·f_q = [K : ℚ]`. -/
theorem sum_ramification_inertia_type {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)] :
    (∑ q : (pZ p).primesOver (𝓞 K), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) =
      Module.finrank ℚ K := by
  classical
  exact (Ideal.sum_ramification_inertia_eq_finrank (R := ℤ) (S := 𝓞 K) (p := pZ p)).trans
    (NumberField.RingOfIntegers.rank (K := K))

/-- Rearrangement (type-sum form): `Σ_{q|p} f_q(e_q − 1) = [K:ℚ] − Σ_{q|p} f_q`. -/
theorem sum_inertia_mul_ramIdx_sub_one_type {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)] :
    (∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ - 1)) =
      Module.finrank ℚ K -
        (∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ) := by
  classical
  let T := (pZ p).primesOver (𝓞 K)
  have hpos (q : T) : 1 ≤ q.1.ramificationIdx ℤ :=
    Nat.succ_le_of_lt (Ideal.ramificationIdx_pos (q := q.1) ℤ)
  have hsplit : (∑ q : T, q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ - 1)) +
      (∑ q : T, q.1.inertiaDeg ℤ) = ∑ q : T, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    conv_rhs => rw [mul_comm]
    exact Nat.sub_add_cancel (Nat.le_mul_of_pos_right (q.1.inertiaDeg ℤ)
      (Nat.succ_le_iff.mp (hpos q)))
  have hle : (∑ q : T, q.1.inertiaDeg ℤ) ≤
      ∑ q : T, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    calc
      (∑ q : T, q.1.inertiaDeg ℤ) = ∑ q : T, 1 * q.1.inertiaDeg ℤ := by simp
      _ ≤ ∑ q : T, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
        apply Finset.sum_le_sum
        intro q hq
        exact Nat.mul_le_mul_right _ (hpos q)
  have hsum : (∑ q : T, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) = Module.finrank ℚ K := by
    simpa [T] using sum_ramification_inertia_type (K := K) p
  rw [← hsum]
  exact ((Nat.sub_eq_iff_eq_add hle).mpr hsplit.symm).symm

/-- The reduction of a monic polynomial under a ring hom is monic of the same degree. -/
theorem monic_natDegree_map {R S : Type*} [Semiring R] [Semiring S] [Nontrivial S]
    (φ : R →+* S) {f : R[X]} (hf : f.Monic) :
    (f.map φ).Monic ∧ (f.map φ).natDegree = f.natDegree := by
  constructor
  · simpa using hf.map φ
  · exact hf.natDegree_map φ

/-- **Unconditional residue comparison (Bhargava Lemma 24, step iii).**
For an integral generator `θ` of a number field `K` of degree `m` and any prime
`p`, the index over `F_p` of the reduction of `minpoly θ` is at least
`Σ_{P | p} f_P·(e_P − 1)`.  No tameness and no `p ∤ exponent` hypothesis. -/
theorem residue_index_ge_ramification {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact (Nat.Prime p)]
    (hdeg : 1 ≤ (minpoly ℤ θ).natDegree)
    (hgen : (minpoly ℤ θ).natDegree = Module.finrank ℚ K) :
    (∑ q : (pZ p).primesOver (𝓞 K),
        q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ - 1)) ≤
      polyIndex (F := ZMod p) ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  classical
  let hbar : (ZMod p)[X] := (minpoly ℤ θ).map (Int.castRingHom (ZMod p))
  have hmon : (minpoly ℤ θ).Monic := minpoly.monic θ.isIntegral
  have hnd : hbar.natDegree = (minpoly ℤ θ).natDegree :=
    (monic_natDegree_map (Int.castRingHom (ZMod p)) hmon).2
  have hS : (UniqueFactorizationMonoid.radical hbar).natDegree ≤
      ∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ :=
    residue_rad_degree_le_inertia_sum_type (K := K) θ p hdeg hgen
  have hsum : (minpoly ℤ θ).natDegree -
        (∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ) ≤
      polyIndex (F := ZMod p) hbar := by
    dsimp [polyIndex]
    rw [hnd]
    exact Nat.sub_le_sub_left hS (minpoly ℤ θ).natDegree
  have hre : (∑ q : (pZ p).primesOver (𝓞 K),
        q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ - 1)) =
      (minpoly ℤ θ).natDegree -
        (∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ) := by
    rw [hgen]
    exact sum_inertia_mul_ramIdx_sub_one_type (K := K) p
  rw [← hre] at hsum
  simpa [hbar] using hsum

/-- Every prime factor of the different lying over `p` is a prime of `𝒪_K`
over `p` (membership in `primesOverFinset`). -/
theorem mem_primesOverFinset_of_mem_diffFactors {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)] {P : Ideal (𝓞 K)}
    (hP : P ∈ (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset) :
    P.LiesOver (pZ p) → P ∈ IsDedekindDomain.primesOverFinset (pZ p) (𝓞 K) := by
  intro hLies
  have hPm : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K)) := Multiset.mem_toFinset.mp hP
  have hδ : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
  have hmax : P.IsMaximal :=
    Commons.NumberTheory.NumberField.isMaximal_of_mem_normalizedFactors hδ hPm
  have hp0 : (pZ p) ≠ ⊥ := by
    dsimp [pZ]
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (Nat.Prime.ne_zero (Fact.out (p := Nat.Prime p)))
  exact (IsDedekindDomain.mem_primesOverFinset_iff (p := pZ p) (B := 𝓞 K) hp0).mpr
    ⟨hmax.isPrime, hLies⟩

/-- The tame different-sum (over factors of 𝔡 over p) does not exceed the sum
over all primes of `𝒪_K` over `p` (same weights `f_P·(e_P−1) ≥ 0`). -/
theorem diffFilter_sum_le_primesOver_sum {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact (Nat.Prime p)] :
    (∑ P ∈ (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
        (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))),
          P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1)) ≤
      ∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ - 1) := by
  classical
  let s := IsDedekindDomain.primesOverFinset (pZ p) (𝓞 K)
  let w := fun P : Ideal (𝓞 K) => P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1)
  have hsub : ((normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
      (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))) ⊆ s := by
    intro P hP
    exact mem_primesOverFinset_of_mem_diffFactors (K := K) p
      (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2
  have hle : (∑ P ∈ ((normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
      (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))), w P) ≤ ∑ P ∈ s, w P := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro x hx hxA; exact Nat.zero_le _)
  rw [← sum_primesOverFinset_eq_sum_type (K := K) p w]
  simpa [s, w] using hle

/-- **Lemma 24 (field version).**  For `p > [K : ℚ]` prime (so `p` is tame at
every prime of `K`), the index over `F_p` of the reduction of `minpoly θ` is at
least `v_p(|Disc K|)`. -/
theorem lemma24_field_index_ge_discrVal {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact (Nat.Prime p)]
    (hdeg : 1 ≤ (minpoly ℤ θ).natDegree)
    (hgen : (minpoly ℤ θ).natDegree = Module.finrank ℚ K)
    (hgt : Module.finrank ℚ K < p) :
    padicValNat p (NumberField.discr K).natAbs ≤
      polyIndex (F := ZMod p) ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  classical
  have h1 := residue_index_ge_ramification (K := K) θ p hdeg hgen
  have h2 := diffFilter_sum_le_primesOver_sum (K := K) p
  have h2' := diffFilter_sum_le_primesOver_sum (K := K) p
  have h3 := discr_val_tame_of_gt_degree (K := K) p hgt
  rw [h3]
  exact le_trans h2' h1

/-! ## The `Kpoly f` instantiation (Lemma 24 over the field of `f`)

For `f ∈ ℤ[X]` monic irreducible of degree `n` (so `Kpoly f = ℚ[x]/(f)` is a
number field), with `θ = ⟨gen, ·⟩ : 𝓞 (Kpoly f)` the adjoined root, the
minimal polynomial over `ℤ` of `θ` is exactly `f`
(`minpoly_int_kpolyTheta_eq_f`, via `minpoly_kpoly_gen` + the
integrally-closed `ℤ ⊂ ℚ` comparison).  Combining that identification with
`lemma24_field_index_ge_discrVal` gives **Lemma 24 (field version) over
`Kpoly f`**: for `p > n`, `polyIndex` over `F_p` of `f mod p` is at least
`v_p(|Disc K_f|) = padicValNat p (fieldDisc f)` — the residue-side input of
Case I's per-discriminant sieve.
-/

section KpolyLemma24

/-- `θ := ⟨α, integral⟩` is the power-basis generator of `𝓞(Kpoly f)`. -/
noncomputable abbrev kpolyTheta (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] (hf : f.Monic) :
    𝓞 (Kpoly f) :=
  ⟨(kpolyPowerBasis f hf).gen, kpolyPowerBasis_gen_isIntegralInt f hf⟩

/-- The image of `θ` in `Kpoly f` is the power-basis generator. -/
theorem kpolyTheta_coe_gen (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] (hf : f.Monic) :
    ((kpolyTheta f hf : 𝓞 (Kpoly f)) : Kpoly f) = (kpolyPowerBasis f hf).gen := by
  rfl

/-- `φℚ = Int.castRingHom ℚ` (as ring homomorphisms `ℤ → ℚ`). -/
theorem phiQ_eq_intCastRingHom : φℚ = Int.castRingHom ℚ := by
  ext n
  rfl

/-- For the generator `θ` of `𝓞(Kpoly f)`, `minpoly ℤ θ = f`. -/
theorem minpoly_int_kpolyTheta_eq_f (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] (hf : f.Monic) :
    minpoly ℤ (kpolyTheta f hf) = f := by
  classical
  let θ : 𝓞 (Kpoly f) := kpolyTheta f hf
  have hqf : minpoly ℚ (θ : Kpoly f) = f.map φℚ := by
    rw [kpolyTheta_coe_gen f hf]
    exact minpoly_kpoly_gen f hf
  have hqf' : minpoly ℚ (θ : Kpoly f) = f.map (Int.castRingHom ℚ) := by
    simpa [phiQ_eq_intCastRingHom] using hqf
  have hzt := minpoly.isIntegrallyClosed_eq_field_fractions (R := ℤ) (K := ℚ) (L := Kpoly f)
    (s := θ) (NumberField.RingOfIntegers.isIntegral θ)
  have hz : minpoly ℚ (θ : Kpoly f) = (minpoly ℤ θ).map (Int.castRingHom ℚ) := by
    simpa [NumberField.RingOfIntegers.coe_eq_algebraMap] using hzt
  have hmap : (minpoly ℤ θ).map (Int.castRingHom ℚ) = f.map (Int.castRingHom ℚ) := by
    rw [← hz]
    exact hqf'
  exact (Polynomial.map_injective (Int.castRingHom ℚ) (by exact Int.cast_injective)) (by
    simpa [θ] using hmap)

/-- `[Kpoly f : ℚ] = natDegree f` (for monic `f`). -/
theorem finrank_kpoly_eq_natDegree (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] (hf : f.Monic) :
    Module.finrank ℚ (Kpoly f) = f.natDegree := by
  have hfin := (AdjoinRoot.isAdjoinRootMonic (f.map φℚ) (hf.map φℚ)).finrank
  rw [hfin]
  exact hf.natDegree_map (Int.castRingHom ℚ)

/-- **Lemma 24 (field version) over `Kpoly f`**: for `f` monic irreducible of
degree `n ≥ 1` and a prime `p > n`, the index over `F_p` of `f mod p` is at
least `v_p(|Disc K_f|) = padicValNat p (fieldDisc f)`. -/
theorem lemma24_field_Kpoly (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] (hf : f.Monic)
    (n : ℕ) (hn : f.natDegree = n) (hnpos : 1 ≤ n)
    (p : ℕ) [Fact (Nat.Prime p)] (hgt : n < p) :
    padicValNat p (fieldDisc f) ≤
      polyIndex (F := ZMod p) (f.map (Int.castRingHom (ZMod p))) := by
  classical
  let K := Kpoly f
  let θ : 𝓞 K := kpolyTheta f hf
  have hmin : minpoly ℤ θ = f := by
    simpa [θ] using minpoly_int_kpolyTheta_eq_f f hf
  have hdeg : 1 ≤ (minpoly ℤ θ).natDegree := by
    rw [hmin, hn]
    exact hnpos
  have hgen : (minpoly ℤ θ).natDegree = Module.finrank ℚ K := by
    rw [hmin]
    exact (finrank_kpoly_eq_natDegree f hf).symm
  have hgt' : Module.finrank ℚ K < p := by
    rw [finrank_kpoly_eq_natDegree f hf, hn]
    exact hgt
  have hL := lemma24_field_index_ge_discrVal (K := K) θ p hdeg hgen hgt'
  dsimp [fieldDisc]
  simpa [θ, hmin] using hL

end KpolyLemma24

end
end Submission.Vdw
