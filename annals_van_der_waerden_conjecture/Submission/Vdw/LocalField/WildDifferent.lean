import Submission.Vdw.LocalField.KapTrace
import Submission.Vdw.LocalField.RamificationCompat
import Submission.Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le
import Submission.Commons.NumberTheory.NumberField.different_not_pow_dvd_of_wild_witness
open Classical
open IsLocalRing
open IsDedekindDomain
open UniqueFactorizationMonoid
open scoped NumberField WithZero Valued
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-!
# WildDifferent — the per-prime wild different bound (S1 gate), foundation

GOAL (recorded in Roadmap Session-54/95; the hypothesis `hwild` of
`WildBound.discrVal_le_wild`): for every prime `p` and every maximal ideal
`P` of `𝓞 K` over `(p)`,

    m_P := (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P
         ≤ e_P − 1 + e_P · v_p(e_P),        e_P := P.ramificationIdx ℤ

— the classical wild bound on the different exponent.  Combined with
`WildBound.discrVal_le_wild` this closes the S1 small-prime cap
`v_p(|discr K|) ≤ [K:ℚ]·(1 + log_p [K:ℚ])` for the Case-I small-prime
split (Roadmap Session-54 §1: RestrictedSieve → discrVal_le_wild →
CaseIDisc → squarefull tail).

THE EISENSTEIN ROUTE (Roadmap Session-54 §4 + Session-95 addendum):
localize at `P`; let `K_P := kpAdic p P`, `W := ℚ_p(ζ)` the unramified
subfield of degree `f := P.inertiaDeg ℤ` (`Wk p P α`), and `ϖ` a
uniformizer of `K_P` over `𝒪_W` (ϖ generates `𝔪_{K_P}`; the DVR
uniformizer `uniformizer p P` of `kpInt p P`).  Then

1.  `f_ϖ := minpoly (Wk p P α) ϖ` is **Eisenstein** over `𝒪_W` of degree
    `e := P.ramificationIdx ℤ` (coefficients in `𝔪_W = OW_ker`, constant
    term a uniformizer of `𝒪_W`; `[K_P : W] = e` is `finrank_kpAdic_over_Wk_eq_ramIdx`);
2.  writing `f_ϖ = X^e + Σ_{i<e} c_i X^i`, the derivative terms
    `i·c_i·ϖ^{i−1}` (`c_e := 1`) have **pairwise distinct valuations
    modulo e** (since `c_i ∈ W` has `v_P(c_i) ≡ 0 mod e` and
    `v_P(ϖ^{i-1}) = i−1`), so
    `v_P(f_ϖ'(ϖ)) = min_{i ≤ e} v_P(i·c_i·ϖ^{i−1}) ≤ v_P(e·ϖ^{e−1}) = e·v_p(e) + e−1`
    (the e-term is present with `c_e = 1`; no cancellation — exactly the
    content of `sum_exact_pow_min` below);
3.  the local conductor-different formula `𝔡_{K_P/ℚ_p} = 𝔡_{K_P/W}`
    (unramified base) with `(f_ϖ'(ϖ)) = 𝔠·𝔡`, `𝔠 ⊆ 𝔒_{K_P}` a conductor,
    gives `m_P = v_P(𝔡_{K_P/ℚ_p}) ≤ v_P(f_ϖ'(ϖ))`, and completion/loc-
    alization transports the count to the global `differentIdeal`.

WHAT IS IN THIS FILE (foundation of step 2/3, all 0 sorries):

* generic adic-filtration lemmas (comm ring + ideal + Finset):
  `sum_mem_pow_of_all`, `sum_not_mem_pow_of_others_small` (two-level
  separation), `sum_exact_pow_min` (no cancellation among exactly-valued
  terms; a commons version was requested in parallel as
  `Commons.RingTheory.Ideal.sum_exact_pow_min`);
* kpInt uniformizer filtration facts (`𝔪 := maximalIdeal (kpInt p P)`,
  `ϖ := uniformizer p P`): `uniformizer_mem_maximalIdeal`,
  `uniformizer_not_mem_sq` (`ϖ ∈ 𝔪 \ 𝔪²`),
  `uniformizer_pow_mem_maximalIdeal_pow` (`ϖ^k ∈ 𝔪^k`),
  `uniformizer_pow_not_mem_maximalIdeal_succ` (`ϖ^k ∉ 𝔪^{k+1}`),
  `unit_mul_uniformizer_pow_mem_maximalIdeal_pow` /
  `unit_mul_uniformizer_pow_not_mem_succ` (for a unit `u` of `kpInt`,
  `u·ϖ^k ∈ 𝔪^k \ 𝔪^{k+1}` — the exact filtration degree of a monomial
  with unit coefficient).

NEXT (dependency-ordered): (a) the ramification-index-at-norm level:
`‖p‖ = ‖ϖ‖^e` (i.e. `(p)·kpInt = 𝔪^e`), so the integer `e = ϖ^e·unit`
factors; (b) the embedding `𝒪_W ⊆ kpInt` with `𝔪_W·kpInt = 𝔪^e` and the
minimal polynomial of `ϖ` over `W` (`f_ϖ`, monic degree `e`, coefficients
integral); (c) Eisenstein property of `f_ϖ` over `𝒪_W`; (d) the
local-conductor/different and completion transport.  Do not `sorry`-state
any of these until each is proved.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-! ## Generic adic-filtration lemmas -/

/-- A Finset sum of elements each lying in `I ^ (a j)`, with all exponents
`≥ N`, lies in `I ^ N`. -/
lemma sum_mem_pow_of_all {R : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} (s : Finset ι) (x : ι → R) (a : ι → ℕ) (N : ℕ)
    (hN : ∀ j ∈ s, N ≤ a j)
    (hmem : ∀ j ∈ s, x j ∈ I ^ a j) :
    (∑ j ∈ s, x j) ∈ I ^ N := by
  classical
  refine Submodule.sum_mem (I ^ N) ?_
  intro j hj
  exact (Ideal.pow_le_pow_right (hN j hj)) (hmem j hj)

/-- **Two-level separation**: if one term of the sum is outside `I^(N+1)`
and all the others are inside it, then the whole sum is outside `I^(N+1)`
(no cancellation can drag the distinguished term into the smaller ideal). -/
lemma sum_not_mem_pow_of_others_small {R : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → R) {j₀ : ι} (hj₀ : j₀ ∈ s)
    (N : ℕ)
    (hbig : x j₀ ∉ I ^ (N + 1))
    (hsmall : ∀ j ∈ s, j ≠ j₀ → x j ∈ I ^ (N + 1)) :
    (∑ j ∈ s, x j) ∉ I ^ (N + 1) := by
  classical
  intro hsum
  apply hbig
  have hsplit : (∑ j ∈ s.erase j₀, x j) + x j₀ = ∑ j ∈ s, x j := by
    simpa using (Finset.sum_erase_add (s := s) (f := x) (a := j₀) hj₀)
  have hmem : x j₀ = (∑ j ∈ s, x j) - (∑ j ∈ s.erase j₀, x j) := by
    rw [← hsplit]
    abel
  rw [hmem]
  exact Submodule.sub_mem _ hsum (Submodule.sum_mem (I ^ (N + 1)) (by
    intro j hj
    have hje : j ≠ j₀ := (Finset.mem_erase.mp hj).1
    have hjs : j ∈ s := (Finset.mem_erase.mp hj).2
    exact hsmall j hjs hje))

/-- **No cancellation among exactly-valued terms**: a Finset sum of elements
each lying exactly in `I^(a j)` (in, not beyond), with the exponents having a
unique minimum at `j₀`, lies in `I^(a j₀)` but not in `I^(a j₀ + 1)`. -/
lemma sum_exact_pow_min {R : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → R) (a : ι → ℕ)
    {j₀ : ι} (hj₀ : j₀ ∈ s)
    (hmem : ∀ j ∈ s, x j ∈ I ^ a j)
    (hnot : ∀ j ∈ s, x j ∉ I ^ (a j + 1))
    (hmin : ∀ j ∈ s, a j₀ ≤ a j)
    (hstrict : ∀ j ∈ s, j ≠ j₀ → a j₀ < a j) :
    (∑ j ∈ s, x j) ∈ I ^ a j₀ ∧ (∑ j ∈ s, x j) ∉ I ^ (a j₀ + 1) := by
  classical
  constructor
  · exact sum_mem_pow_of_all I s x a (a j₀) (fun j hj => hmin j hj) hmem
  · apply sum_not_mem_pow_of_others_small I s x hj₀ (a j₀) (hnot j₀ hj₀)
    intro j hj hne
    have ha : a j₀ + 1 ≤ a j := Nat.succ_le_of_lt (hstrict j hj hne)
    exact (Ideal.pow_le_pow_right ha) (hmem j hj)

/-! ## kpInt uniformizer filtration facts -/

/-- The chosen uniformizer of `kpInt` lies in the maximal ideal. -/
lemma uniformizer_mem_maximalIdeal (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    uniformizer p P ∈ maximalIdeal (kpInt p P) := by
  rw [maximalIdeal_eq_span_uniformizer]
  exact Submodule.mem_span_singleton_self _

/-- The uniformizer does NOT lie in the square of the maximal ideal:
`ϖ ∈ 𝔪 \ 𝔪²` (a uniformizer has exact valuation 1). -/
lemma uniformizer_not_mem_sq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    uniformizer p P ∉ (maximalIdeal (kpInt p P)) ^ 2 := by
  classical
  intro hmem
  have hnorm : ‖uniformizer p P‖ ≤ ‖uniformizer p P‖ ^ 2 :=
    (mem_maximalIdeal_pow_iff_norm_le p P (uniformizer p P) 2).mp hmem
  have hlt : ‖uniformizer p P‖ ^ 2 < ‖uniformizer p P‖ := by
    simpa using (pow_lt_pow_right_of_lt_one₀ (uniformizer_norm_pos p P)
      (uniformizer_norm_lt_one p P) (by norm_num : (1 : ℕ) < 2))
  exact (lt_irrefl _ (lt_of_le_of_lt hnorm hlt))

/-- The uniformizer power `ϖ^k` lies in `𝔪^k`. -/
lemma uniformizer_pow_mem_maximalIdeal_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (k : ℕ) :
    uniformizer p P ^ k ∈ (maximalIdeal (kpInt p P)) ^ k := by
  rw [maximalIdeal_pow_eq_span p P k]
  exact Submodule.mem_span_singleton_self _

/-- `ϖ^k ∉ 𝔪^{k+1}` for every `k`: the uniformizer powers have exact
filtration degree `k`. -/
lemma uniformizer_pow_not_mem_maximalIdeal_succ (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (k : ℕ) :
    uniformizer p P ^ k ∉ (maximalIdeal (kpInt p P)) ^ (k + 1) := by
  classical
  intro hmem
  have hnorm : ‖uniformizer p P ^ k‖ ≤ ‖uniformizer p P‖ ^ (k + 1) :=
    (mem_maximalIdeal_pow_iff_norm_le p P (uniformizer p P ^ k) (k + 1)).mp hmem
  rw [uniformizer_norm_pow] at hnorm
  have hlt : ‖uniformizer p P‖ ^ (k + 1) < ‖uniformizer p P‖ ^ k := by
    exact pow_lt_pow_right_of_lt_one₀ (uniformizer_norm_pos p P) (uniformizer_norm_lt_one p P)
      (Nat.lt_succ_self k)
  exact (lt_irrefl (‖uniformizer p P‖ ^ k)) (lt_of_le_of_lt hnorm hlt)

/-- For a unit `u` of the valuation ring, `u·ϖ^k` lies in `𝔪^k`. -/
lemma unit_mul_uniformizer_pow_mem_maximalIdeal_pow (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (u : (kpInt p P)ˣ) (k : ℕ) :
    ((u : kpInt p P) * uniformizer p P ^ k) ∈ (maximalIdeal (kpInt p P)) ^ k := by
  rw [maximalIdeal_pow_eq_span p P k]
  exact Ideal.mem_span_singleton.mpr ⟨(u : kpInt p P), by ring⟩

/-- For a unit `u` of the valuation ring, `u·ϖ^k` is NOT in `𝔪^{k+1}`
(`‖u‖ = 1`, so the norm is exactly `‖ϖ‖^k`): monomials with unit
coefficient have exact filtration degree `k`. -/
lemma unit_mul_uniformizer_pow_not_mem_succ (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (u : (kpInt p P)ˣ) (k : ℕ) :
    ((u : kpInt p P) * uniformizer p P ^ k) ∉ (maximalIdeal (kpInt p P)) ^ (k + 1) := by
  classical
  intro hmem
  have hnorm : ‖(u : kpInt p P) * uniformizer p P ^ k‖ ≤ ‖uniformizer p P‖ ^ (k + 1) :=
    (mem_maximalIdeal_pow_iff_norm_le p P ((u : kpInt p P) * uniformizer p P ^ k) (k + 1)).mp hmem
  have hnorm' : ‖(u : kpInt p P) * uniformizer p P ^ k‖ = ‖uniformizer p P‖ ^ k := by
    rw [norm_mul, uniformizer_norm_pow, norm_eq_one_of_unit p P u]
    simp
  rw [hnorm'] at hnorm
  have hlt : ‖uniformizer p P‖ ^ (k + 1) < ‖uniformizer p P‖ ^ k := by
    exact pow_lt_pow_right_of_lt_one₀ (uniformizer_norm_pos p P) (uniformizer_norm_lt_one p P)
      (Nat.lt_succ_self k)
  exact (lt_irrefl (‖uniformizer p P‖ ^ k)) (lt_of_le_of_lt hnorm hlt)

/-! ## Sub-stone (a): the extension of the base maximal ideal is the
top maximal ideal to the ramification-index power

For the tower `ℤ → QpInt p → kpInt p P` (`QpInt p = ℤ_[p]` the base
valuation ring, `kpInt p P` the valuation ring of the completion `K_P` at
the prime `P | (p)` of `𝓞 K`), with

    mR := maximalIdeal (QpInt p)      ( = (p)·QpInt,  `qpIntMaximalIdeal_eq_span_p`)
    mS := maximalIdeal (kpInt p P)    ( = P·kpInt, the top uniformizer)
    e  := P.ramificationIdx ℤ

this section proves

* `int_p_ne_zero` — the integer `p` is nonzero in `kpInt p P` (so it has a
  DVR factorization);
* `algebraMap_qpInt_injective` — the inclusion `QpInt → kpInt` is injective
  (torsion-freeness of `kpInt` over the domain `QpInt`);
* `span_unit_mul` — a unit times a generator spans the same principal ideal;
* `count_maximalIdeal_pow_self` — `count mS (mS^m) = m` for every `m`
  (via `Ideal.count_normalizedFactors_eq`, the uniformizer power `ϖ^m`
  being exactly of filtration degree `m`);
* `count_maximalIdeal_map` — `count mS (mR.map …) = e`
  (`ramificationIdx_eq_normalizedFactors_count` at `QpInt → kpInt` +
  `ramificationIdx_compat` — the completed-tower ramification index equals
  the global `P.ramificationIdx ℤ`);
* **`int_uniformizer_eq`** — the DVR factorization of `p`:
  `∃ u : (kpInt p P)ˣ, (p : kpInt p P) = u · ϖ^e` (the exponent `m` of the
  abstract DVR decomposition is tied to `e` by counting `mS` in the two
  expressions of the same ideal `mR.map`);
* **`mR_map_eq_mS_pow_ramIdx`** — the ideal identity
  `mR.map (algebraMap (QpInt p) (kpInt p P)) = mS ^ P.ramificationIdx ℤ`
  (equivalently `(p)·kpInt = 𝔪^e`).

This is WildDifferent sub-stone (a) (Roadmap Session-96): it makes the
integer `e` factor in `kpInt` as `e = p^a·e' = (ϖ^e·u)^a·e'` with `e'` a
unit (for the exact-filtration computation of the Eisenstein-derivative
`e`-term `v_P(e·ϖ^{e−1}) = e·v_p(e) + e−1` of the next sub-stones).

The proof of `int_uniformizer_eq`: `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`
gives `p = u·ϖ^m` for some `m` (`int_p_ne_zero`); `span{p} = mS^m`
(`span_unit_mul` + `maximalIdeal_pow_eq_span`), and also
`span{p} = mR.map` (`test-map` step via `qpIntMaximalIdeal_eq_span_p` +
`Ideal.map_span`); counting `mS` gives `m = e` from
`count_maximalIdeal_map` and `count_maximalIdeal_pow_self`.
-/

/-- The inclusion `QpInt p → kpInt p P` is injective: `kpInt` is
torsion-free over the integral domain `QpInt p`, so a nonzero scalar
annihilating `1` would be zero. -/
lemma algebraMap_qpInt_injective (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Function.Injective (algebraMap (QpInt p) (kpInt p P)) := by
  classical
  have htf : Module.IsTorsionFree (QpInt p) (kpInt p P) := kpInt_torsionFree p P
  intro a b hab
  have hsmul : a • (1 : kpInt p P) = b • (1 : kpInt p P) := by
    rw [Algebra.smul_def, Algebra.smul_def, hab]
  have hsub : (a - b) • (1 : kpInt p P) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hsmul
  rw [smul_eq_zero] at hsub
  rcases hsub with h | h
  · exact sub_eq_zero.mp h
  · exact False.elim (one_ne_zero h)

/-- The natural number `p` is nonzero in the ℚ_p-adic numbers (its image
under the injective ℚ-algebra map of the completion is the nonzero
rational `p`). -/
lemma qpAdic_natCast_p_ne_zero (p : ℕ) [Fact (Nat.Prime p)] : (p : QpAdic p) ≠ 0 := by
  intro hz
  have hinj : Function.Injective (algebraMap ℚ (QpAdic p)) := RingHom.injective _
  have hcast : (p : QpAdic p) = algebraMap ℚ (QpAdic p) (p : ℚ) := by
    exact (map_natCast (algebraMap ℚ (QpAdic p)) p).symm
  have hq : (p : ℚ) = 0 := hinj (by rw [← hcast]; exact hz)
  exact (Rat.cast_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out (p := Nat.Prime p))))) hq

/-- The integer `p` is nonzero in the valuation ring `kpInt p P` of the
completion (via the injective `QpInt → kpInt` inclusion and
`qpAdic_natCast_p_ne_zero`). -/
lemma int_p_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (p : kpInt p P) ≠ 0 := by
  classical
  intro hz
  have hpx : algebraMap (QpInt p) (kpInt p P) ((p : ℤ) : QpInt p) =
      ((p : ℤ) : kpInt p P) := by
    exact algebraMap_QpInt_int p P (p : ℤ)
  have hz0 : algebraMap (QpInt p) (kpInt p P) ((p : ℤ) : QpInt p) = 0 := by
    rw [hpx]
    exact hz
  have hz0' : algebraMap (QpInt p) (kpInt p P) ((p : ℤ) : QpInt p) =
      algebraMap (QpInt p) (kpInt p P) (0 : QpInt p) := by
    simpa using hz0
  have hq0 : ((p : ℤ) : QpInt p) = 0 := algebraMap_qpInt_injective p P hz0'
  have hq0' : ((p : ℤ) : QpAdic p) = 0 := by
    exact congrArg (fun z : QpInt p => (z : QpAdic p)) hq0
  exact qpAdic_natCast_p_ne_zero p hq0'

/-- A unit times a generator spans the same principal ideal. -/
lemma span_unit_mul {R : Type*} [CommSemiring R] (u : Rˣ) (v : R) :
    Ideal.span ({(u : R) * v} : Set R) = Ideal.span ({v} : Set R) := by
  classical
  ext z
  constructor
  · intro hz
    rcases (Ideal.mem_span_singleton.mp hz) with ⟨c, hc⟩
    refine Ideal.mem_span_singleton.mpr ⟨c * (u : R), ?_⟩
    rw [hc]
    ring
  · intro hz
    rcases (Ideal.mem_span_singleton.mp hz) with ⟨c, hc⟩
    refine Ideal.mem_span_singleton.mpr ⟨c * ((u⁻¹ : Rˣ) : R), ?_⟩
    rw [hc]
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- The image of the base maximal ideal is the principal ideal of the
integer `p` in the top valuation ring:
`mR.map (algebraMap (QpInt p) (kpInt p P)) = (p)·kpInt`. -/
lemma mR_map_eq_span_p (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (IsLocalRing.maximalIdeal (QpInt p)).map (algebraMap (QpInt p) (kpInt p P))
      = Ideal.span ({(p : kpInt p P)} : Set (kpInt p P)) := by
  classical
  let mR : Ideal (QpInt p) := IsLocalRing.maximalIdeal (QpInt p)
  let φ : QpInt p →+* kpInt p P := algebraMap (QpInt p) (kpInt p P)
  calc
    mR.map φ = (Ideal.span ({(p : QpInt p)} : Set (QpInt p))).map φ := by
      congr 1
      exact qpIntMaximalIdeal_eq_span_p p
    _ = Ideal.span ({(p : kpInt p P)} : Set (kpInt p P)) := by
      rw [Ideal.map_span, Set.image_singleton]
      apply congrArg Ideal.span
      apply congrArg Set.singleton
      rw [map_natCast φ p]

/-- The DVR factorization of the integer `p` in the valuation ring:
`(p : kpInt p P) = u · ϖ^m` for some exponent `m` and unit `u`
(`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`). -/
lemma int_dvr_factorization (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    ∃ (m : ℕ) (u : (kpInt p P)ˣ),
      (p : kpInt p P) = (u : kpInt p P) * uniformizer p P ^ m := by
  classical
  exact IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (p : kpInt p P)) (int_p_ne_zero p P) (uniformizer_irreducible p P)

/-- The maximal ideal `mS` occurs exactly `m` times in its own `m`-th
power: `count mS (mS^m) = m` (the uniformizer power `ϖ^m` generates `mS^m`
but not `mS^(m+1)`). -/
lemma count_maximalIdeal_pow_self (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (m : ℕ) :
    (normalizedFactors ((maximalIdeal (kpInt p P)) ^ m)).count (maximalIdeal (kpInt p P)) = m := by
  classical
  let mS : Ideal (kpInt p P) := maximalIdeal (kpInt p P)
  have hle : mS ^ m ≤ mS ^ m := le_rfl
  have hlt : ¬ mS ^ m ≤ mS ^ (m + 1) := by
    intro h
    have hmem : uniformizer p P ^ m ∈ mS ^ (m + 1) := by
      exact h (uniformizer_pow_mem_maximalIdeal_pow p P m)
    exact (uniformizer_pow_not_mem_maximalIdeal_succ p P m) (by simpa [mS] using hmem)
  have hc := Ideal.count_normalizedFactors_eq (p := mS) (x := mS ^ m) (n := m) hle hlt
  simpa [mS] using hc

/-- The maximal ideal `mS` occurs in the extended base maximal ideal exactly
`e := P.ramificationIdx ℤ` times: `count mS (mR.map …) = e` (the
ramification index of the completed tower — equal to the global index by
`ramificationIdx_compat` — is by definition this count). -/
lemma count_maximalIdeal_map (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (normalizedFactors ((maximalIdeal (QpInt p)).map (algebraMap (QpInt p) (kpInt p P)))).count
        (maximalIdeal (kpInt p P)) = P.ramificationIdx ℤ := by
  classical
  let mR : Ideal (QpInt p) := maximalIdeal (QpInt p)
  let mS : Ideal (kpInt p P) := maximalIdeal (kpInt p P)
  haveI hSL : mS.LiesOver mR := by
    simpa [mS, mR] using (mS_liesOver_mR p P)
  have hp0 : mR.map (algebraMap (QpInt p) (kpInt p P)) ≠ ⊥ := by
    intro hb
    have hxmem : (p : kpInt p P) ∈
        (maximalIdeal (QpInt p)).map (algebraMap (QpInt p) (kpInt p P)) := by
      have hm := mR_map_eq_span_p p P
      rw [hm]
      exact Submodule.mem_span_singleton_self _
    have hmem0 : (p : kpInt p P) ∈ (⊥ : Ideal (kpInt p P)) := by
      simpa [mR] using (by rw [hb] at hxmem; exact hxmem)
    exact int_p_ne_zero p P (Ideal.mem_bot.mp hmem0)
  have hc := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (R := QpInt p) (S := kpInt p P) (p := mR) (q := mS) hp0
  have hcompat := ramificationIdx_compat p P
  rw [← hcompat]
  simpa [mS, mR] using hc.symm

/-- **The DVR factorization of `p` at the ramification-index exponent**:
`(p : kpInt p P) = u · ϖ^e` with `e := P.ramificationIdx ℤ`.  The abstract
DVR decomposition exponent `m` of `int_dvr_factorization` is identified
with `e` by counting the prime `mS` in the two expressions of the same
ideal `mR.map` (= `span{p}` = `mS^m`). -/
theorem int_uniformizer_eq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    ∃ u : (kpInt p P)ˣ,
      (p : kpInt p P) = (u : kpInt p P) * uniformizer p P ^ P.ramificationIdx ℤ := by
  classical
  rcases int_dvr_factorization p P with ⟨m, u, hx⟩
  have hspan : Ideal.span ({(p : kpInt p P)} : Set (kpInt p P)) =
      (maximalIdeal (kpInt p P)) ^ m := by
    calc
      Ideal.span ({(p : kpInt p P)} : Set (kpInt p P))
          = Ideal.span ({(u : kpInt p P) * uniformizer p P ^ m} : Set (kpInt p P)) := by rw [hx]
      _ = Ideal.span ({(uniformizer p P ^ m)} : Set (kpInt p P)) := span_unit_mul u _
      _ = (maximalIdeal (kpInt p P)) ^ m := by
            rw [maximalIdeal_pow_eq_span p P m]
  have hm_eq_span : (maximalIdeal (QpInt p)).map (algebraMap (QpInt p) (kpInt p P)) =
      (maximalIdeal (kpInt p P)) ^ m := by
    rw [mR_map_eq_span_p p P]
    exact hspan
  have hm : m = P.ramificationIdx ℤ := by
    have hc1 : (normalizedFactors ((maximalIdeal (QpInt p)).map (algebraMap (QpInt p) (kpInt p P)))).count
        (maximalIdeal (kpInt p P)) = m := by
      rw [hm_eq_span]
      exact count_maximalIdeal_pow_self p P m
    exact (((count_maximalIdeal_map p P).symm).trans hc1).symm
  refine ⟨u, ?_⟩
  rw [hm] at hx
  exact hx

/-- **The extension of the base maximal ideal is the top maximal ideal to
the ramification-index power**:
`mR.map (algebraMap (QpInt p) (kpInt p P)) = mS ^ P.ramificationIdx ℤ`
— equivalently `(p)·kpInt = 𝔪^e` with `e := P.ramificationIdx ℤ`.  Follows
from `int_uniformizer_eq`: `mR.map = span{p} = span{u·ϖ^e} = span{ϖ^e} =
mS^e`. -/
theorem mR_map_eq_mS_pow_ramIdx (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (maximalIdeal (QpInt p)).map (algebraMap (QpInt p) (kpInt p P))
      = (maximalIdeal (kpInt p P)) ^ P.ramificationIdx ℤ := by
  classical
  rcases int_uniformizer_eq p P with ⟨u, hx⟩
  calc
    (maximalIdeal (QpInt p)).map (algebraMap (QpInt p) (kpInt p P))
        = Ideal.span ({(p : kpInt p P)} : Set (kpInt p P)) := mR_map_eq_span_p p P
    _ = Ideal.span ({(u : kpInt p P) * uniformizer p P ^ P.ramificationIdx ℤ} : Set (kpInt p P)) := by
          rw [hx]
    _ = Ideal.span ({(uniformizer p P ^ P.ramificationIdx ℤ)} : Set (kpInt p P)) := span_unit_mul u _
    _ = (maximalIdeal (kpInt p P)) ^ P.ramificationIdx ℤ := by
          rw [maximalIdeal_pow_eq_span p P (P.ramificationIdx ℤ)]


/-- **The convergence engine**: if `x ∈ 𝔪` then `ϖ^n·x ∈ 𝔪^(n+1)` for every
`n` (write `x = c·ϖ` in `𝔪 = (ϖ)`, then `ϖ^n·c·ϖ = c·ϖ^(n+1)` in
`𝔪^(n+1) = (ϖ^(n+1))`).  This is the step that moves a member of the
`n`-th ideal power one level up after multiplying by a uniformizer-power —
the engine of the 𝒪_W[ϖ]-partial-sum approximation of Route (I) for
`K_P = W(ϖ)` (Roadmap Session-103). -/
lemma uniformizer_mul_mem_maximalIdeal_pow_succ (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (n : ℕ) (x : kpInt p P)
    (hx : x ∈ maximalIdeal (kpInt p P)) :
    uniformizer p P ^ n * x ∈ (maximalIdeal (kpInt p P)) ^ (n + 1) := by
  classical
  rw [maximalIdeal_eq_span_uniformizer p P] at hx
  rcases (Ideal.mem_span_singleton.mp hx) with ⟨c, hc⟩
  rw [maximalIdeal_pow_eq_span p P (n + 1)]
  refine Ideal.mem_span_singleton.mpr ⟨c, ?_⟩
  rw [hc]
  simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]


/-! ## (f)-target reformulation: the wild bound in divisibility and witness form

The S1 gate is the single per-prime statement (`wild_different_count_le`,
consumed by `WildBound.discrVal_le_wild`):

    m_P := (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P
         ≤ e_P − 1 + e_P · v_p(e_P),        e_P := P.ramificationIdx ℤ.

Via the power-divisibility ↔ count bridge
(`Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le`)
this is EQUIVALENT to the divisibility form `¬ P^(e·(v_p(e)+1)) ∣ 𝔡`
(`wild_count_le_iff_not_pow_dvd`, mirroring the tame-case interface
`TamePrep.different_count_le_iff_not_pow_dvd`), and the divisibility form
follows from a wild trace witness at level `v_p(e)` (fleet L78
`Commons.NumberTheory.NumberField.different_not_pow_dvd_of_wild_witness`):
`wild_count_le_of_wild_witness`.  These pin down the exact statement that
the local conductor-different transport (sub-stone (f)) must deliver.
-/

/-- count-form ⟺ divisibility-form: `m_P ≤ e−1+e·v_p(e)` iff
`¬ P^(e·(v_p(e)+1)) ∣ 𝔡`. -/
theorem wild_count_le_iff_not_pow_dvd (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P
        ≤ P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) ↔
      ¬ P ^ (P.ramificationIdx ℤ * (padicValNat p (P.ramificationIdx ℤ) + 1)) ∣
          differentIdeal ℤ (𝓞 K) := by
  classical
  have hδ : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
  have hpos : 0 < P.ramificationIdx ℤ := Ideal.ramificationIdx_pos P ℤ
  haveI : P.IsPrime := ‹P.IsMaximal›.isPrime
  have heq : P.ramificationIdx ℤ * (padicValNat p (P.ramificationIdx ℤ) + 1)
      = P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + P.ramificationIdx ℤ := by
    ring
  constructor
  · intro hle hpe
    have hge : P.ramificationIdx ℤ * (padicValNat p (P.ramificationIdx ℤ) + 1) ≤
        (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P :=
      (Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le (K := K) P
        (differentIdeal ℤ (𝓞 K)) hδ (P.ramificationIdx ℤ * (padicValNat p (P.ramificationIdx ℤ) + 1))).mp hpe
    rw [heq] at hge
    omega
  · intro hnot
    by_contra hle
    have hge0 : P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + P.ramificationIdx ℤ ≤
        (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P := by omega
    have hge : P.ramificationIdx ℤ * (padicValNat p (P.ramificationIdx ℤ) + 1) ≤
        (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P := by
      rw [heq]
      exact hge0
    exact hnot ((Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le (K := K) P
      (differentIdeal ℤ (𝓞 K)) hδ (P.ramificationIdx ℤ * (padicValNat p (P.ramificationIdx ℤ) + 1))).mpr hge)

/-- The divisibility-form wild bound follows from a wild witness at level
`v_p(e_P)`: `y ∈ Q^(v_p(e)+1)` whose integer trace is not divisible by
`p^(v_p(e)+1)` (L78
`Commons.NumberTheory.NumberField.different_not_pow_dvd_of_wild_witness`). -/
theorem wild_count_le_of_wild_witness (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (Q : Ideal (𝓞 K)) (hsup : P ⊔ Q = ⊤)
    (hspl : (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) =
        P ^ P.ramificationIdx ℤ * Q)
    (y : 𝓞 K) (hyQ : (y : 𝓞 K) ∈ Q ^ (padicValNat p (P.ramificationIdx ℤ) + 1))
    (hy : ¬ (p : ℤ) ^ (padicValNat p (P.ramificationIdx ℤ) + 1) ∣
        Algebra.intTrace ℤ (𝓞 K) y) :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P
      ≤ P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) := by
  classical
  have hnp := Commons.NumberTheory.NumberField.different_not_pow_dvd_of_wild_witness
    (K := K) p P Q hsup hspl (padicValNat p (P.ramificationIdx ℤ)) y hyQ hy
  -- hnp : ¬ P ^ (e·(v+1)) ∣ 𝔡
  exact (wild_count_le_iff_not_pow_dvd p P).2 hnp


end
end Submission.Vdw.LocalField
