import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletion_intCast_eq_padicValInt
import Submission.Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow
import Submission.NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg
import Submission.NK.LocalReciprocityLubinTate.Units.natCard_units_quot_pow_maximalIdeal

/-!
# The additive cover of the `M`-th power of the maximal ideal by `e·f` elements

For a number field `K`, a finite prime `q` of `K` of residue characteristic `2`, and `M ≥ 1`, the
additive group `𝔪^M` of the ring of integers `R = 𝓞_{K_q}` of the `q`-adic completion is covered by
`e·f = [K_q : ℚ_2]` elements modulo multiplication by `2`:

`NK.NUV2.BallCoverAux.ballCover_two'`.

The pieces are:

* `v_two_eq`: `v 2 = exp (-e)` for the normalised valuation `v` of `K_q`, via
  `val_adicCompletionMap_eq_pow` and the computation of `v` on `ℚ_2`;
* `span_two_eq`: `Ideal.span {2} = 𝔪^e`;
* `isDVR`: `𝓞_{K_q}` is a discrete valuation ring;
* `natCard_residueField_eq`, `natCard_layer`: `#(𝓞/𝔪) = 2^f` and `#(𝔪^M/𝔪^{M+e}) = 2^{e f}`;
* `ballCover_two'`: the cover, from the fact that `𝔪^M/𝔪^{M+e}` is a `𝔽₂`-vector space of
  dimension `e·f` (a `ZMod 2`-module with a basis of that size).
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField WithZero
open IsDedekindDomain

namespace NK.NUV2.BallCoverAux

variable {K : Type} [Field K] [NumberField K]


variable {K : Type} [Field K] [NumberField K]

theorem v_two_eq (q : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hlies : q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})) :
    Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (2 : q.adicCompletion K) =
      WithZero.exp (-(q.asIdeal.ramificationIdx ℤ : ℤ)) := by
  let Q := NK.LocalInputs.primeBelow K q
  have hQ : q.asIdeal.LiesOver Q.asIdeal := NK.LocalInputs.primeBelow_liesOver K q
  have hram : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) =
      q.asIdeal.ramificationIdx ℤ :=
    NK.LocalInputs.Degree.ramificationIdx_rat_eq q.asIdeal q.ne_bot
  have hmemQ : (2 : NumberField.RingOfIntegers ℚ) ∈ Q.asIdeal := by
    rw [NK.LocalInputs.primeBelow_asIdeal]
    rw [Ideal.mem_under]
    rw [show (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K))
        (2 : NumberField.RingOfIntegers ℚ) = (2 : NumberField.RingOfIntegers K) from
      map_natCast _ 2]
    have h2 : (2 : ℤ) ∈ q.asIdeal.under ℤ := by
      rw [← hlies.over]
      exact Ideal.mem_span_singleton_self _
    have h3 : (algebraMap ℤ (NumberField.RingOfIntegers K)) (2 : ℤ) ∈ q.asIdeal :=
      (Ideal.mem_under (A := ℤ) (P := q.asIdeal)).mp h2
    simpa using h3
  have hvalQ : Valued.v (R := Q.adicCompletion ℚ) (Γ₀ := WithZero (Multiplicative ℤ))
      (2 : Q.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
    have h := Commons.NumberTheory.NumberField.Completion.val_adicCompletion_intCast_eq_padicValInt
      Q 2 (by norm_num) hmemQ 2 (by norm_num)
    have hself : padicValInt 2 (2 : ℤ) = 1 := by
      simpa using (padicValInt_self (p := 2))
    rw [hself] at h
    norm_num at h
    simpa using h
  have hφ := Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
    (K := ℚ) (L := K) Q q hQ (2 : Q.adicCompletion ℚ)
  rw [hram] at hφ
  rw [show (Commons.RingTheory.Henselian.adicCompletionMap Q q hQ) (2 : Q.adicCompletion ℚ)
      = (2 : q.adicCompletion K) from map_natCast _ 2, hvalQ] at hφ
  rw [hφ, ← WithZero.exp_nsmul]
  congr 1
  simp

theorem span_two_eq (q : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hlies : q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})) :
    Ideal.span {(2 : q.adicCompletionIntegers K)} =
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ (q.asIdeal.ramificationIdx ℤ) := by
  have hval2 := v_two_eq (K := K) q hlies
  obtain ⟨π, hπv, hπmax⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_adicCompletionIntegers q
  have hπe : Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((π ^ q.asIdeal.ramificationIdx ℤ : q.adicCompletionIntegers K) : q.adicCompletion K)) =
      WithZero.exp (-(q.asIdeal.ramificationIdx ℤ : ℤ)) := by
    rw [show ((π ^ q.asIdeal.ramificationIdx ℤ : q.adicCompletionIntegers K) : q.adicCompletion K)
        = (π : q.adicCompletion K) ^ (q.asIdeal.ramificationIdx ℤ) from by push_cast; ring,
      Valuation.map_pow, hπv, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hspan : Ideal.span {(π ^ q.asIdeal.ramificationIdx ℤ : q.adicCompletionIntegers K)} =
      Ideal.span {(2 : q.adicCompletionIntegers K)} :=
    Commons.NumberTheory.NumberField.Completion.span_eq_span_of_valuation_eq _
      (by rw [hπe]; exact hval2.symm)
      (by rw [hπe]; exact WithZero.exp_ne_zero (a := -(q.asIdeal.ramificationIdx ℤ : ℤ)))
  rw [← hspan, ← Ideal.span_singleton_pow, hπmax]



open scoped NumberField WithZero
open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

theorem isDVR (q : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hlies : q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})) :
    IsDiscreteValuationRing (q.adicCompletionIntegers K) := by
  have hspan := span_two_eq (K := K) q hlies
  have hepos : 0 < q.asIdeal.ramificationIdx ℤ := Ideal.ramificationIdx_pos _ ℤ
  have h2mem : (2 : q.adicCompletionIntegers K) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) := by
    have hmem : (2 : q.adicCompletionIntegers K) ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ (q.asIdeal.ramificationIdx ℤ) := by
      rw [← hspan]
      exact Ideal.mem_span_singleton_self _
    exact Ideal.pow_le_self hepos.ne' hmem
  have h2ne : (2 : q.adicCompletionIntegers K) ≠ 0 := by
    intro h
    have hzero : (2 : q.adicCompletion K) = 0 := by
      have h1 : ((2 : q.adicCompletionIntegers K) : q.adicCompletion K) = 0 := by
        rw [h]; rfl
      have hcoe : ((2 : q.adicCompletionIntegers K) : q.adicCompletion K) =
          (2 : q.adicCompletion K) := SubringClass.coe_natCast (q.adicCompletionIntegers K) 2
      rw [hcoe] at h1
      exact h1
    have hv := v_two_eq (K := K) q hlies
    rw [hzero] at hv
    refine WithZero.exp_ne_zero (a := -(q.asIdeal.ramificationIdx ℤ : ℤ)) ?_
    rw [← hv]
    exact (Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))).map_zero
  exact IsDiscreteValuationRing.mk (fun hbot => h2ne (by
    have : (2 : q.adicCompletionIntegers K) ∈ (⊥ : Ideal (q.adicCompletionIntegers K)) :=
      hbot ▸ h2mem
    simpa using this))



open scoped NumberField WithZero
open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

/-- The residue cardinality of `𝓞_{K_q}` is `2^f`. -/
theorem natCard_residueField_eq (q : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hlies : q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})) :
    Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers K)) =
      2 ^ (q.asIdeal.inertiaDeg ℤ) := by
  rw [Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletionIntegers_eq_natCard_quotient
    K q]
  have hmax : (Ideal.span {(2 : ℤ)}).IsMaximal := by
    rw [← Ideal.irreducible_iff_isMaximal_span_singleton (p := (2 : ℤ)) (by norm_num)]
    exact (Nat.prime_iff_prime_int.mp (by norm_num : Nat.Prime 2)).irreducible
  haveI := hmax
  haveI : q.asIdeal.IsMaximal := HeightOneSpectrum.isMaximal q
  haveI : Finite (NumberField.RingOfIntegers K ⧸ q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient q.ne_bot
  rw [Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {(2 : ℤ)}) q.asIdeal]
  letI : Field (ℤ ⧸ Ideal.span {(2 : ℤ)}) := Ideal.Quotient.field _
  have hfin : Module.Finite (ℤ ⧸ Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers K ⧸ q.asIdeal) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ℤ ⧸ Ideal.span {(2 : ℤ)})
    (V := NumberField.RingOfIntegers K ⧸ q.asIdeal)]
  have hcard : Nat.card (ℤ ⧸ Ideal.span {(2 : ℤ)}) = 2 :=
    (Nat.card_congr (Int.quotientSpanNatEquivZMod 2).toEquiv).trans (by simp)
  rw [hcard]

/-- **The layer cardinality** `#(𝔪^M/𝔪^{M+e}) = 2^{e·f}`. -/
theorem natCard_layer (q : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hlies : q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})) (M : ℕ) :
    Nat.card ↥(Submodule.map
      (Submodule.mkQ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^
        (M + q.asIdeal.ramificationIdx ℤ)))
      ((IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M :
        Ideal (q.adicCompletionIntegers K)) : Submodule (q.adicCompletionIntegers K)
          (q.adicCompletionIntegers K))) =
      2 ^ (q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ) := by
  haveI hDVR : IsDiscreteValuationRing (q.adicCompletionIntegers K) := isDVR q hlies
  have hq := natCard_residueField_eq (K := K) q hlies
  have hqne : Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers K)) ≠ 0 := by
    rw [hq]
    exact pow_ne_zero _ (by norm_num)
  have hmain := Submodule.card_quotient_mul_card_quotient
    (R := q.adicCompletionIntegers K) (M := q.adicCompletionIntegers K)
    ((IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M : Ideal _) : Submodule _ _)
    ((IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^
      (M + q.asIdeal.ramificationIdx ℤ) : Ideal _) : Submodule _ _)
    (Ideal.pow_le_pow_right (Nat.le_add_right M (q.asIdeal.ramificationIdx ℤ)))
  rw [NK.LocalReciprocityLubinTate.Units.natCard_quot_maximalIdeal_pow
        (q.adicCompletionIntegers K) M,
      NK.LocalReciprocityLubinTate.Units.natCard_quot_maximalIdeal_pow
        (q.adicCompletionIntegers K) (M + q.asIdeal.ramificationIdx ℤ)] at hmain
  have hp : Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers K)) ^
        (M + q.asIdeal.ramificationIdx ℤ) =
      Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers K)) ^ M *
        Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers K)) ^
          (q.asIdeal.ramificationIdx ℤ) := pow_add _ _ _
  rw [hp] at hmain
  have hQ : Nat.card ↥(Submodule.map
      (Submodule.mkQ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^
        (M + q.asIdeal.ramificationIdx ℤ)))
      ((IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M : Ideal _) : Submodule _ _)) =
      Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers K)) ^
        (q.asIdeal.ramificationIdx ℤ) := by
    refine Nat.eq_of_mul_eq_mul_right (n := _) (k := _)
      (pow_pos (Nat.pos_of_ne_zero hqne) M) ?_
    rw [mul_comm (Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers K)) ^
      (q.asIdeal.ramificationIdx ℤ))
      (Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers K)) ^ M)]
    exact hmain
  rw [hQ, hq, ← pow_mul, mul_comm]


open scoped NumberField WithZero
open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

/-- The cover of `𝔪^M` by `e·f` elements modulo `2`. -/
theorem ballCover_two' (q : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hlies : q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)})) (M : ℕ) :
    ∃ b : Fin (q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ) →
        q.adicCompletionIntegers K,
      (∀ i, b i ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M) ∧
      (∀ x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M,
        ∃ z ∈ AddSubgroup.closure (Set.range b),
        ∃ y ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers K) ^ M,
          x = z + (2 : q.adicCompletionIntegers K) * y) := by
  classical
  let R := q.adicCompletionIntegers K
  let e := q.asIdeal.ramificationIdx ℤ
  let f := q.asIdeal.inertiaDeg ℤ
  have hspan : Ideal.span {(2 : R)} = IsLocalRing.maximalIdeal R ^ e :=
    span_two_eq (K := K) q hlies
  have h2M : IsLocalRing.maximalIdeal R ^ (M + e) =
      Ideal.span {(2 : R)} * IsLocalRing.maximalIdeal R ^ M := by
    rw [show M + e = e + M from Nat.add_comm M e, pow_add, hspan]
  let N : Ideal R := IsLocalRing.maximalIdeal R ^ (M + e)
  let Q : Submodule R (R ⧸ N) :=
    Submodule.map (Submodule.mkQ N) (IsLocalRing.maximalIdeal R ^ M : Ideal R)
  have hQcard : Nat.card ↥Q = 2 ^ (e * f) := by
    have h := natCard_layer (K := K) q hlies M
    simpa [Q, N, e, f, R] using h
  have hexp : ∀ x : ↥Q, (2 : ℕ) • x = 0 := by
    rintro ⟨y, hy⟩
    obtain ⟨y₀, hy₀, hyval⟩ := (Submodule.mem_map).mp hy
    have hmem : (2 : R) * y₀ ∈ N := by
      rw [show N = Ideal.span {(2 : R)} * IsLocalRing.maximalIdeal R ^ M from h2M]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hy₀
    apply Subtype.ext
    show (2 : ℕ) • y = (0 : R ⧸ N)
    rw [← hyval, ← map_nsmul, nsmul_eq_mul]
    exact (Submodule.Quotient.mk_eq_zero N).mpr hmem
  letI : Module (ZMod 2) ↥Q := AddCommGroup.zmodModule (G := ↥Q) hexp
  have hsmulval : ∀ (c : ZMod 2) (x : ↥Q), c • x = c.val • x := fun c x => rfl
  haveI : Finite ↥Q := Nat.finite_of_card_ne_zero (by
    rw [hQcard]
    exact pow_ne_zero _ (by norm_num))
  haveI : Module.Finite (ZMod 2) ↥Q := Module.Finite.of_finite
  haveI : Module.Free (ZMod 2) ↥Q := Module.Free.of_divisionRing _ _
  have hfinrank : Module.finrank (ZMod 2) ↥Q = e * f := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥Q)
    have h2 : Nat.card (ZMod 2) = 2 := by simp
    rw [h2, hQcard] at h
    exact (Nat.pow_right_injective (by norm_num) h).symm
  let b : Module.Basis (Fin (e * f)) (ZMod 2) ↥Q :=
    (Module.finBasis (ZMod 2) ↥Q).reindex (finCongr hfinrank)
  choose b' hb'mem hb'val using fun i => (Submodule.mem_map).mp (b i).2
  refine ⟨b', fun i => hb'mem i, ?_⟩
  intro x hx
  have hxQ : Submodule.mkQ N x ∈ Q := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  set xbar : ↥Q := ⟨Submodule.mkQ N x, hxQ⟩ with hxbar
  have hxmem : xbar ∈ Submodule.span (ZMod 2) (Set.range b) := by
    rw [b.span_eq]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hxmem
  have hcoef : (∑ i, ((c i) • b i : ↥Q)) = xbar := hc
  have hsum2 : (∑ i, (c i).val • (b i : R ⧸ N)) = Submodule.mkQ N x := by
    have h1 := congrArg (fun z : ↥Q => (Submodule.subtype Q) z) hcoef
    rw [map_sum] at h1
    have h2 : ∀ i, (Submodule.subtype Q) ((c i) • b i) = (c i).val • (b i : R ⧸ N) := by
      intro i
      rw [hsmulval (c i) (b i)]
      rfl
    rw [Finset.sum_congr rfl fun i _ => h2 i] at h1
    simpa [hxbar] using h1
  have hclass : Submodule.mkQ N (∑ i, (c i).val • b' i) = Submodule.mkQ N x := by
    rw [map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hsum2
    rw [map_nsmul, hb'val i]
  have hmemN : x - ∑ i, (c i).val • b' i ∈ N := by
    refine (Submodule.Quotient.mk_eq_zero N).mp ?_
    show (Submodule.mkQ N) (x - ∑ i, (c i).val • b' i) = 0
    rw [map_sub, hclass, sub_self]
  have hmem2 : x - ∑ i, (c i).val • b' i ∈
      IsLocalRing.maximalIdeal R ^ M * Ideal.span {(2 : R)} := by
    rw [show IsLocalRing.maximalIdeal R ^ M * Ideal.span {(2 : R)} = N from by
      rw [show N = Ideal.span {(2 : R)} * IsLocalRing.maximalIdeal R ^ M from h2M, Ideal.mul_comm]]
    exact hmemN
  obtain ⟨y, hy, hyval⟩ := (Ideal.mem_mul_span_singleton).mp hmem2
  refine ⟨∑ i, (c i).val • b' i, ?_, y, hy, ?_⟩
  · refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.nsmul_mem _ ?_ _
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  · rw [show x = (∑ i, (c i).val • b' i) + (x - ∑ i, (c i).val • b' i) from by ring, ← hyval]
    ring

end NK.NUV2.BallCoverAux
