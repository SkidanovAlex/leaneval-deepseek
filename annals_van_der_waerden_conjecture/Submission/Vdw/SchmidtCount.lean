import Mathlib
import Submission.Vdw.PerFieldFibreAll
import Submission.Commons.NumberTheory.NumberField.exists_nonrational_house_le
import Submission.Commons.NumberTheory.NumberField.abs_trace_le_finrank_mul_house
import Submission.Commons.Algebra.Trace.trace_one_eq_finrank
import Submission.Commons.NumberTheory.NumberField.minpoly_coeff_le_pow_sub
import Submission.Commons.NumberTheory.NumberField.minpoly_nextCoeff_eq_zero_of_trace_eq_zero
import Submission.Commons.NumberTheory.NumberField.nonempty_algEquiv_of_minpoly_eq
import Submission.Commons.NumberTheory.Polynomial.prod_bound_schmidt
import Submission.Commons.NumberTheory.Polynomial.finite_monic_poly_coeff_le
import Submission.Commons.NumberTheory.Polynomial.ncard_monic_poly_coeff_le_free

open Polynomial Filter Asymptotics
open NumberField MeasureTheory Metric
open NumberField.mixedEmbedding
open scoped NumberField BigOperators Classical ENNReal NNReal
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Submission.Vdw

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

/-- From a non-rational element of small house, build a trace-zero one. -/
theorem exists_trace_zero_house_le (K : Type*) [Field K] [NumberField K]
    (hn : 2 ≤ Module.finrank ℚ K) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ Algebra.trace ℚ K ((a : K)) = 0 ∧
      NumberField.house ((a : K)) ≤ 2 ^ (2 * Module.finrank ℚ K + 6) *
        |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (2 * ((Module.finrank ℚ K : ℝ) - 1))) := by
  classical
  obtain ⟨b, hbne, hbnr, hbhouse⟩ :=
    Commons.NumberTheory.NumberField.exists_nonrational_house_le K hn
  set n : ℕ := Module.finrank ℚ K with hn_def
  set t : ℤ := Algebra.trace ℤ (𝓞 K) b with ht_def
  have hY1 : (1 : ℝ) ≤ |((NumberField.discr K : ℤ) : ℝ)| := by
    have h0 : (NumberField.discr K : ℤ) ≠ 0 := NumberField.discr_ne_zero K
    have h2 : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs h0
    have h3 : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast h2
    simpa using h3
  have htw : ((Algebra.trace ℚ K ((b : K)) : ℚ) : ℝ) = (t : ℝ) := by
    rw [ht_def, ← Algebra.coe_trace_int (K := K) (x := b)]
    norm_num
  have htbound : |(t : ℝ)| ≤ (n : ℝ) * NumberField.house ((b : K)) := by
    have h := Commons.NumberTheory.NumberField.abs_trace_le_finrank_mul_house (K := K) b
    rw [← htw, hn_def]
    exact h
  refine ⟨n • b - t • 1, ?_, ?_, ?_⟩
  · -- nonzero
    intro hzero
    apply hbnr
    have hc : (n : K) * (b : K) = (t : K) := by
      have hc0 := congrArg (fun x : 𝓞 K => (x : K)) hzero
      simp only [map_sub, map_mul, nsmul_eq_mul, map_one, map_intCast, mul_one,
        zsmul_eq_mul, map_natCast] at hc0
      exact sub_eq_zero.mp hc0
    have hnK : (n : K) ≠ 0 := by
      intro hcon
      have h0 : (n : ℚ) = 0 := (algebraMap ℚ K).injective (by simpa using hcon)
      have : n = 0 := by exact_mod_cast h0
      omega
    refine ⟨(t : ℚ) / (n : ℚ), ?_⟩
    have hq : algebraMap ℚ K ((t : ℚ) / (n : ℚ)) = (t : K) / (n : K) := by
      rw [map_div₀, map_intCast, map_natCast]
    rw [hq, div_eq_iff hnK, mul_comm]
    exact hc.symm
  · -- trace zero
    have h1 : Algebra.trace ℤ (𝓞 K) (n • b - t • 1) = 0 := by
      rw [map_sub, map_nsmul, map_zsmul, ht_def,
        Commons.Algebra.Trace.trace_one_eq_finrank, RingOfIntegers.rank]
      ring
    have h2 : Algebra.trace ℚ K (((n • b - t • 1 : 𝓞 K)) : K) = 0 := by
      rw [← Algebra.coe_trace_int (K := K) (x := n • b - t • 1), h1]
      norm_num
    exact h2
  · -- house bound
    have h1 : NumberField.house ((n • b - t • 1 : 𝓞 K) : K) ≤
        NumberField.house ((n : K) * (b : K)) + NumberField.house ((t : K) * (1 : K)) := by
      have hsub : (((n • b - t • 1 : 𝓞 K)) : K) = (n : K) * (b : K) - (t : K) * (1 : K) := by
        simp only [map_sub, map_mul, nsmul_eq_mul, map_one, map_intCast, mul_one,
          map_natCast, map_zsmul, zsmul_eq_mul]
      rw [hsub, sub_eq_add_neg]
      refine le_trans (NumberField.house_add_le _ _) (le_of_eq ?_)
      simp only [NumberField.house, map_neg, norm_neg]
    have h2 : NumberField.house ((n : K) * (b : K)) = (n : ℝ) * NumberField.house ((b : K)) := by
      rw [NumberField.house_nat_mul]
    have h3 : NumberField.house ((t : K) * (1 : K)) = |(t : ℝ)| := by
      rw [mul_one, NumberField.house_intCast, Int.cast_abs]
    refine le_trans h1 ?_
    rw [h2, h3]
    have hbnd := hbhouse
    have hY0 : (0 : ℝ) < |((NumberField.discr K : ℤ) : ℝ)| := lt_of_lt_of_le one_pos hY1
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by rw [hn_def]; exact Module.finrank_pos
      exact_mod_cast this
    have hpow1 : (1 : ℝ) ≤ |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (2 * ((n : ℝ) - 1))) :=
      Real.one_le_rpow hY1 (by
        have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h : (0 : ℝ) < (n : ℝ) - 1 := by linarith
        positivity)
    calc (n : ℝ) * NumberField.house ((b : K)) + |(t : ℝ)|
        ≤ (n : ℝ) * NumberField.house ((b : K)) + (n : ℝ) * NumberField.house ((b : K)) := by
          linarith [htbound]
      _ = 2 * (n : ℝ) * NumberField.house ((b : K)) := by ring
      _ ≤ 2 * (n : ℝ) * (2 ^ (n + 5) *
            |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (2 * ((n : ℝ) - 1)))) := by
          have h2n0 : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left hbnd h2n0
      _ ≤ 2 ^ (2 * n + 6) * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (2 * ((n : ℝ) - 1))) := by
          have hn2 : (n : ℝ) ≤ 2 ^ n := by
            have := Nat.lt_two_pow_self (n := n)
            exact_mod_cast (le_of_lt this)
          have hcoef : 2 * (n : ℝ) * 2 ^ (n + 5) ≤ 2 ^ (2 * n + 6) := by
            have h1 : (2:ℝ) * 2 ^ (n + 5) = 2 ^ (n + 6) := by
              rw [mul_comm, ← pow_succ]
            have e : 2 * (n : ℝ) * 2 ^ (n + 5) = (2 * 2 ^ (n + 5)) * (n : ℝ) := by ring
            rw [e, h1]
            calc (2:ℝ) ^ (n + 6) * (n : ℝ) ≤ 2 ^ (n + 6) * 2 ^ n :=
                  mul_le_mul_of_nonneg_left hn2 (by positivity)
              _ = 2 ^ (2 * n + 6) := by rw [← pow_add]; ring_nf
          calc 2 * (n : ℝ) * (2 ^ (n + 5) * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (2 * ((n : ℝ) - 1))))
              = (2 * (n : ℝ) * 2 ^ (n + 5)) *
                  |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (2 * ((n : ℝ) - 1))) := by ring
            _ ≤ 2 ^ (2 * n + 6) *
                  |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (2 * ((n : ℝ) - 1))) :=
                mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hY0.le _)




/-- **The per-class polynomial.** -/
lemma exists_classPoly (n H : ℕ) (hn : 1 ≤ n) (hnn : 2 ≤ n)
    (f : ↥(SubcaseI_P2 n H)) :
    ∃ P : ℤ[X], P.Monic ∧ P.natDegree = n ∧ P.coeff (n - 1) = 0 ∧
      (∀ i, i ≤ n → i ≠ n - 1 → |((P.coeff i : ℤ) : ℝ)| ≤
        2 ^ n * (2 ^ (2 * n + 6) *
          (subcaseI_P2_disc n H f : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n - i)) ∧
      (∃ y : Kpoly (f : ℤ[X]), Algebra.adjoin ℚ ({y} : Set (Kpoly (f : ℤ[X]))) = ⊤ ∧
        minpoly ℚ y = P.map φℚ) := by
  classical
  have hIrr : Irreducible (((f : ℤ[X])).map φℚ) := subcaseI_P2_irreducible n H hn f
  haveI : Fact (Irreducible (((f : ℤ[X])).map φℚ)) := ⟨hIrr⟩
  have hbox : (f : ℤ[X]) ∈ Box n H := subcaseI_P2_subset_Box n H f.2
  have hdeg : ((f : ℤ[X])).natDegree = n :=
    Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1
  have hfin : Module.finrank ℚ (Kpoly (f : ℤ[X])) = n := finrank_Kpoly hbox.1 hdeg
  obtain ⟨h, hprim, -⟩ := f.2.1.2
  obtain ⟨α, hαne, hαtr, hαhouse⟩ :=
    exists_trace_zero_house_le (Kpoly (f : ℤ[X])) (by rw [hfin]; omega)
  have hαhouse' : NumberField.house ((α : Kpoly (f : ℤ[X]))) ≤
      2 ^ (2 * n + 6) * |((NumberField.discr (Kpoly (f : ℤ[X])) : ℤ) : ℝ)| ^
        (1 / (2 * ((n : ℝ) - 1))) := by
    rw [hfin] at hαhouse
    exact hαhouse
  have hint : IsIntegral ℤ α := IsIntegralClosure.isIntegral ℤ (Kpoly (f : ℤ[X])) α
  have hdisc : ((subcaseI_P2_disc n H f : ℕ) : ℝ) =
      |((NumberField.discr (Kpoly (f : ℤ[X])) : ℤ) : ℝ)| := by
    rw [subcaseI_P2_disc]
    exact fieldDiscExp_coe (f := (f : ℤ[X]))
  have hαnr : ((α : Kpoly (f : ℤ[X]))) ∉
      Set.range (algebraMap ℚ (Kpoly (f : ℤ[X]))) := by
    rintro ⟨r, hr⟩
    apply hαne
    have htr : Algebra.trace ℚ (Kpoly (f : ℤ[X]))
        (algebraMap ℚ (Kpoly (f : ℤ[X])) r) =
        r * (Module.finrank ℚ (Kpoly (f : ℤ[X])) : ℚ) := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul,
        Commons.Algebra.Trace.trace_one_eq_finrank]
      rfl
    have htr0 : r * (Module.finrank ℚ (Kpoly (f : ℤ[X])) : ℚ) = 0 := by
      rw [← htr]
      rw [hr]
      exact hαtr
    rw [hfin] at htr0
    rcases mul_eq_zero.mp htr0 with h1 | h2
    · subst h1
      rw [map_zero] at hr
      exact Subtype.ext hr.symm
    · have hn0 : (n : ℚ) ≠ 0 := by
        have : (0 : ℕ) < n := by omega
        exact_mod_cast this.ne'
      exact absurd h2 hn0
  have hgen : Algebra.adjoin ℚ ({((α : Kpoly (f : ℤ[X])))} :
      Set (Kpoly (f : ℤ[X]))) = ⊤ :=
    adjoin_eq_top_of_galPrimitive hIrr hprim hαnr
  set P : ℤ[X] := minpoly ℤ α with hP
  have hPmonic : P.Monic := by
    rw [hP]
    exact minpoly.monic hint
  have hmap : minpoly ℚ ((α : Kpoly (f : ℤ[X]))) = P.map φℚ := by
    rw [hP]
    exact minpoly.isIntegrallyClosed_eq_field_fractions ℚ (Kpoly (f : ℤ[X])) hint
  have hIF : IntermediateField.adjoin ℚ ({((α : Kpoly (f : ℤ[X])))} :
      Set (Kpoly (f : ℤ[X]))) = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff).mpr hgen
  have hPdeg : P.natDegree = n := by
    have h1 : (minpoly ℚ ((α : Kpoly (f : ℤ[X])))).natDegree =
        Module.finrank ℚ (Kpoly (f : ℤ[X])) :=
      (Field.primitive_element_iff_minpoly_natDegree_eq (F := ℚ) _).mp hIF
    rw [hfin, hmap, hPmonic.natDegree_map] at h1
    exact h1
  have hPnext : P.coeff (n - 1) = 0 := by
    have h1 : P.nextCoeff = 0 := by
      rw [hP]
      exact Commons.NumberTheory.NumberField.minpoly_nextCoeff_eq_zero_of_trace_eq_zero α hαtr
    rw [Polynomial.nextCoeff, hPdeg, if_neg (by omega : ¬ n = 0)] at h1
    exact h1
  have hPbdd : ∀ i, i ≤ n → i ≠ n - 1 → |((P.coeff i : ℤ) : ℝ)| ≤
      2 ^ n * (2 ^ (2 * n + 6) *
        (subcaseI_P2_disc n H f : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n - i) := by
    intro i hi hne
    have hcoe := Commons.NumberTheory.NumberField.minpoly_coeff_le_pow_sub
      (K := Kpoly (f : ℤ[X])) α (NumberField.house ((α : Kpoly (f : ℤ[X])))) le_rfl
      (NumberField.one_le_house_of_isIntegral (NumberField.RingOfIntegers.isIntegral_coe α) (by
        intro h0
        exact hαne (Subtype.ext h0))) i
    rw [hfin] at hcoe
    have hle : NumberField.house ((α : Kpoly (f : ℤ[X]))) ≤
        2 ^ (2 * n + 6) *
          (subcaseI_P2_disc n H f : ℝ) ^ (1 / (2 * ((n : ℝ) - 1))) := by
      rw [hdisc]
      exact hαhouse'
    have hmono : NumberField.house ((α : Kpoly (f : ℤ[X]))) ^ (n - i) ≤
        (2 ^ (2 * n + 6) *
          (subcaseI_P2_disc n H f : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n - i) :=
      pow_le_pow_left₀ (NumberField.house_nonneg _) hle _
    rw [← hP] at hcoe
    exact hcoe.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
  exact ⟨P, hPmonic, hPdeg, hPnext, hPbdd, ⟨(α : Kpoly (f : ℤ[X])), hgen, hmap⟩⟩

end

end Submission.Vdw

namespace Submission.Vdw

noncomputable section


variable (n H : ℕ) (hn : 1 ≤ n) (hnn : 2 ≤ n)

/-- The chosen polynomial of a field-isomorphism class. -/
noncomputable def classPoly (q : Quotient (fieldIsoSetoid n H hn)) : ℤ[X] :=
  (exists_classPoly n H hn hnn (Quotient.out q)).choose

lemma classPoly_spec (q : Quotient (fieldIsoSetoid n H hn)) :
    (classPoly n H hn hnn q).Monic ∧
      (classPoly n H hn hnn q).natDegree = n ∧
      (classPoly n H hn hnn q).coeff (n - 1) = 0 ∧
      (∀ i, i ≤ n → i ≠ n - 1 → |(((classPoly n H hn hnn q).coeff i : ℤ) : ℝ)| ≤
        2 ^ n * (2 ^ (2 * n + 6) *
          (subcaseI_P2_disc n H (Quotient.out q) : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n - i)) ∧
      (∃ y : Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]),
        Algebra.adjoin ℚ ({y} : Set (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))) = ⊤ ∧
        minpoly ℚ y = (classPoly n H hn hnn q).map φℚ) :=
  (exists_classPoly n H hn hnn (Quotient.out q)).choose_spec

lemma classPoly_monic (q : Quotient (fieldIsoSetoid n H hn)) :
    (classPoly n H hn hnn q).Monic :=
  (classPoly_spec n H hn hnn q).1

lemma classPoly_natDegree (q : Quotient (fieldIsoSetoid n H hn)) :
    (classPoly n H hn hnn q).natDegree = n :=
  (classPoly_spec n H hn hnn q).2.1

lemma classPoly_nextCoeff (q : Quotient (fieldIsoSetoid n H hn)) :
    (classPoly n H hn hnn q).coeff (n - 1) = 0 :=
  (classPoly_spec n H hn hnn q).2.2.1

lemma classPoly_witness (q : Quotient (fieldIsoSetoid n H hn)) :
    ∃ y : Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]),
      Algebra.adjoin ℚ ({y} : Set (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X]))) = ⊤ ∧
      minpoly ℚ y = (classPoly n H hn hnn q).map φℚ :=
  (classPoly_spec n H hn hnn q).2.2.2.2

/-- Equal polynomials give isomorphic fields. -/
lemma classPoly_inj : Function.Injective (classPoly n H hn hnn) := by
  intro q q' h
  obtain ⟨y, hygen, hymin⟩ := classPoly_witness n H hn hnn q
  obtain ⟨y', hy'gen, hy'min⟩ := classPoly_witness n H hn hnn q'
  have hmin : minpoly ℚ y = minpoly ℚ y' := by rw [hymin, h, hy'min]
  have hiso : fieldIsoRel n H hn (Quotient.out q) (Quotient.out q') := by
    letI : Fact (Irreducible ((((Quotient.out q : ↥(SubcaseI_P2 n H)) : ℤ[X])).map φℚ)) :=
      ⟨subcaseI_P2_irreducible n H hn (Quotient.out q)⟩
    letI : Fact (Irreducible ((((Quotient.out q' : ↥(SubcaseI_P2 n H)) : ℤ[X])).map φℚ)) :=
      ⟨subcaseI_P2_irreducible n H hn (Quotient.out q')⟩
    exact Commons.NumberTheory.NumberField.nonempty_algEquiv_of_minpoly_eq hygen hy'gen hmin
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  exact Quotient.sound hiso

end

end Submission.Vdw

namespace Submission.Vdw

noncomputable section

open scoped ENNReal

/-!
# Schmidt's field count for the Case-II region

The number of degree-`n` fields of discriminant `≤ Y` in the Case-II region is `O(Y^((n+2)/4)`
(Schmidt).  The region's members have *primitive* Galois group, so by
`PerFieldFibreAll.adjoin_eq_top_of_galPrimitive` every non-rational element of such a field
generates it.  Combining that with the trace-zero Minkowski element
(`exists_trace_zero_house_le`) shows that each class is determined by the minimal polynomial of
a trace-zero generator of height `≪ |Disc|^(1/(2(n-1)))`, whence the field count. -/

/-- **Schmidt's field count for the Case-II region.** -/
theorem fieldCountBound_schmidt (n : ℕ) (hn : 3 ≤ n) :
    FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hnn : 2 ≤ n := by omega
  have hnnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  refine ⟨2 ^ (n * (n + 2)) * (2 ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1) * 2, by positivity, ?_⟩
  intro H Y hY
  have hYR : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  set Bfun : ℕ → ℝ := fun i =>
    2 ^ n * (2 ^ (2 * n + 6) * (Y : ℝ) ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n - i) with hBfun
  have hBfun0 : ∀ i, 0 ≤ Bfun i := by
    intro i; rw [hBfun]; positivity
  set T : Set ℤ[X] := {P : ℤ[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff (n - 1) = 0 ∧
      ∀ i, i ≤ n → i ≠ n - 1 → |((P.coeff i : ℤ) : ℝ)| ≤ Bfun i} with hT
  have hexp0 : (0 : ℝ) ≤ 1 / (2 * ((n : ℝ) - 1)) := by positivity
  have hmem : ∀ q : {q : Quotient (fieldIsoSetoid n H hn1) // classDisc n H hn1 q ≤ Y},
      classPoly n H hn1 hnn q.1 ∈ T := by
    intro q
    obtain ⟨hm, hd, hc, hb, -⟩ := classPoly_spec n H hn1 hnn q.1
    refine ⟨hm, hd, hc, ?_⟩
    intro i hi hne
    refine (hb i hi hne).trans ?_
    have hdisc : (subcaseI_P2_disc n H (Quotient.out q.1) : ℝ) ≤ (Y : ℝ) := by
      have := q.2
      rw [classDisc_out n H hn1 q.1] at this
      exact_mod_cast this
    have hdisc0 : (0 : ℝ) ≤ (subcaseI_P2_disc n H (Quotient.out q.1) : ℝ) :=
      Nat.cast_nonneg _
    have hpowle : (subcaseI_P2_disc n H (Quotient.out q.1) : ℝ) ^ (1 / (2 * ((n : ℝ) - 1))) ≤
        (Y : ℝ) ^ (1 / (2 * ((n : ℝ) - 1))) :=
      Real.rpow_le_rpow hdisc0 hdisc hexp0
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine pow_le_pow_left₀ (by positivity) ?_ _
    exact mul_le_mul_of_nonneg_left hpowle (by positivity)
  haveI : Fintype ↥T := ((Commons.NumberTheory.Polynomial.finite_monic_poly_coeff_le
    (fun i => if i = n - 1 then 0 else Bfun i)).subset (by
      intro P hP
      refine ⟨hP.1, hP.2.1, fun i hi => ?_⟩
      by_cases h : i = n - 1
      · subst h; rw [if_pos rfl]; simp [hP.2.2.1]
      · rw [if_neg h]; exact hP.2.2.2 i hi h)).fintype
  have hinj : Function.Injective
      (fun q : {q : Quotient (fieldIsoSetoid n H hn1) // classDisc n H hn1 q ≤ Y} =>
        (⟨classPoly n H hn1 hnn q.1, hmem q⟩ : ↥T)) := by
    intro q q' h
    have h1 : classPoly n H hn1 hnn q.1 = classPoly n H hn1 hnn q'.1 :=
      congrArg Subtype.val h
    exact Subtype.ext (classPoly_inj n H hn1 hnn h1)
  have hcard1 : Nat.card {q : Quotient (fieldIsoSetoid n H hn1) //
      classDisc n H hn1 q ≤ Y} ≤ T.ncard := by
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_coe_set_eq] at h
  calc ((Nat.card {q : Quotient (fieldIsoSetoid n H hn1) //
        classDisc n H hn1 q ≤ Y} : ℕ) : ℝ)
      ≤ ((T.ncard : ℕ) : ℝ) := by exact_mod_cast hcard1
    _ ≤ ∏ i ∈ (Finset.range (n + 1)).erase (n - 1), (2 * Bfun i + 1) :=
        Commons.NumberTheory.Polynomial.ncard_monic_poly_coeff_le_free Bfun hBfun0
    _ ≤ (2 ^ (n * (n + 2)) * (2 ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1) * 2) *
          (Y : ℝ) ^ (((n : ℝ) + 2) / 4) := by
        have h := Commons.NumberTheory.Polynomial.prod_bound_schmidt n hn hYR
        rw [hBfun]
        exact h


/-! ## Endpoints with Schmidt's theorem discharged -/

/-- **The challenge theorem in every prime degree `n ≥ 7`, unconditionally.**
For prime `n` the imprimitive input is vacuous (`ImprimitiveBad n H = ∅`), the
Lemke Oliver–Thorne per-field fibre bound is a theorem in every degree
(`PerFieldFibreAll.perFieldFibreBound_all`) and the field count is Schmidt's
theorem, proved above (`fieldCountBound_schmidt`). -/
theorem theorem_1_prime (n : ℕ) (hn : 7 ≤ n) (hp : Nat.Prime n) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_schmidt_of_prime n hn hp (fieldCountBound_schmidt n (by omega))

/-- **Degrees `n ≥ 6` from Widmer's imprimitive bound alone.**  With Schmidt's
field count now a theorem, the only input left in composite degree is Widmer's
`O(H^(n/2+2))` bound for the imprimitive polynomials. -/
theorem theorem_1_of_schmidt_and_widmer_all (n : ℕ) (hn : 6 ≤ n)
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_schmidt_and_widmer n hn (fieldCountBound_schmidt n (by omega)) hw


/-- **The Case-II slice is `O(H^(n-1))` in every degree `n ≥ 6`, unconditionally.**  Both inputs
of the Case-II analysis — the Lemke Oliver–Thorne per-field fibre bound and Schmidt's field count
— are now theorems of the project. -/
theorem subcaseIM_P2_isBigO (n : ℕ) (hn : 6 ≤ n) :
    (fun H : ℕ => ((SubcaseIM_P2 n (weylM n) H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < ((n : ℝ) + 2) / 4 := by
    have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    rw [div_lt_iff₀ hden]
    nlinarith
  exact SubcaseIM_P2_isBigO_of_countBound n (weylM n) (((n : ℝ) + 2) / 4) (by omega)
    (four_mul_le_weylM n) hβ (weylM_exponent_schmidt n hn)
    (caseIICountBound_of_field_inputs n (by omega) (((n : ℝ) + 2) / 4) hβ
      (perFieldFibreBound_all n (by omega)) (fieldCountBound_schmidt n (by omega)))

end

end Submission.Vdw
