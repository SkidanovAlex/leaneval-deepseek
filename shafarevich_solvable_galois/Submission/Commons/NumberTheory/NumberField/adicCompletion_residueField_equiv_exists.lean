import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

noncomputable section

open IsDedekindDomain Topology Filter

/-- The value group `ℤᵐ⁰` used by the discrete valuations in this file. -/
abbrev _root_.Zstar0 := WithZero (Multiplicative ℤ)

variable {K : Type*} [Field K] [NumberField K]

/-- The elements of the valuation ring of the completion lying in its maximal ideal are exactly
the elements of valuation `< 1`. -/
lemma adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
    (V : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (z : V.adicCompletionIntegers K) :
    z ∈ IsLocalRing.maximalIdeal (V.adicCompletionIntegers K) ↔
      Valued.v (z : V.adicCompletion K) < (1 : Zstar0) := by
  rw [IsLocalRing.mem_maximalIdeal]
  rw [mem_nonunits_iff]
  constructor
  · intro hnz
    have hle : Valued.v (z : V.adicCompletion K) ≤ (1 : Zstar0) := z.2
    have hne : Valued.v (z : V.adicCompletion K) ≠ (1 : Zstar0) := by
      intro hz
      apply hnz
      exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (R := 𝓞 K) (K := K) (v := V) (a := z)).2 hz
    exact lt_of_le_of_ne hle hne
  · intro hz hu
    exact (ne_of_lt hz)
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (R := 𝓞 K) (K := K) (v := V) (a := z)).1 hu)

/-- In the completion, the open unit ball `{y | v (y - x) < 1}` around any point `x` of the
valuation ring is a neighbourhood of `x`. -/
lemma valued_lt_one_mem_nhds (V : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : V.adicCompletion K) :
    {y : V.adicCompletion K | Valued.v (y - x) < (1 : Zstar0)} ∈ 𝓝 x := by
  rw [Valued.mem_nhds]
  refine ⟨Units.mk0 (1 : MonoidWithZeroHom.ValueGroup₀
    (.ofClass (Valued.v : Valuation (V.adicCompletion K) Zstar0))) one_ne_zero, ?_⟩
  intro y hy
  simpa [Valuation.restrict_lt_one_iff] using hy


/-- Every element of the valuation ring of the completion is congruent modulo the maximal ideal
to an element of the ring of integers `𝓞 K` (the ring of integers is dense in the residue field:
the residue field of the completion is `𝓞 K / v`). -/
lemma exists_sub_ringOfIntegers_mem_maximalIdeal
    (V : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : V.adicCompletionIntegers K) :
    ∃ r : 𝓞 K, x - algebraMap (𝓞 K) (V.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (V.adicCompletionIntegers K) := by
  classical
  let t : V.adicCompletion K := (x : V.adicCompletion K)
  have hD : DenseRange (algebraMap K (V.adicCompletion K)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) V
  obtain ⟨k, hk⟩ := hD.mem_nhds (valued_lt_one_mem_nhds V t)
  have hv1 : Valued.v ((k : V.adicCompletion K) - t) < (1 : Zstar0) := by exact hk
  have hle_sub : Valued.v ((k : V.adicCompletion K) - t) ≤ (1 : Zstar0) := le_of_lt hv1
  have hle_t : Valued.v t ≤ (1 : Zstar0) := x.2
  have hkval_le : Valued.v ((k : V.adicCompletion K)) ≤ (1 : Zstar0) := by
    calc
      Valued.v (k : V.adicCompletion K) =
          Valued.v (((k : V.adicCompletion K) - t) + t) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v ((k : V.adicCompletion K) - t)) (Valued.v t) :=
        Valuation.map_add Valued.v _ _
      _ ≤ (1 : Zstar0) := max_le hle_sub hle_t
  have hvk : IsDedekindDomain.HeightOneSpectrum.valuation K V k ≤ (1 : Zstar0) := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (R := 𝓞 K) (K := K) V k]
    exact hkval_le
  obtain ⟨r : 𝓞 K, hr⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer
    (R := 𝓞 K) (K := K) V hvk (Units.mk0 (1 : Zstar0) one_ne_zero)
  -- prove Valued.v (t - (algebraMap R A r : Kv)) < 1
  have hru : Valued.v ((k : V.adicCompletion K) -
      (algebraMap (𝓞 K) (V.adicCompletionIntegers K) r : V.adicCompletion K)) < (1 : Zstar0) := by
    have hc : Valued.v ((algebraMap (𝓞 K) (V.adicCompletionIntegers K) r : V.adicCompletion K) -
        (k : V.adicCompletion K)) < (1 : Zstar0) := by
      have hcv : Valued.v ((algebraMap (𝓞 K) K r : V.adicCompletion K) -
          (k : V.adicCompletion K)) =
          IsDedekindDomain.HeightOneSpectrum.valuation K V
            ((algebraMap (𝓞 K) K r) - k) := by
        change Valued.v (algebraMap K (V.adicCompletion K) (algebraMap (𝓞 K) K r) -
            algebraMap K (V.adicCompletion K) k) =
            IsDedekindDomain.HeightOneSpectrum.valuation K V ((algebraMap (𝓞 K) K r) - k)
        rw [← map_sub]
        exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
          (R := 𝓞 K) (K := K) V (algebraMap (𝓞 K) K r - k)
      have hcv' : Valued.v ((algebraMap (𝓞 K) (V.adicCompletionIntegers K) r : V.adicCompletion K) -
          (k : V.adicCompletion K)) < (1 : Zstar0) := by
        have hb : ((algebraMap (𝓞 K) (V.adicCompletionIntegers K) r : V.adicCompletionIntegers K) :
            V.adicCompletion K) = (algebraMap (𝓞 K) K r : V.adicCompletion K) := rfl
        rw [hb, hcv]
        simpa using hr
      exact hcv'
    rw [Valuation.map_sub_swap]
    exact hc
  have htu : Valued.v (t - (algebraMap (𝓞 K) (V.adicCompletionIntegers K) r : V.adicCompletion K)) <
      (1 : Zstar0) := by
    have hmid := Valuation.map_add Valued.v (t - (k : V.adicCompletion K))
      ((k : V.adicCompletion K) - (algebraMap (𝓞 K) (V.adicCompletionIntegers K) r : V.adicCompletion K))
    have hsum : (t - (k : V.adicCompletion K)) + ((k : V.adicCompletion K) -
        (algebraMap (𝓞 K) (V.adicCompletionIntegers K) r : V.adicCompletion K)) =
        t - (algebraMap (𝓞 K) (V.adicCompletionIntegers K) r : V.adicCompletion K) := by
      abel
    have hlt1 : Valued.v (t - (k : V.adicCompletion K)) < (1 : Zstar0) := by
      rw [Valuation.map_sub_swap]
      exact hv1
    have hlt2 : Valued.v ((k : V.adicCompletion K) -
        (algebraMap (𝓞 K) (V.adicCompletionIntegers K) r : V.adicCompletion K)) < (1 : Zstar0) := hru
    rw [← hsum]
    exact lt_of_le_of_lt hmid (max_lt hlt1 hlt2)
  -- convert into membership of maximal ideal
  refine ⟨r, ?_⟩
  rw [adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one V (x - algebraMap (𝓞 K)
    (V.adicCompletionIntegers K) r)]
  simpa [t] using htu


/-- The kernel of the reduction map `𝓞 K → (V.adicCompletionIntegers K) ⧸ maximalIdeal` is
exactly the prime ideal `V.asIdeal`. -/
lemma quotientMap_ker_eq_asIdeal (V : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (V.adicCompletionIntegers K))).comp
      (algebraMap (𝓞 K) (V.adicCompletionIntegers K))) = V.asIdeal := by
  ext r
  rw [RingHom.mem_ker]
  rw [RingHom.comp_apply]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rw [adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one V
    (algebraMap (𝓞 K) (V.adicCompletionIntegers K) r)]
  -- Valued.v (coe (algebraMap R A r)) < 1 ↔ r ∈ V.asIdeal
  have hval : Valued.v ((algebraMap (𝓞 K) (V.adicCompletionIntegers K) r : V.adicCompletionIntegers K) :
      V.adicCompletion K) = Valued.v (algebraMap (𝓞 K) (V.adicCompletion K) r) := by
    rfl
  rw [hval]
  have hval2 : Valued.v (algebraMap (𝓞 K) (V.adicCompletion K) r) =
      IsDedekindDomain.HeightOneSpectrum.valuation K V (algebraMap (𝓞 K) K r) := by
    exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation
      (R := 𝓞 K) (K := K) V r)
  rw [hval2]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (R := 𝓞 K) (K := K) V r

/-- The reduction map `𝓞 K → (V.adicCompletionIntegers K) ⧸ maximalIdeal` is surjective. -/
lemma quotientMap_surjective (V : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (V.adicCompletionIntegers K))).comp
      (algebraMap (𝓞 K) (V.adicCompletionIntegers K))) := by
  intro q
  rcases Ideal.Quotient.mk_surjective q with ⟨x, hx⟩
  obtain ⟨r, hr⟩ := exists_sub_ringOfIntegers_mem_maximalIdeal V x
  refine ⟨r, ?_⟩
  rw [RingHom.comp_apply, ← hx]
  rw [Ideal.Quotient.eq]
  -- algebraMap R A r - x ∈ maximalIdeal, from x - algebraMap R A r ∈ maximalIdeal
  have hneg : -(x - algebraMap (𝓞 K) (V.adicCompletionIntegers K) r) ∈
      IsLocalRing.maximalIdeal (V.adicCompletionIntegers K) := by
    exact (Ideal.neg_mem_iff (I := IsLocalRing.maximalIdeal (V.adicCompletionIntegers K))).mpr hr
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

/-- The residue field of the ring of integers of the `v`-adic completion of a number field `K`
is isomorphic to the residue field `𝓞 K / v` of the prime ideal `v`. -/
theorem adicCompletion_residueField_equiv_exists {K : Type*} [Field K] [NumberField K]
    (V : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Nonempty (((V.adicCompletionIntegers K) ⧸
        IsLocalRing.maximalIdeal (V.adicCompletionIntegers K)) ≃+* ((𝓞 K) ⧸ V.asIdeal)) := by
  classical
  let A : ValuationSubring (V.adicCompletion K) := V.adicCompletionIntegers K
  let m : Ideal A := IsLocalRing.maximalIdeal A
  have hker : RingHom.ker (algebraMap (𝓞 K) (A ⧸ m)) = V.asIdeal := by
    change RingHom.ker ((Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (V.adicCompletionIntegers K))).comp
      (algebraMap (𝓞 K) (V.adicCompletionIntegers K))) = V.asIdeal
    exact quotientMap_ker_eq_asIdeal V
  have hsurj : Function.Surjective (algebraMap (𝓞 K) (A ⧸ m)) := by
    change Function.Surjective ((Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (V.adicCompletionIntegers K))).comp
      (algebraMap (𝓞 K) (V.adicCompletionIntegers K)))
    exact quotientMap_surjective V
  let e : (𝓞 K) ⧸ V.asIdeal ≃+* A ⧸ m := by
    rw [← hker]
    exact RingHom.quotientKerEquivOfSurjective
      (f := (algebraMap (𝓞 K) (A ⧸ m))) hsurj
  exact ⟨e.symm⟩

end

end Commons.NumberTheory.NumberField