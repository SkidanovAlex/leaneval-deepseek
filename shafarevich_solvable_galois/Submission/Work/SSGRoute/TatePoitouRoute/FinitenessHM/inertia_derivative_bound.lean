import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.finrank_le_natDegree_of_aeval_eq_zero
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.inertiaRing_span_p_isMaximal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree of the minimal polynomial of a uniformiser and the bound on its derivative

Let `p` be a prime, `Q₀ = (p)` the prime of `𝓞 ℚ` it generates, `K` a number field and `Q | Q₀` a
prime of `𝓞 K`.  Write `L := Q.adicCompletion K`, `B := 𝒪_L`, `ℚ_p := Q₀.adicCompletion ℚ`,
`ℤ_p := Q₀.adicCompletionIntegers ℚ` and let `E := ℚ_p(ζ) ⊆ L` be the inertia subfield with ring
of integers `C := 𝒪_E ⊆ E` (`inertiaField`/`inertiaRing` of `adicLocExpInertia.lean`).

This file proves the two facts about the minimal polynomial `F := minpoly C π` of a uniformiser
`π ∈ B` that the classical bound for the exponent of the different needs:

* `deg F = e = e(Q/Q₀)`, i.e. `[E(π) : E] = e` (so `F` is Eisenstein of degree `e`), and
* `ord_{𝔪_L}(F'(π)) ≤ e · v_p(e) + e - 1`.

Both are proved by the congruence ("unique minimum") argument: the summands of `F(π) = 0` resp.
`F'(π)` have `𝔪_L`-adic orders congruent to `j` modulo `e`, and for `j < e` the residues are
pairwise distinct.  The order computations use the two hypotheses `hordc` (`ord_{𝔪_L}` of an
element of `C` is `e` times its `(p)`-order) and `hordn` (`(p)`-order of a natural number is its
`p`-adic valuation), together with `ord_{𝔪_L} π = 1` which follows from `hπ`.
-/

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open IsDedekindDomain
open scoped NumberField
open Polynomial

section Helpers

variable {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
  (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
  (hQ0 : Q0.asIdeal = Ideal.span
    ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
  (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  [hQ : Q.asIdeal.LiesOver Q0.asIdeal]
  (ζ : Q.adicCompletionIntegers K)

/-- **The congruence ("unique minimum") argument, nonvanishing form.**

Let `τ 0, …, τ d` be elements of a Dedekind domain whose `P`-adic orders are congruent to `j`
modulo `e`; if `d < e` and `τ d ≠ 0`, then the sum `Σ_{j ≤ d} τ j` is nonzero.  Indeed the
residues modulo `e` of the orders of the nonzero summands are pairwise distinct, so the minimum
order is attained exactly once and the sum cannot vanish. -/
lemma inertiaDeriv_ordAt_sum_ne_zero_of_cong {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : IsDedekindDomain.HeightOneSpectrum R) (e : ℕ) (he : 0 < e)
    (τ : ℕ → R) (d : ℕ) (hd : d < e) (hlast : τ d ≠ 0)
    (hcong : ∀ j, j ≤ d → τ j ≠ 0 → ordAt v.asIdeal (τ j) % e = j % e) :
    (∑ j ∈ Finset.range (d + 1), τ j) ≠ 0 := by
  classical
  intro hsum
  set S : Finset ℕ := (Finset.range (d + 1)).filter (fun j => τ j ≠ 0) with hS
  have hmemS : ∀ j, j ∈ S ↔ j ≤ d ∧ τ j ≠ 0 := by
    intro j
    rw [hS, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; exact ⟨by omega, h.2⟩
    · intro h; exact ⟨by omega, h.2⟩
  have hdS : d ∈ S := (hmemS d).mpr ⟨le_rfl, hlast⟩
  obtain ⟨j₀, hj₀S, hj₀min⟩ :=
    Finset.exists_min_image S (fun j => ordAt v.asIdeal (τ j)) ⟨d, hdS⟩
  have hj₀le : j₀ ≤ d := ((hmemS j₀).mp hj₀S).1
  have hj₀ne : τ j₀ ≠ 0 := ((hmemS j₀).mp hj₀S).2
  set N : ℕ := ordAt v.asIdeal (τ j₀) with hN
  -- every summand lies in `P ^ N`
  have hall : ∀ j ∈ Finset.range (d + 1), τ j ∈ v.asIdeal ^ N := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases eq_or_ne (τ j) 0 with h0 | h0
    · rw [h0]; exact (v.asIdeal ^ N).zero_mem
    · rw [mem_pow_iff_le_ordAt v h0]
      by_cases hje : j = j₀
      · subst hje; exact le_rfl
      · exact hj₀min j ((hmemS j).mpr ⟨by omega, h0⟩)
  -- every summand other than `τ j₀` lies in `P ^ (N+1)`
  have hrest : (∑ j ∈ (Finset.range (d + 1)).erase j₀, τ j) ∈ v.asIdeal ^ (N + 1) := by
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [Finset.mem_erase] at hj
    obtain ⟨hjj, hjrange⟩ := hj
    rw [Finset.mem_range] at hjrange
    rcases eq_or_ne (τ j) 0 with h0 | h0
    · rw [h0]; exact (v.asIdeal ^ (N + 1)).zero_mem
    · rw [mem_pow_iff_le_ordAt v h0]
      have hle : N ≤ ordAt v.asIdeal (τ j) :=
        hj₀min j ((hmemS j).mpr ⟨by omega, h0⟩)
      have hne : ordAt v.asIdeal (τ j) ≠ N := by
        intro hcon
        have h1 := hcong j (by omega) h0
        have h2 := hcong j₀ hj₀le hj₀ne
        have h3 : j % e = j₀ % e := by rw [← h1, hcon, hN, h2]
        rw [Nat.mod_eq_of_lt (by omega : j < e),
          Nat.mod_eq_of_lt (by omega : j₀ < e)] at h3
        exact hjj h3
      omega
  -- the sum is `rest + τ j₀`, which vanishes
  have hsplit : (∑ j ∈ (Finset.range (d + 1)).erase j₀, τ j) + τ j₀ = 0 := by
    rw [Finset.sum_erase_add (Finset.range (d + 1)) τ (Finset.mem_range.mpr (by omega)),
      hsum]
  have hj₀not : τ j₀ ∉ v.asIdeal ^ (N + 1) := by
    intro h
    have := (mem_pow_iff_le_ordAt v hj₀ne (N + 1)).mp h
    omega
  refine hj₀not ?_
  have hτ : τ j₀ = ((∑ j ∈ (Finset.range (d + 1)).erase j₀, τ j) + τ j₀) -
      (∑ j ∈ (Finset.range (d + 1)).erase j₀, τ j) := (add_sub_cancel_left _ _).symm
  rw [hτ, hsplit]
  exact Submodule.sub_mem _ (v.asIdeal ^ (N + 1)).zero_mem hrest

/-- A natural number which is nonzero stays nonzero in the ring of integers `𝒪_L` of the
completion. -/
lemma inertiaDeriv_natCast_ne_zero (n : ℕ) (hn : n ≠ 0) :
    (n : Q.adicCompletionIntegers K) ≠ 0 := by
  haveI : CharZero (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion (K := K) Q
  intro h
  have h2 : ((n : Q.adicCompletionIntegers K) : Q.adicCompletion K) = 0 := by rw [h]; rfl
  have h3 : (n : Q.adicCompletion K) = 0 := by simpa using h2
  exact hn (Nat.cast_injective h3)

/-- The `𝔪_L`-adic order of a natural number in `𝒪_L` is `e · v_p(n)`. -/
lemma inertiaDeriv_ordAt_natCast
    (hordc : ∀ c : ↥(inertiaRing Q0 Q ζ),
      ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
          (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c) =
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
          ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ))) c)
    (hordn : ∀ n : ℕ, n ≠ 0 →
      ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)))
        ((n : ↥(inertiaRing Q0 Q ζ))) = padicValNat p n)
    (n : ℕ) (hn : n ≠ 0) :
    ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        (n : Q.adicCompletionIntegers K) =
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) * padicValNat p n := by
  rw [← map_natCast (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) n,
    hordc, hordn n hn]

/-- **The order of a summand `a · π^j` of `F(π)`.** -/
lemma inertiaDeriv_ordAt_algebraMap_mul_pow
    (hordc : ∀ c : ↥(inertiaRing Q0 Q ζ),
      ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
          (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c) =
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
          ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ))) c)
    (π : Q.adicCompletionIntegers K)
    (hπ : Valued.v (π : Q.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (a : ↥(inertiaRing Q0 Q ζ)) (ha : a ≠ 0) (j : ℕ) :
    ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) a * π ^ j) =
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
          ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ))) a +
        j := by
  haveI : IsDiscreteValuationRing (Q.adicCompletionIntegers K) := inferInstance
  have hπneL : (π : Q.adicCompletion K) ≠ 0 := by
    rintro h
    rw [h, Valuation.map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hπne : π ≠ 0 := fun h => hπneL (by rw [h]; rfl)
  have haB : algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) a ≠ 0 := by
    intro h
    refine ha (inertiaMap_injective Q0 Q ζ ?_)
    simpa [RingHom.algebraMap_toAlgebra] using h
  have hπord : ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) π = 1 := by
    rw [ordAt_maximalIdeal_eq_toNat_adicValExp Q π hπneL, adicValExp_eq_one_of_uniformizer Q hπ]
    norm_num
  have hbot : IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField (Q.adicCompletionIntegers K)
      ((IsLocalRing.isField_iff_maximalIdeal_eq (R := Q.adicCompletionIntegers K)).mpr h)
  let vB : IsDedekindDomain.HeightOneSpectrum (Q.adicCompletionIntegers K) :=
    ⟨IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K),
      (IsLocalRing.maximalIdeal.isMaximal _).isPrime, hbot⟩
  have hvB : vB.asIdeal = IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := rfl
  rw [ordAt_mul vB haB (pow_ne_zero j hπne), ordAt_pow vB hπne j, hvB, hordc a, hπord]
  ring

/-- **The order of a summand `(j+1)·a·π^j` of `F'(π)`.** -/
lemma inertiaDeriv_ordAt_intCast_mul_algebraMap_mul_pow
    (hordc : ∀ c : ↥(inertiaRing Q0 Q ζ),
      ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
          (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c) =
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
          ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ))) c)
    (hordn : ∀ n : ℕ, n ≠ 0 →
      ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)))
        ((n : ↥(inertiaRing Q0 Q ζ))) = padicValNat p n)
    (π : Q.adicCompletionIntegers K)
    (hπ : Valued.v (π : Q.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (a : ↥(inertiaRing Q0 Q ζ)) (ha : a ≠ 0) (j : ℕ) :
    ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        (((j : Q.adicCompletionIntegers K) + 1) *
          algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) a * π ^ j) =
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) * padicValNat p (j + 1) +
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
          ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ))) a +
      j := by
  haveI : IsDiscreteValuationRing (Q.adicCompletionIntegers K) := inferInstance
  have hπneL : (π : Q.adicCompletion K) ≠ 0 := by
    rintro h
    rw [h, Valuation.map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hπne : π ≠ 0 := fun h => hπneL (by rw [h]; rfl)
  have haB : algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) a ≠ 0 := by
    intro h
    refine ha (inertiaMap_injective Q0 Q ζ ?_)
    simpa [RingHom.algebraMap_toAlgebra] using h
  have hπord : ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) π = 1 := by
    rw [ordAt_maximalIdeal_eq_toNat_adicValExp Q π hπneL, adicValExp_eq_one_of_uniformizer Q hπ]
    norm_num
  have hj1ne : j + 1 ≠ 0 := by omega
  have hcast : ((j : Q.adicCompletionIntegers K) + 1) =
      ((j + 1 : ℕ) : Q.adicCompletionIntegers K) := by push_cast; ring
  have hj1ord : ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
      ((j : Q.adicCompletionIntegers K) + 1) =
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) * padicValNat p (j + 1) := by
    rw [hcast, ← map_natCast (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K))
        (j + 1), hordc, hordn (j + 1) hj1ne]
  have hbot : IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField (Q.adicCompletionIntegers K)
      ((IsLocalRing.isField_iff_maximalIdeal_eq (R := Q.adicCompletionIntegers K)).mpr h)
  let vB : IsDedekindDomain.HeightOneSpectrum (Q.adicCompletionIntegers K) :=
    ⟨IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K),
      (IsLocalRing.maximalIdeal.isMaximal _).isPrime, hbot⟩
  have hvB : vB.asIdeal = IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := rfl
  have hj1B : ((j : Q.adicCompletionIntegers K) + 1) ≠ 0 := by
    haveI : CharZero (Q.adicCompletion K) :=
      Commons.NumberTheory.NumberField.charZero_adicCompletion (K := K) Q
    rw [hcast]
    intro h
    have h2 : ((j + 1 : ℕ) : Q.adicCompletion K) = 0 := by
      have h3 : (((j + 1 : ℕ) : Q.adicCompletionIntegers K) : Q.adicCompletion K) = 0 := by
        rw [h]; rfl
      simpa using h3
    exact hj1ne (Nat.cast_injective h2)
  rw [ordAt_mul vB (mul_ne_zero hj1B haB) (pow_ne_zero j hπne),
    ordAt_mul vB hj1B haB, ordAt_pow vB hπne j, hvB, hj1ord, hordc a, hπord]
  ring

/-- **The local fundamental identity for the inertia field**: `[L : E] = e(Q/Q₀)`. -/
lemma inertiaDeriv_finrank_inertiaField
    (hfin : Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) =
      Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ)) :
    Module.finrank ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) =
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) := by
  have h1 : Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
      Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) =
      Module.finrank (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q0 Q hQ
  have h2 : Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) *
      Module.finrank ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) =
      Module.finrank (Q0.adicCompletion ℚ) (Q.adicCompletion K) :=
    Module.finrank_mul_finrank _ _ _
  rw [hfin] at h2
  refine Nat.mul_left_cancel (Ideal.inertiaDeg_pos Q.asIdeal (NumberField.RingOfIntegers ℚ)) ?_
  rw [h2, ← h1, mul_comm]

/-- **The degree of the minimal polynomial over `C = 𝒪_E` is at most `[L : E]`.** -/
lemma inertiaDeriv_natDegree_minpoly_le (π : Q.adicCompletionIntegers K) :
    (minpoly ↥(inertiaRing Q0 Q ζ) π).natDegree ≤
      Module.finrank ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) := by
  have hmap : minpoly ↥(inertiaField Q0 Q ζ)
        ((algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)) π) =
      (minpoly ↥(inertiaRing Q0 Q ζ) π).map
        (algebraMap ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions (R := ↥(inertiaRing Q0 Q ζ))
      (S := Q.adicCompletionIntegers K) (↥(inertiaField Q0 Q ζ)) (Q.adicCompletion K)
      (Algebra.IsIntegral.isIntegral π)
  have h2 : (minpoly ↥(inertiaRing Q0 Q ζ) π).natDegree =
      (minpoly ↥(inertiaField Q0 Q ζ)
        ((algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)) π)).natDegree := by
    rw [hmap, Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)) _]
  rw [h2]
  exact minpoly.natDegree_le (A := ↥(inertiaField Q0 Q ζ)) _

/-- `(e * A + j) % e = j % e`, the elementary congruence underlying the summand estimates. -/
lemma inertiaDeriv_mul_add_mod_self (e A j : ℕ) : (e * A + j) % e = j % e := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left]

end Helpers

theorem inertia_derivative_bound {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hQ0 : Q0.asIdeal = Ideal.span
      ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [hQ : Q.asIdeal.LiesOver Q0.asIdeal]
    (ζ : Q.adicCompletionIntegers K)
    (hζ : IsPrimitiveRoot (ζ : Q.adicCompletion K)
      (Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) - 1))
    (hfin : Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) =
      Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ))
    (hmax : (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ))).IsMaximal)
    (hunder : Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)) =
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).comap
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)))
    (hordc : ∀ c : ↥(inertiaRing Q0 Q ζ),
      ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
          (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c) =
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
          ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ))) c)
    (hordn : ∀ n : ℕ, n ≠ 0 →
      ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)))
        ((n : ↥(inertiaRing Q0 Q ζ))) = padicValNat p n)
    (π : Q.adicCompletionIntegers K)
    (hπ : Valued.v (π : Q.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    (minpoly ↥(inertiaRing Q0 Q ζ) π).natDegree =
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) ∧
      ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
          (Polynomial.aeval π (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π))) ≤
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
            padicValNat p (Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ)) +
          Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) - 1 := by
  classical
  -- ### setup
  set f : Polynomial ↥(inertiaRing Q0 Q ζ) := minpoly ↥(inertiaRing Q0 Q ζ) π with hf
  set d : ℕ := f.natDegree with hd
  set e : ℕ := Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) with he_def
  set mB : Ideal (Q.adicCompletionIntegers K) :=
    IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) with hmB
  have hordc' : ∀ c : ↥(inertiaRing Q0 Q ζ),
      ordAt mB (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) c) =
        e * ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ))) c := by
    intro c
    rw [hmB, he_def]
    exact hordc c
  haveI hDVR : IsDiscreteValuationRing (Q.adicCompletionIntegers K) := inferInstance
  have hmB_bot : mB ≠ ⊥ := by
    rw [hmB]
    intro h
    exact IsDiscreteValuationRing.not_isField (Q.adicCompletionIntegers K)
      ((IsLocalRing.isField_iff_maximalIdeal_eq (R := Q.adicCompletionIntegers K)).mpr h)
  let vB : IsDedekindDomain.HeightOneSpectrum (Q.adicCompletionIntegers K) :=
    ⟨mB, (by rw [hmB]; exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime), hmB_bot⟩
  have he : 0 < e := by
    rw [he_def]
    exact Ideal.ramificationIdx_pos (NumberField.RingOfIntegers ℚ) Q.asIdeal
  have hfmonic : f.Monic := by
    rw [hf]
    exact minpoly.monic (Algebra.IsIntegral.isIntegral π)
  have hfaeval : aeval π f = 0 := by
    rw [hf]
    exact minpoly.aeval _ _
  have hπneL : (π : Q.adicCompletion K) ≠ 0 := by
    rintro h
    rw [h, Valuation.map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hπne : π ≠ 0 := fun h => hπneL (by rw [h]; rfl)
  -- ### `[L : E] = e`
  have hfinE : Module.finrank ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) = e := by
    rw [he_def]
    exact inertiaDeriv_finrank_inertiaField Q0 Q ζ hfin
  -- ### `deg F ≤ e`
  have hdle : d ≤ e := by
    rw [hd, hf]
    exact (inertiaDeriv_natDegree_minpoly_le Q0 Q ζ π).trans (le_of_eq hfinE)
  -- ### `e ≤ deg F`
  have hdge : e ≤ d := by
    by_contra hcon
    have hlt : d < e := not_le.mp hcon
    set τ : ℕ → Q.adicCompletionIntegers K := fun j =>
      algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) (f.coeff j) * π ^ j with hτ
    have hcoeff_d : f.coeff d = 1 := by
      rw [hd]
      exact hfmonic.coeff_natDegree
    have hlast : τ d ≠ 0 := by
      have h1 : τ d = π ^ d := by simp [hτ, hcoeff_d]
      rw [h1]
      exact pow_ne_zero d hπne
    have hcong : ∀ j, j ≤ d → τ j ≠ 0 → ordAt mB (τ j) % e = j % e := by
      intro j _ hne
      have hcoeff_ne : f.coeff j ≠ 0 := by
        intro h0
        refine hne ?_
        simp [hτ, h0]
      have hord := inertiaDeriv_ordAt_algebraMap_mul_pow p Q0 Q ζ hordc' π hπ (f.coeff j)
        hcoeff_ne j
      have hord' : ordAt mB (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)
            (f.coeff j) * π ^ j) =
          e * ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)))
            (f.coeff j) + j := by
        rw [hmB, he_def]
        exact hord
      simp only [hτ]
      rw [hord']
      exact inertiaDeriv_mul_add_mod_self e _ j
    have hsum0 : (∑ j ∈ Finset.range (d + 1), τ j) = 0 := by
      have h1 : (∑ j ∈ Finset.range (d + 1), τ j) = aeval π f := by
        rw [hd]
        simp only [hτ]
        rw [aeval_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def]
      rw [h1, hfaeval]
    exact inertiaDeriv_ordAt_sum_ne_zero_of_cong vB e he τ d hlt hlast hcong hsum0
  have hdeg : d = e := le_antisymm hdle hdge
  refine ⟨hdeg, ?_⟩
  -- ### the derivative bound
  set τ : ℕ → Q.adicCompletionIntegers K := fun j =>
    ((j : Q.adicCompletionIntegers K) + 1) *
      algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) (f.coeff (j + 1)) *
      π ^ j with hτ
  have hcong : ∀ j, j < e → τ j ≠ 0 → ordAt mB (τ j) % e = j % e := by
    intro j _ hne
    have hcoeff_ne : f.coeff (j + 1) ≠ 0 := by
      intro h0
      refine hne ?_
      simp [hτ, h0]
    have hord := inertiaDeriv_ordAt_intCast_mul_algebraMap_mul_pow p Q0 Q ζ hordc' hordn π hπ
      (f.coeff (j + 1)) hcoeff_ne j
    have hord' : ordAt mB (((j : Q.adicCompletionIntegers K) + 1) *
          algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) (f.coeff (j + 1)) *
          π ^ j) =
        e * padicValNat p (j + 1) +
          e * ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)))
            (f.coeff (j + 1)) + j := by
      rw [hmB, he_def]
      exact hord
    simp only [hτ]
    rw [hord', ← Nat.mul_add]
    exact inertiaDeriv_mul_add_mod_self e _ j
  have hlast : ordAt mB (τ (e - 1)) = e * padicValNat p e + e - 1 := by
    have hcoeff_e : f.coeff e = 1 := by
      rw [← hdeg, hd]
      exact hfmonic.coeff_natDegree
    have hone : ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)))
        (1 : ↥(inertiaRing Q0 Q ζ)) = 0 := by
      rw [ordAt, Ideal.span_singleton_one, ← Ideal.one_eq_top,
        UniqueFactorizationMonoid.normalizedFactors_one, Multiset.count_zero]
    have he1 : e - 1 + 1 = e := Nat.sub_add_cancel he
    have hne1 : f.coeff e ≠ 0 := by rw [hcoeff_e]; exact one_ne_zero
    have hord := inertiaDeriv_ordAt_intCast_mul_algebraMap_mul_pow p Q0 Q ζ hordc' hordn π hπ
      (f.coeff e) hne1 (e - 1)
    have hord' : ordAt mB ((((e - 1 : ℕ) : Q.adicCompletionIntegers K) + 1) *
          algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) (f.coeff e) *
          π ^ (e - 1)) =
        e * padicValNat p ((e - 1) + 1) +
          e * ordAt (Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)))
            (f.coeff e) + (e - 1) := by
      rw [hmB, he_def]
      exact hord
    simp only [hτ]
    rw [he1, hord', he1, hcoeff_e, hone]
    omega
  have hsum_eq : (∑ j ∈ Finset.range e, τ j) = aeval π (Polynomial.derivative f) := by
    rw [← hdeg, hd]
    simp only [hτ]
    rw [aeval_derivative_eq_sum]
  calc ordAt mB (aeval π (Polynomial.derivative f))
      = ordAt mB (∑ j ∈ Finset.range e, τ j) := by rw [hsum_eq]
    _ ≤ e * padicValNat p e + e - 1 := ordAt_sum_le he vB τ hcong hlast

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
