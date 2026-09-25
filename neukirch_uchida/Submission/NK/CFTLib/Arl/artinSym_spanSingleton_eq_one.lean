import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_integral
import Submission.NK.CFTLib.Arl.exists_denominator_ideal

/-!
# The Artin symbol of a principal ideal `(b)` with `b ≡ 1 mod m` totally positive

Let `L/K` be a finite abelian (Galois) extension of number fields, `m > 0` a modulus such that the
primes not dividing `(m)` are unramified in `L`, and assume the ideal-theoretic Artin reciprocity
law at modulus `m` (`hprinc`, i.e. `NK.CFTLib.artinKillsPrincipal K L m`): the Artin symbol of
every principal ideal `(a)` with `a ∈ 𝓞 K`, `a ≡ 1 mod m` and `a` totally positive is trivial.

The main result of this file, `NK.CFTLib.Arl.artinSym_spanSingleton_eq_one`, removes the
integrality restriction: if `b ∈ Kˣ` satisfies `b ≡ 1 mod m` at every prime `𝔭 | (m)`
(the valuation hypothesis `hcong`) and is positive at every real place (`hpos`), then
`artinSym (b·𝓞 K) = 1`.

The proof has three ingredients.

* `NK.CFTLib.Arl.exists_denominator_ideal`: the ideal `B` of elements `x` with `b x` integral and
  `b x ≡ x mod m`; it contains a solution of `x ≡ 1 mod m` (`a0`) and a nonzero element `y`.
* Positivity: for `N` large the element `A0 = a0 + m·N·y²` is still `≡ 1 mod m` and its values at
  the real embeddings are `φ a0 + m N φ(y)² > 0`, so `A0` is totally positive (if it happens to
  vanish, one uses `A0 + m y²` instead).  The associated numerator `A1` with `A1 = b A0` in `B` is
  then integral, `≡ 1 mod m` and totally positive too.
* `NK.CFTLib.Arl.artinSym_spanSingleton_integral` gives `artinSym (A1) = artinSym (A0) = 1`, and
  multiplicativity of `artinSym` turns `(b) = (A1)/(A0)` into `artinSym (b) = 1`.

The auxiliary lemma `forall_ringHom_pos_of_realPlace_pos` identifies the hypothesis `hpos` (a
statement about the completions at the real places) with the positivity hypothesis in the
`φ : K →+* ℝ` form used by `hprinc`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

variable {K : Type*} [Field K] [NumberField K]

/-- **Positivity at the real places versus positivity at every ring homomorphism `K →+* ℝ`.**

Every ring homomorphism `φ : K →+* ℝ` of a number field into `ℝ` is, up to the identification
`K_w ≅ ℝ` at a real place `w`, the real embedding of a real place.  Hence positivity of `x` at all
real places (read in the completions) is equivalent to `0 < φ x` for all `φ : K →+* ℝ`. -/
theorem forall_ringHom_pos_of_realPlace_pos {x : K}
    (h : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap K w.Completion x)) :
    ∀ φ : K →+* ℝ, 0 < φ x := by
  intro φ
  -- `φ` composed with `ℝ ⊆ ℂ` is a real complex embedding
  have hψ : ComplexEmbedding.IsReal ((algebraMap ℝ ℂ).comp φ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext z
    rw [ComplexEmbedding.conjugate_coe_eq]
    simp
  set w : InfinitePlace K := InfinitePlace.mk ((algebraMap ℝ ℂ).comp φ) with hwdef
  have hw : w.IsReal := InfinitePlace.isReal_mk_iff.mpr hψ
  have hkey : (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap K w.Completion x)
      = φ x := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    apply Complex.ofReal_injective
    rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    have h1 : InfinitePlace.Completion.extensionEmbedding w (algebraMap K w.Completion x)
        = w.embedding x := by
      rw [show (algebraMap K w.Completion x : w.Completion)
        = ((WithAbs.toAbs w.1 x : WithAbs w.1) : w.Completion) from rfl]
      rw [InfinitePlace.Completion.extensionEmbedding_coe]
      simp
    rw [h1, hwdef, InfinitePlace.embedding_mk_eq_of_isReal hψ]
    simp
  rw [← hkey]
  exact h w hw

theorem artinSym_spanSingleton_eq_one {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : ∀ (a : NumberField.RingOfIntegers K),
      a - 1 ∈ Ideal.span {(m : NumberField.RingOfIntegers K)} →
      (∀ φ : K →+* ℝ, 0 < φ ((a : K))) →
      ∀ (s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
        (e : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ)
        (σ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → Gal(L/K)),
        (∀ p ∈ s, (m : NumberField.RingOfIntegers K) ∉ p.asIdeal) →
        Ideal.span {a} = ∏ p ∈ s, p.asIdeal ^ e p →
        (∀ p ∈ s, NK.Chebotarev.IsFrobAtPrime (L := L) p (σ p)) →
        (s.toList.map (fun p => σ p ^ e p)).prod = 1)
    (b : Kˣ)
    (hcong : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal →
        Valued.v (algebraMap K (𝔭.adicCompletion K) (b : K) - 1)
          ≤ Valued.v ((m : ℕ) : 𝔭.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap K w.Completion (b : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K)) = 1 := by
  classical
  -- rewrite the positivity hypothesis in the `K →+* ℝ` form used by `hprinc`
  have hpos' : ∀ φ : K →+* ℝ, 0 < φ ((b : K)) :=
    forall_ringHom_pos_of_realPlace_pos (K := K) (x := (b : K)) (fun w hw => hpos w hw)
  -- the ideal of elements `x` with `b x` integral and `b x ≡ x mod m`
  obtain ⟨B, ⟨a0, ha0B, ha0cong⟩, ⟨y, hyB, hyne⟩, hprop⟩ :=
    exists_denominator_ideal (K := K) m hm b hcong
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  -- how large `N` has to be
  let M : ℕ := Finset.univ.sup (fun φ : K →+* ℝ =>
    ⌈max 0 (- (φ ((a0 : 𝓞 K) : K)) / ((m:ℝ) * (φ ((y : 𝓞 K) : K))^2))⌉₊)
  let N : ℕ := M + 1
  have hyneK : ((y : 𝓞 K) : K) ≠ 0 := fun h => hyne (IsFractionRing.injective (𝓞 K) K h)
  have hterm : ∀ φ : K →+* ℝ,
      - (φ ((a0 : 𝓞 K) : K)) / ((m:ℝ) * (φ ((y : 𝓞 K) : K))^2) < (N : ℝ) := by
    intro φ
    have hsup : ⌈max 0 (- (φ ((a0 : 𝓞 K) : K)) / ((m:ℝ) * (φ ((y : 𝓞 K) : K))^2))⌉₊ ≤ M :=
      Finset.le_sup (f := fun φ : K →+* ℝ =>
        ⌈max 0 (- (φ ((a0 : 𝓞 K) : K)) / ((m:ℝ) * (φ ((y : 𝓞 K) : K))^2))⌉₊)
        (Finset.mem_univ φ)
    have h1 : max 0 (- (φ ((a0 : 𝓞 K) : K)) / ((m:ℝ) * (φ ((y : 𝓞 K) : K))^2)) ≤ (M : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hsup)
    have h2 : - (φ ((a0 : 𝓞 K) : K)) / ((m:ℝ) * (φ ((y : 𝓞 K) : K))^2) ≤ (M : ℝ) :=
      le_trans (le_max_right _ _) h1
    have h3 : (M : ℝ) < (N : ℝ) := by simp only [N]; push_cast; linarith
    linarith
  have hposN : ∀ φ : K →+* ℝ,
      0 < φ ((a0 : 𝓞 K) : K) + (m:ℝ) * (N:ℝ) * (φ ((y : 𝓞 K) : K))^2 := by
    intro φ
    have hy' : φ ((y : 𝓞 K) : K) ≠ 0 := (map_ne_zero φ).mpr hyneK
    have hy2pos : 0 < (φ ((y : 𝓞 K) : K))^2 := sq_pos_of_ne_zero hy'
    have hd : 0 < (m:ℝ) * (φ ((y : 𝓞 K) : K))^2 := mul_pos hmR hy2pos
    have h1 : - (φ ((a0 : 𝓞 K) : K)) < (N:ℝ) * ((m:ℝ) * (φ ((y : 𝓞 K) : K))^2) :=
      (div_lt_iff₀ hd).mp (hterm φ)
    nlinarith [h1]
  -- the candidate `A0 ∈ B`, congruent to `1` modulo `m` and totally positive
  set A0 : 𝓞 K := a0 + (m : 𝓞 K) * (N : 𝓞 K) * y^2 with hA0
  have hA0B : A0 ∈ B := by
    rw [hA0]
    refine B.add_mem ha0B ?_
    exact Ideal.mul_mem_left B ((m : 𝓞 K) * (N : 𝓞 K)) (by
      rw [pow_two]
      exact Ideal.mul_mem_left B y hyB)
  have hA0cong : A0 - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
    rw [hA0]
    have h2 : (m : 𝓞 K) * (N : 𝓞 K) * y ^ 2 ∈ Ideal.span {(m : 𝓞 K)} := by
      rw [show (m : 𝓞 K) * (N : 𝓞 K) * y ^ 2 = ((N : 𝓞 K) * y ^ 2) * (m : 𝓞 K) by ring]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have h3 : a0 + (m : 𝓞 K) * (N : 𝓞 K) * y ^ 2 - 1
        = (a0 - 1) + (m : 𝓞 K) * (N : 𝓞 K) * y ^ 2 := by ring
    rw [h3]
    exact Ideal.add_mem _ ha0cong h2
  have hA0pos : ∀ φ : K →+* ℝ, 0 < φ ((A0 : 𝓞 K) : K) := by
    intro φ
    have h1 : φ ((A0 : 𝓞 K) : K)
        = φ ((a0 : 𝓞 K) : K) + (m:ℝ) * (N:ℝ) * (φ ((y : 𝓞 K) : K))^2 := by
      rw [hA0]
      push_cast
      simp only [map_add, map_mul, map_pow, map_natCast]
    rw [h1]
    exact hposN φ
  have hy2B : y^2 ∈ B := by rw [pow_two]; exact Ideal.mul_mem_left B y hyB
  have hmK : (m : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hmspan : ∀ x : 𝓞 K, (m : 𝓞 K) * x ∈ Ideal.span {(m : 𝓞 K)} := by
    intro x
    rw [show (m : 𝓞 K) * x = x * (m : 𝓞 K) by ring]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  -- `A0`, or `A0 + m y²` if `A0` happens to vanish, is a valid totally positive denominator
  have hmain : ∃ A2 : 𝓞 K, A2 ∈ B ∧ A2 - 1 ∈ Ideal.span {(m : 𝓞 K)} ∧ A2 ≠ 0 ∧
      (∀ φ : K →+* ℝ, 0 < φ ((A2 : 𝓞 K) : K)) := by
    by_cases hz : A0 = 0
    · refine ⟨A0 + (m : 𝓞 K) * y^2, ?_, ?_, ?_, ?_⟩
      · exact B.add_mem hA0B (Ideal.mul_mem_left B (m : 𝓞 K) hy2B)
      · have h3 : A0 + (m : 𝓞 K) * y^2 - 1 = (A0 - 1) + (m : 𝓞 K) * y^2 := by ring
        rw [h3]
        exact Ideal.add_mem _ hA0cong (hmspan (y^2))
      · rw [hz, zero_add]
        exact mul_ne_zero hmK (pow_ne_zero 2 hyne)
      · intro φ
        have h3 : φ (((A0 + (m : 𝓞 K) * y^2 : 𝓞 K)) : K)
            = φ ((A0 : 𝓞 K) : K) + (m:ℝ) * (φ ((y : 𝓞 K) : K))^2 := by
          push_cast
          simp only [map_add, map_mul, map_pow, map_natCast]
        rw [h3]
        have h4 : 0 ≤ (m:ℝ) * (φ ((y : 𝓞 K) : K))^2 :=
          mul_nonneg (le_of_lt hmR) (by positivity)
        linarith [hA0pos φ]
    · exact ⟨A0, hA0B, hA0cong, hz, hA0pos⟩
  obtain ⟨A2, hA2B, hA2cong, hA2ne, hA2pos⟩ := hmain
  -- the numerator `A1 = b A2`
  obtain ⟨A1, hA1eq, hA1sub⟩ := hprop A2 hA2B
  have hA2neK : ((A2 : 𝓞 K) : K) ≠ 0 := fun h => hA2ne (IsFractionRing.injective (𝓞 K) K h)
  have hBneK : ((b : K)) ≠ 0 := Units.ne_zero b
  have hA1ne : A1 ≠ 0 := by
    intro h0
    have h1 : ((A1 : 𝓞 K) : K) = 0 := by rw [h0]; simp
    rw [hA1eq] at h1
    exact mul_ne_zero hBneK hA2neK h1
  have hA1cong : A1 - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
    have h3 : A1 - 1 = (A1 - A2) + (A2 - 1) := by ring
    rw [h3]
    exact Ideal.add_mem _ hA1sub hA2cong
  have hA1pos : ∀ φ : K →+* ℝ, 0 < φ ((A1 : 𝓞 K) : K) := by
    intro φ
    rw [hA1eq, map_mul]
    exact mul_pos (hpos' φ) (hA2pos φ)
  -- the integral case for `A1` and `A2`
  have hI1 := artinSym_spanSingleton_integral (K := K) (L := L) hcomm m hm hram hprinc
    A1 hA1ne hA1cong hA1pos
  have hI2 := artinSym_spanSingleton_integral (K := K) (L := L) hcomm m hm hram hprinc
    A2 hA2ne hA2cong hA2pos
  -- multiplicativity settles the principal ideal `(b) = (A1)/(A2)`
  have hAne : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((b : K)) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hBneK
  have hA2ne0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((A2 : 𝓞 K) : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hA2neK
  have hkey : artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (b : K))
      * artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((A2 : 𝓞 K) : K)) = 1 := by
    rw [← artinSym_mul (K := K) (L := L) hcomm hAne hA2ne0,
      FractionalIdeal.spanSingleton_mul_spanSingleton, ← hA1eq, hI1]
  rw [hI2, mul_one] at hkey
  exact hkey

end NK.CFTLib.Arl
