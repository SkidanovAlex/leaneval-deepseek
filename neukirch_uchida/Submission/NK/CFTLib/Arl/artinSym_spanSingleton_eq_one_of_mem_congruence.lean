import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.exists_denominator_ideal
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_integral

/-!
# The Artin symbol of a principal ideal `(b)` with `(b)` in the congruence subgroup of `m`

Let `L/K` be a finite abelian (Galois) extension of number fields, `m > 0` a modulus whose
prime divisors are unramified in `L`, and `hprinc` the ideal-theoretic reciprocity law at modulus
`m`: the Artin symbol of every principal ideal `(a)` with `a ∈ 𝓞 K`, `a ≡ 1 mod m` and `a` totally
positive is trivial.

The main result, `NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_mem_congruence`, is the
principal case of the well-definedness of the idèlic Artin map: if `U ≤ 𝕀 K` is the congruence
subgroup of modulus `m` (`NK.CFTLib.Arl.IsCongruenceSubgroup m U`) and the principal idèle of
`b ∈ Kˣ` lies in `U`, then `artinSym (b·𝒪_K) = 1`.

The proof proceeds in three steps.

* `NK.CFTLib.Arl.forall_ringHom_pos_of_forall_realPlace_pos`: the positivity hypothesis of
  `hprinc`, which is stated for the ring homomorphisms `K →+* ℝ`, is the same as positivity at the
  real places (read in the completions `K_w ≅ ℝ`), which is what the definition of the congruence
  subgroup provides.
* `NK.CFTLib.Arl.exists_integral_denominator_of_congr`: the arithmetic reduction.  The ideal `B`
  of `NK.CFTLib.Arl.exists_denominator_ideal` consists of the `x` with `b x` integral and
  `b x ≡ x mod m`; it is coprime to `(m)` and contains an element `≡ 1 mod m` and a nonzero
  element.  Hence there are `n ∈ B` with `n ≡ 1 mod m` and `n ≠ 0`, and the numerator `c` of `b n`;
  then `c = b n²` is integral and `c ≡ 1 mod m`.  (The square is what makes the total positivity
  free: if `a = 0` happens to satisfy the congruence, `a + m y` and `a + 2 m y` do too, and at
  least one of the latter two is nonzero.)
* `NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_congr_pos` assembles the two: `n²` and
  `c = b n²` are both integral, `≡ 1 mod m` and totally positive, so
  `artinSym (n²) = artinSym (c) = 1` by the integral case
  (`NK.CFTLib.Arl.artinSym_spanSingleton_integral`), and multiplicativity of `artinSym` on the
  identity `(c) = (b)·(n²)` yields `artinSym (b) = 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

/-! ## Positivity at the real places versus positivity at the real embeddings -/

/-- **Positivity at the real places versus total positivity.**  A ring homomorphism `φ : K →+* ℝ`
of a number field is the real embedding of a real place `w`, read through the identification
`K_w ≅ ℝ`; hence positivity of `x` at every real place is the same as positivity of `φ x` for every
`φ : K →+* ℝ`. -/
theorem forall_ringHom_pos_of_forall_realPlace_pos {K : Type*} [Field K] [NumberField K] (x : K)
    (h : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap K w.Completion x)) :
    ∀ φ : K →+* ℝ, 0 < φ x := by
  intro φ
  -- the complexification of `φ` is a real complex embedding
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

/-! ## The arithmetic reduction -/

/-- **A denominator of `b` which is `≡ 1 mod m`.**  If `b ∈ Kˣ` is congruent to `1` modulo `m` at
every prime `𝔭 | (m)`, then there are `n, c ∈ 𝓞 K` with `n ≠ 0`, `n ≡ 1 mod m`, `c = b n²` and
`c ≡ 1 mod m`.

The element `n` is an element of the ideal `B` of `NK.CFTLib.Arl.exists_denominator_ideal`
(consisting of the `x` with `b x` integral and `b x ≡ x mod m`) which is `≡ 1 mod m`, made nonzero
by adding a multiple of `m y` for a nonzero `y ∈ B`; the numerator `c = b n² = (b n)·n` is then
integral, and congruent to `1` because `b ≡ 1` and `n ≡ 1`.  The square is what makes the total
positivity in the next step automatic. -/
theorem exists_integral_denominator_of_congr {K : Type*} [Field K] [NumberField K]
    (m : ℕ) (hm : 0 < m) (b : Kˣ)
    (hcong : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
      Valued.v (algebraMap K (𝔭.adicCompletion K) (b : K) - 1)
        ≤ Valued.v ((m : ℕ) : 𝔭.adicCompletion K)) :
    ∃ n : 𝓞 K, n ≠ 0 ∧ n - 1 ∈ Ideal.span {(m : 𝓞 K)} ∧
      ∃ c : 𝓞 K, (c : K) = (b : K) * (n : K) ^ 2 ∧ c - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
  classical
  obtain ⟨B, ⟨a, haB, ha1⟩, ⟨y, hyB, hy0⟩, hprop⟩ :=
    exists_denominator_ideal (K := K) m hm b hcong
  have hm0 : (m : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hmJ : (m : 𝓞 K) ∈ Ideal.span {(m : 𝓞 K)} := Ideal.mem_span_singleton_self _
  have hmyB : (m : 𝓞 K) * y ∈ B := Ideal.mul_mem_left B (m : 𝓞 K) hyB
  have hmyJ : (m : 𝓞 K) * y ∈ Ideal.span {(m : 𝓞 K)} :=
    Ideal.mul_mem_right y (Ideal.span {(m : 𝓞 K)}) hmJ
  -- the numerator `p·n` of an `n ∈ B` with `n ≡ 1 mod m` is the required element
  have key : ∀ n : 𝓞 K, n ∈ B → n - 1 ∈ Ideal.span {(m : 𝓞 K)} →
      ∃ c : 𝓞 K, (c : K) = (b : K) * (n : K) ^ 2 ∧ c - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
    intro n hnB hn1
    obtain ⟨p, hp, hpx⟩ := hprop n hnB
    refine ⟨p * n, ?_, ?_⟩
    · rw [show ((p * n : 𝓞 K) : K) = (p : K) * (n : K) by push_cast; ring, hp]; ring
    · rw [show p * n - 1 = (p - n) * n + (n * n - 1) by ring,
        show n * n - 1 = (n - 1) * (n + 1) by ring]
      exact Ideal.add_mem _ (Ideal.mul_mem_right n (Ideal.span {(m : 𝓞 K)}) hpx)
        (Ideal.mul_mem_right (n + 1) (Ideal.span {(m : 𝓞 K)}) hn1)
  by_cases h0 : a + (m : 𝓞 K) * y = 0
  · -- `a` is a vanishing solution of the congruence; `a + 2 m y = m y` is a nonzero one
    have hmem : a + 2 * ((m : 𝓞 K) * y) ∈ B :=
      Ideal.add_mem _ haB (Ideal.mul_mem_left B (2 : 𝓞 K) hmyB)
    have hlig : a + 2 * ((m : 𝓞 K) * y) - 1 = (a - 1) + 2 * ((m : 𝓞 K) * y) := by ring
    have hcong' : a + 2 * ((m : 𝓞 K) * y) - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
      rw [hlig]
      exact Ideal.add_mem _ ha1 (Ideal.mul_mem_left _ (2 : 𝓞 K) hmyJ)
    have hne : a + 2 * ((m : 𝓞 K) * y) ≠ 0 := by
      have h2 : a + 2 * ((m : 𝓞 K) * y) = (a + (m : 𝓞 K) * y) + (m : 𝓞 K) * y := by ring
      rw [h2, h0, zero_add]
      exact mul_ne_zero hm0 hy0
    exact ⟨_, hne, hcong', key _ hmem hcong'⟩
  · -- otherwise `a + m y` itself is a nonzero solution
    refine ⟨a + (m : 𝓞 K) * y, h0, ?_, key _ (Ideal.add_mem _ haB hmyB) ?_⟩
    · rw [show a + (m : 𝓞 K) * y - 1 = (a - 1) + (m : 𝓞 K) * y by ring]
      exact Ideal.add_mem _ ha1 hmyJ
    · rw [show a + (m : 𝓞 K) * y - 1 = (a - 1) + (m : 𝓞 K) * y by ring]
      exact Ideal.add_mem _ ha1 hmyJ

/-! ## The principal case -/

/-- **The Artin symbol of `(b)` is trivial for `b ≡ 1 mod m` totally positive** (the principal case
of the reciprocity law, for a fractional ideal). -/
theorem artinSym_spanSingleton_eq_one_of_congr_pos {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
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
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion (b : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K)) = 1 := by
  classical
  obtain ⟨n, hn0, hn1, c, hc, hc1⟩ := exists_integral_denominator_of_congr (K := K) m hm b hcong
  have hnK : (n : K) ≠ 0 := fun h => hn0 (IsFractionRing.injective (𝓞 K) K (by simpa using h))
  have hbpos : ∀ φ : K →+* ℝ, 0 < φ ((b : K)) :=
    forall_ringHom_pos_of_forall_realPlace_pos (K := K) (b : K) hpos
  have hsq : ∀ φ : K →+* ℝ, 0 < φ ((n : K)) ^ 2 := fun φ =>
    sq_pos_of_ne_zero (fun h => hnK ((map_eq_zero φ).mp h))
  -- the two integral elements
  have hn2K : (((n ^ 2 : 𝓞 K)) : K) = (n : K) ^ 2 := by push_cast; ring
  have hn2ne : (n ^ 2 : 𝓞 K) ≠ 0 := pow_ne_zero 2 hn0
  have hn2cong : n ^ 2 - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
    rw [show n ^ 2 - 1 = (n - 1) * (n + 1) by ring]
    exact Ideal.mul_mem_right (n + 1) (Ideal.span {(m : 𝓞 K)}) hn1
  have hn2pos : ∀ φ : K →+* ℝ, 0 < φ (((n ^ 2 : 𝓞 K)) : K) := by
    intro φ; rw [hn2K, map_pow]; exact hsq φ
  have hcne : c ≠ 0 := by
    intro h0
    have h1 : (c : K) = 0 := by rw [h0]; simp
    rw [hc] at h1
    exact mul_ne_zero (Units.ne_zero b) (pow_ne_zero 2 hnK) h1
  have hcpos : ∀ φ : K →+* ℝ, 0 < φ ((c : 𝓞 K) : K) := by
    intro φ; rw [hc, map_mul, map_pow]; exact mul_pos (hbpos φ) (hsq φ)
  -- the integral case for both
  have hI1 := artinSym_spanSingleton_integral (K := K) (L := L) hcomm m hm hram hprinc
    c hcne hc1 hcpos
  have hI2 := artinSym_spanSingleton_integral (K := K) (L := L) hcomm m hm hram hprinc
    (n ^ 2) hn2ne hn2cong hn2pos
  -- multiplicativity settles `(b) = (c)/(n²)`
  have hAne : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((b : K)) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero b)
  have hBne : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (((n ^ 2 : 𝓞 K) : K)) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (by rw [hn2K]; exact pow_ne_zero 2 hnK)
  have hkey : artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (b : K))
      * artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (((n ^ 2 : 𝓞 K) : K))) = 1 := by
    rw [← artinSym_mul (K := K) (L := L) hcomm hAne hBne,
      FractionalIdeal.spanSingleton_mul_spanSingleton, hn2K, ← hc, hI1]
  rw [hI2, mul_one] at hkey
  exact hkey

/-! ## The target -/

-- See Submission/Work/CFTLib/Arl/NOTES_artinSym_congruence.md for the intended proof plan; the statement is exactly `NK.CFTLib.Arl.artinSym_spanSingleton_eq_one` with `hcong`/`hpos` replaced by `hU`/`hb`.
theorem artinSym_spanSingleton_eq_one_of_mem_congruence {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
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
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (b : Kˣ) (hb : NK.GlobalCFT.Idele.principalIdele K b ∈ U) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K)) = 1 := by
  obtain ⟨hcong, hpos⟩ := (hU.2 b).mp hb
  exact artinSym_spanSingleton_eq_one_of_congr_pos (K := K) (L := L) hcomm m hm hram hprinc
    b hcong hpos

end NK.CFTLib.Arl
