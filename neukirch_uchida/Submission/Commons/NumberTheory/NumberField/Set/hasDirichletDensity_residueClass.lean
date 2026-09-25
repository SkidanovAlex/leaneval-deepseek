import Mathlib
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal
import Submission.Commons.NumberTheory.NumberField.Set.isBigO_primeIdealZetaSum_sub_log
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_of_isBigO_primeIdealZetaSum_sub_log
import Submission.Commons.NumberTheory.DirichletCharacter.primeSum_chi_isBigO_one

open scoped Classical
open scoped BigOperators
open Filter Asymptotics

namespace Commons.NumberTheory.NumberField.Set

open IsDedekindDomain

/-- The absolute norm of the prime ideal of `𝓞 ℚ` attached to a rational prime is that prime. -/
lemma absNorm_eq_primesEquiv (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Ideal.absNorm v.asIdeal = (Rat.HeightOneSpectrum.primesEquiv v : ℕ) := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := NumberField.RingOfIntegers ℚ) v
  have hcard : Nat.card (NumberField.RingOfIntegers ℚ ⧸ v.asIdeal)
      = Nat.card (ℤ ⧸ Ideal.span ({(Rat.HeightOneSpectrum.natGenerator
          (R := NumberField.RingOfIntegers ℚ) v : ℤ)} : Set ℤ)) :=
    Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ (Rat.IsIntegralClosure.intEquiv _) h).toEquiv
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hcard]
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [Commons.NumberTheory.NumberField.DedekindZeta.absNorm_span_int]
  rfl

/-- The prime-ideal zeta sum over `ℚ` is the sum over all rational primes. -/
lemma primeIdealZetaSum_univ_rat_eq (s : ℝ) :
    NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))) s
      = ∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s)) := by
  rw [Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_univ_eq_tsum ℚ s]
  trans ∑' v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      ((((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)) : ℕ) : ℝ) ^ (-s)
  · exact tsum_congr fun v => by rw [absNorm_eq_primesEquiv]
  · exact Equiv.tsum_eq (Rat.HeightOneSpectrum.primesEquiv)
      (fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))

/-- Reindex the prime-ideal zeta sum over `ℚ` restricted to a residue class as a sum over
natural primes in that class. -/
lemma primeIdealZetaSum_residueClass_eq (n : ℕ) (a : ZMod n) (s : ℝ) :
    NumberField.Set.primeIdealZetaSum
      {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) |
        ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) = a} s
      = ∑' p : {p : Nat.Primes // ((p.1 : ℕ) : ZMod n) = a}, (((p.1 : ℕ) : ℝ) ^ (-s)) := by
  rw [NumberField.Set.primeIdealZetaSum_def]
  let e : {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) |
        ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) = a} ≃
      {p : Nat.Primes // ((p.1 : ℕ) : ZMod n) = a} :=
    Equiv.subtypeEquiv (Rat.HeightOneSpectrum.primesEquiv) (fun v => by
      simp only [Set.mem_ofPred_eq]
      rw [absNorm_eq_primesEquiv v])
  rw [← Equiv.tsum_eq e.symm (fun v : {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) |
        ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) = a} => (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s))]
  refine tsum_congr fun p => ?_
  have hcoe : (e.symm p).1 = Rat.HeightOneSpectrum.primesEquiv.symm p.1 := rfl
  rw [hcoe, absNorm_eq_primesEquiv, Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply]

lemma one_char_apply (n : ℕ) (x : ZMod n) :
    (1 : DirichletCharacter ℂ n) x = if IsUnit x then 1 else 0 := by
  classical
  by_cases h : IsUnit x
  · rw [if_pos h, MulChar.one_apply h]
  · rw [if_neg h, MulChar.map_nonunit _ h]

lemma summable_primes_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => ((p.1 : ℕ) : ℝ) ^ (-s)) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    (Real.summable_nat_rpow).mpr (by linarith)
  exact h.subtype _

lemma summable_primes_rpow_neg_complex {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) :=
  (summable_primes_rpow_neg hs).map Complex.ofRealCLM Complex.continuous_ofReal

/-- The complex character-orthogonality identity for the prime sum in a residue class,
in indicator form over all rational primes. -/
lemma class_indicator_identity (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) {s : ℝ} (hs : 1 < s) :
    (n.totient : ℂ) * (∑' p : Nat.Primes,
        (if (a : ZMod n) = ((p.1 : ℕ) : ZMod n) then ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) else 0))
      = ∑ χ : DirichletCharacter ℂ n,
          χ ((a : ZMod n))⁻¹
            * (∑' p : Nat.Primes, χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
  classical
  have hsumm_all : Summable (fun p : Nat.Primes => ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) :=
    summable_primes_rpow_neg_complex hs
  have hsumm : ∀ χ : DirichletCharacter ℂ n,
      Summable (fun p : Nat.Primes => χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
    intro χ
    refine Summable.of_norm_bounded (g := fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))
      (f := fun p : Nat.Primes => χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      (summable_primes_rpow_neg hs) (fun p => ?_)
    rw [norm_mul]
    have hχ : ‖χ ((p.1 : ℕ) : ZMod n)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hf : 0 ≤ ((p.1 : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc ‖χ ((p.1 : ℕ) : ZMod n)‖ * ‖((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)‖
        ≤ 1 * ‖((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)‖ := mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
      _ = (((p.1 : ℕ) : ℝ) ^ (-s)) := by
          rw [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]
  symm
  calc ∑ χ : DirichletCharacter ℂ n,
          χ ((a : ZMod n))⁻¹
            * (∑' p : Nat.Primes, χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      = ∑ χ : DirichletCharacter ℂ n, ∑' p : Nat.Primes,
          χ ((a : ZMod n))⁻¹ * (χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [tsum_mul_left]
    _ = ∑' p : Nat.Primes, ∑ χ : DirichletCharacter ℂ n,
          χ ((a : ZMod n))⁻¹ * (χ ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
        rw [Summable.tsum_finsetSum]
        intro χ _
        exact (hsumm χ).mul_left _
    _ = ∑' p : Nat.Primes,
          (∑ χ : DirichletCharacter ℂ n, χ ((a : ZMod n))⁻¹ * χ ((p.1 : ℕ) : ZMod n))
            * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
        refine tsum_congr (fun p => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun χ _ => by ring)
    _ = ∑' p : Nat.Primes,
          (if (a : ZMod n) = ((p.1 : ℕ) : ZMod n) then (n.totient : ℂ) else 0)
            * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
        refine tsum_congr (fun p => ?_)
        rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit ((p.1 : ℕ) : ZMod n)]
    _ = (n.totient : ℂ) * ∑' p : Nat.Primes,
          (if (a : ZMod n) = ((p.1 : ℕ) : ZMod n) then ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) else 0) := by
        rw [← tsum_mul_left]
        refine tsum_congr (fun p => ?_)
        by_cases hp : (a : ZMod n) = ((p.1 : ℕ) : ZMod n) <;> simp [hp]


/-- Splitting `∑_p p^{-s}` into the primes coprime to `n` and those dividing `n`. -/
lemma split_sum (n : ℕ) [NeZero n] {s : ℝ} (hs : 1 < s) :
    (∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s)))
      = (∑' p : Nat.Primes, (if IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0))
        + (∑' p : Nat.Primes, (if IsUnit ((p.1 : ℕ) : ZMod n) then 0 else (((p.1 : ℕ) : ℝ) ^ (-s)))) := by
  have hA : Summable (fun p : Nat.Primes =>
      (if IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0)) := by
    refine Summable.of_norm_bounded (g := fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))
      (f := fun p : Nat.Primes =>
        (if IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0))
      (summable_primes_rpow_neg hs) (fun p => ?_)
    rw [Real.norm_eq_abs]
    have hf : 0 ≤ ((p.1 : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    by_cases h : IsUnit ((p.1 : ℕ) : ZMod n)
    · rw [if_pos h, abs_of_nonneg hf]
    · rw [if_neg h, abs_zero]; exact hf
  have hB : Summable (fun p : Nat.Primes =>
      (if IsUnit ((p.1 : ℕ) : ZMod n) then 0 else (((p.1 : ℕ) : ℝ) ^ (-s)))) := by
    refine Summable.of_norm_bounded (g := fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))
      (f := fun p : Nat.Primes =>
        (if IsUnit ((p.1 : ℕ) : ZMod n) then 0 else (((p.1 : ℕ) : ℝ) ^ (-s))))
      (summable_primes_rpow_neg hs) (fun p => ?_)
    rw [Real.norm_eq_abs]
    have hf : 0 ≤ ((p.1 : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    by_cases h : IsUnit ((p.1 : ℕ) : ZMod n)
    · rw [if_pos h, abs_zero]; exact hf
    · rw [if_neg h, abs_of_nonneg hf]
  rw [← Summable.tsum_add hA hB]
  refine tsum_congr fun p => ?_
  by_cases h : IsUnit ((p.1 : ℕ) : ZMod n) <;> simp [h]

/-- The real part of the `χ = 1` term is the sum over primes coprime to `n`. -/
lemma W_one_re (n : ℕ) [NeZero n] {s : ℝ} (hs : 1 < s) :
    (∑' p : Nat.Primes, (1 : DirichletCharacter ℂ n) ((p.1 : ℕ) : ZMod n)
        * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)).re
      = ∑' p : Nat.Primes,
          (if IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0) := by
  have hsumm : Summable (fun p : Nat.Primes =>
      (1 : DirichletCharacter ℂ n) ((p.1 : ℕ) : ZMod n) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) := by
    refine Summable.of_norm_bounded (g := fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))
      (f := fun p : Nat.Primes => (1 : DirichletCharacter ℂ n) ((p.1 : ℕ) : ZMod n)
        * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)) (summable_primes_rpow_neg hs) (fun p => ?_)
    rw [norm_mul]
    have hχ : ‖(1 : DirichletCharacter ℂ n) ((p.1 : ℕ) : ZMod n)‖ ≤ 1 :=
      DirichletCharacter.norm_le_one _ _
    have hf : 0 ≤ ((p.1 : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc ‖(1 : DirichletCharacter ℂ n) ((p.1 : ℕ) : ZMod n)‖ * ‖((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)‖
        ≤ 1 * ‖((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
      _ = (((p.1 : ℕ) : ℝ) ^ (-s)) := by
          rw [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]
  rw [Complex.re_tsum hsumm]
  refine tsum_congr fun p => ?_
  rw [one_char_apply]
  by_cases h : IsUnit ((p.1 : ℕ) : ZMod n)
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h]; simp

set_option backward.isDefEq.respectTransparency false in
lemma not_isUnit_iff_dvd (n : ℕ) (p : Nat.Primes) :
    ¬ IsUnit (((p.1 : ℕ) : ZMod n)) ↔ p.1 ∣ n := by
  rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd p.2, not_not]

set_option backward.isDefEq.respectTransparency false in
lemma mem_badPrimes (n : ℕ) [NeZero n] (p : Nat.Primes) :
    p ∈ n.primeFactors.attach.image
        (fun q => (⟨q.1, (Nat.mem_primeFactors.mp q.2).1⟩ : Nat.Primes)) ↔ p.1 ∣ n := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, _, hq⟩
    have hq1 : q.1 = p.1 := by rw [← hq]
    rw [← hq1]
    exact (Nat.mem_primeFactors.mp q.2).2.1
  · intro h
    refine ⟨⟨p.1, Nat.Prime.mem_primeFactors p.2 h (NeZero.ne n)⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

set_option backward.isDefEq.respectTransparency false in
lemma sum_bad_le (n : ℕ) [NeZero n] {s : ℝ} (hs : 0 ≤ s) :
    (∑' p : Nat.Primes,
        (if IsUnit ((p.1 : ℕ) : ZMod n) then 0 else (((p.1 : ℕ) : ℝ) ^ (-s))))
      ≤ (n.primeFactors.card : ℝ) := by
  classical
  have hbad : ∀ p : Nat.Primes,
      (if IsUnit ((p.1 : ℕ) : ZMod n) then (0:ℝ) else (((p.1 : ℕ) : ℝ) ^ (-s)))
        = (if ¬ IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0) := by
    intro p
    by_cases h : IsUnit ((p.1 : ℕ) : ZMod n) <;> simp [h]
  rw [tsum_congr hbad]
  set bad : Finset Nat.Primes := n.primeFactors.attach.image
      (fun q => (⟨q.1, (Nat.mem_primeFactors.mp q.2).1⟩ : Nat.Primes)) with hbaddef
  rw [tsum_eq_sum (s := bad) (fun p hp => by
    rw [if_neg]
    rw [not_isUnit_iff_dvd]
    intro hd
    exact hp (by rw [hbaddef, mem_badPrimes]; exact hd))]
  calc ∑ p ∈ bad, (if ¬ IsUnit ((p.1 : ℕ) : ZMod n) then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0)
      ≤ ∑ _p ∈ bad, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hp1 : (1 : ℝ) ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast p.2.one_le
        by_cases h : ¬ IsUnit ((p.1 : ℕ) : ZMod n)
        · rw [if_pos h]; exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
        · rw [if_neg h]; norm_num
    _ = (bad.card : ℝ) := by simp
    _ ≤ (n.primeFactors.card : ℝ) := by
        have : bad.card ≤ n.primeFactors.card := by
          rw [hbaddef]
          calc _ ≤ (n.primeFactors.attach).card := Finset.card_image_le
            _ = n.primeFactors.card := Finset.card_attach
        exact_mod_cast this


lemma primeSum_all_isBigO :
    (fun s : ℝ => (∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s)))
        - Real.log (1 / (s - 1)))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℝ)) := by
  refine (Commons.NumberTheory.NumberField.Set.isBigO_primeIdealZetaSum_sub_log ℚ).congr'
    (Filter.EventuallyEq.of_eq (funext fun s => ?_)) Filter.EventuallyEq.rfl
  rw [primeIdealZetaSum_univ_rat_eq]

/-- The Dirichlet-density asymptotic of the indicator of the residue class, reduced to the
character orthogonality identity and the boundedness of the nontrivial prime sums. -/
theorem primeSum_indicator_isBigO (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    (fun s : ℝ => (∑' p : Nat.Primes,
        (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0))
        - (n.totient : ℝ)⁻¹ * Real.log (1 / (s - 1)))
      =O[nhdsWithin (1:ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1:ℝ)) := by
  classical
  have hSne : (fun s : ℝ => ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
      (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n) * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re)
      =O[nhdsWithin (1:ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1:ℝ)) := by
    have hsum : (∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
        fun s : ℝ => (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
          * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re)
        =O[nhdsWithin (1:ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1:ℝ)) := by
      apply IsBigO.sum
      intro χ hχ
      have hχne : χ ≠ 1 := by simpa using hχ
      have h1 : (fun s : ℝ => (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re)
          =O[nhdsWithin (1:ℝ) (Set.Ioi 1)]
            (fun s : ℝ => ‖χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖) := by
        apply IsBigO.of_bound 1
        filter_upwards with s
        rw [Real.norm_eq_abs, Real.norm_of_nonneg (norm_nonneg _), one_mul]
        exact Complex.abs_re_le_norm _
      have h2 : (fun s : ℝ => ‖χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖)
          =O[nhdsWithin (1:ℝ) (Set.Ioi 1)]
            (fun s : ℝ => ‖(∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖) := by
        apply IsBigO.of_bound 1
        filter_upwards with s
        simp only [one_mul, Real.norm_of_nonneg (norm_nonneg _)]
        calc ‖χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖
            ≤ ‖χ ((a:ZMod n))⁻¹‖ * ‖(∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖ := norm_mul_le _ _
          _ ≤ 1 * ‖(∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))‖ :=
              mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (norm_nonneg _)
          _ = _ := one_mul _
      exact h1.trans (h2.trans ((Commons.NumberTheory.DirichletCharacter.primeSum_chi_isBigO_one
        χ hχne).norm_left))
    refine hsum.congr' (Filter.EventuallyEq.of_eq (funext fun s => ?_)) Filter.EventuallyEq.rfl
    simp only [Finset.sum_apply]
  -- Extract the constant for the all-primes sum.
  obtain ⟨Call, hCall⟩ : ∃ Call : ℝ, ∀ᶠ s in nhdsWithin (1:ℝ) (Set.Ioi 1),
      ‖(∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1))‖ ≤ Call := by
    have h := primeSum_all_isBigO
    rw [Asymptotics.isBigO_iff] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by filter_upwards [hc] with s hs; simpa using hs⟩
  -- Extract constants bounding the nontrivial-character contributions.
  obtain ⟨Cne, hCne⟩ : ∃ Cne : ℝ, ∀ᶠ s in nhdsWithin (1:ℝ) (Set.Ioi 1),
      ‖∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
        (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
          * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re‖ ≤ Cne := by
    have h := hSne
    rw [Asymptotics.isBigO_iff] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by filter_upwards [hc] with s hs; simpa using hs⟩
  -- Assemble.
  have hφpos : 0 < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos n)
  refine IsBigO.of_bound ((n.totient : ℝ)⁻¹ * (Call + (n.primeFactors.card : ℝ) + Cne)) ?_
  filter_upwards [self_mem_nhdsWithin, hCall, hCne] with s hs1 hCall' hCne'
  have hs : 1 < s := Set.mem_Ioi.mp hs1
  have hs0 : 0 ≤ s := by linarith
  -- identity
  have hid := class_indicator_identity n a hs
  -- real part of the identity
  have hPS : (∑' p : Nat.Primes, (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then
        ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ) else 0)).re
      = ∑' p : Nat.Primes, (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0) := by
    have hsumm : Summable (fun p : Nat.Primes => (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then
        ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ) else 0)) := by
      refine Summable.of_norm_bounded (g := fun p : Nat.Primes => (((p.1 : ℕ) : ℝ) ^ (-s)))
        (f := fun p : Nat.Primes => (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then
          ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ) else 0)) (summable_primes_rpow_neg hs) (fun p => ?_)
      have hf : 0 ≤ ((p.1:ℕ):ℝ)^(-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      by_cases h : (a : ZMod n) = ((p.1:ℕ):ZMod n)
      · rw [if_pos h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]
      · rw [if_neg h, norm_zero]; exact hf
    rw [Complex.re_tsum hsumm]
    refine tsum_congr fun p => ?_
    by_cases h : (a : ZMod n) = ((p.1:ℕ):ZMod n) <;> simp [h]
  have hidre : (n.totient : ℝ) * (∑' p : Nat.Primes, (if (a : ZMod n) = ((p.1:ℕ):ZMod n)
        then (((p.1:ℕ):ℝ)^(-s)) else 0))
      = ∑ χ : DirichletCharacter ℂ n,
          (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re := by
    have h := congrArg Complex.re hid
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, hPS] at h
    rw [← Complex.reCLM_apply, map_sum Complex.reCLM] at h
    exact h
  -- split the finite sum
  have hsplit : ∑ χ : DirichletCharacter ℂ n,
        (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
          * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re
      = ((1 : DirichletCharacter ℂ n) ((a:ZMod n))⁻¹
          * (∑' p : Nat.Primes, (1 : DirichletCharacter ℂ n) ((p.1:ℕ):ZMod n)
            * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re
        + ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
            (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re := by
    rw [Fintype.sum_eq_add_sum_compl 1]
  -- the trivial term
  have hone : ((1 : DirichletCharacter ℂ n) ((a:ZMod n))⁻¹
        * (∑' p : Nat.Primes, (1 : DirichletCharacter ℂ n) ((p.1:ℕ):ZMod n)
          * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re
      = (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0)) := by
    have h1 : (1 : DirichletCharacter ℂ n) ((a:ZMod n))⁻¹ = 1 := by
      rw [ZMod.inv_coe_unit, MulChar.one_apply (Units.isUnit a⁻¹)]
    rw [h1, one_mul]
    exact W_one_re n hs
  -- split the all-primes sum
  have hsplit2 := split_sum (n := n) hs
  -- bad bound
  have hbad : (∑' p : Nat.Primes,
        (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s)))) ≤ (n.primeFactors.card : ℝ) :=
    sum_bad_le n hs0
  -- assemble the pointwise bound
  have key : (n.totient : ℝ)
        * (∑' p : Nat.Primes, (if (a : ZMod n) = ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0))
        - Real.log (1 / (s - 1))
      = ((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
        - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))
        + ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
            (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re := by
    rw [hidre, hsplit, hone]
    have hsun : (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0))
        = (∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s)))
          - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s)))) := by
      linarith [hsplit2]
    rw [hsun]; ring
  rw [Real.norm_eq_abs, norm_one, mul_one]
  have hA : |(∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1))| ≤ Call := by
    rw [← Real.norm_eq_abs]; exact hCall'
  have hB0 : 0 ≤ (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s)))) := by
    refine tsum_nonneg fun p => ?_
    by_cases h : IsUnit ((p.1:ℕ):ZMod n)
    · simp [h]
    · simp only [h, if_false]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hB : |(∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))|
      ≤ (n.primeFactors.card : ℝ) := by
    rw [abs_of_nonneg hB0]; exact hbad
  have hC : |∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
        (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
          * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re| ≤ Cne := by
    rw [← Real.norm_eq_abs]; exact hCne'
  have hb : |((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
        - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))
        + ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
            (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
              * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re|
      ≤ Call + (n.primeFactors.card : ℝ) + Cne := by
    have hsub : |((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
        - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))|
        ≤ Call + (n.primeFactors.card : ℝ) := by
      have htri : |((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
          - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))|
          ≤ |(∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1))|
            + |(∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))| := by
        rw [abs_le]
        constructor <;>
          linarith [neg_le_abs ((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1))),
            le_abs_self ((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1))),
            neg_le_abs (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s)))),
            le_abs_self (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))]
      linarith
    calc |((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
          - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))
          + ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
              (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
                * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re|
        ≤ |((∑' p : Nat.Primes, (((p.1 : ℕ) : ℝ) ^ (-s))) - Real.log (1 / (s - 1)))
            - (∑' p : Nat.Primes, (if IsUnit ((p.1:ℕ):ZMod n) then 0 else (((p.1:ℕ):ℝ)^(-s))))|
          + |∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
              (χ ((a:ZMod n))⁻¹ * (∑' p : Nat.Primes, χ ((p.1:ℕ):ZMod n)
                * ((((p.1:ℕ):ℝ)^(-s):ℝ):ℂ))).re| := abs_add_le _ _
      _ ≤ (Call + (n.primeFactors.card : ℝ)) + Cne := add_le_add hsub hC
      _ = Call + (n.primeFactors.card : ℝ) + Cne := by ring
  rw [show (∑' p : Nat.Primes, (if (a:ZMod n) = ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0))
      - (n.totient:ℝ)⁻¹ * Real.log (1/(s-1))
      = (n.totient:ℝ)⁻¹ * ((n.totient:ℝ) * (∑' p : Nat.Primes,
          (if (a:ZMod n) = ((p.1:ℕ):ZMod n) then (((p.1:ℕ):ℝ)^(-s)) else 0))
          - Real.log (1/(s-1))) from by
      field_simp]
  rw [abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hφpos)), key]
  exact mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.mpr hφpos))


/-- The residue-class sum over `Nat.Primes` (as a subtype) equals the indicator sum. -/
lemma subtype_eq_indicator (n : ℕ) (a : ZMod n) (s : ℝ) :
    (∑' p : {p : Nat.Primes // ((p.1 : ℕ) : ZMod n) = a}, (((p.1 : ℕ) : ℝ) ^ (-s)))
      = ∑' p : Nat.Primes, (if ((p.1 : ℕ) : ZMod n) = a then (((p.1 : ℕ) : ℝ) ^ (-s)) else 0) := by
  let G : Nat.Primes → ℝ := fun p => (((p.1 : ℕ) : ℝ) ^ (-s))
  change (∑' p : {p : Nat.Primes // ((p.1 : ℕ) : ZMod n) = a}, G p)
      = ∑' p : Nat.Primes, (if ((p.1 : ℕ) : ZMod n) = a then G p else 0)
  rw [show (∑' p : {p : Nat.Primes // ((p.1 : ℕ) : ZMod n) = a}, G p)
      = ∑' p : {p : Nat.Primes // p ∈ {q : Nat.Primes | ((q.1 : ℕ) : ZMod n) = a}}, G p from rfl]
  rw [tsum_subtype]
  refine tsum_congr fun p => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- **Dirichlet's theorem on primes in arithmetic progressions, Dirichlet-density form.**

The set of rational primes `p` with `p ≡ a (mod n)` has Dirichlet density `1/φ(n)`. -/
theorem hasDirichletDensity_residueClass (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    NumberField.Set.HasDirichletDensity
      {p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) |
        ((Ideal.absNorm p.asIdeal : ℕ) : ZMod n) = (a : ZMod n)}
      ((Nat.totient n : ℝ)⁻¹) := by
  refine Commons.NumberTheory.NumberField.Set.hasDirichletDensity_of_isBigO_primeIdealZetaSum_sub_log ?_
  refine (primeSum_indicator_isBigO n a).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards with s
  rw [primeIdealZetaSum_residueClass_eq, subtype_eq_indicator]
  congr 1
  refine tsum_congr fun p => ?_
  by_cases h : (a : ZMod n) = ((p.1 : ℕ) : ZMod n)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

end Commons.NumberTheory.NumberField.Set
