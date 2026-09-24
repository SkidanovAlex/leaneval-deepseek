import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.JR2.numeric_helpers
import Submission.Work.ChenPlan.LinearSieve.JR2.sharp_gp
import Submission.Work.ChenPlan.LinearSieve.JR2.q_trick_lower_core
import Submission.Work.ChenPlan.LinearSieve.JR2.subSieve_SharpNorm
import Submission.Work.ChenPlan.LinearSieve.JR2.Qmod_mul_VfR
import Submission.Work.ChenPlan.LinearSieve.Framework
import Submission.Work.ChenPlan.LinearSieve.RI.support_lt
import Submission.Work.ChenPlan.LinearSieve.Numerics.riPsi_le

namespace Work.ChenPlan.LinearSieve.JR2

open Finset
open scoped BigOperators

noncomputable section

open Work.NumberTheory.Chen.APSwitchUpper

set_option maxHeartbeats 2000000

/-! ## Elementary helpers -/

/-- The sharp error profile is at most one. -/
lemma errH_le_one (s : ℝ) : errH s ≤ 1 := by
  by_cases h : s ≤ 2
  · rw [errH_of_le_two h, Real.exp_le_one_iff]; norm_num
  · rw [not_le] at h
    by_cases h3 : s ≤ 3
    · rw [errH_of_between h h3, Real.exp_le_one_iff]; linarith
    · rw [not_le] at h3
      rw [errH_of_three_lt h3, div_le_one (by linarith)]
      have h4 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith

/-- The sharp-sieve error `ε·C₂·errH s` is below `η/2000`. -/
lemma sharp_err_le_eta (ε η : ℝ) (hε0 : 0 ≤ ε) (hεη : ε ≤ min η 1 / 10 ^ 11)
    (hη : 0 < η) (s : ℝ) : ε * (1000 * 10100) * errH s ≤ η / 2000 := by
  have h1 : ε ≤ η / 10 ^ 11 := by
    have h2 : min η 1 ≤ η := min_le_left _ _
    linarith
  have h3 : ε * (1000 * 10100) ≤ η / 2000 := by
    nlinarith [h1, hε0, hη]
  have h4 : 0 ≤ ε * (1000 * 10100) := by positivity
  have h6 : ε * (1000 * 10100) * errH s ≤ ε * (1000 * 10100) :=
    calc ε * (1000 * 10100) * errH s ≤ ε * (1000 * 10100) * 1 :=
          mul_le_mul_of_nonneg_left (errH_le_one s) h4
      _ = ε * (1000 * 10100) := mul_one _
  linarith

/-- The `Pz`-truncated remainder sum is bounded by `remSum` at any larger level. -/
lemma sum_filter_Pz_le_remSum (A : BoundingSieve) (Z D₁ D : ℝ) (h : D₁ ≤ D) :
    (∑ m ∈ (Pz A Z).divisors.filter (fun m : ℕ => (m : ℝ) < D₁),
        (3 : ℝ) ^ m.primeFactors.card * |A.rem m|)
      ≤ Submission.ChenPlan.remSum A D := by
  rw [Submission.ChenPlan.remSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  obtain ⟨hmd, hmlt⟩ := hm
  exact ⟨Nat.mem_divisors.mpr
      ⟨(Nat.mem_divisors.mp hmd).1.trans (RI.Pz_dvd_prodPrimes A Z), A.prodPrimes_ne_zero⟩,
    lt_of_lt_of_le hmlt h⟩

/-- **The lower half of the v6 contract, assembled** (mirror of `linear_sieve_upper_v6`).

Inputs: `hL : LayerSharpBound 1000 (99/100)`, `hLip : RiLipschitz`.

RECIPE.  Given `K ≥ 0`, `η > 0`, put `ε := min (1/100) (min η 1 / 10^11)`,
`u₀ := max 2 (exp (K/ε))`, `Qb := ∏_{p < ⌈u₀⌉₊} p`, `Q := Qmod A u₀`, `D'' := ⌊D/Q⌋`,
`σ := log D/log z ≥ 49/10`, and take the thresholds
`D₀ := max (max 2 (2*Qb+2)) 4` and
`z₀ := max (max (exp 8) (u₀+1)) (exp (10^6 * (u₀+2)^2 / η))` — the `η`-dependence of `z₀` is
what makes the `Q`-shift loss `C·(σ - σ'')` smaller than `η` (uniformly for all `D, z ≥ z₀`).

`sharp_gm 1000 (99/100) …` gives
`VfR(P/Q) z·(1 - riPsi σ'' - ε·(1000·10100)·errH σ'') ≤ RI.Gm (P/Q) z D''` for
`σ'' := log D''/log z` (its hypotheses: `2 ≤ z`, `1 ≤ D''`, `SharpNorm (subSieve A Q _) z ε` from
`subSieve_SharpNorm` with `K ≤ ε log u₀`, and `2 ≤ σ''`, which holds since `σ'' ≥ 49/10 - η`).
`q_trick_lower_core` (its `Z² ≤ D''` side condition holds since `σ'' ≥ 2`) gives the `λ⁻` minorant
for `siftedSumR A z`; splitting `multSum = ν·X + rem` the main term factorises as
`∏_{p∣Q}(1-ν_p)·Σ_d λ⁻(d)ν_d = ∏_{p∣Q}(1-ν_p)·RI.Gm (P/Q) z D''` (`Gm_eq_sum_lamMinus` +
`lamMinus_eq_of_dvd`), the product combines with `VfR(P/Q) z` into `VfR A z` by `Qmod_mul_VfR`, and
the remainder is `≥ -remSum A D` (the third conjunct of `q_trick_lower_core` has the absolute
values, and `Σ_{m | Pz A z, m < Q·D''}3^{ω(m)}|rem m| ≤ remSum A D` since `Q·D'' ≤ D`).

Numerics: `riPsi σ'' ≤ riPsi (49/10) + C(σ-σ'') ≤ 7/1000 + η/2000` using `BTermCount.riPsi_antitone`
(`riPsi` is antitone, so for `σ'' ≥ 49/10` monotonicity suffices, and for `σ'' < 49/10` the shift
bound gives it a uniform `≤ C(σ-σ'') ≤ η/2000`) and `Numerics.riPsi_le` (`riPsi (49/10) ≤ 7/1000`);
also `ε·(1000·10100)·errH σ'' ≤ η/2000` for `ε ≤ min η 1 / 10^11` (`sharpness_error_le` with `η`
in place of `1/4000`, i.e. `ε·C₂ ≤ η/10^11·10^7 = η/10^4 ≤ η/2000`).  Hence
`1 - riPsi σ'' - εC₂errH σ'' ≥ 1 - 7/1000 - η/1000 ≥ 993/1000 - η`. -/
theorem linear_sieve_lower_v6 (hL : Work.ChenPlan.LinearSieve.JR2.LayerSharpBound 1000 (99/100))
    (hLip : Work.ChenPlan.LinearSieve.JR2.RiLipschitz) :
    Submission.ChenPlan.LinearSieveLower := by
  intro K hK η hη
  have hεpos : 0 < min η 1 / 10 ^ 11 := by
    have h1 : 0 < min η 1 := lt_min hη one_pos
    positivity
  set ε : ℝ := min (1 / 100) (min η 1 / 10 ^ 11) with hεdef
  have hεgt : 0 < ε := by rw [hεdef]; exact lt_min (by norm_num) hεpos
  have hε0 : 0 ≤ ε := hεgt.le
  have hε1 : ε ≤ 1 / 100 := by rw [hεdef]; exact min_le_left _ _
  have hεη : ε ≤ min η 1 / 10 ^ 11 := by rw [hεdef]; exact min_le_right _ _
  set u₀ : ℝ := max 2 (Real.exp (K / ε)) with hu₀def
  have hu₀2 : 2 ≤ u₀ := by rw [hu₀def]; exact le_max_left _ _
  have hKε : K ≤ ε * Real.log u₀ := by
    rw [hu₀def]; exact (u0_bounds K ε hεgt).2
  set Qb : ℕ := primorial ⌈u₀⌉₊ with hQbdef
  set R : ℝ := 2 * (Qb : ℝ) + 2 with hRdef
  have hR2 : 2 ≤ R := by
    rw [hRdef]
    have h : (0 : ℝ) ≤ (Qb : ℝ) := Nat.cast_nonneg _
    linarith
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  refine ⟨max 2 R, max (max (u₀ + 2) R) (Real.exp (200001 * Real.log R / η)), ?_⟩
  intro A z D hD0 hz0 hz2 hlin hlinR hlinL hlinM hX hs
  -- ## The threshold consequences
  have hD2 : (2 : ℝ) ≤ D := le_trans (le_max_left _ _) hD0
  have hDR : R ≤ D := le_trans (le_max_right _ _) hD0
  have hDpos : 0 < D := by linarith
  have hzR : R ≤ z := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hz0)
  have hzu₀ : u₀ ≤ z := by
    have h1 : u₀ + 2 ≤ max (u₀ + 2) R := le_max_left _ _
    have h2 : max (u₀ + 2) R ≤ max (max (u₀ + 2) R) (Real.exp (200001 * Real.log R / η)) :=
      le_max_left _ _
    linarith [le_trans (le_trans h1 h2) hz0]
  have hzE : Real.exp (200001 * Real.log R / η) ≤ z := le_trans (le_max_right _ _) hz0
  have hzlog : 200001 * Real.log R / η ≤ Real.log z := by
    have h := Real.log_le_log (Real.exp_pos _) hzE
    rwa [Real.log_exp] at h
  have hz1 : 1 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  -- ## `Q` and its size
  set Q : ℕ := Qmod A u₀ with hQdef
  have hQnz : Q ≠ 0 := Qmod_ne_zero A u₀
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQnz
  have hQle : Q ≤ Qb := by
    have hsub : A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < u₀) ⊆ Nat.primesLE ⌈u₀⌉₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Nat.mem_primesLE]
      exact ⟨le_of_lt (Nat.lt_ceil.mpr hp.2), Nat.prime_of_mem_primeFactors hp.1⟩
    have h := Finset.prod_le_prod_of_subset_of_one_le₀ (f := fun p : ℕ => p) hsub
      (fun i _ => by positivity) (fun i hi _ => (Nat.mem_primesLE.mp hi).2.one_le)
    rw [hQdef, Qmod, hQbdef, primorial_eq_prod_primesLE]
    exact h
  have hQ2R : 2 * (Q : ℝ) ≤ R := by
    have h : (Q : ℝ) ≤ (Qb : ℝ) := by exact_mod_cast hQle
    rw [hRdef]; linarith
  have hzQ2 : 2 * (Q : ℝ) ≤ z := le_trans hQ2R hzR
  have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hQpos : 0 < (Q : ℝ) := by linarith
  have h2Q1 : 1 ≤ 2 * (Q : ℝ) := by linarith
  have h2Qpos : 0 < 2 * (Q : ℝ) := by linarith
  have h2QR : 2 * (Q : ℝ) < R := by
    have h : (Q : ℝ) ≤ (Qb : ℝ) := by exact_mod_cast hQle
    rw [hRdef]; linarith
  -- ## The `Q`-shift is small
  have hlog2Q : Real.log (2 * (Q : ℝ)) ≤ η / 200000 * Real.log z := by
    have hle : Real.log (2 * (Q : ℝ)) ≤ Real.log R := by
      rw [hRdef]
      exact Real.log_le_log h2Qpos (by linarith)
    have hstep : Real.log R ≤ η / 200000 * Real.log z := by
      have ha : Real.log R ≤ η / 200001 * Real.log z := by
        have h := hzlog
        rw [div_le_iff₀ hη] at h
        nlinarith [h]
      have hb : η / 200001 * Real.log z ≤ η / 200000 * Real.log z := by
        apply mul_le_mul_of_nonneg_right _ hlogz.le
        exact div_le_div_of_nonneg_left hη.le (by norm_num) (by norm_num)
      linarith
    linarith
  -- ## The shifted level `D''`
  set D'' : ℝ := D / (2 * (Q : ℝ)) with hD''def
  have hD''pos : 0 < D'' := by rw [hD''def]; positivity
  have hD''1 : 1 < D'' := by
    rw [hD''def, lt_div_iff₀ h2Qpos]
    linarith
  have hD''leD : D'' ≤ D := by
    rw [hD''def, div_le_iff₀ h2Qpos]
    nlinarith [hDpos, h2Q1]
  have hQD'' : (Q : ℝ) * D'' = D / 2 := by
    rw [hD''def]; field_simp
  have hlogD'' : Real.log D'' = Real.log D - Real.log (2 * (Q : ℝ)) := by
    rw [hD''def, Real.log_div (ne_of_gt hDpos) (ne_of_gt h2Qpos)]
  have hD''z2 : z ^ 2 ≤ D'' := by
    rw [← Real.log_le_log_iff (by positivity : (0 : ℝ) < z ^ 2) hD''pos, Real.log_pow, hlogD'']
    have hlogDge : 49 / 10 * Real.log z ≤ Real.log D := (le_div_iff₀ hlogz).mp hs
    have h2Qz : Real.log (2 * (Q : ℝ)) ≤ Real.log z := Real.log_le_log h2Qpos hzQ2
    push_cast
    linarith
  have hσ''2 : 2 ≤ Real.log D'' / Real.log z := by
    have h := hD''z2
    rw [← Real.log_le_log_iff (by positivity : (0 : ℝ) < z ^ 2) hD''pos, Real.log_pow] at h
    push_cast at h
    rw [le_div_iff₀ hlogz]
    linarith
  have hσ''σ : Real.log D'' / Real.log z ≤ Real.log D / Real.log z := by
    have h := Real.log_le_log hD''pos hD''leD
    calc Real.log D'' / Real.log z = Real.log D'' * (Real.log z)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ Real.log D * (Real.log z)⁻¹ := mul_le_mul_of_nonneg_right h (by positivity)
      _ = Real.log D / Real.log z := by rw [div_eq_mul_inv]
  have hshift : Real.log D / Real.log z - Real.log D'' / Real.log z ≤ η / 200000 := by
    have heq : Real.log D / Real.log z - Real.log D'' / Real.log z
        = Real.log (2 * (Q : ℝ)) / Real.log z := by
      rw [hlogD'', div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [heq, div_le_iff₀ hlogz]
    linarith [hlog2Q]
  -- ## The numerical content of the main term
  have hriPsi : riPsi (Real.log D'' / Real.log z) ≤ 7 / 1000 + η / 2000 := by
    obtain ⟨C, hC0, hC100, -, hCpsi⟩ := hLip
    have h1 := hCpsi (Real.log D / Real.log z) (Real.log D'' / Real.log z) hσ''2 hσ''σ
    rw [abs_le] at h1
    have h2 : riPsi (Real.log D / Real.log z) ≤ 7 / 1000 := Numerics.riPsi_le _ hs
    have h4 : 0 ≤ Real.log D / Real.log z - Real.log D'' / Real.log z := by linarith
    have h5 := mul_le_mul hC100 hshift h4 (by norm_num : (0 : ℝ) ≤ 100)
    have h3 : C * (Real.log D / Real.log z - Real.log D'' / Real.log z) ≤ η / 2000 := by
      nlinarith [h5]
    linarith [h1.2, h2, h3]
  set κ : ℝ := 1 - riPsi (Real.log D'' / Real.log z)
    - ε * (1000 * 10100) * errH (Real.log D'' / Real.log z) with hκdef
  have hκge : 993 / 1000 - η ≤ κ := by
    have herr := sharp_err_le_eta ε η hε0 hεη hη (Real.log D'' / Real.log z)
    rw [hκdef]
    linarith [hriPsi, herr]
  -- ## The `Q`-trick
  have hcore := q_trick_lower_core A u₀ z D'' hu₀2 hzu₀ hz2 hD''1 hD''z2
  obtain ⟨hminor, hfac, hrem3⟩ := hcore
  set Λ : ℝ := ∏ p ∈ (Qmod A u₀).primeFactors, (1 - A.nu p) with hΛdef
  set sub : BoundingSieve := subSieve A Q (Qmod_dvd A u₀) with hsubdef
  set T' : ℝ := ∑ d ∈ (Pz sub z).divisors, lamMinus (A.prodPrimes / Q) D'' d * A.nu d with hT'def
  set Sν : ℝ := ∑ q ∈ Q.divisors, ∑ d ∈ (Pz sub z).divisors,
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d * A.nu (q * d)
    with hSνdef
  set Sr : ℝ := ∑ q ∈ Q.divisors, ∑ d ∈ (Pz sub z).divisors,
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d * A.rem (q * d)
    with hSrdef
  set S : ℝ := ∑ q ∈ Q.divisors, ∑ d ∈ (Pz sub z).divisors,
    ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d * A.multSum (q * d)
    with hSdef
  -- positivity of the `Q`-product
  have hΛnn : 0 ≤ Λ := by
    rw [hΛdef, Qmod_primeFactors]
    exact VfR_nonneg A u₀
  -- the `Gm` identification
  have hGmEq : T' = RI.Gm sub z D'' := by
    rw [hT'def, ← Gm_eq_sum_lamMinus sub z D'']
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdd : d ∣ Pz sub z := (Nat.mem_divisors.mp hd).1
    have hd2 : d ∣ A.prodPrimes / Q := hdd.trans (RI.Pz_dvd_prodPrimes sub z)
    rw [lamMinus_eq_of_dvd hdd hd2]
    rfl
  -- the sharp lower sieve for the `P/Q`-problem
  have hSharp : SharpNorm sub z ε := subSieve_SharpNorm A hK hε0 hu₀2 hKε hlinR
  have hgm : VfR sub z * κ ≤ RI.Gm sub z D'' := by
    have h := sharp_gm 1000 (99 / 100) (by norm_num) (by norm_num) (by norm_num) hL
      sub ε z D'' hε0 hε1 hz2 (le_of_lt hD''1) hSharp hσ''2
    rw [hκdef]
    exact h
  -- ## Splitting `multSum`
  have hsplit : S = A.totalMass * Sν + Sr := by
    rw [hSdef, hSνdef, hSrdef]
    have hpt : ∀ q d : ℕ,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d * A.multSum (q * d)
        = ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d * A.nu (q * d)
            * A.totalMass
          + ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d
              * A.rem (q * d) := by
      intro q d; rw [BoundingSieve.multSum_eq_main_err]; ring
    simp only [hpt]
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
    have h1 : (∑ q ∈ Q.divisors, ∑ d ∈ (Pz sub z).divisors,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d
            * A.nu (q * d) * A.totalMass)
        = A.totalMass * (∑ q ∈ Q.divisors, ∑ d ∈ (Pz sub z).divisors,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d
            * A.nu (q * d)) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun d _ => by ring))
    rw [h1]
  -- ## The main term
  have hmain : Sν = Λ * T' := by
    rw [hSνdef, hΛdef, hT'def]
    exact hfac
  have hGmchain : VfR sub z * κ ≤ T' := by rw [hGmEq]; exact hgm
  have hVfRmul : Λ * (VfR sub z * κ) = VfR A z * κ := by
    rw [hΛdef]
    rw [← mul_assoc, Qmod_mul_VfR A hzu₀]
  have hVfRsieve : VfR A z = Submission.ChenPlan.sieveV A := VfR_eq_sieveV A hlin.1
  -- ## The remainder term
  have hQD''le : (Qmod A u₀ : ℝ) * D'' ≤ D := by
    have h : (Q : ℝ) * D'' ≤ D := by rw [hQD'']; linarith [hDpos]
    exact h
  have hrem : -(Submission.ChenPlan.remSum A D) ≤ Sr := by
    have hneg : -(∑ q ∈ Q.divisors, ∑ d ∈ (Pz sub z).divisors,
          |((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d|
            * |A.rem (q * d)|) ≤ Sr := by
      rw [hSrdef]
      have hpt : ∀ q d : ℕ,
          -(|((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d|
              * |A.rem (q * d)|)
            ≤ ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d
                * A.rem (q * d) := by
        intro q d
        have h := neg_abs_le (((ArithmeticFunction.moebius q : ℤ) : ℝ)
            * lamMinus (A.prodPrimes / Q) D'' d * A.rem (q * d))
        rwa [abs_mul] at h
      have hstep : (∑ q ∈ Q.divisors, ∑ d ∈ (Pz sub z).divisors,
            -(|((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d|
              * |A.rem (q * d)|))
          ≤ (∑ q ∈ Q.divisors, ∑ d ∈ (Pz sub z).divisors,
              ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D'' d
                * A.rem (q * d)) := by
        apply Finset.sum_le_sum
        intro q _
        apply Finset.sum_le_sum
        intro d _
        exact hpt q d
      simp only [Finset.sum_neg_distrib] at hstep
      exact hstep
    have hsubset := sum_filter_Pz_le_remSum A z ((Qmod A u₀ : ℝ) * D'') D hQD''le
    linarith [hneg, hrem3, hsubset]
  -- ## Assembly
  have hkey : A.totalMass * Submission.ChenPlan.sieveV A * κ ≤ A.totalMass * Sν := by
    have hC : VfR sub z * κ ≤ T' := hGmchain
    have hD : Λ * (VfR sub z * κ) ≤ Λ * T' := mul_le_mul_of_nonneg_left hC hΛnn
    rw [hVfRmul, hVfRsieve, ← hmain] at hD
    calc A.totalMass * Submission.ChenPlan.sieveV A * κ
        = A.totalMass * (Submission.ChenPlan.sieveV A * κ) := by ring
      _ ≤ A.totalMass * Sν := mul_le_mul_of_nonneg_left hD hX
  have hmain_le : A.totalMass * Sν + Sr ≤ siftedSumR A z := by
    rw [← hsplit]; exact hminor
  have hstep1 : A.totalMass * Submission.ChenPlan.sieveV A * κ - Submission.ChenPlan.remSum A D
      ≤ siftedSumR A z := by
    linarith [hkey, hrem, hmain_le]
  have hXnn : 0 ≤ A.totalMass * Submission.ChenPlan.sieveV A :=
    mul_nonneg hX (le_of_lt (sieveV_pos A))
  have hstep2 : A.totalMass * Submission.ChenPlan.sieveV A * (993 / 1000 - η)
      ≤ A.totalMass * Submission.ChenPlan.sieveV A * κ :=
    mul_le_mul_of_nonneg_left hκge hXnn
  rw [siftedSumR_eq_siftedSum A hlin.1] at hstep1
  linarith [hstep1, hstep2]

end

end Work.ChenPlan.LinearSieve.JR2
