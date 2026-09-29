import Mathlib

/-!
# Substitution of power series: convergence and evaluation

This file proves the classical "composition of convergent power series" statement in the
`PowerSeries` formalisation: if `f g ∈ ℚ⟦x⟧` with `constantCoeff g = 0`, if the coefficients of
`f` decay geometrically at rate `R`, and if the absolute series of `g` at radius `ρ` is `< R`,
then, on `‖z‖ ≤ ρ`, the substituted series `f.subst g` converges absolutely and its sum at `z`
is `f` evaluated at the value of `g` at `z`.

The mathematical content is a double-sum rearrangement (Tonelli) justified by absolute
convergence.  The two analytic ingredients are

* `pow_coeff_eval`: the Cauchy powers `g ^ d` evaluated at `z` converge absolutely to the `d`-th
  power of the value of `g`, with the submultiplicative absolute bound
  `∑ₙ ‖coeff n (g ^ d)‖‖z‖ⁿ ≤ (∑ₙ ‖coeff n g‖‖z‖ⁿ)^d`;
* `coeff_subst_eq_tsum`: Cauchy's formula `coeff n (f.subst g) = ∑' d, coeff d f · coeff n (g ^ d)`.

We prove the result first for `ℂ⟦x⟧` (`subst_eval_abs_C`), where the summations take place, and
deduce the stated result for `ℚ⟦x⟧` by pushing the coefficients along `algebraMap ℚ ℂ`.
-/

namespace Work.C17I

open PowerSeries

noncomputable section

/-! ## Cauchy's formula for the coefficients of a substituted series -/

/-- Cauchy's formula for the coefficients of a substituted power series, in `tsum` form.
If `g` has zero constant coefficient then `coeff n (g ^ d) = 0` for `d > n`, so `finsum`
(Mathlib's Cauchy formula `PowerSeries.coeff_subst'`) is a finite sum which we may write as a
`tsum`. -/
lemma coeff_subst_eq_tsum {f g : PowerSeries ℂ} (hg0 : PowerSeries.constantCoeff g = 0)
    (n : ℕ) :
    PowerSeries.coeff n (f.subst g)
      = ∑' d : ℕ, PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) := by
  have hsub : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  have hfin : Function.HasFiniteSupport
      (fun d : ℕ => PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)) := by
    refine Set.Finite.subset (Finset.finite_toSet (Finset.range (n + 1))) fun d hd => ?_
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hle
    refine hd ?_
    have hnd : n < d := by omega
    have hlt : (n : ℕ∞) < (g ^ d).order :=
      lt_of_lt_of_le (Nat.cast_lt.mpr hnd)
        (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg0)
    show PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) = 0
    rw [PowerSeries.coeff_of_lt_order n hlt, mul_zero]
  rw [PowerSeries.coeff_subst' hsub, tsum_eq_finsum hfin]
  exact finsum_congr (fun d => by rw [smul_eq_mul])

/-! ## Cauchy powers of a power series -/

/-- The `d`-th Cauchy power `g ^ d` evaluated at `z`: absolute convergence, the value, and the
submultiplicative bound on the sum of the absolute values. -/
private lemma pow_coeff_eval {g : PowerSeries ℂ} {ρ : ℝ} {z : ℂ} (hρ : 0 < ρ)
    (hgS : Summable fun n : ℕ => ‖PowerSeries.coeff n g‖ * ρ ^ n) (hz : ‖z‖ ≤ ρ) (d : ℕ) :
    Summable (fun n : ℕ => PowerSeries.coeff n (g ^ d) * z ^ n) ∧
      (∑' n : ℕ, PowerSeries.coeff n (g ^ d) * z ^ n)
        = (∑' n : ℕ, PowerSeries.coeff n g * z ^ n) ^ d ∧
      Summable (fun n : ℕ => ‖PowerSeries.coeff n (g ^ d) * z ^ n‖) ∧
      (∑' n : ℕ, ‖PowerSeries.coeff n (g ^ d) * z ^ n‖)
        ≤ (∑' n : ℕ, ‖PowerSeries.coeff n g‖ * ‖z‖ ^ n) ^ d := by
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hBs : Summable fun n : ℕ => ‖PowerSeries.coeff n g‖ * ‖z‖ ^ n :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hznn hz n) (norm_nonneg _)) hgS
  have hw1 : Summable fun n : ℕ => PowerSeries.coeff n g * z ^ n := by
    refine Summable.of_norm_bounded hBs (fun n => ?_)
    rw [norm_mul, norm_pow]
  have hBs' : Summable fun n : ℕ => ‖PowerSeries.coeff n g * z ^ n‖ :=
    hBs.congr (fun n => by rw [norm_mul, norm_pow])
  induction d with
  | zero =>
    have h1 : (fun n : ℕ => PowerSeries.coeff n (g ^ 0) * z ^ n)
        = fun n : ℕ => if n = 0 then (1 : ℂ) else 0 := by
      funext n
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs with hn
      · rw [hn]; simp
      · simp
    have h2 : (fun n : ℕ => ‖PowerSeries.coeff n (g ^ 0) * z ^ n‖)
        = fun n : ℕ => if n = 0 then (1 : ℝ) else 0 := by
      funext n
      rw [congrFun h1 n]
      split_ifs with hn
      · simp
      · simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1]; exact (hasSum_ite_eq 0 (1 : ℂ)).summable
    · rw [h1, (hasSum_ite_eq 0 (1 : ℂ)).tsum_eq, pow_zero]
    · rw [h2]; exact (hasSum_ite_eq 0 (1 : ℝ)).summable
    · rw [h2, (hasSum_ite_eq 0 (1 : ℝ)).tsum_eq, pow_zero]
  | succ d ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    have ih3' : Summable fun x : ℕ => ‖‖PowerSeries.coeff x (g ^ d) * z ^ x‖‖ :=
      ih3.congr (fun x => by rw [Real.norm_of_nonneg (norm_nonneg _)])
    have hBs'' : Summable fun x : ℕ => ‖‖PowerSeries.coeff x g * z ^ x‖‖ :=
      hBs'.congr (fun x => by rw [Real.norm_of_nonneg (norm_nonneg _)])
    have hcauchC := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' (R := ℂ)
      (f := fun x : ℕ => PowerSeries.coeff x (g ^ d) * z ^ x)
      (g := fun x : ℕ => PowerSeries.coeff x g * z ^ x) ih3 ih1 hBs' hw1
    have hcauchR := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (R := ℝ)
      (f := fun x : ℕ => ‖PowerSeries.coeff x (g ^ d) * z ^ x‖)
      (g := fun x : ℕ => ‖PowerSeries.coeff x g * z ^ x‖) ih3' hBs''
    have hinnerC : ∀ n : ℕ, (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          (PowerSeries.coeff kl.1 (g ^ d) * z ^ kl.1) * (PowerSeries.coeff kl.2 g * z ^ kl.2))
        = PowerSeries.coeff n (g ^ (d + 1)) * z ^ n := by
      intro n
      calc ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
              (PowerSeries.coeff kl.1 (g ^ d) * z ^ kl.1) * (PowerSeries.coeff kl.2 g * z ^ kl.2)
          = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
              (PowerSeries.coeff kl.1 (g ^ d) * PowerSeries.coeff kl.2 g) * z ^ n := by
            refine Finset.sum_congr rfl (fun kl hkl => ?_)
            rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]; ring
        _ = (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
              PowerSeries.coeff kl.1 (g ^ d) * PowerSeries.coeff kl.2 g) * z ^ n :=
            (Finset.sum_mul _ _ _).symm
        _ = PowerSeries.coeff n (g ^ d * g) * z ^ n := by rw [PowerSeries.coeff_mul]
        _ = PowerSeries.coeff n (g ^ (d + 1)) * z ^ n := by rw [pow_succ]
    have hinnerR : ∀ n : ℕ, ‖PowerSeries.coeff n (g ^ (d + 1)) * z ^ n‖
        ≤ ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
            ‖PowerSeries.coeff kl.1 (g ^ d) * z ^ kl.1‖ *
              ‖PowerSeries.coeff kl.2 g * z ^ kl.2‖ := by
      intro n
      calc ‖PowerSeries.coeff n (g ^ (d + 1)) * z ^ n‖
          = ‖PowerSeries.coeff n (g ^ (d + 1))‖ * ‖z‖ ^ n := by rw [norm_mul, norm_pow]
        _ = ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
              PowerSeries.coeff kl.1 (g ^ d) * PowerSeries.coeff kl.2 g‖ * ‖z‖ ^ n := by
            rw [pow_succ, PowerSeries.coeff_mul]
        _ ≤ (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
              ‖PowerSeries.coeff kl.1 (g ^ d)‖ * ‖PowerSeries.coeff kl.2 g‖) * ‖z‖ ^ n := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hznn n)
            refine le_trans (norm_sum_le _ _) ?_
            exact Finset.sum_le_sum (fun kl _ => norm_mul_le _ _)
        _ = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
              (‖PowerSeries.coeff kl.1 (g ^ d)‖ * ‖z‖ ^ kl.1) *
                (‖PowerSeries.coeff kl.2 g‖ * ‖z‖ ^ kl.2) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun kl hkl => ?_)
            rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]; ring
        _ = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
              ‖PowerSeries.coeff kl.1 (g ^ d) * z ^ kl.1‖ *
                ‖PowerSeries.coeff kl.2 g * z ^ kl.2‖ := by
            refine Finset.sum_congr rfl (fun kl _ => ?_)
            rw [norm_mul, norm_pow, norm_mul, norm_pow]
    have hsummR : Summable fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        ‖PowerSeries.coeff kl.1 (g ^ d) * z ^ kl.1‖ * ‖PowerSeries.coeff kl.2 g * z ^ kl.2‖ :=
      summable_sum_mul_antidiagonal_of_summable_norm' (R := ℝ)
        (f := fun x : ℕ => ‖PowerSeries.coeff x (g ^ d) * z ^ x‖)
        (g := fun x : ℕ => ‖PowerSeries.coeff x g * z ^ x‖) ih3' ih3 hBs'' hBs'
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (summable_sum_mul_antidiagonal_of_summable_norm' (R := ℂ)
        (f := fun x : ℕ => PowerSeries.coeff x (g ^ d) * z ^ x)
        (g := fun x : ℕ => PowerSeries.coeff x g * z ^ x) ih3 ih1 hBs' hw1).congr
        (fun n => hinnerC n)
    · have heq : (∑' n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
            (PowerSeries.coeff kl.1 (g ^ d) * z ^ kl.1) * (PowerSeries.coeff kl.2 g * z ^ kl.2))
          = ∑' n : ℕ, PowerSeries.coeff n (g ^ (d + 1)) * z ^ n := tsum_congr hinnerC
      rw [← heq, ← hcauchC, ih2, pow_succ]
    · exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hinnerR hsummR
    · refine le_trans (Summable.tsum_le_tsum hinnerR
        (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hinnerR hsummR) hsummR) ?_
      rw [← hcauchR]
      refine le_trans (mul_le_mul ih4 (le_of_eq (tsum_congr
        (fun n => by rw [norm_mul, norm_pow]))) (tsum_nonneg (fun n => norm_nonneg _))
        (pow_nonneg (tsum_nonneg (fun n => by positivity)) d)) (le_of_eq ?_)
      simp only [pow_succ]

/-! ## The main ℂ-statement -/

/-- Convergence and evaluation of a substituted power series over `ℂ`. -/
theorem subst_eval_abs_C {f g : PowerSeries ℂ} {C R ρ : ℝ} {z : ℂ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hR : 0 < R)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hf : ∀ n : ℕ, ‖PowerSeries.coeff n f‖ * R ^ n ≤ C)
    (hgS : Summable fun n : ℕ => ‖PowerSeries.coeff n g‖ * ρ ^ n)
    (hgR : (∑' n : ℕ, ‖PowerSeries.coeff n g‖ * ρ ^ n) < R)
    (hz : ‖z‖ ≤ ρ) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (f.subst g) * z ^ n)
      (∑' n : ℕ, PowerSeries.coeff n f * (∑' m : ℕ, PowerSeries.coeff m g * z ^ m) ^ n) := by
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hBs : Summable fun m : ℕ => ‖PowerSeries.coeff m g‖ * ‖z‖ ^ m :=
    Summable.of_nonneg_of_le (fun m => by positivity)
      (fun m => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hznn hz m) (norm_nonneg _)) hgS
  have hBs2 : Summable fun m : ℕ => ‖PowerSeries.coeff m g * z ^ m‖ :=
    hBs.congr (fun m => by rw [norm_mul, norm_pow])
  set Bv : ℝ := ∑' m : ℕ, ‖PowerSeries.coeff m g‖ * ‖z‖ ^ m with hBv
  have hBvnn : 0 ≤ Bv := by rw [hBv]; exact tsum_nonneg (fun m => by positivity)
  have hBvlt : Bv < R := by
    rw [hBv]
    exact lt_of_le_of_lt (Summable.tsum_le_tsum
      (fun m => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hznn hz m) (norm_nonneg _)) hBs hgS)
      hgR
  set w : ℂ := ∑' m : ℕ, PowerSeries.coeff m g * z ^ m with hw
  have hwnorm : ‖w‖ ≤ Bv := by
    rw [hw, hBv]
    refine le_trans (norm_tsum_le_tsum_norm hBs2) (le_of_eq (tsum_congr (fun m => ?_)))
    rw [norm_mul, norm_pow]
  have hpow : ∀ d : ℕ,
      Summable (fun n : ℕ => PowerSeries.coeff n (g ^ d) * z ^ n) ∧
      (∑' n : ℕ, PowerSeries.coeff n (g ^ d) * z ^ n) = w ^ d ∧
      Summable (fun n : ℕ => ‖PowerSeries.coeff n (g ^ d) * z ^ n‖) ∧
      (∑' n : ℕ, ‖PowerSeries.coeff n (g ^ d) * z ^ n‖) ≤ Bv ^ d := by
    intro d
    obtain ⟨h1, h2, h3, h4⟩ := pow_coeff_eval hρ hgS hz d
    exact ⟨h1, by rw [hw]; exact h2, h3, by rw [hBv]; exact h4⟩
  set D : ℕ × ℕ → ℂ :=
    fun p => PowerSeries.coeff p.1 f * (PowerSeries.coeff p.2 (g ^ p.1) * z ^ p.2) with hD
  have hDs : Summable D := by
    have hmaj : Summable (fun p : ℕ × ℕ =>
        ‖PowerSeries.coeff p.1 f‖ * ‖PowerSeries.coeff p.2 (g ^ p.1) * z ^ p.2‖) := by
      refine (summable_prod_of_nonneg (f := fun p : ℕ × ℕ =>
        ‖PowerSeries.coeff p.1 f‖ * ‖PowerSeries.coeff p.2 (g ^ p.1) * z ^ p.2‖)
        (fun p => by positivity)).2 ⟨?_, ?_⟩
      · intro d
        have hh : Summable fun y : ℕ => ‖PowerSeries.coeff d f‖ *
            ‖PowerSeries.coeff y (g ^ d) * z ^ y‖ :=
          ((hpow d).2.2.1).mul_left (‖PowerSeries.coeff d f‖)
        simpa only using hh
      · have hgeom : Summable fun d : ℕ => C * (Bv / R) ^ d := by
          have h0 : ‖Bv / R‖ < 1 := by
            rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hBvnn hR.le), div_lt_one hR]
            exact hBvlt
          exact (summable_geometric_iff_norm_lt_one.mpr h0).mul_left C
        refine Summable.of_nonneg_of_le ?_ ?_ hgeom
        · intro d
          exact tsum_nonneg (fun y => by positivity)
        · intro d
          have hh : (∑' y : ℕ, ‖PowerSeries.coeff d f‖ *
                ‖PowerSeries.coeff y (g ^ d) * z ^ y‖) ≤ C * (Bv / R) ^ d := by
            rw [Summable.tsum_mul_left (‖PowerSeries.coeff d f‖) ((hpow d).2.2.1)]
            refine le_trans (mul_le_mul_of_nonneg_left (hpow d).2.2.2 (norm_nonneg _)) ?_
            have hRd : (0 : ℝ) < R ^ d := pow_pos hR d
            have h2 : ‖PowerSeries.coeff d f‖ ≤ C / R ^ d := (le_div_iff₀ hRd).mpr (hf d)
            refine le_trans (mul_le_mul_of_nonneg_right h2 (pow_nonneg hBvnn d)) ?_
            refine le_of_eq ?_
            rw [div_pow]; ring
          simpa only using hh
    exact Summable.of_norm_bounded hmaj (fun p => le_of_eq (norm_mul _ _))
  have hF1 : ∀ n : ℕ, ∑' d : ℕ, D (d, n) = PowerSeries.coeff n (f.subst g) * z ^ n := by
    intro n
    have hsA : Summable fun d : ℕ => PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) :=
      summable_of_ne_finset_zero (s := Finset.range (n + 1)) (fun d hd => by
        have hnd : n < d := by
          simp only [Finset.mem_range, not_lt] at hd; omega
        have hlt : (n : ℕ∞) < (g ^ d).order :=
          lt_of_lt_of_le (Nat.cast_lt.mpr hnd)
            (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg0)
        rw [PowerSeries.coeff_of_lt_order n hlt, mul_zero])
    calc ∑' d : ℕ, D (d, n)
        = ∑' d : ℕ, (PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)) * z ^ n := by
          refine tsum_congr (fun d => ?_)
          simp only [hD]; ring
      _ = (∑' d : ℕ, PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)) * z ^ n :=
          Summable.tsum_mul_right (z ^ n) hsA
      _ = PowerSeries.coeff n (f.subst g) * z ^ n := by rw [coeff_subst_eq_tsum hg0 n]
  have hF2 : ∀ d : ℕ, ∑' n : ℕ, D (d, n) = PowerSeries.coeff d f * w ^ d := by
    intro d
    calc ∑' n : ℕ, D (d, n)
        = ∑' n : ℕ, PowerSeries.coeff d f * (PowerSeries.coeff n (g ^ d) * z ^ n) := by
          refine tsum_congr (fun n => ?_)
          simp only [hD]
      _ = PowerSeries.coeff d f * (∑' n : ℕ, PowerSeries.coeff n (g ^ d) * z ^ n) :=
          Summable.tsum_mul_left (PowerSeries.coeff d f) (hpow d).1
      _ = PowerSeries.coeff d f * w ^ d := by rw [(hpow d).2.1]
  have hsum1 : ∑' p : ℕ × ℕ, D p = ∑' n : ℕ, PowerSeries.coeff n (f.subst g) * z ^ n := by
    rw [show (∑' p : ℕ × ℕ, D p) = ∑' p : ℕ × ℕ, D p.swap from
      ((Equiv.prodComm ℕ ℕ).tsum_eq D).symm]
    rw [Summable.tsum_prod hDs.prod_symm]
    exact tsum_congr hF1
  have hsum2 : ∑' p : ℕ × ℕ, D p = ∑' d : ℕ, PowerSeries.coeff d f * w ^ d := by
    rw [Summable.tsum_prod hDs]
    exact tsum_congr hF2
  have hfiber : ∀ n : ℕ, HasSum (fun d : ℕ => D (d, n))
      (PowerSeries.coeff n (f.subst g) * z ^ n) := by
    intro n
    have hsA : Summable fun d : ℕ => PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) :=
      summable_of_ne_finset_zero (s := Finset.range (n + 1)) (fun d hd => by
        have hnd : n < d := by
          simp only [Finset.mem_range, not_lt] at hd; omega
        have hlt : (n : ℕ∞) < (g ^ d).order :=
          lt_of_lt_of_le (Nat.cast_lt.mpr hnd)
            (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg0)
        rw [PowerSeries.coeff_of_lt_order n hlt, mul_zero])
    have hsD : Summable fun d : ℕ => D (d, n) := by
      refine (hsA.mul_right (z ^ n)).congr (fun d => ?_)
      simp only [hD]; ring
    have h := hsD.hasSum
    rwa [hF1 n] at h
  have hfinal : HasSum (fun n : ℕ => PowerSeries.coeff n (f.subst g) * z ^ n)
      (∑' d : ℕ, PowerSeries.coeff d f * w ^ d) := by
    rw [← hsum2]
    rw [← (Equiv.prodComm ℕ ℕ).tsum_eq D]
    exact hDs.prod_symm.hasSum.prod_fiberwise hfiber
  have hgoal : (∑' d : ℕ, PowerSeries.coeff d f * w ^ d)
      = ∑' n : ℕ, PowerSeries.coeff n f
        * (∑' m : ℕ, PowerSeries.coeff m g * z ^ m) ^ n := by
    rw [hw]
  exact hgoal ▸ hfinal

/-! ## The stated result over `ℚ` -/

/-- **Composition of convergent power series.**  If `f g ∈ ℚ⟦x⟧` with `constantCoeff g = 0`,
if the coefficients of `f` decay geometrically at rate `R`, and if the absolute series of `g`
at the radius `ρ` is `< R`, then on `‖z‖ ≤ ρ` the substituted series `f.subst g` converges
absolutely and its sum is `f` evaluated at the value of `g` at `z`. -/
theorem subst_eval_abs {f g : PowerSeries ℚ} {C R ρ : ℝ} {z : ℂ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hR : 0 < R)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hf : ∀ n : ℕ, ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ * R ^ n ≤ C)
    (hgS : Summable fun n : ℕ => ‖((PowerSeries.coeff n g : ℚ) : ℂ)‖ * ρ ^ n)
    (hgR : (∑' n : ℕ, ‖((PowerSeries.coeff n g : ℚ) : ℂ)‖ * ρ ^ n) < R)
    (hz : ‖z‖ ≤ ρ) :
    HasSum (fun n : ℕ => ((PowerSeries.coeff n (f.subst g) : ℚ) : ℂ) * z ^ n)
      (∑' n : ℕ, ((PowerSeries.coeff n f : ℚ) : ℂ)
        * (∑' m : ℕ, ((PowerSeries.coeff m g : ℚ) : ℂ) * z ^ m) ^ n) := by
  have hcoeff_f : ∀ n : ℕ,
      PowerSeries.coeff n (f.map (algebraMap ℚ ℂ)) = ((PowerSeries.coeff n f : ℚ) : ℂ) :=
    fun n => PowerSeries.coeff_map (algebraMap ℚ ℂ) n f
  have hcoeff_g : ∀ n : ℕ,
      PowerSeries.coeff n (g.map (algebraMap ℚ ℂ)) = ((PowerSeries.coeff n g : ℚ) : ℂ) :=
    fun n => PowerSeries.coeff_map (algebraMap ℚ ℂ) n g
  have hsubst_c : ∀ n : ℕ,
      PowerSeries.coeff n ((f.map (algebraMap ℚ ℂ)).subst (g.map (algebraMap ℚ ℂ)))
        = ((PowerSeries.coeff n (f.subst g) : ℚ) : ℂ) := by
    intro n
    have h1 : PowerSeries.coeff n (MvPowerSeries.map (algebraMap ℚ ℂ) (f.subst g))
        = ((PowerSeries.coeff n (f.subst g) : ℚ) : ℂ) :=
      PowerSeries.coeff_map (algebraMap ℚ ℂ) n (f.subst g)
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hg0) f] at h1
    exact h1
  have hg0' : PowerSeries.constantCoeff (g.map (algebraMap ℚ ℂ)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff_g 0,
      show PowerSeries.coeff 0 g = (0 : ℚ) by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0]]
    simp
  have hf' : ∀ n : ℕ, ‖PowerSeries.coeff n (f.map (algebraMap ℚ ℂ))‖ * R ^ n ≤ C :=
    fun n => by rw [hcoeff_f n]; exact hf n
  have hgS' : Summable fun n : ℕ => ‖PowerSeries.coeff n (g.map (algebraMap ℚ ℂ))‖ * ρ ^ n :=
    hgS.congr (fun n => by rw [hcoeff_g n])
  have hgR' : (∑' n : ℕ, ‖PowerSeries.coeff n (g.map (algebraMap ℚ ℂ))‖ * ρ ^ n) < R := by
    rw [tsum_congr (fun n => by rw [hcoeff_g n])]
    exact hgR
  have hkey := subst_eval_abs_C (f := f.map (algebraMap ℚ ℂ)) (g := g.map (algebraMap ℚ ℂ))
    (C := C) (R := R) (ρ := ρ) (z := z) hC hρ hR hg0' hf' hgS' hgR' hz
  simp only [hsubst_c, hcoeff_f, hcoeff_g] at hkey
  exact hkey

end

end Work.C17I
