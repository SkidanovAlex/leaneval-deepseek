import Mathlib
import Submission.Work.FIArea4.S15box
import Submission.Work.FITop3.Defs3
import Submission.Work.FIPlan.Interface

namespace Work.FIArea4

open scoped BigOperators
open scoped Classical

noncomputable section

/-! ## Elementary Gaussian-number facts (self-contained copies) -/

lemma crude_gnorm_eq_normSq (z : GaussianInt) :
    Complex.normSq (z : ℂ) = ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
  rw [Work.FIPlan.gnorm, Nat.cast_natAbs,
    abs_of_nonneg (by exact_mod_cast GaussianInt.norm_nonneg z), GaussianInt.intCast_real_norm]

lemma crude_gnorm_mul (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

lemma crude_norm_toComplex_eq_sqrt (z : GaussianInt) :
    ‖(z : ℂ)‖ = Real.sqrt (((Work.FIPlan.gnorm z : ℕ) : ℝ)) := by
  rw [← crude_gnorm_eq_normSq z, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

lemma crude_delta_toComplex_im (z1 z2 : GaussianInt) :
    ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ) = (star (z1 : ℂ) * (z2 : ℂ)).im := by
  have h : ((star z1 * z2 : GaussianInt) : ℂ) = star (z1 : ℂ) * (z2 : ℂ) := by
    rw [GaussianInt.toComplex_mul, GaussianInt.toComplex_star]; simp
  rw [Work.FIPlan.Delta, GaussianInt.intCast_im, h]

lemma crude_absDelta_le_sqrt_gnorm (z1 z2 : GaussianInt) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
  have h1 : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)| := by
    rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs]
  calc ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      = |((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)| := h1
    _ = |(star (z1 : ℂ) * (z2 : ℂ)).im| := by rw [crude_delta_toComplex_im]
    _ ≤ ‖star (z1 : ℂ) * (z2 : ℂ)‖ := Complex.abs_im_le_norm _
    _ = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ := by rw [norm_mul, norm_star]
    _ = Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
        rw [crude_norm_toComplex_eq_sqrt, crude_norm_toComplex_eq_sqrt]
    _ = Real.sqrt ((((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    _ = Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
        rw [crude_gnorm_mul, Nat.cast_mul]

lemma crude_sqrt_gnorm_mul_le (N : ℝ) (z1 z2 : GaussianInt)
    (hg1 : (Work.FIPlan.gnorm z1 : ℝ) ≤ 2 * N)
    (hg2 : (Work.FIPlan.gnorm z2 : ℝ) ≤ 2 * N) :
    Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) ≤ 2 * N := by
  have h2N : 0 ≤ 2 * N := le_trans (Nat.cast_nonneg _) hg1
  have h1 : Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) ≤ Real.sqrt (2 * N) :=
    Real.sqrt_le_sqrt hg1
  have h2 : Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) ≤ Real.sqrt (2 * N) :=
    Real.sqrt_le_sqrt hg2
  calc Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
      = Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
        rw [crude_gnorm_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    _ ≤ Real.sqrt (2 * N) * Real.sqrt (2 * N) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * N := by
        rw [← Real.sqrt_mul h2N, show 2 * N * (2 * N) = (2 * N) ^ 2 by ring, Real.sqrt_sq h2N]

/-- Two-sided bound for the (7.10) logarithm: if `|zᵢ|² ≤ 2N` with `N ≥ 1` then
`|log(2|z₁z₂|/|Δ(z₁,z₂)|)| ≤ 1 + log(4N)`. -/
lemma crude_logFac_abs_le (N : ℝ) (hN : 1 ≤ N) (z1 z2 : GaussianInt)
    (hg1 : (Work.FIPlan.gnorm z1 : ℝ) ≤ 2 * N)
    (hg2 : (Work.FIPlan.gnorm z2 : ℝ) ≤ 2 * N) :
    |Work.FITop3.logFac z1 z2| ≤ Real.log (4 * N) + 1 := by
  have hNpos : 0 < N := by linarith
  have hlog4 : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
  have hsqrt := crude_sqrt_gnorm_mul_le N z1 z2 hg1 hg2
  rcases Nat.eq_zero_or_pos (Work.FIPlan.absDelta z1 z2) with h0 | hpos
  · have hz : Work.FITop3.logFac z1 z2 = 0 := by
      unfold Work.FITop3.logFac
      rw [h0]; simp
    rw [hz, abs_zero]; linarith
  · have hΔ1 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hΔpos : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by linarith
    have hge : 1 ≤ 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hΔpos]
      linarith [crude_absDelta_le_sqrt_gnorm z1 z2]
    have hstep : 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
        ≤ 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := by
      rw [div_le_iff₀ hΔpos]
      nlinarith [Real.sqrt_nonneg (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)), hΔ1]
    have hle : 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 4 * N := le_trans hstep (by linarith)
    have hargpos : 0 < 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by linarith
    rw [show Work.FITop3.logFac z1 z2
        = Real.log (2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
            / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) from rfl,
      abs_of_nonneg (Real.log_nonneg hge)]
    calc Real.log (2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ≤ Real.log (4 * N) :=
          Real.log_le_log hargpos hle
      _ ≤ Real.log (4 * N) + 1 := by linarith

/-- A finite set of positive integers all `< R` has at most `R + 1` elements. -/
lemma crude_card_le_of_lt (A : Finset ℕ) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ d ∈ A, 1 ≤ d ∧ (d : ℝ) < R) :
    (A.card : ℝ) ≤ R + 1 := by
  have hsub : A ⊆ Finset.Icc 1 (Nat.floor R) := by
    intro d hd
    have hd' := h d hd
    rw [Finset.mem_Icc]
    exact ⟨hd'.1, Nat.le_floor (le_of_lt hd'.2)⟩
  have hcard : A.card ≤ (Finset.Icc 1 (Nat.floor R)).card := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have h1 : A.card ≤ Nat.floor R := by simpa using hcard
  have h2 : (A.card : ℝ) ≤ (Nat.floor R : ℝ) := by exact_mod_cast h1
  have h3 : (Nat.floor R : ℝ) ≤ R := Nat.floor_le hR
  linarith

/-! ## The inner `d`-sum of `VcutMod`, as a real number -/

/-- The inner `d`-sum of the `(z₁,z₂)`-term of `VcutMod (Rz) X β`, as a real number: the sum over
`1 ≤ d ≤ |Δ|/4 + 1` with `4d ∣ |Δ|` and the cut (10.16) `X < d ∧ 4dX < |Δ|`, weighted by
`φ(d)/d · (jacobi) · logFac`. -/
def vcutDsum (X : ℕ) (z1 z2 : GaussianInt) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
      ((Nat.totient d : ℝ) / (d : ℝ)) *
        (if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) *
        (jacobiSym ((star z1 * z2).re) d : ℝ) * Work.FITop3.logFac z1 z2

/-! ## The `(z₁,z₂)`-summand of `VcutMod` -/

/-- The `(z₁,z₂)`-summand of `VcutMod (Rz) X β`: the coprimality cut times the coefficient product
`β z₁ β̄ z₂` times the inner `d`-sum. -/
def vcutInner (X : ℕ) (β : GaussianInt → ℂ) (z1 z2 : GaussianInt) : ℂ :=
  if Work.FIPlan.GaussCoprime z1 z2 then (β z1 * star (β z2)) * (vcutDsum X z1 z2 : ℂ) else 0

lemma vcutMod_eq (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) :
    Work.FITop3.VcutMod Rz X β
      = 2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          vcutInner X β z1 z2 := by
  rw [Work.FITop3.VcutMod, Work.FITop3.TcutMod]
  congr 1
  refine Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => ?_))
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos hc, vcutInner, if_pos hc]
    congr 1
    rw [vcutDsum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    push_cast
    ring
  · rw [if_neg hc, vcutInner, if_neg hc]

/-! ## The inner `d`-sum bound -/

lemma vcutDsum_abs_le (Pa : Work.FITop.Params) (X : ℕ) (hX1 : 1 ≤ X) (φ : ℝ)
    {z1 z2 : GaussianInt} (h1 : Work.FITop3.InPolarBox Pa φ z1)
    (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    |vcutDsum X z1 z2| ≤ (4 * Real.pi * Pa.θ * Pa.N / X + 1) * (Real.log (4 * Pa.N) + 1) := by
  rw [vcutDsum]
  have hLnn : 0 ≤ Real.log (4 * Pa.N) + 1 := by
    have : (0:ℝ) ≤ Real.log (4 * Pa.N) := Real.log_nonneg (by linarith [Pa.hN1])
    linarith
  have hg1 : (Work.FIPlan.gnorm z1 : ℝ) ≤ 2 * Pa.N := by
    have h := h1.2.2.1; nlinarith [Pa.hN1, theta_le_one Pa]
  have hg2 : (Work.FIPlan.gnorm z2 : ℝ) ≤ 2 * Pa.N := by
    have h := h2.2.2.1; nlinarith [Pa.hN1, theta_le_one Pa]
  have hlf : |Work.FITop3.logFac z1 z2| ≤ Real.log (4 * Pa.N) + 1 :=
    crude_logFac_abs_le Pa.N Pa.hN1 z1 z2 hg1 hg2
  set Ds : Finset ℕ := (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
      (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2) with hDs
  set A : Finset ℕ := Ds.filter
      (fun d => X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2) with hA
  have hsum_eq : (∑ d ∈ Ds, ((Nat.totient d : ℝ) / (d : ℝ)) *
        (if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) *
        (jacobiSym ((star z1 * z2).re) d : ℝ) * Work.FITop3.logFac z1 z2)
      = ∑ d ∈ A, ((Nat.totient d : ℝ) / (d : ℝ)) *
        (if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) *
        (jacobiSym ((star z1 * z2).re) d : ℝ) * Work.FITop3.logFac z1 z2 := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro d hd
      rw [hA] at hd
      exact (Finset.mem_filter.mp hd).1
    · intro d hdDs hdA
      have hP : ¬ (X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2) := by
        intro hc
        exact hdA (by rw [hA]; exact Finset.mem_filter.mpr ⟨hdDs, hc⟩)
      rw [if_neg hP]
      ring
  rw [hsum_eq]
  have hterm : ∀ d ∈ A, |((Nat.totient d : ℝ) / (d : ℝ)) *
        (if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) *
        (jacobiSym ((star z1 * z2).re) d : ℝ) * Work.FITop3.logFac z1 z2|
        ≤ Real.log (4 * Pa.N) + 1 := by
    intro d hd
    have hdDs : d ∈ Ds := by
      rw [hA] at hd; exact (Finset.mem_filter.mp hd).1
    have hdIcc : d ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1) :=
      (Finset.mem_filter.mp hdDs).1
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
    have hcond : X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 := by
      rw [hA] at hd; exact (Finset.mem_filter.mp hd).2
    have h1' : |(Nat.totient d : ℝ) / (d : ℝ)| ≤ 1 := by
      have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd1)
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _),
        div_le_one hdpos]
      exact_mod_cast Nat.totient_le d
    have h2' : |(if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1:ℝ) else 0)| ≤ 1 := by
      rw [if_pos hcond]; norm_num
    have h3' : |(jacobiSym ((star z1 * z2).re) d : ℝ)| ≤ 1 := by
      rcases jacobiSym.trichotomy ((star z1 * z2).re) d with hh | hh | hh <;> rw [hh] <;> norm_num
    simp only [abs_mul]
    have hAB : |(Nat.totient d : ℝ) / (d : ℝ)| *
        |(if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1:ℝ) else 0)| ≤ 1 * 1 :=
      mul_le_mul h1' h2' (abs_nonneg _) (by norm_num)
    have hABC : |(Nat.totient d : ℝ) / (d : ℝ)| *
        |(if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1:ℝ) else 0)| *
        |(jacobiSym ((star z1 * z2).re) d : ℝ)| ≤ 1 * 1 * 1 :=
      mul_le_mul hAB h3' (abs_nonneg _) (by norm_num)
    have hABCD : |(Nat.totient d : ℝ) / (d : ℝ)| *
        |(if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1:ℝ) else 0)| *
        |(jacobiSym ((star z1 * z2).re) d : ℝ)| * |Work.FITop3.logFac z1 z2|
        ≤ 1 * 1 * 1 * (Real.log (4 * Pa.N) + 1) :=
      mul_le_mul hABC hlf (abs_nonneg _) (by norm_num)
    linarith [hABCD]
  have hAcard : (A.card : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N / X + 1 := by
    apply crude_card_le_of_lt
    · have hθ0 : (0:ℝ) < Pa.θ := Pa.hθ0
      have hN0 : (0:ℝ) < Pa.N := by linarith [Pa.hN1]
      have hXpos : (0:ℝ) < (X:ℝ) := by
        exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hX1)
      positivity
    · intro d hd
      have hdDs : d ∈ Ds := by rw [hA] at hd; exact (Finset.mem_filter.mp hd).1
      have hdIcc : d ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1) :=
        (Finset.mem_filter.mp hdDs).1
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
      have hcut : 4 * d * X < Work.FIPlan.absDelta z1 z2 := by
        rw [hA] at hd; exact (Finset.mem_filter.mp hd).2.2
      exact ⟨hd1, d_mul_X_lt Pa φ X hX1 h1 h2 hcut⟩
  calc |∑ d ∈ A, ((Nat.totient d : ℝ) / (d : ℝ)) *
        (if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) *
        (jacobiSym ((star z1 * z2).re) d : ℝ) * Work.FITop3.logFac z1 z2|
      ≤ ∑ d ∈ A, |((Nat.totient d : ℝ) / (d : ℝ)) *
        (if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) *
        (jacobiSym ((star z1 * z2).re) d : ℝ) * Work.FITop3.logFac z1 z2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ A, (Real.log (4 * Pa.N) + 1) := Finset.sum_le_sum hterm
    _ = (A.card : ℝ) * (Real.log (4 * Pa.N) + 1) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * Real.pi * Pa.θ * Pa.N / X + 1) * (Real.log (4 * Pa.N) + 1) :=
        mul_le_mul_of_nonneg_right hAcard hLnn

/-! ## The per-pair bound -/

lemma vcutInner_norm_le (Pa : Work.FITop.Params) (X : ℕ) (hX1 : 1 ≤ X) (φ Bmax : ℝ)
    (β : GaussianInt → ℂ) (z1 z2 : GaussianInt)
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (hB1 : ‖β z1‖ ≤ Bmax) (hB2 : ‖β z2‖ ≤ Bmax) :
    ‖vcutInner X β z1 z2‖
      ≤ Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1) * (Real.log (4 * Pa.N) + 1) := by
  have hBmax : 0 ≤ Bmax := le_trans (norm_nonneg _) hB1
  have hSd := vcutDsum_abs_le Pa X hX1 φ h1 h2
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · rw [vcutInner, if_pos hc, norm_mul, norm_mul, norm_star, Complex.norm_real,
      Real.norm_eq_abs]
    have hmul : ‖β z1‖ * ‖β z2‖ ≤ Bmax * Bmax :=
      mul_le_mul hB1 hB2 (norm_nonneg _) hBmax
    have h2 := mul_le_mul hmul hSd (abs_nonneg _) (mul_nonneg hBmax hBmax)
    nlinarith [h2]
  · rw [vcutInner, if_neg hc, norm_zero]
    have hθ0 : (0:ℝ) < Pa.θ := Pa.hθ0
    have hN0 : (0:ℝ) < Pa.N := by linarith [Pa.hN1]
    have hXpos : (0:ℝ) < (X:ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hX1)
    have hLnn : 0 ≤ Real.log (4 * Pa.N) + 1 := by
      have : (0:ℝ) ≤ Real.log (4 * Pa.N) := Real.log_nonneg (by linarith [Pa.hN1])
      linarith
    positivity

/-! ## The crude pair bound -/

/-- **Crude (trivial) pair bound for `V(β)`, with the box-size saving.**  Let `β` be supported
on a finite set `S` of Gaussian integers, all of them in the polar box (5.14) of `Pa` with
parameter `φ`, let `Bmax` bound `‖β z‖` on that support, and let `1 ≤ X`.  Then, provided
`supp β ⊆ gBox Rz`,

  `‖VcutMod Rz X β‖ ≤ 2·Bmax²·#S²·(πθN/X + 1)·(log(4N) + 1)`.

Proof: `VcutMod` is a sum over ordered pairs `(z₁,z₂)` with the coprimality constraint
`GaussCoprime z₁ z₂`, each weighted by `β z₁ β̄ z₂` times at most
`#{d : 4d ∣ |Δ|, d ≤ |Δ|/4 + 1, X < d, 4dX < |Δ|} · logFac(z₁,z₂)`; by the sector bound
`d_mul_X_lt` (from (6.2)) the admissible `d` obey `d < 4πθN/X`, so there are at most `4πθN/X + 1`
of them, and `log(2) ≤ logFac(z₁,z₂) ≤ log(4N)` because `1 ≤ |Δ| ≤ |z₁z₂| ≤ 2N`.  The coprimality
indicator only removes terms, and dropping it gives the ordered-pair count `#S²`.  (The hypothesis
`1 ≤ X` is essential: at `X = 0` the cut keeps all `d` with `4d ∣ |Δ|`, so no divisor-free bound
of this shape can hold.)

This is the bound used for the *concentrated-support* configuration of §15 (few support points),
where the averaged divisor estimates do not apply. -/
theorem VcutMod_le_pair_crude (Pa : Work.FITop.Params) (Rz : ℤ) (X : ℕ) (hX1 : 1 ≤ X)
    (φ Bmax : ℝ) (β : GaussianInt → ℂ) (S : Finset GaussianInt)
    (hS : ∀ z, β z ≠ 0 → z ∈ S)
    (hsupp : ∀ z, β z ≠ 0 → z ∈ Work.FIPlan.gBox Rz)
    (hpo : ∀ z, β z ≠ 0 → Work.FITop3.InPolarBox Pa φ z)
    (hB : ∀ z, ‖β z‖ ≤ Bmax) :
    ‖Work.FITop3.VcutMod Rz X β‖
      ≤ 2 * Bmax ^ 2 * (S.card : ℝ) ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
          * (Real.log (4 * Pa.N) + 1) := by
  have hLnn : 0 ≤ Real.log (4 * Pa.N) + 1 := by
    have : (0:ℝ) ≤ Real.log (4 * Pa.N) := Real.log_nonneg (by linarith [Pa.hN1])
    linarith
  have hgn : ∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
    intro z hb
    have hle : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := (hpo z hb).2.2.1
    nlinarith [Pa.hN1, theta_le_one Pa]
  set T : Finset GaussianInt := (Work.FIPlan.gBox Rz).filter (fun z => β z ≠ 0) with hT
  have hbT : ∀ z ∈ T, β z ≠ 0 := by
    intro z hz; rw [hT, Finset.mem_filter] at hz; exact hz.2
  have hcardT : (T.card : ℝ) ≤ (S.card : ℝ) := by
    have hsub : T ⊆ S := fun z hz => hS z (hbT z hz)
    exact_mod_cast Finset.card_le_card hsub
  have hpair : ∀ z1 ∈ T, ∀ z2 ∈ T, ‖vcutInner X β z1 z2‖
      ≤ Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1) * (Real.log (4 * Pa.N) + 1) := by
    intro z1 hz1 z2 hz2
    exact vcutInner_norm_le Pa X hX1 φ Bmax β z1 z2 (hpo z1 (hbT z1 hz1))
      (hpo z2 (hbT z2 hz2)) (hB z1) (hB z2)
  have hzeroR : ∀ z1 z2, β z2 = 0 → ‖vcutInner X β z1 z2‖ = 0 := by
    intro z1 z2 hz
    have h0 : vcutInner X β z1 z2 = 0 := by
      by_cases hc : Work.FIPlan.GaussCoprime z1 z2 <;> simp [vcutInner, hc, hz]
    rw [h0, norm_zero]
  have hzeroL : ∀ z1 z2, β z1 = 0 → ‖vcutInner X β z1 z2‖ = 0 := by
    intro z1 z2 hz
    have h0 : vcutInner X β z1 z2 = 0 := by
      by_cases hc : Work.FIPlan.GaussCoprime z1 z2 <;> simp [vcutInner, hc, hz]
    rw [h0, norm_zero]
  have hred : (∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
        ‖vcutInner X β z1 z2‖)
      = ∑ z1 ∈ T, ∑ z2 ∈ T, ‖vcutInner X β z1 z2‖ := by
    have hinner : ∀ z1, (∑ z2 ∈ Work.FIPlan.gBox Rz, ‖vcutInner X β z1 z2‖)
        = ∑ z2 ∈ T, ‖vcutInner X β z1 z2‖ := by
      intro z1
      refine (Finset.sum_subset ?_ ?_).symm
      · intro z hz; rw [hT, Finset.mem_filter] at hz; exact hz.1
      · intro z hzg hzT
        have hb : β z = 0 := by
          by_contra h
          exact hzT (by rw [hT, Finset.mem_filter]; exact ⟨hzg, h⟩)
        rw [hzeroR z1 z hb]
    calc ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz, ‖vcutInner X β z1 z2‖
        = ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ T, ‖vcutInner X β z1 z2‖ :=
          Finset.sum_congr rfl (fun z1 _ => hinner z1)
      _ = ∑ z1 ∈ T, ∑ z2 ∈ T, ‖vcutInner X β z1 z2‖ := by
          refine (Finset.sum_subset ?_ ?_).symm
          · intro z hz; rw [hT, Finset.mem_filter] at hz; exact hz.1
          · intro z hzg hzT
            have hb : β z = 0 := by
              by_contra h
              exact hzT (by rw [hT, Finset.mem_filter]; exact ⟨hzg, h⟩)
            exact Finset.sum_eq_zero (fun z2 _ => hzeroL z z2 hb)
  have htri : ‖∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
        vcutInner X β z1 z2‖
      ≤ ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
        ‖vcutInner X β z1 z2‖ := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun z1 _ => ?_)
    exact norm_sum_le _ _
  have hKnn : 0 ≤ Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
      * (Real.log (4 * Pa.N) + 1) := by
    refine mul_nonneg (mul_nonneg (sq_nonneg _) ?_) hLnn
    have hθ0 : (0:ℝ) < Pa.θ := Pa.hθ0
    have hN0 : (0:ℝ) < Pa.N := by linarith [Pa.hN1]
    have hXpos : (0:ℝ) < (X:ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hX1)
    positivity
  have hmain : ‖∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
        vcutInner X β z1 z2‖
      ≤ Bmax ^ 2 * (S.card : ℝ) ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
          * (Real.log (4 * Pa.N) + 1) := by
    have hbnd : (∑ z1 ∈ T, ∑ z2 ∈ T, ‖vcutInner X β z1 z2‖)
        ≤ (S.card : ℝ) * ((S.card : ℝ) * (Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
            * (Real.log (4 * Pa.N) + 1))) := by
      have h1 : (∑ z1 ∈ T, ∑ z2 ∈ T, ‖vcutInner X β z1 z2‖)
          ≤ ∑ z1 ∈ T, ∑ _z2 ∈ T, (Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
              * (Real.log (4 * Pa.N) + 1)) :=
        Finset.sum_le_sum (fun z1 hz1 => Finset.sum_le_sum (fun z2 hz2 => hpair z1 hz1 z2 hz2))
      have h2 : (∑ z1 ∈ T, ∑ _z2 ∈ T, (Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
              * (Real.log (4 * Pa.N) + 1)))
          = (T.card : ℝ) * ((T.card : ℝ) * (Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
              * (Real.log (4 * Pa.N) + 1))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      have h3 : (T.card : ℝ) * ((T.card : ℝ) * (Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
              * (Real.log (4 * Pa.N) + 1)))
          ≤ (S.card : ℝ) * ((S.card : ℝ) * (Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
              * (Real.log (4 * Pa.N) + 1))) := by
        have hSnn : (0:ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
        have h1' : (T.card : ℝ) * (T.card : ℝ) ≤ (S.card : ℝ) * (S.card : ℝ) :=
          mul_le_mul hcardT hcardT (Nat.cast_nonneg _) hSnn
        calc (T.card : ℝ) * ((T.card : ℝ) * (Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
                * (Real.log (4 * Pa.N) + 1)))
            = ((T.card : ℝ) * (T.card : ℝ)) * (Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
                * (Real.log (4 * Pa.N) + 1)) := by ring
          _ ≤ ((S.card : ℝ) * (S.card : ℝ)) * (Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
                * (Real.log (4 * Pa.N) + 1)) := mul_le_mul_of_nonneg_right h1' hKnn
          _ = (S.card : ℝ) * ((S.card : ℝ) * (Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
                * (Real.log (4 * Pa.N) + 1))) := by ring
      linarith [h1, h2, h3]
    calc ‖∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz, vcutInner X β z1 z2‖
        ≤ ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
            ‖vcutInner X β z1 z2‖ := htri
      _ = ∑ z1 ∈ T, ∑ z2 ∈ T, ‖vcutInner X β z1 z2‖ := hred
      _ ≤ (S.card : ℝ) * ((S.card : ℝ) * (Bmax ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
            * (Real.log (4 * Pa.N) + 1))) := hbnd
      _ = Bmax ^ 2 * (S.card : ℝ) ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
            * (Real.log (4 * Pa.N) + 1) := by ring
  rw [vcutMod_eq Rz X β, norm_mul]
  simp only [Complex.norm_ofNat]
  calc 2 * ‖∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz, vcutInner X β z1 z2‖
      ≤ 2 * (Bmax ^ 2 * (S.card : ℝ) ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
          * (Real.log (4 * Pa.N) + 1)) := mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = 2 * Bmax ^ 2 * (S.card : ℝ) ^ 2 * (4 * Real.pi * Pa.θ * Pa.N / X + 1)
          * (Real.log (4 * Pa.N) + 1) := by ring

end

end Work.FIArea4
