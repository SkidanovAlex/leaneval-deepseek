import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Solutions.block_transfer

/-!
# Floquet theory at rational frequency: `|tr A_q| ≤ 2` for a generalized eigenfunction

(Auxiliary module for `Work.TMC7Core.Solutions.floquet_trace_bound`.)

If `u ≠ 0` is a polynomially bounded formal solution of the almost Mathieu difference
equation at frequency `α = p/q`, phase `0` and energy `E`, then the transfer matrix over
one period, `A_q = iterC α lam E q 0 = S((q-1)α)⋯S(0)`, has `‖tr A_q‖ ≤ 2`.

Writing `W k = (u (k q), u (k q - 1))`, one period of the cocycle advances the state,
`W (k+1) = A_q ·ᵥ W k` for every `k : ℤ` (`block_transfer`), so `W k = A_q^k W 0`; both
coordinates of `W k` are bounded polynomially in `|k|`, and `W 0 ≠ 0` because `u ≠ 0`
(a solution with `u 0 = u (-1) = 0` vanishes identically, `floquet_vanish`).

The core (`orbit_trace_norm_le_two`) is the classical Wronskian argument, carried out over
`ℂ` without any eigenvalue decomposition.  Put `t = tr A_q` and `s k = det (W 0, W k)`.  By
Cayley--Hamilton (`A_q² = t A_q - 1`) the sequence `s` satisfies the second order recurrence
`s (k+2) = t s (k+1) - s k`, whence `‖s (k+2)‖ ≥ ‖t‖ ‖s (k+1)‖ - ‖s k‖`.  If `det (W 0, W 1)
≠ 0` the growth lemma `floquet_recur_growth` turns this into exponential growth of `‖s k‖`,
contradicting the polynomial bound.  If `det (W 0, W 1) = 0` then `W 1 = λ W 0` for some
`λ ≠ 0`, the orbit is `W k = λ^k W 0` for `k ≥ 0` and `W (-k) = λ^{-k} W 0` for `k ≥ 0`, so
`‖λ‖ = 1`; the characteristic identity `λ² - t λ + 1 = 0` then gives
`‖t‖ ≤ ‖λ‖ + ‖λ‖⁻¹ = 2`.

This is the same development as the shared workspace module
`Submission.Work.TMC7Core.Solutions.floquet_of_genEigen` (which is imported by the glue rules
of the rational-frequency component); it is reproduced here under the namespace
`Work.TMC7Core.FtbAux` because that module declares an auxiliary theorem called
`floquet_trace_bound`, a name that this component's target theorem must itself be allowed to
use.  Apart from the renaming, the mathematics and the proof scripts are identical.
-/

namespace Work.TMC7Core.FtbAux

open Work.TMC7Core

/-- One step of the recurrence, solved for `u (n+1)`. -/
lemma floquet_step_fwd (α lam θ : ℝ) (E : ℂ) (u : ℤ → ℂ)
    (hu : ∀ n : ℤ, amoAct α lam θ u n = E * u n) (n : ℤ) :
    u (n+1) = (E - ((amoPot α lam θ n : ℝ):ℂ)) * u n - u (n-1) := by
  have h := hu n
  simp only [amoAct] at h
  linear_combination h

/-- One step of the recurrence, solved for `u (n-1)`. -/
lemma floquet_step_bwd (α lam θ : ℝ) (E : ℂ) (u : ℤ → ℂ)
    (hu : ∀ n : ℤ, amoAct α lam θ u n = E * u n) (n : ℤ) :
    u (n-1) = (E - ((amoPot α lam θ n : ℝ):ℂ)) * u n - u (n+1) := by
  have h := hu n
  simp only [amoAct] at h
  linear_combination h

/-- A formal solution with `u 0 = u (-1) = 0` vanishes identically: the recurrence is
determined both forwards and backwards by those two values. -/
lemma floquet_vanish (α lam θ : ℝ) (E : ℂ) (u : ℤ → ℂ)
    (hu : ∀ n : ℤ, amoAct α lam θ u n = E * u n)
    (h0 : u 0 = 0) (hm1 : u (-1) = 0) : u = 0 := by
  have hb := floquet_step_bwd α lam θ E u hu
  have hf := floquet_step_fwd α lam θ E u hu
  have hpos : ∀ n : ℕ, u (n:ℤ) = 0 ∧ u ((n:ℤ) - 1) = 0 := by
    intro n
    induction n with
    | zero => exact ⟨h0, by simpa using hm1⟩
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · have h := hf ((n:ℤ))
        rw [show ((n:ℤ) + 1) = ((n+1 : ℕ) : ℤ) by push_cast; ring] at h
        rw [h, ih.1, ih.2]
        ring
      · rw [show (((n+1 : ℕ) : ℤ) - 1) = (n:ℤ) by push_cast; ring]
        exact ih.1
  have hneg : ∀ n : ℕ, u (-(n:ℤ)) = 0 ∧ u (-(n:ℤ) - 1) = 0 := by
    intro n
    induction n with
    | zero => exact ⟨h0, by simpa using hm1⟩
    | succ n ih =>
      have key : u (-(n:ℤ) - 2) = 0 := by
        have h := hb (-(n:ℤ) - 1)
        rw [show (-(n:ℤ) - 1) - 1 = -(n:ℤ) - 2 by ring,
            show (-(n:ℤ) - 1) + 1 = -(n:ℤ) by ring] at h
        rw [h, ih.1, ih.2]
        ring
      refine ⟨?_, ?_⟩
      · rw [show -(((n+1 : ℕ)) : ℤ) = -(n:ℤ) - 1 by push_cast; ring]
        exact ih.2
      · rw [show -(((n+1 : ℕ)) : ℤ) - 1 = -(n:ℤ) - 2 by push_cast; ring]
        exact key
  funext m
  rcases Int.eq_nat_or_neg m with ⟨n, hn | hn⟩
  · rw [hn]; exact (hpos n).1
  · rw [hn]
    cases n with
    | zero => simpa using h0
    | succ k => exact (hneg (k+1)).1

/-- Polynomial bound for the sampled state `W k = (u (k q), u (k q - 1))`, with the single
constant `2 C (1 + q)`. -/
lemma floquet_bound (q : ℕ) (u : ℤ → ℂ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n:ℝ)|)) (k : ℤ) :
    ‖u (k*q)‖ ≤ (2*C*(1+q)) * (1 + |(k:ℝ)|) ∧
      ‖u (k*q - 1)‖ ≤ (2*C*(1+q)) * (1 + |(k:ℝ)|) := by
  have hq0 : (0:ℝ) ≤ (q:ℝ) := by positivity
  have hk0 : (0:ℝ) ≤ |(k:ℝ)| := abs_nonneg _
  have hkq : ((k*q : ℤ) : ℝ) = (k:ℝ) * (q:ℝ) := by push_cast; ring
  have hkq1 : (((k*q - 1 : ℤ)) : ℝ) = (k:ℝ) * (q:ℝ) - 1 := by push_cast; ring
  have hkey1 : (1:ℝ) + |(k:ℝ)| * (q:ℝ) ≤ (1 + (q:ℝ)) * (1 + |(k:ℝ)|) := by nlinarith
  have hkey2 : (2:ℝ) + |(k:ℝ)| * (q:ℝ) ≤ 2 * ((1 + (q:ℝ)) * (1 + |(k:ℝ)|)) := by
    nlinarith [hq0, hk0]
  constructor
  · calc ‖u (k*q)‖ ≤ C * (1 + |((k*q : ℤ) : ℝ)|) := hC (k*q)
      _ = C * (1 + |(k:ℝ)| * (q:ℝ)) := by rw [hkq, abs_mul, abs_of_nonneg hq0]
      _ ≤ C * ((1 + (q:ℝ)) * (1 + |(k:ℝ)|)) := mul_le_mul_of_nonneg_left hkey1 hC0
      _ ≤ (2*C*(1+q)) * (1 + |(k:ℝ)|) := by
            have hX : 0 ≤ C * ((1 + (q:ℝ)) * (1 + |(k:ℝ)|)) := by positivity
            nlinarith [hX]
  · have h2 : |(k:ℝ) * (q:ℝ) - 1| ≤ |(k:ℝ)| * (q:ℝ) + 1 := by
      have h := abs_sub_le ((k:ℝ)*(q:ℝ)) 0 1
      simp only [sub_zero, zero_sub, abs_neg, abs_one] at h
      rw [abs_mul, abs_of_nonneg hq0] at h
      linarith
    calc ‖u (k*q - 1)‖ ≤ C * (1 + |((k*q - 1 : ℤ) : ℝ)|) := hC (k*q - 1)
      _ = C * (1 + |(k:ℝ) * (q:ℝ) - 1|) := by rw [hkq1]
      _ ≤ C * (1 + (|(k:ℝ)| * (q:ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (by linarith) hC0
      _ = C * (2 + |(k:ℝ)| * (q:ℝ)) := by ring
      _ ≤ C * (2 * ((1 + (q:ℝ)) * (1 + |(k:ℝ)|))) := mul_le_mul_of_nonneg_left hkey2 hC0
      _ = (2*C*(1+q)) * (1 + |(k:ℝ)|) := by ring


lemma floquet_CH (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.det_fin_two,
      Matrix.smul_apply] <;> ring

def floquet_det2 (v w : Fin 2 → ℂ) : ℂ := v 0 * w 1 - v 1 * w 0

lemma floquet_det2_sub_right (v w w' : Fin 2 → ℂ) : floquet_det2 v (w - w') = floquet_det2 v w - floquet_det2 v w' := by
  simp [floquet_det2]; ring
lemma floquet_det2_smul_right (v w : Fin 2 → ℂ) (c : ℂ) : floquet_det2 v (c • w) = c * floquet_det2 v w := by
  simp [floquet_det2]; ring

lemma floquet_det2_eq_zero_iff (v w : Fin 2 → ℂ) (hv : v ≠ 0) :
    floquet_det2 v w = 0 → ∃ c : ℂ, w = c • v := by
  intro h
  have hdet : v 0 * w 1 - v 1 * w 0 = 0 := by
    have h' := h; rw [floquet_det2] at h'; exact h'
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro hh
      exact hv (by funext i; fin_cases i <;> simp [h0, hh])
    have hw0 : w 0 = 0 := by
      have hh : v 1 * w 0 = 0 := by
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at hdet
        exact hdet
      exact (mul_eq_zero.mp hh).resolve_left h1
    refine ⟨w 1 / v 1, ?_⟩
    funext i
    fin_cases i
    · simp [hw0, h0]
    · show w 1 = w 1 / v 1 * v 1
      rw [div_mul_cancel₀ _ h1]
  · have hw1 : w 1 = w 0 / v 0 * v 1 := by
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination hdet
    refine ⟨w 0 / v 0, ?_⟩
    funext i
    fin_cases i
    · show w 0 = w 0 / v 0 * v 0
      rw [div_mul_cancel₀ _ h0]
    · exact hw1

/-- Exponential growth beats any affine bound. -/
lemma floquet_exp_beats_linear (r : ℝ) (hr : 1 < r) (a b C : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hC : 0 ≤ C) : ∃ n : ℕ, b + C * (1 + (n : ℝ)) < a * r ^ n := by
  have hr0 : 0 < r := by linarith
  have h1 : Filter.Tendsto (fun n : ℕ => ((b + C) / a) * (r^n)⁻¹) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_atTop_of_one_lt hr).inv_tendsto_atTop
    simpa using h.const_mul ((b + C) / a)
  have h2 : Filter.Tendsto (fun n : ℕ => (C / a) * ((n:ℝ) / r^n)) Filter.atTop (nhds 0) := by
    have h := tendsto_pow_const_div_const_pow_of_one_lt (1 : ℕ) hr
    simpa using h.const_mul (C / a)
  have h3 : Filter.Tendsto (fun n : ℕ => ((b + C) / a) * (r^n)⁻¹ + (C / a) * ((n:ℝ) / r^n))
      Filter.atTop (nhds 0) := by
    simpa using h1.add h2
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ((b + C) / a) * (r^n)⁻¹ + (C / a) * ((n:ℝ) / r^n) < 1 :=
    h3.eventually (eventually_lt_nhds zero_lt_one)
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨n, ?_⟩
  have hrpow : (0:ℝ) < r^n := pow_pos hr0 n
  have key : ((b + C) / a) * (r^n)⁻¹ + (C / a) * ((n:ℝ) / r^n)
      = (b + C * (1 + (n:ℝ))) / (a * r^n) := by
    field_simp
    ring
  rw [key, div_lt_one (by positivity)] at hn
  exact hn

lemma floquet_mono_of_recur (T : ℝ) (hT : 2 < T) (R : ℕ → ℝ) (hR0 : R 0 ≤ 0) (hRnn : ∀ k, 0 ≤ R k)
    (hrec : ∀ k : ℕ, T * R (k+1) - R k ≤ R (k+2)) :
    ∀ n : ℕ, R (n+1) ≤ R (n+2) := by
  intro n
  induction n with
  | zero =>
      have h1 := hrec 0
      have h2 : (0:ℝ) ≤ R (0+1) := hRnn (0+1)
      ring_nf at h1 h2 hR0 ⊢
      have h4 : (T-1) * R 1 ≤ R 2 := by nlinarith [h1, hR0]
      have h5 : R 1 ≤ (T-1) * R 1 := by
        have hh := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ T - 1 by linarith) h2
        simpa using hh
      linarith
  | succ j ih =>
      have h1 := hrec (j+1)
      have h2 : (0:ℝ) ≤ R ((j+1)+1) := hRnn ((j+1)+1)
      ring_nf at h1 h2 ih ⊢
      have h4 : (T-1) * R (2+j) ≤ R (3+j) := by nlinarith [h1, ih]
      have h5 : R (2+j) ≤ (T-1) * R (2+j) := by
        have hh := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ T - 1 by linarith) h2
        simpa using hh
      linarith

lemma floquet_recur_growth (T : ℝ) (hT : 2 < T) (R : ℕ → ℝ) (hR0 : R 0 ≤ 0) (hRnn : ∀ k, 0 ≤ R k)
    (hrec : ∀ k : ℕ, T * R (k+1) - R k ≤ R (k+2)) :
    ∀ k : ℕ, (T-1)^k * R 1 ≤ R (k+1) := by
  have hmono := floquet_mono_of_recur T hT R hR0 hRnn hrec
  intro k
  induction k with
  | zero => simp
  | succ j ih =>
    have hstep : (T-1) * R (j+1) ≤ R (j+2) := by
      cases j with
      | zero =>
        have h1 := hrec 0
        have h2 : (0:ℝ) ≤ R (0+1) := hRnn (0+1)
        ring_nf at h1 h2 hR0 ⊢
        nlinarith [h1, h2, hR0]
      | succ i =>
        have h1 := hrec (i+1)
        have hm : R (i+1) ≤ R (i+1+1) := hmono i
        ring_nf at h1 hm ⊢
        nlinarith [h1, hm]
    calc (T-1)^(j+1) * R 1 = (T-1) * ((T-1)^j * R 1) := by ring
      _ ≤ (T-1) * R (j+1) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ R (j+2) := hstep



/-- **Core linear algebra.**  A nonzero orbit of `A ∈ SL₂(ℂ)` that grows at most linearly in
both directions forces `‖tr A‖ ≤ 2`. -/
theorem orbit_trace_norm_le_two (A : Matrix (Fin 2) (Fin 2) ℂ) (W : ℤ → Fin 2 → ℂ) (C : ℝ)
    (hdet : A.det = 1) (hrec : ∀ k : ℤ, W (k + 1) = A.mulVec (W k)) (h0 : W 0 ≠ 0)
    (h : ∀ k : ℤ, ‖W k 0‖ ≤ C * (1 + |(k : ℝ)|) ∧ ‖W k 1‖ ≤ C * (1 + |(k : ℝ)|)) :
    ‖A.trace‖ ≤ 2 := by
  by_contra hc
  rw [not_le] at hc
  have hC0 : 0 ≤ C := by
    have hh := (h 0).1
    simp only [Int.cast_zero, abs_zero, add_zero, mul_one] at hh
    linarith [norm_nonneg (W 0 0)]
  set t : ℂ := A.trace with ht
  have hAA : A * A = t • A - 1 := by
    rw [ht, floquet_CH A, hdet]; simp
  have hleft : (t • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A) * A = 1 := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hAA, sub_sub_cancel]
  have hinj : ∀ v v' : Fin 2 → ℂ, A.mulVec v = A.mulVec v' → v = v' := by
    intro v v' hv
    have h1 : (t • 1 - A).mulVec (A.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
    have h2 : (t • 1 - A).mulVec (A.mulVec v') = v' := by
      rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
    rw [← h1, hv, h2]
  have hSrec : ∀ k : ℤ, floquet_det2 (W 0) (W (k+2)) = t * floquet_det2 (W 0) (W (k+1)) - floquet_det2 (W 0) (W k) := by
    intro k
    have hk : W (k+2) = t • W (k+1) - W k := by
      have e1 : W ((k+1)+1) = A.mulVec (W (k+1)) := hrec (k+1)
      have e2 : W (k+1) = A.mulVec (W k) := hrec k
      rw [show k+2 = (k+1)+1 by ring, e1, e2, Matrix.mulVec_mulVec, hAA,
          Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hk, floquet_det2_sub_right, floquet_det2_smul_right]
  have hSbd : ∀ k : ℤ, ‖floquet_det2 (W 0) (W k)‖ ≤ (‖W 0 0‖ + ‖W 0 1‖) * (2 * C * (1 + |(k:ℝ)|)) := by
    intro k
    have h1 := (h k).1
    have h2 := (h k).2
    have hM0 : 0 ≤ ‖W 0 0‖ + ‖W 0 1‖ := by positivity
    calc ‖floquet_det2 (W 0) (W k)‖ = ‖(W 0 0) * (W k 1) - (W 0 1) * (W k 0)‖ := by simp [floquet_det2]
      _ ≤ ‖(W 0 0) * (W k 1)‖ + ‖(W 0 1) * (W k 0)‖ := norm_sub_le _ _
      _ = ‖W 0 0‖ * ‖W k 1‖ + ‖W 0 1‖ * ‖W k 0‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖W 0 0‖ * (C * (1 + |(k:ℝ)|)) + ‖W 0 1‖ * (C * (1 + |(k:ℝ)|)) := by
            gcongr
      _ = (‖W 0 0‖ + ‖W 0 1‖) * (C * (1 + |(k:ℝ)|)) := by ring
      _ ≤ (‖W 0 0‖ + ‖W 0 1‖) * (2 * C * (1 + |(k:ℝ)|)) := by
            apply mul_le_mul_of_nonneg_left _ hM0
            nlinarith [hC0, abs_nonneg (k:ℝ), mul_nonneg hC0 (by positivity : (0:ℝ) ≤ 1 + |(k:ℝ)|)]
  by_cases hdelta : floquet_det2 (W 0) (W (1:ℤ)) = 0
  · -- Case B: `W 1 = lam • W 0`
    obtain ⟨lam, hlam⟩ := floquet_det2_eq_zero_iff (W 0) (W (1:ℤ)) h0 hdelta
    have hW1 : W (1:ℤ) = lam • W 0 := hlam
    have hA0 : A.mulVec (W 0) = lam • W 0 := by
      rw [← hrec 0]; simpa using hW1
    have hlam0 : lam ≠ 0 := by
      intro hl
      have h1 : lam • W 0 = 0 := by rw [hl, zero_smul]
      have h2 : A.mulVec (W 0) = A.mulVec 0 := by rw [hA0, h1, Matrix.mulVec_zero]
      exact h0 (hinj (W 0) 0 h2)
    have hpowk : ∀ n : ℕ, W (n:ℤ) = lam^n • W 0 := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        have h1 : W ((m:ℤ)+1) = A.mulVec (W (m:ℤ)) := hrec (m:ℤ)
        rw [show (((m+1:ℕ)):ℤ) = (m:ℤ)+1 by push_cast; ring, h1, ih, Matrix.mulVec_smul,
            hA0, smul_smul, pow_succ]
    have hpown : ∀ n : ℕ, W (-(n:ℤ)) = (lam⁻¹)^n • W 0 := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        apply hinj
        have h1 : A.mulVec (W (-(((m+1:ℕ)):ℤ))) = A.mulVec ((lam⁻¹)^(m+1) • W 0) := by
          rw [← hrec (-(((m+1:ℕ)):ℤ))]
          rw [show -(((m+1:ℕ)):ℤ) + 1 = -(m:ℤ) by push_cast; ring, ih]
          rw [Matrix.mulVec_smul, hA0, smul_smul, pow_succ, mul_assoc, inv_mul_cancel₀ hlam0, mul_one]
        exact h1
    obtain ⟨j, hj⟩ : ∃ j : Fin 2, W 0 j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact h0 (funext fun i => hcon i)
    have hbndj : ∀ n : ℤ, ‖W n j‖ ≤ C * (1 + |(n:ℝ)|) := by
      fin_cases j
      · exact fun n => (h n).1
      · exact fun n => (h n).2
    have hnorm1 : ‖lam‖ ≤ 1 := by
      by_contra hcon
      rw [not_le] at hcon
      have hb : ∀ n : ℕ, ‖lam‖^n * ‖W 0 j‖ ≤ C * (1 + (n:ℝ)) := by
        intro n
        have h1 := hbndj (n:ℤ)
        have h2 : W (n:ℤ) j = lam^n * W 0 j := by
          rw [hpowk n]; simp
        rw [h2, norm_mul] at h1
        simpa using h1
      obtain ⟨n, hn⟩ := floquet_exp_beats_linear ‖lam‖ hcon ‖W 0 j‖ 0 C (norm_pos_iff.mpr hj) le_rfl hC0
      rw [zero_add] at hn
      nlinarith [hb n, hn]
    have hnorm2 : 1 ≤ ‖lam‖ := by
      by_contra hcon
      rw [not_le] at hcon
      have hlt : 1 < ‖lam⁻¹‖ := by
        rw [norm_inv]
        exact (one_lt_inv₀ (norm_pos_iff.mpr hlam0)).mpr hcon
      have hb : ∀ n : ℕ, ‖lam⁻¹‖^n * ‖W 0 j‖ ≤ C * (1 + (n:ℝ)) := by
        intro n
        have h1 := hbndj (-(n:ℤ))
        have h2 : W (-(n:ℤ)) j = (lam⁻¹)^n * W 0 j := by
          rw [hpown n]; simp
        have h4 : ((1:ℝ) + |((-(n:ℤ)) : ℝ)|) = (1 + (n:ℝ)) := by
          have e : ((-(n:ℤ)) : ℝ) = -(n:ℝ) := by push_cast; ring
          rw [e, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
        rw [h2, norm_mul] at h1
        simp only [Int.cast_neg] at h1
        rw [h4] at h1
        simpa using h1
      obtain ⟨n, hn⟩ := floquet_exp_beats_linear ‖lam⁻¹‖ hlt ‖W 0 j‖ 0 C (norm_pos_iff.mpr hj) le_rfl hC0
      rw [zero_add] at hn
      nlinarith [hb n, hn]
    have hlam1 : ‖lam‖ = 1 := le_antisymm hnorm1 hnorm2
    have hquad : lam * lam - t * lam + 1 = 0 := by
      have h1 : A.mulVec (A.mulVec (W 0)) = (A * A).mulVec (W 0) := by rw [Matrix.mulVec_mulVec]
      have h2 : A.mulVec (A.mulVec (W 0)) = (lam * lam) • W 0 := by
        rw [hA0, Matrix.mulVec_smul, hA0, smul_smul]
      have h3 : (A * A).mulVec (W 0) = (t * lam - 1) • W 0 := by
        rw [hAA, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hA0, smul_smul,
            sub_smul, one_smul]
      have h4 : (lam * lam) • W 0 = (t * lam - 1) • W 0 := by rw [← h2, h1, h3]
      have h5 : (lam * lam - t * lam + 1) * W 0 j = 0 := by
        have hh : lam * lam * W 0 j = (t * lam - 1) * (W 0 j) := by
          have hh' := congrFun h4 j
          simpa using hh'
        have h6 : (lam * lam - (t * lam - 1)) * W 0 j = 0 := by
          rw [sub_mul, hh, sub_self]
        rwa [show lam * lam - (t * lam - 1) = lam * lam - t * lam + 1 by ring] at h6
      exact (mul_eq_zero.mp h5).resolve_right hj
    have htval : t = lam + lam⁻¹ := by
      have h1 : t * lam = lam * lam + 1 := by linear_combination -hquad
      have h2 : (lam + lam⁻¹) * lam = lam * lam + 1 := by
        field_simp
      exact mul_right_cancel₀ hlam0 (h1.trans h2.symm)
    have hfin : ‖t‖ ≤ 2 := by
      rw [htval]
      calc ‖lam + lam⁻¹‖ ≤ ‖lam‖ + ‖lam⁻¹‖ := norm_add_le _ _
        _ = 1 + 1 := by rw [hlam1, norm_inv, hlam1, inv_one]
        _ = 2 := by norm_num
    linarith
  · -- Case A: `W 0` and `W 1` are independent
    have hR1pos : 0 < ‖floquet_det2 (W 0) (W (1:ℤ))‖ := norm_pos_iff.mpr hdelta
    have hrecR : ∀ k : ℕ, ‖t‖ * ‖floquet_det2 (W 0) (W (((k+1:ℕ)):ℤ))‖ - ‖floquet_det2 (W 0) (W ((k:ℕ):ℤ))‖
        ≤ ‖floquet_det2 (W 0) (W (((k+2:ℕ)):ℤ))‖ := by
      intro k
      have h := hSrec (k:ℤ)
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h ⊢
      rw [h]
      calc ‖t‖ * ‖floquet_det2 (W 0) (W (k+1))‖ - ‖floquet_det2 (W 0) (W k)‖
          = ‖t * floquet_det2 (W 0) (W (k+1))‖ - ‖floquet_det2 (W 0) (W k)‖ := by rw [norm_mul]
        _ ≤ ‖t * floquet_det2 (W 0) (W (k+1)) - floquet_det2 (W 0) (W k)‖ :=
              le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
    have hgrowth := floquet_recur_growth ‖t‖ hc (fun k : ℕ => ‖floquet_det2 (W 0) (W ((k:ℤ)))‖)
      (by have h0' : floquet_det2 (W 0) (W (0:ℤ)) = 0 := by rw [floquet_det2]; ring
          simp only [Nat.cast_zero, h0', norm_zero, le_refl])
      (fun k => norm_nonneg _) hrecR
    set M : ℝ := (‖W 0 0‖ + ‖W 0 1‖) * (2 * C) with hM
    have hMnn : 0 ≤ M := by rw [hM]; positivity
    have hSbdM : ∀ k : ℤ, ‖floquet_det2 (W 0) (W k)‖ ≤ M * (1 + |(k:ℝ)|) := by
      intro k
      have h1 := hSbd k
      rw [hM]
      calc ‖floquet_det2 (W 0) (W k)‖ ≤ (‖W 0 0‖ + ‖W 0 1‖) * (2 * C * (1 + |(k:ℝ)|)) := h1
        _ = ((‖W 0 0‖ + ‖W 0 1‖) * (2 * C)) * (1 + |(k:ℝ)|) := by ring
    obtain ⟨k, hk⟩ := floquet_exp_beats_linear (‖t‖ - 1) (by linarith) ‖floquet_det2 (W 0) (W (1:ℤ))‖ M M
      hR1pos hMnn hMnn
    have hg : ‖floquet_det2 (W 0) (W (1:ℤ))‖ * (‖t‖ - 1)^k ≤ ‖floquet_det2 (W 0) (W (((k+1:ℕ)):ℤ))‖ := by
      have h1 := hgrowth k
      rw [mul_comm]
      simpa only [Nat.cast_one] using h1
    have hb : ‖floquet_det2 (W 0) (W (((k+1:ℕ)):ℤ))‖ ≤ M * (2 + (k:ℝ)) := by
      have h1 := hSbdM (((k+1:ℕ)):ℤ)
      have h2 : |(((((k+1:ℕ)):ℤ)) : ℝ)| = (k:ℝ) + 1 := by
        have e : (((((k+1:ℕ)):ℤ)) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
        rw [e, abs_of_nonneg (by positivity)]
      rw [h2] at h1
      convert h1 using 2
      ring
    have heq : M + M * (1 + (k:ℝ)) = M * (2 + (k:ℝ)) := by ring
    linarith [hk, hg, hb, heq]


theorem floquet_of_genEigen (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ) (u : ℤ → ℂ) (hu : IsGenEigen ((p : ℝ) / (q : ℝ)) lam 0 E u) : ‖(iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q 0).trace‖ ≤ 2 := by
  obtain ⟨hne, hrec, C, hC⟩ := hu
  have hC0 : 0 ≤ C := by
    have h := hC 0
    simp only [Int.cast_zero, abs_zero, add_zero, mul_one] at h
    linarith [norm_nonneg (u 0)]
  set A : Matrix (Fin 2) (Fin 2) ℂ := iterC ((p:ℝ)/(q:ℝ)) lam (E:ℂ) q 0 with hA
  set W : ℤ → Fin 2 → ℂ := fun k => ![u (k * q), u (k * q - 1)] with hW
  have hW0 : W 0 ≠ 0 := by
    intro h
    have h1 : u 0 = 0 := by
      have hh := congrFun h 0
      simp only [hW, Pi.zero_apply] at hh
      simpa using hh
    have h2 : u (-1) = 0 := by
      have hh := congrFun h 1
      simp only [hW, Pi.zero_apply] at hh
      simpa using hh
    exact hne (floquet_vanish ((p:ℝ)/(q:ℝ)) lam 0 (E:ℂ) u hrec h1 h2)
  have hdet : A.det = 1 := by rw [hA]; exact det_iterC _ _ _ _ _
  have hstep : ∀ k : ℤ, W (k+1) = A.mulVec (W k) := by
    intro k
    simpa only [hA, hW] using (Work.TMC7Core.Solutions.block_transfer p q hq lam E u hrec k).symm
  have hbnd : ∀ k : ℤ, ‖W k 0‖ ≤ (2*C*(1+q)) * (1 + |(k:ℝ)|) ∧
      ‖W k 1‖ ≤ (2*C*(1+q)) * (1 + |(k:ℝ)|) := by
    intro k
    obtain ⟨h1, h2⟩ := floquet_bound q u C hC0 hC k
    exact ⟨by simpa [hW] using h1, by simpa [hW] using h2⟩
  have hmain := orbit_trace_norm_le_two A W (2*C*(1+q)) hdet hstep hW0 hbnd
  rwa [hA] at hmain

end Work.TMC7Core.FtbAux
