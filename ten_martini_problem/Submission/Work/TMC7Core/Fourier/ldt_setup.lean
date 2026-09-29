import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
import Submission.Work.TMC7Core.Cocycle.log_frob_iterC_nonneg
import Submission.Work.TMC7Core.LDT

/-!
# TMC7Core: setup for the large deviation theorem

Basic estimates for `uAvg` (bounds, shift-Lipschitz), the Fejér kernel used in the moving
average, and the moving average itself.  These are the ingredients of the
Bourgain–Jitomirskaya large deviation proof (Lemma 4 of [BJ], arXiv:math-ph/0110040).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Fourier

/-- The ambient constant bounding the Frobenius norm of a single transfer matrix. -/
def ldtF (lam E : ℝ) : ℝ := |E| + 2 * |lam| + 2

theorem one_le_ldtF (lam E : ℝ) : 1 ≤ ldtF lam E := by
  have h : (0:ℝ) ≤ |E| + 2 * |lam| := by positivity
  simp only [ldtF]; linarith

theorem ldtF_pos (lam E : ℝ) : 0 < ldtF lam E := lt_of_lt_of_le one_pos (one_le_ldtF lam E)

/-- A single transfer matrix has Frobenius norm at most `ldtF lam E`. -/
theorem frob_tmC_le (lam E x : ℝ) : frob (tmC lam (E : ℂ) x) ≤ ldtF lam E := by
  set c : ℂ := ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) with hc
  have h2 : |2 * lam * Real.cos (2 * Real.pi * x)| ≤ 2 * |lam| := by
    have hb := abs_mul (2 * lam) (Real.cos (2 * Real.pi * x))
    have hb2 := abs_mul (2 : ℝ) lam
    have h3 : |Real.cos (2 * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    have h4 : |(2:ℝ)| = 2 := by norm_num
    rw [hb, hb2, h4]
    nlinarith [h3, abs_nonneg lam]
  have hbound : ‖(E : ℂ) - c‖ ≤ |E| + 2 * |lam| := by
    have h1 : ‖(E : ℂ) - c‖ ≤ ‖(E : ℂ)‖ + ‖c‖ := norm_sub_le _ _
    have h2' : ‖(E : ℂ)‖ = |E| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h3 : ‖c‖ = |2 * lam * Real.cos (2 * Real.pi * x)| := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hA : (tmC lam (E : ℂ) x) 0 0 = (E : ℂ) - c := rfl
  have hB : (tmC lam (E : ℂ) x) 0 1 = -1 := rfl
  have hC : (tmC lam (E : ℂ) x) 1 0 = 1 := rfl
  have hD : (tmC lam (E : ℂ) x) 1 1 = 0 := rfl
  have hs1 : ‖(E : ℂ) - c‖ ^ 2 ≤ (|E| + 2 * |lam|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hs2 : (|E| + 2 * |lam|) ^ 2 + 2 ≤ (|E| + 2 * |lam| + 2) ^ 2 := by
    nlinarith [abs_nonneg E, abs_nonneg lam]
  have hsq : frob (tmC lam (E : ℂ) x) ^ 2 ≤ (|E| + 2 * |lam| + 2) ^ 2 := by
    rw [Work.TMC7Core.frob_sq, hA, hB, hC, hD]
    simp only [norm_neg, norm_one, norm_zero]
    nlinarith [hs1, hs2]
  rw [ldtF]
  calc frob (tmC lam (E : ℂ) x) = Real.sqrt (frob (tmC lam (E : ℂ) x) ^ 2) :=
        (Real.sqrt_sq (frob_nonneg _)).symm
    _ ≤ Real.sqrt ((|E| + 2 * |lam| + 2) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |E| + 2 * |lam| + 2 := Real.sqrt_sq (by positivity)

/-- The `N`-fold product has Frobenius norm at most `ldtF lam E ^ N` (`N ≥ 1`). -/
theorem frob_iterC_add_le (α lam : ℝ) (E : ℝ) (M : ℕ) (x : ℝ) :
    frob (iterC α lam (E : ℂ) (1 + M) x) ≤ (ldtF lam E) ^ (1 + M) := by
  induction M with
  | zero =>
    have h1 : iterC α lam (E : ℂ) (1 + 0) x = tmC lam (E : ℂ) x := by
      rw [iterC_succ, iterC_zero, mul_one]
      norm_num
    rw [h1]
    simpa using frob_tmC_le lam E x
  | succ M ih =>
    have h1 : iterC α lam (E : ℂ) (1 + (M + 1)) x
        = tmC lam (E : ℂ) (x + ((1 + M : ℕ) : ℝ) * α) * iterC α lam (E : ℂ) (1 + M) x := by
      have := iterC_succ α lam (E : ℂ) (1 + M) x
      simpa [Nat.add_assoc] using this
    have hexp : (ldtF lam E) ^ (1 + (M + 1)) = (ldtF lam E) ^ (1 + M) * ldtF lam E := by
      rw [show 1 + (M + 1) = (1 + M) + 1 by omega, pow_succ]
    rw [h1, hexp]
    calc frob (tmC lam (E : ℂ) (x + ((1 + M : ℕ) : ℝ) * α) * iterC α lam (E : ℂ) (1 + M) x)
        ≤ frob (tmC lam (E : ℂ) (x + ((1 + M : ℕ) : ℝ) * α)) * frob (iterC α lam (E : ℂ) (1 + M) x) :=
          Work.TMC7Core.Cocycle.frob_mul_le _ _
      _ ≤ ldtF lam E * (ldtF lam E) ^ (1 + M) := by
          refine mul_le_mul (frob_tmC_le lam E _) ih (frob_nonneg _)
            (le_trans (by norm_num) (one_le_ldtF lam E))
      _ = (ldtF lam E) ^ (1 + M) * ldtF lam E := by ring

theorem frob_iterC_le (α lam : ℝ) (E : ℝ) (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    frob (iterC α lam (E : ℂ) N x) ≤ (ldtF lam E) ^ N := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  exact frob_iterC_add_le α lam E M x

theorem uAvg_le_ldtF (α lam : ℝ) (E : ℝ) (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    uAvg α lam (E : ℂ) N x ≤ Real.log (ldtF lam E) := by
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hfrobpos : 0 < frob (iterC α lam (E : ℂ) N x) :=
    lt_of_lt_of_le (by norm_num)
      (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one (det_iterC α lam (E:ℂ) N x))
  have hlog : Real.log (frob (iterC α lam (E : ℂ) N x)) ≤ Real.log ((ldtF lam E) ^ N) :=
    Real.log_le_log hfrobpos (frob_iterC_le α lam E N hN x)
  rw [Real.log_pow] at hlog
  rw [uAvg, div_le_iff₀ hNpos]
  calc Real.log (frob (iterC α lam (E : ℂ) N x))
      ≤ (N : ℝ) * Real.log (ldtF lam E) := hlog
    _ = Real.log (ldtF lam E) * (N : ℝ) := by ring

/-- The Frobenius norm is invariant under the adjugate for `2 × 2` complex matrices. -/
theorem frob_adjugate (A : Matrix (Fin 2) (Fin 2) ℂ) : frob A.adjugate = frob A := by
  have h00 : A.adjugate 0 0 = A 1 1 := by rw [Matrix.adjugate_fin_two]; rfl
  have h01 : A.adjugate 0 1 = -A 0 1 := by rw [Matrix.adjugate_fin_two]; rfl
  have h10 : A.adjugate 1 0 = -A 1 0 := by rw [Matrix.adjugate_fin_two]; rfl
  have h11 : A.adjugate 1 1 = A 0 0 := by rw [Matrix.adjugate_fin_two]; rfl
  have hs : frob A.adjugate ^ 2 = frob A ^ 2 := by
    rw [Work.TMC7Core.frob_sq, Work.TMC7Core.frob_sq, h00, h01, h10, h11]
    simp only [norm_neg]
    ring
  calc frob A.adjugate = Real.sqrt (frob A.adjugate ^ 2) := (Real.sqrt_sq (frob_nonneg _)).symm
    _ = Real.sqrt (frob A ^ 2) := by rw [hs]
    _ = frob A := Real.sqrt_sq (frob_nonneg _)

/-- `uAvg` is periodic in `x`. -/
theorem uAvg_period (α lam : ℝ) (E : ℂ) (N : ℕ) (x : ℝ) :
    uAvg α lam E N (x + 1) = uAvg α lam E N x := by
  simp only [uAvg, iterC_periodic]

/-- Matrix core of the shift-Lipschitz estimate: if `X * B = C * A` with `det B = det C = 1`,
then `log ‖X‖ - log ‖A‖` is bounded by `log ‖B‖ + log ‖C‖` (Frobenius norms). -/
theorem frob_log_diff_le (A X B C : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) (hX : X.det = 1)
    (hB : B.det = 1) (hC : C.det = 1)
    (hid : X * B = C * A) (gB gC : ℝ) (hFB : frob B ≤ gB) (hFC : frob C ≤ gC) :
    |Real.log (frob X) - Real.log (frob A)| ≤ Real.log gB + Real.log gC := by
  have hXeq : X = C * A * B.adjugate := by
    calc X = X * (B * B.adjugate) := by rw [Matrix.mul_adjugate, hB, one_smul, mul_one]
      _ = (X * B) * B.adjugate := by rw [Matrix.mul_assoc]
      _ = (C * A) * B.adjugate := by rw [hid]
  have hAeq : A = C.adjugate * X * B := by
    calc A = (C.det • 1) * A := by rw [hC, one_smul, one_mul]
      _ = (C.adjugate * C) * A := by rw [Matrix.adjugate_mul]
      _ = C.adjugate * (C * A) := by rw [Matrix.mul_assoc]
      _ = C.adjugate * (X * B) := by rw [hid]
      _ = C.adjugate * X * B := by rw [Matrix.mul_assoc]
  have hposA : 0 < frob A := lt_of_lt_of_le (by norm_num)
    (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one hA)
  have hposX : 0 < frob X := lt_of_lt_of_le (by norm_num)
    (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one hX)
  have hposB : 0 < frob B := lt_of_lt_of_le (by norm_num)
    (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one hB)
  have hposC : 0 < frob C := lt_of_lt_of_le (by norm_num)
    (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one hC)
  have hup : frob X ≤ frob C * frob A * frob B := by
    have hadj : frob B.adjugate = frob B := frob_adjugate B
    have h0 : frob X ≤ frob (C * A) * frob B := by
      rw [hXeq]
      calc frob ((C * A) * B.adjugate)
          ≤ frob (C * A) * frob B.adjugate := Work.TMC7Core.Cocycle.frob_mul_le _ _
        _ = frob (C * A) * frob B := by rw [hadj]
    calc frob X ≤ frob (C * A) * frob B := h0
      _ ≤ (frob C * frob A) * frob B :=
          mul_le_mul_of_nonneg_right (Work.TMC7Core.Cocycle.frob_mul_le C A) (frob_nonneg B)
      _ = frob C * frob A * frob B := by ring
  have hdown : frob A ≤ frob C * frob X * frob B := by
    have h0 : frob A ≤ frob (C.adjugate * X) * frob B := by
      rw [hAeq]
      exact Work.TMC7Core.Cocycle.frob_mul_le _ _
    have h1 : frob (C.adjugate * X) ≤ frob C * frob X := by
      have h := Work.TMC7Core.Cocycle.frob_mul_le C.adjugate X
      rwa [frob_adjugate] at h
    calc frob A ≤ frob (C.adjugate * X) * frob B := h0
      _ ≤ (frob C * frob X) * frob B := mul_le_mul_of_nonneg_right h1 (frob_nonneg B)
      _ = frob C * frob X * frob B := by ring
  have hup' : Real.log (frob X) ≤ Real.log (frob A) + Real.log gB + Real.log gC := by
    have h1 : Real.log (frob X) ≤ Real.log (frob C * frob A * frob B) :=
      Real.log_le_log hposX hup
    rw [Real.log_mul (mul_ne_zero (ne_of_gt hposC) (ne_of_gt hposA)) (ne_of_gt hposB),
      Real.log_mul (ne_of_gt hposC) (ne_of_gt hposA)] at h1
    have h2 : Real.log (frob C) ≤ Real.log gC := Real.log_le_log hposC hFC
    have h3 : Real.log (frob B) ≤ Real.log gB := Real.log_le_log hposB hFB
    linarith
  have hdown' : Real.log (frob A) ≤ Real.log (frob X) + Real.log gB + Real.log gC := by
    have h1 : Real.log (frob A) ≤ Real.log (frob C * frob X * frob B) :=
      Real.log_le_log hposA hdown
    rw [Real.log_mul (mul_ne_zero (ne_of_gt hposC) (ne_of_gt hposX)) (ne_of_gt hposB),
      Real.log_mul (ne_of_gt hposC) (ne_of_gt hposX)] at h1
    have h2 : Real.log (frob C) ≤ Real.log gC := Real.log_le_log hposC hFC
    have h3 : Real.log (frob B) ≤ Real.log gB := Real.log_le_log hposB hFB
    linarith
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Shift-Lipschitz estimate** (for nonnegative integer shifts): shifting the phase by `k` steps
of `α` changes `uAvg` by at most `2 k log F / N`. -/
theorem uAvg_shift_nat_le (α lam : ℝ) (E : ℝ) (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : 1 ≤ k)
    (x : ℝ) :
    |uAvg α lam (E : ℂ) N (x + (k : ℝ) * α) - uAvg α lam (E : ℂ) N x|
      ≤ 2 * (k : ℝ) * Real.log (ldtF lam E) / (N : ℝ) := by
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hid : iterC α lam (E : ℂ) N (x + (k : ℝ) * α) * iterC α lam (E : ℂ) k x
      = iterC α lam (E : ℂ) k (x + (N : ℝ) * α) * iterC α lam (E : ℂ) N x := by
    have h1 := iterC_add α lam (E : ℂ) N k x
    have h2 := iterC_add α lam (E : ℂ) k N x
    rw [Nat.add_comm k N] at h2
    rw [← h2, ← h1]
  have hmain := frob_log_diff_le (iterC α lam (E : ℂ) N x) (iterC α lam (E : ℂ) N (x + (k:ℝ)*α))
    (iterC α lam (E : ℂ) k x) (iterC α lam (E : ℂ) k (x + (N:ℝ)*α))
    (det_iterC α lam (E : ℂ) N x) (det_iterC α lam (E : ℂ) N (x + (k:ℝ)*α))
    (det_iterC α lam (E : ℂ) k x) (det_iterC α lam (E : ℂ) k (x + (N:ℝ)*α)) hid
    ((ldtF lam E) ^ k) ((ldtF lam E) ^ k)
    (frob_iterC_le α lam E k hk x) (frob_iterC_le α lam E k hk (x + (N:ℝ)*α))
  rw [Real.log_pow] at hmain
  have hkey : |Real.log (frob (iterC α lam (E:ℂ) N (x + (k:ℝ)*α))) / (N:ℝ)
      - Real.log (frob (iterC α lam (E:ℂ) N x)) / (N:ℝ)|
      ≤ 2 * (k:ℝ) * Real.log (ldtF lam E) / (N:ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hNpos]
    rw [div_le_div_iff_of_pos_right hNpos]
    calc |Real.log (frob (iterC α lam (E:ℂ) N (x + (k:ℝ)*α))) - Real.log (frob (iterC α lam (E:ℂ) N x))|
        ≤ (k:ℝ) * Real.log (ldtF lam E) + (k:ℝ) * Real.log (ldtF lam E) := hmain
      _ = 2 * (k:ℝ) * Real.log (ldtF lam E) := by ring
  simpa only [uAvg] using hkey

/-- Shift-Lipschitz for arbitrary integer shifts. -/
theorem uAvg_shift_le (α lam : ℝ) (E : ℝ) (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ℝ) :
    |uAvg α lam (E : ℂ) N (x + (j : ℝ) * α) - uAvg α lam (E : ℂ) N x|
      ≤ 2 * |(j : ℝ)| * Real.log (ldtF lam E) / (N : ℝ) := by
  by_cases hj : 0 ≤ j
  · rcases eq_or_lt_of_le hj with h | h
    · subst h; simp
    · have hk : 1 ≤ j.toNat := by
        have h1 : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
        omega
      have hcast : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
        have h1 : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
        exact_mod_cast h1
      have habs : |((j : ℝ))| = (j : ℝ) := abs_of_nonneg (by exact_mod_cast hj)
      simpa only [hcast, habs] using uAvg_shift_nat_le α lam E N hN j.toNat hk x
  · push_neg at hj
    have hj' : j < 0 := hj
    have hk : 1 ≤ (-j).toNat := by
      have h1 : ((-j).toNat : ℤ) = -j := Int.toNat_of_nonneg (by omega)
      omega
    have hcast : (((-j).toNat : ℕ) : ℝ) = -(j : ℝ) := by
      have h1 : ((-j).toNat : ℤ) = -j := Int.toNat_of_nonneg (by omega)
      exact_mod_cast h1
    have hx : x + (j : ℝ) * α + ((-j).toNat : ℝ) * α = x := by rw [hcast]; ring
    have habs : |((j : ℝ))| = -(j : ℝ) := abs_of_neg (by exact_mod_cast hj')
    have hmain := uAvg_shift_nat_le α lam E N hN (-j).toNat hk (x + (j:ℝ)*α)
    rw [hx, hcast] at hmain
    rw [abs_sub_comm]
    simpa only [habs] using hmain

/-! ## The Fejér kernel -/

/-- The Fejér kernel evaluated along the rotation, normalised to `1` at the origin. -/
def fejerKer (R : ℕ) (θ : ℝ) : ℝ :=
  ‖(∑ j ∈ Finset.range R, Complex.exp (2 * Real.pi * Complex.I * (j : ℝ) * θ)) / (R : ℂ)‖ ^ 2

theorem fejerKer_def' (R : ℕ) (θ : ℝ) :
    fejerKer R θ
      = ‖(∑ j ∈ Finset.range R, Complex.exp (2 * Real.pi * Complex.I * (j : ℝ) * θ)) / (R : ℂ)‖ ^ 2 :=
  rfl

theorem fejerKer_nonneg (R : ℕ) (θ : ℝ) : 0 ≤ fejerKer R θ := by
  rw [fejerKer_def']; positivity

theorem fejerKer_zero (R : ℕ) (hR : 1 ≤ R) : fejerKer R 0 = 1 := by
  have hR0 : (R : ℂ) ≠ 0 := by simp only [Nat.cast_ne_zero]; omega
  rw [fejerKer_def']
  have hterm : ∀ j ∈ Finset.range R,
      Complex.exp (2 * Real.pi * Complex.I * (j : ℝ) * ((0:ℝ) : ℂ)) = 1 := by
    intro j _
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    div_self hR0, norm_one, one_pow]

theorem fejerKer_le_one (R : ℕ) (θ : ℝ) : fejerKer R θ ≤ 1 := by
  have h1 : ‖∑ j ∈ Finset.range R, Complex.exp (2 * Real.pi * Complex.I * (j : ℝ) * θ)‖
      ≤ (R : ℝ) := by
    calc ‖∑ j ∈ Finset.range R, Complex.exp (2 * Real.pi * Complex.I * (j : ℝ) * θ)‖
        ≤ ∑ j ∈ Finset.range R, ‖Complex.exp (2 * Real.pi * Complex.I * (j : ℝ) * θ)‖ :=
          norm_sum_le _ _
      _ = ∑ _j ∈ Finset.range R, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Complex.norm_exp]
          simp [Complex.mul_re, Complex.ofReal_re]
      _ = (R : ℝ) := by simp
  have h2 : ‖(R : ℂ)‖ = (R : ℝ) := by simp
  rcases Nat.eq_zero_or_pos R with h | h
  · subst h; rw [fejerKer_def']; simp
  · have hRpos : (0:ℝ) < R := by exact_mod_cast h
    rw [fejerKer_def', norm_div, h2, div_pow, div_le_one (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-! ## The moving average -/

/-- The Fejér (moving) average of `g` along the orbit of the rotation by `α`: the average of
`g (x + (j - j') α)` over `0 ≤ j, j' < R`. -/
def mAve (g : ℝ → ℂ) (α : ℝ) (R : ℕ) (x : ℝ) : ℂ :=
  ((R : ℂ) ^ 2)⁻¹ * ∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
    g (x + ((j : ℝ) - (j' : ℝ)) * α)

/-- `uAvg` is nonnegative. -/
theorem uAvg_nonneg (α lam : ℝ) (E : ℂ) (N : ℕ) (x : ℝ) : 0 ≤ uAvg α lam E N x := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [uAvg]
  · have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast h
    rw [uAvg, div_nonneg_iff]
    exact Or.inl ⟨Work.TMC7Core.Cocycle.log_frob_iterC_nonneg α lam E N x, hNpos.le⟩

end Work.TMC7Core.Fourier

end
