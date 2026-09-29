import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Rat
import Submission.Work.TMC14Core.hyps_reduce
import Submission.Work.TMComp.LocCantor.frobR_defs
import Submission.Work.TMComp.LocCantor.frobR_mul_self
import Submission.Work.TMComp.LocCantor.trace_sq_sub_four_le_frobR_sq
import Submission.Work.TMComp.LocCantor.defect_arith

/-!
# The lower defect bound in the hyperbolic regime

For `A ∈ SL₂(ℝ)` with `|tr A| ≥ 2` and `m ≥ 1`,

`log ‖A^{2m}‖_F − log ‖A^m‖_F − m log (ρSL (tr A))  ≥  −log 2`,

where `ρSL τ` is the spectral radius of an `SL₂(ℝ)` matrix of trace `τ`, and `‖·‖_F` is the
Frobenius norm of the complexification.

The mathematics.  Put `τ = tr A`, `B = A^m` and `ρ = ρSL τ`.

* The eigenvalues of `A` are real, of modulus `ρ` and `ρ^{-1}`, so the trace sequence
  `m ↦ tr (A^m)` satisfies `|tr (A^m)| = ρ^m + ρ^{-m}` (`trace_abs_pow_eq_rhoSL_aux` below,
  by Cayley–Hamilton `trace_pow_rec` plus the two–step induction for the geometric
  sequence `λ^m + λ^{-m}`).
* Hence `B ∈ SL₂(ℝ)` and `q := (tr B)² = (ρ^m + ρ^{-m})² = R² + 2 + R^{-2}` with `R = ρ^m`.
* For real `B` with `det B = 1`, `B² = (tr B) · B - 1` gives the exact identity
  `‖B²‖_F² = 2 + (tr B)² (‖B‖_F² - 2)` (`frobR_mul_self`), while `B = [[a,b],[c,d]]`
  gives `‖B‖_F² - 2 - ((tr B)² - 4) = (b - c)² ≥ 0`
  (`trace_sq_sub_four_le_frobR_sq`), i.e. `X := ‖B‖_F² ≥ q - 2`.
* Both sides of the wanted bound are affine in `X` with positive leading coefficient, so the
  worst case is `X = q - 2`; the resulting elementary inequality
  `(R²/4) X ≤ 2 + q (X - 2)` is `defect_arith`.
* Taking square roots gives `(ρ^m/2) ‖A^m‖_F ≤ ‖A^{2m}‖_F`, and taking logarithms gives the
  claim.
-/

namespace Work.TMComp.LocCantor

/-! ## 1. The trace of the `m`-th power in terms of `ρSL` -/

/-- If `λ + λ⁻¹ = tr A` with `λ ≠ 0`, then `tr (A^k) = λ^k + λ^{-k}` for the two–term
recurrence of the trace sequence (`Work.TMC14Core.trace_pow_rec`). -/
lemma trace_pow_eq_lam (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (lam : ℝ)
    (hlamne : lam ≠ 0) (hlam : lam + lam⁻¹ = A.trace) (k : ℕ) :
    (A ^ k).trace = lam ^ k + (lam ^ k)⁻¹ := by
  have hrec : ∀ n : ℕ, lam ^ (n + 2) + (lam ^ (n + 2))⁻¹
      = A.trace * (lam ^ (n + 1) + (lam ^ (n + 1))⁻¹) - (lam ^ n + (lam ^ n)⁻¹) := by
    intro n
    rw [← hlam]
    field_simp
    ring
  refine Nat.twoStepInduction ?_ ?_ ?_ k
  · norm_num [Matrix.trace_one]
  · simpa using hlam.symm
  · intro n ih0 ih1
    rw [Work.TMC14Core.trace_pow_rec A hdet n, ih0, ih1]
    exact (hrec n).symm

/-- Consequence for the modulus: `|tr (A^m)| = |λ|^m + |λ|^{-m}`. -/
lemma trace_abs_pow_eq_of_lam (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (lam : ℝ)
    (hlamne : lam ≠ 0) (hlam : lam + lam⁻¹ = A.trace)
    (hlamabs : |lam| = Work.TMC7Core.rhoSL A.trace) (m : ℕ) :
    |(A ^ m).trace| = Work.TMC7Core.rhoSL A.trace ^ m + (Work.TMC7Core.rhoSL A.trace ^ m)⁻¹ := by
  have hpow : (A ^ m).trace = lam ^ m + (lam ^ m)⁻¹ := trace_pow_eq_lam A hdet lam hlamne hlam m
  have hxne : lam ^ m ≠ 0 := pow_ne_zero m hlamne
  have hmul : 0 ≤ lam ^ m * (lam ^ m)⁻¹ := by
    rw [mul_inv_cancel₀ hxne]; norm_num
  have habs : |lam ^ m + (lam ^ m)⁻¹| = |lam ^ m| + |(lam ^ m)⁻¹| :=
    (abs_add_eq_add_abs_iff _ _).mpr (mul_nonneg_iff.mp hmul)
  rw [hpow, habs, abs_pow, abs_inv, abs_pow, hlamabs]

/-- For `A ∈ SL₂(ℝ)` with `|tr A| ≥ 2` the modulus of the trace of `A^m` is exactly
`ρ^m + ρ^{-m}` with `ρ = ρSL (tr A)`. -/
theorem trace_abs_pow_eq_rhoSL_aux (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1)
    (hτ : 2 ≤ |A.trace|) (m : ℕ) :
    |(A ^ m).trace| = Work.TMC7Core.rhoSL A.trace ^ m + (Work.TMC7Core.rhoSL A.trace ^ m)⁻¹ := by
  have hτ2 : 0 ≤ A.trace ^ 2 - 4 := by
    have := sq_abs A.trace
    nlinarith [abs_nonneg A.trace]
  set s : ℝ := Real.sqrt (A.trace ^ 2 - 4) with hs
  have hs2 : s ^ 2 = A.trace ^ 2 - 4 := by rw [hs]; exact Real.sq_sqrt hτ2
  have hsn : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  rcases le_or_gt 0 A.trace with hnn | hneg
  · -- positive trace: the root of larger modulus is `(τ + s)/2`
    have hτge : 2 ≤ A.trace := by rw [abs_of_nonneg hnn] at hτ; exact hτ
    set lam : ℝ := (A.trace + s) / 2 with hl
    have hlpos : 0 < lam := by rw [hl]; linarith
    have hlne : lam ≠ 0 := ne_of_gt hlpos
    have hq : lam ^ 2 - A.trace * lam + 1 = 0 := by
      rw [hl]
      have hkey : ((A.trace + s) / 2) ^ 2 - A.trace * ((A.trace + s) / 2) + 1
          = (s ^ 2 - (A.trace ^ 2 - 4)) / 4 := by ring
      rw [hkey, hs2]; ring
    have hlsum : lam + lam⁻¹ = A.trace := by
      have h1 : lam * (lam + lam⁻¹ - A.trace) = 0 := by
        have hkey : lam * (lam + lam⁻¹ - A.trace) = lam ^ 2 - A.trace * lam + 1 := by
          field_simp
          ring
        rw [hkey, hq]
      have h2 : lam + lam⁻¹ - A.trace = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hlne
        · exact h
      linarith
    have hlabs : |lam| = Work.TMC7Core.rhoSL A.trace := by
      have hρ : Work.TMC7Core.rhoSL A.trace = (A.trace + s) / 2 := by
        rw [Work.TMC7Core.rhoSL, if_pos hτ, abs_of_nonneg hnn, ← hs]
      rw [hρ, abs_of_pos hlpos, hl]
    exact trace_abs_pow_eq_of_lam A hdet lam hlne hlsum hlabs m
  · -- negative trace: the root of larger modulus is `(τ - s)/2`
    have hτle : A.trace ≤ -2 := by
      have h := hτ
      rw [abs_of_neg hneg] at h
      linarith
    set lam : ℝ := (A.trace - s) / 2 with hl
    have hlneg : lam < 0 := by rw [hl]; linarith
    have hlne : lam ≠ 0 := ne_of_lt hlneg
    have hq : lam ^ 2 - A.trace * lam + 1 = 0 := by
      rw [hl]
      have hkey : ((A.trace - s) / 2) ^ 2 - A.trace * ((A.trace - s) / 2) + 1
          = (s ^ 2 - (A.trace ^ 2 - 4)) / 4 := by ring
      rw [hkey, hs2]; ring
    have hlsum : lam + lam⁻¹ = A.trace := by
      have h1 : lam * (lam + lam⁻¹ - A.trace) = 0 := by
        have hkey : lam * (lam + lam⁻¹ - A.trace) = lam ^ 2 - A.trace * lam + 1 := by
          field_simp
          ring
        rw [hkey, hq]
      have h2 : lam + lam⁻¹ - A.trace = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hlne
        · exact h
      linarith
    have hlabs : |lam| = Work.TMC7Core.rhoSL A.trace := by
      have hρ : Work.TMC7Core.rhoSL A.trace = -(A.trace - s) / 2 := by
        rw [Work.TMC7Core.rhoSL, if_pos hτ, abs_of_neg hneg, ← hs]
        ring_nf
      rw [hρ, abs_of_neg hlneg, hl]
      ring_nf
    exact trace_abs_pow_eq_of_lam A hdet lam hlne hlsum hlabs m

/-! ## 2. The logarithm endgame -/

/-- If `(ρ^m/2) G ≤ F` with all quantities positive then
`-log 2 ≤ log F - log G - m log ρ`. -/
lemma defect_lower_log_arith (F G ρ : ℝ) (m : ℕ) (hF : 0 < F) (hG : 0 < G) (hρ : 0 < ρ)
    (hFG : (ρ ^ m / 2) * G ≤ F) :
    -Real.log 2 ≤ Real.log F - Real.log G - (m : ℝ) * Real.log ρ := by
  have hle := Real.log_le_log (mul_pos (by positivity) hG) hFG
  rw [Real.log_mul (by positivity) (ne_of_gt hG),
      Real.log_div (x := ρ ^ m) (y := 2) (by positivity) (by norm_num),
      Real.log_pow] at hle
  linarith

/-! ## 3. The theorem -/

theorem defect_lower_hyperbolic (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (m : ℕ) (hm : 1 ≤ m)
    (hτ : 2 ≤ |A.trace|) :
    -Real.log 2 ≤ Real.log (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ (2 * m)))
      - Real.log (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ m))
      - (m : ℝ) * Real.log (Work.TMC7Core.rhoSL A.trace) := by
  set ρ := Work.TMC7Core.rhoSL A.trace with hρ
  set R : ℝ := ρ ^ m with hR
  have hρ1 : 1 ≤ ρ := by rw [hρ]; exact Work.TMC7Core.rhoSL_one_le _
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ1
  have hR1 : 1 ≤ R := by rw [hR]; exact one_le_pow₀ hρ1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hdetm : (A ^ m).det = 1 := by rw [Matrix.det_pow, hdet, one_pow]
  -- the modulus of the trace of `A^m` is `ρ^m + ρ^{-m}`
  have htr : |(A ^ m).trace| = R + R⁻¹ := by
    rw [hR, hρ]
    exact trace_abs_pow_eq_rhoSL_aux A hdet hτ m
  have htsq : (A ^ m).trace ^ 2 = R ^ 2 + 2 + (R⁻¹) ^ 2 := by
    rw [← sq_abs, htr, add_sq]
    have hRne : R ≠ 0 := ne_of_gt hRpos
    have hmm : 2 * R * R⁻¹ = 2 := by
      rw [mul_assoc, mul_inv_cancel₀ hRne, mul_one]
    rw [hmm]
  have hq_ge : R ^ 2 + 2 + (R⁻¹) ^ 2 ≤ (A ^ m).trace ^ 2 := by rw [htsq]
  have hX_ge : (A ^ m).trace ^ 2 - 2 ≤ frobR (A ^ m) ^ 2 := by
    linarith [trace_sq_sub_four_le_frobR_sq (A ^ m) hdetm]
  have harith := defect_arith R ((A ^ m).trace ^ 2) (frobR (A ^ m) ^ 2) hR1 hq_ge hX_ge
  have hA2 : A ^ (2 * m) = A ^ m * A ^ m := by
    rw [show 2 * m = m * 2 from by ring, pow_mul, pow_two]
  have hY : frobR (A ^ (2 * m)) ^ 2 = 2 + (A ^ m).trace ^ 2 * (frobR (A ^ m) ^ 2 - 2) := by
    rw [hA2]
    exact frobR_mul_self (A ^ m) hdetm
  have hsq : ((R / 2) * frobR (A ^ m)) ^ 2 ≤ frobR (A ^ (2 * m)) ^ 2 := by
    have hpow : ((R / 2) * frobR (A ^ m)) ^ 2 = R ^ 2 / 4 * frobR (A ^ m) ^ 2 := by ring
    rw [hpow, hY]
    exact harith
  have hFG : (R / 2) * frobR (A ^ m) ≤ frobR (A ^ (2 * m)) := by
    have h1 : 0 ≤ (R / 2) * frobR (A ^ m) := by
      have := frobR_nonneg (A ^ m); positivity
    have h2 : 0 ≤ frobR (A ^ (2 * m)) := frobR_nonneg _
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg h1, abs_of_nonneg h2] at h
  have hm_map : (A.map Complex.ofRealHom) ^ m = (A ^ m).map Complex.ofRealHom :=
    (Matrix.map_pow A Complex.ofRealHom m).symm
  have h2m_map : (A.map Complex.ofRealHom) ^ (2 * m)
      = (A ^ (2 * m)).map Complex.ofRealHom :=
    (Matrix.map_pow A Complex.ofRealHom (2 * m)).symm
  have hFG' : (ρ ^ m / 2) * Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ m)
      ≤ Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ (2 * m)) := by
    rw [hm_map, h2m_map, frob_map_eq_frobR, frob_map_eq_frobR]
    rw [hR] at hFG
    exact hFG
  have hRR : R * R⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hRpos)
  have hq4 : 4 ≤ (A ^ m).trace ^ 2 := by
    rw [htsq]
    nlinarith [sq_nonneg (R - R⁻¹), hRR]
  have hG1 : 1 ≤ frobR (A ^ m) := by
    have hX' : 1 ≤ frobR (A ^ m) ^ 2 := by linarith [hX_ge, hq4]
    nlinarith [frobR_nonneg (A ^ m)]
  have hGpos : 0 < Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ m) := by
    rw [hm_map, frob_map_eq_frobR]
    exact lt_of_lt_of_le zero_lt_one hG1
  have hFpos : 0 < Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ (2 * m)) := by
    have hρpow : 0 < ρ ^ m := pow_pos hρpos m
    have hpos : 0 < (ρ ^ m / 2) * Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ m) :=
      mul_pos (by linarith) hGpos
    linarith [hFG']
  have hmain := defect_lower_log_arith (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ (2 * m)))
    (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ m)) ρ m hFpos hGpos hρpos hFG'
  rw [hρ] at hmain
  exact hmain

end Work.TMComp.LocCantor
