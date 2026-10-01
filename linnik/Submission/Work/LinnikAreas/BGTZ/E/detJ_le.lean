import Mathlib
import Submission.Work.LinnikAreas.BGTZ.DetectorEDefs
import Submission.Work.LinnikAreas.BGTZ.DetectorDefs
import Submission.Work.LinnikAreas.BGTZ.DetContourDefs
import Submission.Work.LinnikAreas.LFunction_half_line_hypA_bound
import Submission.Work.LinnikAreas.GSum.ImprimitiveFactor
import Submission.Work.LinnikAreas.BGTZ.ZetaConvexityHalfAlt
import Submission.Work.LinnikAreas.BGTZ.ZetaHalfSmallT
import Submission.Work.LinnikAreas.BGTZ.E.sieveG_half_le

/-!
# The bound for the detector contour integral `detJ`

`detJ χ₁ χ R θw N ρ` is the integral along the line `Re s = 1/2 - Re ρ` of
`L(χ,ρ+s)·L(χχ₁,ρ+s)·G(ρ+s,χ)·N^s/(s(s+1))`, the piece of the shifted Mellin inversion of the
BGTZ detector sum that is not the residue at `s = 1 - ρ` (see `DetectorDefs`, `DetContourDefs`).

The stated bound

`‖detJ‖ ≤ KJ·A²·q^{2θ₀}·exp(2(log q)^{3/4})·(1+|Re ρ|)^{2θ₀}·R(1+log R)^9·N^{1/2-Re ρ}`

is the `J`-estimate of BGTZ Proposition 5.1 with Graham's *trivial* critical-line bound for the
sieve function in place of their Lemma 4.3.  The proof is the plain triangle inequality on the
contour:

* on the line, `ρ + s = 1/2 + i(Im ρ + t)`, so the critical-line bound for `F(s,χ)`
  (`detJA_Fpair_half_le`, proved here from Hypothesis A plus the convexity bound for `ζ` when one
  of the two characters is principal) gives
  `‖L(χ,ρ+s)L(χχ₁,ρ+s)‖ ≤ CF·A²q^{2θ₀}E²(1+|Im ρ|)^{2θ₀}(1+|t|)^{2θ₀}`;
* `‖G(1/2+i(Im ρ+t),χ)‖ ≤ R(1+log R)^9` (`sieveG_half_le`);
* `‖N^s‖ = N^{1/2-Re ρ}`;
* with `3/4 ≤ Re ρ < 1` the kernel is bounded by `(1+|t|)^{2θ₀}/(1/16+t²) ≤ 32(1+|t|)^{-37/25}`
  (as `2θ₀ = 13/25`), which is integrable with finite integral;

and the constant `KJ = (1/2π)·CF·∫ 32(1+|t|)^{-37/25}` is finite and positive.  Nothing here uses
the location of the zeros, the sifting weights beyond `IsSieveWeight`, or `q` beyond `q ≥ 1`.
-/

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ.E

open DirichletCharacter

/-- Absorbing the logarithmic factor of the `ζ`-convexity bound into the extra `1/100`
of the exponent: for every `t`, `log (2+|t|) + 2 ≤ 103 · (1+|t|)^{1/100}`. -/
private lemma detJA_log_two_add_le_rpow (t : ℝ) :
    Real.log (2 + |t|) + 2 ≤ 103 * (1 + |t|) ^ ((1 : ℝ) / 100) := by
  have hu1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hu0 : (0 : ℝ) < 1 + |t| := by linarith
  -- `log (1+|t|) ≤ 100 (1+|t|)^{1/100}`
  have hlog : Real.log (1 + |t|) ≤ 100 * (1 + |t|) ^ ((1 : ℝ) / 100) := by
    have h := Real.log_le_rpow_div (x := 1 + |t|) (ε := (1 : ℝ) / 100) hu0.le (by norm_num)
    have he : (1 + |t|) ^ ((1 : ℝ) / 100) / ((1 : ℝ) / 100)
        = 100 * (1 + |t|) ^ ((1 : ℝ) / 100) := by ring
    rw [he] at h; exact h
  -- `log (2+|t|) ≤ log 2 + log (1+|t|) ≤ 1 + log (1+|t|)`
  have hlog2 : Real.log (2 + |t|) ≤ 1 + Real.log (1 + |t|) := by
    have h2 : (2 + |t|) ≤ 2 * (1 + |t|) := by linarith [abs_nonneg t]
    have h3 : Real.log (2 + |t|) ≤ Real.log (2 * (1 + |t|)) :=
      Real.log_le_log (by linarith [abs_nonneg t]) h2
    have h4 : Real.log (2 * (1 + |t|)) = Real.log 2 + Real.log (1 + |t|) :=
      Real.log_mul (by norm_num) (ne_of_gt hu0)
    have h5 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      exact le_of_lt Real.exp_one_gt_two
    linarith [h3, h4]
  have hu100 : (1 : ℝ) ≤ (1 + |t|) ^ ((1 : ℝ) / 100) := Real.one_le_rpow hu1 (by norm_num)
  linarith [hlog, hlog2, hu100]

/-- The convexity bound for `ζ` on the critical line, in the exponent `thA`. -/
private lemma detJA_zeta_half_le : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ C * (1 + |t|) ^ thA := by
  obtain ⟨Cz, hCzpos, hCz⟩ := ZetaConvexityHalfAlt
  obtain ⟨Cs, hCspos, hCs⟩ := ZetaHalfSmallT
  have hthA : thA = 1 / 4 + 1 / 100 := rfl
  refine ⟨103 * Cz + Cs + 1, by positivity, ?_⟩
  intro t
  rcases lt_or_ge (1:ℝ) |t| with ht | ht
  · have h := hCz (1 / 2) t (by norm_num) (by norm_num) ht.le
    have hlog := detJA_log_two_add_le_rpow t
    have hsplit : (1 + |t|) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 100)
        = (1 + |t|) ^ thA := by
      rw [← Real.rpow_add (by linarith [abs_nonneg t]), hthA]
    calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Cz * (1 + |t|) ^ ((1 : ℝ) / 4) * (Real.log (2 + |t|) + 2) := h
      _ ≤ Cz * (1 + |t|) ^ ((1 : ℝ) / 4) * (103 * (1 + |t|) ^ ((1 : ℝ) / 100)) := by
          have hCz4 : (0 : ℝ) ≤ Cz * (1 + |t|) ^ ((1 : ℝ) / 4) := by positivity
          exact mul_le_mul_of_nonneg_left hlog hCz4
      _ = 103 * Cz * ((1 + |t|) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 100)) := by ring
      _ = 103 * Cz * (1 + |t|) ^ thA := by rw [hsplit]
      _ ≤ (103 * Cz + Cs + 1) * (1 + |t|) ^ thA := by
          have h1 : (1 : ℝ) ≤ (1 + |t|) ^ thA :=
            Real.one_le_rpow (by linarith [abs_nonneg t]) (by rw [hthA]; norm_num)
          nlinarith [h1, hCzpos, hCspos]
  · have h := hCs t ht
    have h1 : (1 : ℝ) ≤ (1 + |t|) ^ thA :=
      Real.one_le_rpow (by linarith [abs_nonneg t]) (by rw [hthA]; norm_num)
    calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cs := h
      _ ≤ (103 * Cz + Cs + 1) * (1 + |t|) ^ thA := by nlinarith [h1, hCzpos, hCspos]

/-- **The principal character on the critical line.**  `L(s,1) = ζ(s)·∏_{p|q}(1-p^{-s})`, and
the Euler product is `≤ exp((log q)^{3/4})` at `Re s = 1/2`. -/
private lemma detJA_LFunction_one_half_le : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ t : ℝ,
      ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 + |t|) ^ thA := by
  obtain ⟨Cz, hCzpos, hCz⟩ := detJA_zeta_half_le
  refine ⟨Cz, hCzpos, ?_⟩
  intro q _ hq t
  have hsre : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 := by simp
  have hsig : (1 / 2 : ℝ) ≤ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re := by norm_num [hsre]
  have hsig1 : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re ≤ 1 := by norm_num [hsre]
  have hp := Work.LinnikAreas.GSum.principal_case hq
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) hsig hsig1
  have hexp : (Real.log (q : ℝ)) ^ (1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re / 2)
      = (Real.log (q : ℝ)) ^ (3 / 4 : ℝ) := by rw [hsre]; norm_num
  rw [hexp] at hp
  calc ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) := hp
    _ ≤ (Cz * (1 + |t|) ^ thA) * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right (hCz t) (Real.exp_pos _).le
    _ = Cz * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 + |t|) ^ thA := by ring

/-- Arithmetic assembly: two nonnegative factors, one bounded by `C₁·E·P` and one by
`C₂·M·E·P`, multiply to at most `CF·(M'·E²·P²)`. -/
private lemma detJA_two_factor_bound {C1 Ch A qθ q2θ E P X Y CFc : ℝ}
    (hX : X ≤ C1 * E * P) (hY : Y ≤ Ch * (A * qθ) * E * P)
    (hY0 : 0 ≤ Y)
    (hC1 : 0 ≤ C1) (hCh : 0 ≤ Ch) (hA : 0 ≤ A) (hqθ : 0 ≤ qθ) (hq2θ : 0 ≤ q2θ)
    (hE : 0 ≤ E) (hP : 0 ≤ P) (hCFc : 0 ≤ CFc)
    (hCF : C1 * Ch ≤ CFc) (hAV : A * qθ ≤ A ^ 2 * q2θ) :
    X * Y ≤ CFc * (A ^ 2 * q2θ) * (E * E) * (P * P) := by
  have hB1 : 0 ≤ C1 * E * P := by positivity
  have hstep : X * Y ≤ (C1 * E * P) * (Ch * (A * qθ) * E * P) := mul_le_mul hX hY hY0 hB1
  have h2 : (C1 * E * P) * (Ch * (A * qθ) * E * P)
      = (C1 * Ch * (A * qθ)) * (E * E) * (P * P) := by ring
  have h3 : C1 * Ch * (A * qθ) ≤ CFc * (A ^ 2 * q2θ) :=
    mul_le_mul hCF hAV (mul_nonneg hA hqθ) hCFc
  have h4 : (C1 * Ch * (A * qθ)) * (E * E) * (P * P)
      ≤ (CFc * (A ^ 2 * q2θ)) * (E * E) * (P * P) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (mul_nonneg hE hE)) (mul_nonneg hP hP)
  rw [h2] at hstep
  exact hstep.trans h4

private theorem detJA_Fpair_half_le :
    ∃ CF : ℝ, 0 < CF ∧ ∀ (q : ℕ) [NeZero q], 400000 < q →
      ∀ (χ₁ χ : DirichletCharacter ℂ q), χ₁ ^ 2 = 1 → χ₁ ≠ 1 →
      ∀ {A : ℝ}, 1 ≤ A → Work.LinnikAreas.BGTZ.HypA A Work.LinnikAreas.BGTZ.thA → ∀ t : ℝ,
        ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          * DirichletCharacter.LFunction (χ * χ₁) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * (1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA) := by
  obtain ⟨C1, hC1pos, hC1⟩ := detJA_LFunction_one_half_le
  obtain ⟨Ch, hChpos, hCh⟩ := Work.LinnikAreas.LFunction_half_line_hypA_bound
  refine ⟨C1 * Ch + Ch ^ 2 + 1, by positivity, ?_⟩
  intro q _ hq χ₁ χ hsq hχ₁ A hA1 hHypA t
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs
  have hq3 : 3 ≤ q := by omega
  have hqR0 : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := by omega
    exact_mod_cast this
  have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by
    have h1q : 1 ≤ q := by omega
    exact_mod_cast h1q
  have h1t0 : (0 : ℝ) < 1 + |t| := by positivity
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hthA0 : (0 : ℝ) ≤ thA := by norm_num [thA]
  have hA2 : A ≤ A ^ 2 := by nlinarith
  have hqpow : (q : ℝ) ^ thA ≤ (q : ℝ) ^ (2 * thA) :=
    Real.rpow_le_rpow_of_exponent_le hqR1 (by linarith)
  have hAV : A * (q : ℝ) ^ thA ≤ A ^ 2 * (q : ℝ) ^ (2 * thA) :=
    mul_le_mul hA2 hqpow (Real.rpow_nonneg hqR0.le _) (by positivity)
  have hEE : Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
        * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
      = Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hPP : (1 + |t|) ^ thA * (1 + |t|) ^ thA = (1 + |t|) ^ (2 * thA) := by
    rw [← Real.rpow_add h1t0]; congr 1; ring
  have hqq : (q : ℝ) ^ thA * (q : ℝ) ^ thA = (q : ℝ) ^ (2 * thA) := by
    rw [← Real.rpow_add hqR0]; congr 1; ring
  have hCF1 : C1 * Ch ≤ C1 * Ch + Ch ^ 2 + 1 := by nlinarith [sq_nonneg Ch]
  have hCF3 : Ch ^ 2 + 1 ≤ C1 * Ch + Ch ^ 2 + 1 := by nlinarith [mul_pos hC1pos hChpos]
  have h1t1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  by_cases hχ : χ = 1
  · rw [hχ, one_mul]
    have hX : ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖
        ≤ C1 * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 + |t|) ^ thA := by
      simpa only [hs] using hC1 q hq t
    have hY : ‖DirichletCharacter.LFunction χ₁ s‖
        ≤ Ch * (A * (q : ℝ) ^ thA) * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (1 + |t|) ^ thA := by
      have h := hCh q χ₁ hχ₁ hq3 A thA hHypA t
      simpa only [hs, mul_assoc] using h
    have hb := detJA_two_factor_bound (C1 := C1) (Ch := Ch) (A := A) (qθ := (q : ℝ) ^ thA)
      (q2θ := (q : ℝ) ^ (2 * thA)) (E := Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)))
      (P := (1 + |t|) ^ thA)
      (X := ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖)
      (Y := ‖DirichletCharacter.LFunction χ₁ s‖) (CFc := C1 * Ch + Ch ^ 2 + 1)
      hX hY (norm_nonneg _) hC1pos.le hChpos.le hA0 (Real.rpow_nonneg hqR0.le _)
      (Real.rpow_nonneg hqR0.le _) (Real.exp_pos _).le (Real.rpow_nonneg h1t0.le _)
      (by positivity) hCF1 hAV
    calc ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s
          * DirichletCharacter.LFunction χ₁ s‖
        = ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖
          * ‖DirichletCharacter.LFunction χ₁ s‖ := norm_mul _ _
      _ ≤ (C1 * Ch + Ch ^ 2 + 1)
            * (A ^ 2 * (q : ℝ) ^ (2 * thA))
            * (Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
                * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)))
            * ((1 + |t|) ^ thA * (1 + |t|) ^ thA) := hb
      _ = (C1 * Ch + Ch ^ 2 + 1) * A ^ 2 * (q : ℝ) ^ (2 * thA)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * (1 + |t|) ^ (2 * thA) := by rw [hEE, hPP]; ring
  · by_cases hχχ : χ * χ₁ = 1
    · -- the other factor is principal: `χ = χ₁`
      have hsq' : χ₁ * χ₁ = 1 := by simpa [pow_two] using hsq
      have hχeq : χ = χ₁ := by
        have h : χ * (χ₁ * χ₁) = χ₁ := by rw [← mul_assoc, hχχ, one_mul]
        simpa [hsq'] using h
      rw [hχχ, hχeq]
      have hY : ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖
          ≤ C1 * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 + |t|) ^ thA := by
        simpa only [hs] using hC1 q hq t
      have hX : ‖DirichletCharacter.LFunction χ₁ s‖
          ≤ Ch * (A * (q : ℝ) ^ thA) * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * (1 + |t|) ^ thA := by
        have h := hCh q χ₁ hχ₁ hq3 A thA hHypA t
        simpa only [hs, mul_assoc] using h
      have hb := detJA_two_factor_bound (C1 := C1) (Ch := Ch) (A := A) (qθ := (q : ℝ) ^ thA)
        (q2θ := (q : ℝ) ^ (2 * thA)) (E := Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)))
        (P := (1 + |t|) ^ thA)
        (X := ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖)
        (Y := ‖DirichletCharacter.LFunction χ₁ s‖)
        (CFc := C1 * Ch + Ch ^ 2 + 1)
        hY hX (norm_nonneg _) hC1pos.le hChpos.le hA0 (Real.rpow_nonneg hqR0.le _)
        (Real.rpow_nonneg hqR0.le _) (Real.exp_pos _).le (Real.rpow_nonneg h1t0.le _)
        (by positivity) hCF1 hAV
      calc ‖DirichletCharacter.LFunction χ₁ s
            * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖
          = ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖
            * ‖DirichletCharacter.LFunction χ₁ s‖ := by rw [norm_mul, mul_comm]
        _ ≤ (C1 * Ch + Ch ^ 2 + 1)
              * (A ^ 2 * (q : ℝ) ^ (2 * thA))
              * (Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
                  * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)))
              * ((1 + |t|) ^ thA * (1 + |t|) ^ thA) := hb
        _ = (C1 * Ch + Ch ^ 2 + 1) * A ^ 2 * (q : ℝ) ^ (2 * thA)
              * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
              * (1 + |t|) ^ (2 * thA) := by rw [hEE, hPP]; ring
    · -- both factors non-principal
      have hX : ‖DirichletCharacter.LFunction χ s‖
          ≤ Ch * (A * (q : ℝ) ^ thA) * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * (1 + |t|) ^ thA := by
        have h := hCh q χ hχ hq3 A thA hHypA t
        simpa only [hs, mul_assoc] using h
      have hY : ‖DirichletCharacter.LFunction (χ * χ₁) s‖
          ≤ Ch * (A * (q : ℝ) ^ thA) * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * (1 + |t|) ^ thA := by
        have h := hCh q (χ * χ₁) hχχ hq3 A thA hHypA t
        simpa only [hs, mul_assoc] using h
      set E : ℝ := Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) with hE
      set M : ℝ := A * (q : ℝ) ^ thA with hM
      set P : ℝ := (1 + |t|) ^ thA with hP
      have hE0 : 0 ≤ E := by rw [hE]; positivity
      have hP0 : 0 ≤ P := by rw [hP]; positivity
      have hM0 : 0 ≤ M := by rw [hM]; positivity
      have hMM : M * M = A ^ 2 * (q : ℝ) ^ (2 * thA) := by
        rw [hM]
        have hss : A * (q : ℝ) ^ thA * (A * (q : ℝ) ^ thA)
            = A ^ 2 * ((q : ℝ) ^ thA * (q : ℝ) ^ thA) := by ring
        rw [hss, hqq]
      have hXX : ‖DirichletCharacter.LFunction χ s‖ ≤ Ch * M * E * P := by
        rw [hM, hE, hP]; exact hX
      have hYY : ‖DirichletCharacter.LFunction (χ * χ₁) s‖ ≤ Ch * M * E * P := by
        rw [hM, hE, hP]; exact hY
      calc ‖DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction (χ * χ₁) s‖
          = ‖DirichletCharacter.LFunction χ s‖
            * ‖DirichletCharacter.LFunction (χ * χ₁) s‖ := norm_mul _ _
        _ ≤ (Ch * M * E * P) * (Ch * M * E * P) :=
            mul_le_mul hXX hYY (norm_nonneg _) (by positivity)
        _ = Ch ^ 2 * (M * M) * (E * E) * (P * P) := by ring
        _ = Ch ^ 2 * (A ^ 2 * (q : ℝ) ^ (2 * thA))
              * (Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
                  * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)))
              * ((1 + |t|) ^ thA * (1 + |t|) ^ thA) := by rw [hMM, hE, hP]
        _ ≤ (C1 * Ch + Ch ^ 2 + 1) * (A ^ 2 * (q : ℝ) ^ (2 * thA))
              * (Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
                  * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)))
              * ((1 + |t|) ^ thA * (1 + |t|) ^ thA) := by
            have hC2 : Ch ^ 2 ≤ C1 * Ch + Ch ^ 2 + 1 := by nlinarith [mul_pos hC1pos hChpos]
            have hA2' : (0 : ℝ) ≤ A ^ 2 * (q : ℝ) ^ (2 * thA) := by positivity
            have hE2' : (0 : ℝ) ≤ Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
                * Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) := by positivity
            have hP2' : (0 : ℝ) ≤ (1 + |t|) ^ thA * (1 + |t|) ^ thA := by positivity
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hA2') hE2') hP2'
        _ = (C1 * Ch + Ch ^ 2 + 1) * A ^ 2 * (q : ℝ) ^ (2 * thA)
              * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
              * (1 + |t|) ^ (2 * thA) := by rw [hEE, hPP]; ring

/-- `(1+|γ+t|)^θ ≤ (1+|γ|)^θ (1+|t|)^θ` for `θ ≥ 0`. -/
private lemma detJL_rpow_abs_add_le (γ t θ : ℝ) (hθ : 0 ≤ θ) :
    (1 + |γ + t|) ^ θ ≤ (1 + |γ|) ^ θ * (1 + |t|) ^ θ := by
  have h : 1 + |γ + t| ≤ (1 + |γ|) * (1 + |t|) := by
    have h1 : |γ + t| ≤ |γ| + |t| := abs_add_le _ _
    nlinarith [abs_nonneg γ, abs_nonneg t]
  have hpos : 0 ≤ 1 + |γ + t| := by positivity
  calc (1 + |γ + t|) ^ θ ≤ ((1 + |γ|) * (1 + |t|)) ^ θ := Real.rpow_le_rpow hpos h hθ
    _ = (1 + |γ|) ^ θ * (1 + |t|) ^ θ :=
        Real.mul_rpow (by positivity) (by positivity)

/-- The kernel majorant: `(1+|t|)^(13/25)/(1/16+t²) ≤ 32 (1+|t|)^(-(37/25))`. -/
private lemma detJL_kernel_div_le (t : ℝ) :
    (1 + |t|) ^ ((13:ℝ)/25) / (1/16 + t^2) ≤ 32 * (1 + |t|) ^ (-(37/25 : ℝ)) := by
  have hpos : 0 < 1 + |t| := by positivity
  have hden : 0 < 1/16 + t^2 := by positivity
  have hkey : (1 + |t|) ^ (2:ℝ) ≤ 32 * (1/16 + t^2) := by
    have h2 : (1 + |t|) ^ (2:ℝ) = (1 + |t|)^2 := by
      rw [← Real.rpow_natCast]; norm_num
    rw [h2]
    nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 1)]
  have hsplit : (1 + |t|) ^ ((13:ℝ)/25)
      = (1 + |t|) ^ (2:ℝ) * (1 + |t|) ^ (-(37/25 : ℝ)) := by
    rw [← Real.rpow_add hpos]; norm_num
  have hnn : 0 ≤ (1 + |t|) ^ (-(37/25 : ℝ)) := Real.rpow_nonneg (by positivity) _
  rw [hsplit, div_le_iff₀ hden]
  calc (1 + |t|) ^ (2:ℝ) * (1 + |t|) ^ (-(37/25 : ℝ))
      ≤ (32 * (1/16 + t^2)) * (1 + |t|) ^ (-(37/25 : ℝ)) :=
        mul_le_mul_of_nonneg_right hkey hnn
    _ = 32 * (1 + |t|) ^ (-(37/25 : ℝ)) * (1/16 + t^2) := by ring

/-- The pointwise bound of the contour integrand. -/
private lemma detJL_norm_detInt_bound
    {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q)
    (CF A : ℝ) (hA : 1 ≤ A) (hCF : 0 ≤ CF)
    {R : ℕ} {θw : ℕ → ℝ}
    (hF : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          * DirichletCharacter.LFunction (χ * χ₁) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * (1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA))
    (hG : ∀ τ : ℝ, ‖Work.LinnikAreas.BGTZ.sieveG χ₁ R θw (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) χ‖
      ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9)
    {ρ : ℂ} (hρlo : 3 / 4 ≤ ρ.re) (hρhi : ρ.re < 1) {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ‖Work.LinnikAreas.BGTZ.detInt χ₁ χ R θw N ρ (Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I)‖
      ≤ (CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) * (N : ℝ) ^ (1 / 2 - ρ.re))
        * (32 * (1 + |t|) ^ (-(37/25 : ℝ))) := by
  have hθ2 : 2 * Work.LinnikAreas.BGTZ.thA = (13:ℝ)/25 := by
    rw [Work.LinnikAreas.BGTZ.thA]; norm_num
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hρs : ρ + (Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I)
      = ((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I := by
    rw [Work.LinnikAreas.BGTZ.detLine]
    apply Complex.ext <;> simp <;> ring
  have hsre : (Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I).re = 1/2 - ρ.re := by
    rw [Work.LinnikAreas.BGTZ.detLine]; simp
  have hNb : ‖(N : ℂ) ^ (Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I)‖
      = (N : ℝ) ^ (1 / 2 - ρ.re) := by
    rw [show (N:ℂ) = ((N:ℝ):ℂ) by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos, hsre]
  have hDb : (1:ℝ)/16 + t^2 ≤ ‖(Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I)
      * (Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I + 1)‖ := by
    rw [Work.LinnikAreas.BGTZ.detLine]
    have h1 : ‖(((1/2 - ρ.re : ℝ)):ℂ) + (t:ℂ)*I‖ = Real.sqrt ((1/2-ρ.re)^2 + t^2) :=
      Complex.norm_add_mul_I _ _
    have h2 : ‖(((1/2 - ρ.re : ℝ)):ℂ) + (t:ℂ)*I + 1‖ = Real.sqrt ((3/2-ρ.re)^2 + t^2) := by
      rw [show ((((1/2 - ρ.re : ℝ)):ℂ) + (t:ℂ)*I) + 1 = (((3/2-ρ.re : ℝ)):ℂ) + (t:ℂ)*I by
        apply Complex.ext <;> simp <;> ring]
      rw [Complex.norm_add_mul_I]
    rw [norm_mul, h1, h2]
    have ha : Real.sqrt ((1/2-ρ.re)^2 + t^2) = Real.sqrt ((ρ.re-1/2)^2 + t^2) := by ring_nf
    rw [ha]
    have hb : Real.sqrt ((ρ.re-1/2)^2 + t^2) ≤ Real.sqrt ((3/2-ρ.re)^2 + t^2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg (ρ.re-1/2), sq_nonneg (3/2-ρ.re), abs_nonneg t]
    calc 1/16 + t^2 ≤ (ρ.re-1/2)^2 + t^2 := by nlinarith [hρlo]
      _ = Real.sqrt ((ρ.re-1/2)^2 + t^2) * Real.sqrt ((ρ.re-1/2)^2 + t^2) := by
          rw [Real.mul_self_sqrt (by nlinarith [sq_nonneg (ρ.re-1/2), sq_nonneg t])]
      _ ≤ Real.sqrt ((3/2-ρ.re)^2 + t^2) * Real.sqrt ((ρ.re-1/2)^2 + t^2) :=
          mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)
      _ = Real.sqrt ((ρ.re-1/2)^2 + t^2) * Real.sqrt ((3/2-ρ.re)^2 + t^2) := by ring
  have hFF : ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)
        * DirichletCharacter.LFunction (χ * χ₁) (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)‖
      ≤ CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * ((1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA) * (1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA)) := by
    calc _ ≤ CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
              * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
              * (1 + |ρ.im + t|) ^ (2 * Work.LinnikAreas.BGTZ.thA) := hF (ρ.im + t)
      _ ≤ CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
              * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
              * ((1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA) * (1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA)) :=
            mul_le_mul_of_nonneg_left
              (detJL_rpow_abs_add_le ρ.im t (2 * Work.LinnikAreas.BGTZ.thA) (by positivity))
              (by positivity)
  have hGG : ‖Work.LinnikAreas.BGTZ.sieveG χ₁ R θw
        (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I) χ‖
      ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9 := hG (ρ.im + t)
  have hP1nn : (0:ℝ) ≤ CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
      * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
      * ((1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA) * (1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA)) := by
    have h1 : (0:ℝ) ≤ A^2 := sq_nonneg A
    have h2 : (0:ℝ) ≤ (q:ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA) := Real.rpow_nonneg hqpos.le _
    have h3 : (0:ℝ) ≤ (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA) := Real.rpow_nonneg (by positivity) _
    have h4 : (0:ℝ) ≤ (1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA) := Real.rpow_nonneg (by positivity) _
    positivity
  have hP2nn : (0:ℝ) ≤ (R:ℝ) * (1 + Real.log (R:ℝ))^9 := by positivity
  have hNnn : (0:ℝ) ≤ (N:ℝ) ^ (1/2 - ρ.re) := Real.rpow_nonneg hNpos.le _
  set NUM : ℝ := (CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
      * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
      * ((1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA) * (1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA)))
      * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) * (N : ℝ) ^ (1/2 - ρ.re) with hNUMdef
  have hNUMnn : 0 ≤ NUM := by
    rw [hNUMdef]; exact mul_nonneg (mul_nonneg hP1nn hP2nn) hNnn
  have hnumLe : ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)
        * DirichletCharacter.LFunction (χ * χ₁) (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)
        * Work.LinnikAreas.BGTZ.sieveG χ₁ R θw (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I) χ
        * (N : ℂ) ^ (Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I)‖ ≤ NUM := by
    rw [hNUMdef]
    have hsp : ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)
        * DirichletCharacter.LFunction (χ * χ₁) (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)
        * Work.LinnikAreas.BGTZ.sieveG χ₁ R θw (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I) χ
        * (N : ℂ) ^ (Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I)‖
        = ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)
          * DirichletCharacter.LFunction (χ * χ₁) (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)‖
          * ‖Work.LinnikAreas.BGTZ.sieveG χ₁ R θw (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I) χ‖
          * (N : ℝ) ^ (1/2 - ρ.re) := by rw [norm_mul, norm_mul, hNb]
    rw [hsp]
    have h12 : ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)
          * DirichletCharacter.LFunction (χ * χ₁) (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)‖
          * ‖Work.LinnikAreas.BGTZ.sieveG χ₁ R θw (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I) χ‖
        ≤ (CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * ((1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA) * (1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA)))
          * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) :=
        mul_le_mul hFF hGG (norm_nonneg _) hP1nn
    exact mul_le_mul h12 (le_refl _) hNnn (mul_nonneg hP1nn hP2nn)
  have hden_pos : (0:ℝ) < 1/16 + t^2 := by positivity
  have hstep : ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)
        * DirichletCharacter.LFunction (χ * χ₁) (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)
        * Work.LinnikAreas.BGTZ.sieveG χ₁ R θw (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I) χ
        * (N : ℂ) ^ (Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I)‖
        / ‖(Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I)
            * (Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I + 1)‖
      ≤ NUM / (1/16 + t^2) := div_le_div₀ hNUMnn hnumLe hden_pos hDb
  rw [Work.LinnikAreas.BGTZ.detInt, hρs, norm_div]
  refine hstep.trans ?_
  have hNUMeq : NUM = (CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) * (N : ℝ) ^ (1/2 - ρ.re))
        * (1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA) := by
    rw [hNUMdef]; ring
  have hK1nn : (0:ℝ) ≤ CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) * (N : ℝ) ^ (1/2 - ρ.re) := by
    have h1 : (0:ℝ) ≤ A^2 := sq_nonneg A
    have h2 : (0:ℝ) ≤ (q:ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA) := Real.rpow_nonneg hqpos.le _
    have h3 : (0:ℝ) ≤ (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA) := Real.rpow_nonneg (by positivity) _
    positivity
  have hKb : (1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA) / (1/16 + t^2)
      ≤ 32 * (1 + |t|) ^ (-(37/25 : ℝ)) := by
    rw [hθ2]; exact detJL_kernel_div_le t
  rw [hNUMeq, mul_div_assoc]
  calc (CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) * (N : ℝ) ^ (1/2 - ρ.re))
        * ((1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA) / (1/16 + t^2))
      ≤ (CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
          * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) * (N : ℝ) ^ (1/2 - ρ.re))
        * (32 * (1 + |t|) ^ (-(37/25 : ℝ))) := mul_le_mul_of_nonneg_left hKb hK1nn

theorem detJ_le :
    ∃ KJ : ℝ, 0 < KJ ∧ ∀ (q : ℕ) [NeZero q], 400000 < q →
      ∀ (χ₁ χ : DirichletCharacter ℂ q), χ₁ ^ 2 = 1 → χ₁ ≠ 1 →
      ∀ {A : ℝ}, 1 ≤ A → Work.LinnikAreas.BGTZ.HypA A Work.LinnikAreas.BGTZ.thA →
      ∀ {R : ℕ} {θw : ℕ → ℝ}, Work.LinnikAreas.BGTZ.IsSieveWeight R θw →
      ∀ {ρ : ℂ}, 3 / 4 ≤ ρ.re → ρ.re < 1 → ∀ {N : ℕ}, 1 ≤ N →
        ‖Work.LinnikAreas.BGTZ.detJ χ₁ χ R θw N ρ‖
          ≤ KJ * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
            * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9)
            * (N : ℝ) ^ ((1 / 2 : ℝ) - ρ.re) := by
  obtain ⟨CF, hCFpos, hF⟩ := detJA_Fpair_half_le
  have hφint : Integrable (fun t : ℝ => 32 * (1 + |t|) ^ (-(37/25 : ℝ))) := by
    have h := (integrable_one_add_norm (E := ℝ) (μ := (volume : Measure ℝ))
      (r := (37/25 : ℝ)) (by rw [Module.finrank_self]; norm_num)).const_mul (32 : ℝ)
    simpa only [Real.norm_eq_abs] using h
  refine ⟨(1 / (2 * Real.pi)) * CF * ∫ t : ℝ, 32 * (1 + |t|) ^ (-(37/25 : ℝ)), ?hpos, ?hmain⟩
  · have hφnn' : 0 ≤ (fun t : ℝ => 32 * (1 + |t|) ^ (-(37/25 : ℝ))) := fun t => by positivity
    have hintpos : 0 < ∫ t : ℝ, 32 * (1 + |t|) ^ (-(37/25 : ℝ)) := by
      rw [MeasureTheory.integral_pos_iff_support_of_nonneg hφnn' hφint]
      have heq : Function.support (fun t : ℝ => 32 * (1 + |t|) ^ (-(37/25 : ℝ))) = Set.univ := by
        ext t
        simp only [Function.mem_support, Set.mem_univ, iff_true]
        exact ne_of_gt (by positivity : (0:ℝ) < 32 * (1 + |t|) ^ (-(37/25 : ℝ)))
      rw [heq]
      have h2 : (0 : ENNReal) < volume (Set.Icc (-1:ℝ) 1) := by
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ) < 1 - (-1))
      exact lt_of_lt_of_le h2 (measure_mono (Set.subset_univ _))
    exact mul_pos (mul_pos (by positivity) hCFpos) hintpos
  · intro q _ hq χ₁ χ hχ₁ hχ₁ne A hA hHypA R θw hθw ρ hρlo hρhi N hN
    have hF' : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          * DirichletCharacter.LFunction (χ * χ₁) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * (1 + |t|) ^ (2 * Work.LinnikAreas.BGTZ.thA) :=
      fun t => hF q hq χ₁ χ hχ₁ hχ₁ne hA hHypA t
    have hG' : ∀ τ : ℝ, ‖Work.LinnikAreas.BGTZ.sieveG χ₁ R θw
        (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) χ‖
        ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9 :=
      fun τ => sieveG_half_le χ₁ χ hχ₁ hθw τ
    have hpt : ∀ t : ℝ,
        ‖Work.LinnikAreas.BGTZ.detInt χ₁ χ R θw N ρ
            (Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I)‖
          ≤ (CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
              * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
              * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
              * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) * (N : ℝ) ^ (1 / 2 - ρ.re))
            * (32 * (1 + |t|) ^ (-(37/25 : ℝ))) :=
      fun t => detJL_norm_detInt_bound χ₁ χ CF A hA hCFpos.le hF' hG' hρlo hρhi hN t
    have hIntG : Integrable (fun t : ℝ =>
        (CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
            * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) * (N : ℝ) ^ (1 / 2 - ρ.re))
          * (32 * (1 + |t|) ^ (-(37/25 : ℝ)))) :=
      hφint.const_mul _
    have hkey := MeasureTheory.norm_integral_le_of_norm_le hIntG (Filter.Eventually.of_forall hpt)
    have hscale : ‖((1:ℂ) / ((2:ℂ) * (Real.pi:ℂ)))‖ = 1/(2*Real.pi) := by
      have heq : (1:ℂ) / ((2:ℂ) * (Real.pi:ℂ)) = ((1/(2*Real.pi) : ℝ) : ℂ) := by
        push_cast; ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [Work.LinnikAreas.BGTZ.detJ_eq_integral, norm_mul, hscale]
    calc (1 / (2 * Real.pi))
          * ‖∫ t : ℝ, Work.LinnikAreas.BGTZ.detInt χ₁ χ R θw N ρ
              (Work.LinnikAreas.BGTZ.detLine ρ + (t : ℂ) * I)‖
        ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ,
            (CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
              * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
              * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
              * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) * (N : ℝ) ^ (1 / 2 - ρ.re))
            * (32 * (1 + |t|) ^ (-(37/25 : ℝ))) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (1 / (2 * Real.pi)) * ((CF * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
              * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
              * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
              * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) * (N : ℝ) ^ (1 / 2 - ρ.re))
            * ∫ t : ℝ, 32 * (1 + |t|) ^ (-(37/25 : ℝ))) := by
          rw [MeasureTheory.integral_const_mul]
      _ = ((1 / (2 * Real.pi)) * CF * ∫ t : ℝ, 32 * (1 + |t|) ^ (-(37/25 : ℝ)))
            * A ^ 2 * (q : ℝ) ^ (2 * Work.LinnikAreas.BGTZ.thA)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
            * (1 + |ρ.im|) ^ (2 * Work.LinnikAreas.BGTZ.thA)
            * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9)
            * (N : ℝ) ^ ((1 / 2 : ℝ) - ρ.re) := by ring

