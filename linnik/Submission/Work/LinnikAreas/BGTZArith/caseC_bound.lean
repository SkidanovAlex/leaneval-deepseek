import Mathlib

namespace Work.LinnikAreas.BGTZArith

/-- Case (c) of the BGTZ repulsion assembly: a zero with `Re ρ < 1/2 + 1/100`, so
`L = (1 - Re ρ)log q ≥ (49/100)log q`, while the Landau--Siegel normalisation gives
`λ₁ > 1/(q^{1/100} log q)`; the exponential factor `e^{LU}` (with `U ≥ 11/5`) then dwarfs
`1/λ₁`. -/
lemma caseC_bound {q : ℕ} {cZ Lq U P L : ℝ} (hq : 1 < (q : ℝ))
    (hLq : Lq = Real.log (q : ℝ)) (hLqbig : 1000 ≤ Lq) (hU : 11 / 5 ≤ U)
    (hP : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Lq) < P) (hL : (49 / 100) * Lq ≤ L) :
    1 ≤ P * max (1000 / cZ) 1000 * U * Real.exp (L * U) := by
  have hQpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hLqpos : 0 < Lq := by linarith
  have hpowpos : 0 < (q : ℝ) ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hQpos _
  have hXpos : 0 < (q : ℝ) ^ (1 / 100 : ℝ) * Lq := mul_pos hpowpos hLqpos
  have hPX : 1 < P * ((q : ℝ) ^ (1 / 100 : ℝ) * Lq) := (div_lt_iff₀ hXpos).mp hP
  have hPpos : 0 < P := by nlinarith [hPX, hXpos]
  -- `q^{1/100} = e^{log q / 100} = e^{Lq/100}`
  have hpow_eq : (q : ℝ) ^ (1 / 100 : ℝ) = Real.exp (Lq / 100) := by
    rw [Real.rpow_def_of_pos hQpos, ← hLq]
    congr 1
    ring
  have hM : (1000 : ℝ) ≤ max (1000 / cZ) 1000 := le_max_right _ _
  have hLnn : 0 ≤ L := by nlinarith [hL, hLqbig]
  have hMU : (2200 : ℝ) ≤ max (1000 / cZ) 1000 * U := by
    have h := mul_le_mul hM hU (by norm_num) (by linarith)
    norm_num at h
    linarith
  -- `L * U ≥ (49/100) log q · (11/5) = (539/500) Lq`
  have hLU : (49 / 100) * Lq * (11 / 5) ≤ L * U := mul_le_mul hL hU (by norm_num) hLnn
  have hLU2 : Lq ≤ L * U - Lq / 100 := by nlinarith [hLU, hLqbig]
  have hE : Lq + 1 ≤ Real.exp (L * U - Lq / 100) := by
    have h1 : Real.exp Lq ≤ Real.exp (L * U - Lq / 100) := Real.exp_le_exp.mpr hLU2
    have h2 : Lq + 1 ≤ Real.exp Lq := Real.add_one_le_exp Lq
    linarith
  have hpowp : 0 < Real.exp (Lq / 100) := Real.exp_pos _
  have hexp_split : Real.exp (L * U) = Real.exp (L * U - Lq / 100) * Real.exp (Lq / 100) := by
    rw [← Real.exp_add]
    congr 1
    ring
  -- The key geometric bound: `q^{1/100} · Lq ≤ M · U · e^{LU}`.
  have hbound : (q : ℝ) ^ (1 / 100 : ℝ) * Lq ≤ max (1000 / cZ) 1000 * U * Real.exp (L * U) := by
    have hstep1 : (2200 : ℝ) * Real.exp (L * U) ≤ max (1000 / cZ) 1000 * U * Real.exp (L * U) :=
      mul_le_mul_of_nonneg_right hMU (Real.exp_pos _).le
    have hstep2 : (q : ℝ) ^ (1 / 100 : ℝ) * Lq ≤ 2200 * Real.exp (L * U) := by
      rw [hpow_eq, hexp_split]
      have key : Lq ≤ 2200 * Real.exp (L * U - Lq / 100) := by
        nlinarith [hE, Real.exp_pos (L * U - Lq / 100)]
      calc Real.exp (Lq / 100) * Lq
          ≤ Real.exp (Lq / 100) * (2200 * Real.exp (L * U - Lq / 100)) :=
            mul_le_mul_of_nonneg_left key hpowp.le
        _ = 2200 * (Real.exp (L * U - Lq / 100) * Real.exp (Lq / 100)) := by ring
    linarith [hstep1, hstep2]
  have h1 : P * ((q : ℝ) ^ (1 / 100 : ℝ) * Lq) ≤
      P * (max (1000 / cZ) 1000 * U * Real.exp (L * U)) :=
    mul_le_mul_of_nonneg_left hbound hPpos.le
  have h2 : 1 < P * (max (1000 / cZ) 1000 * U * Real.exp (L * U)) := lt_of_lt_of_le hPX h1
  have heq : P * (max (1000 / cZ) 1000 * U * Real.exp (L * U)) =
      P * max (1000 / cZ) 1000 * U * Real.exp (L * U) := by ring
  rw [heq] at h2
  exact le_of_lt h2

end Work.LinnikAreas.BGTZArith
