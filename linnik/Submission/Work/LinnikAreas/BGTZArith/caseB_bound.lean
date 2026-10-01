import Mathlib

namespace Work.LinnikAreas.BGTZArith

/-- Case (b) of the BGTZ repulsion assembly: a zero `ρ = β₁ + iγ` (`γ ≠ 0`) of the same real part
as the exceptional zero, pushed by the zero-free region `cZ ≤ (1-β₁)·log(q·T)` only.  With
`T = max 4|γ|` and `U ≥ 11/5 + (11/10)(log T - log 4)/log q`, the quantity `λ₁·C₀·U` already
exceeds `1`. -/
lemma caseB_bound {cZ Lq T U P q : ℝ}
    (hcZ : 0 < cZ) (hq : 1 < q) (hLq : Lq = Real.log q) (hLqbig : 1000 ≤ Lq)
    (hT : 4 ≤ T) (hU : 11 / 5 + (11 / 10) * ((Real.log T - Real.log 4) / Lq) ≤ U)
    (hzfr : cZ ≤ (P / Lq) * Real.log (q * T)) :
    1 ≤ P * max (1000 / cZ) 1000 * U := by
  -- replace `Lq` by `Real.log q` everywhere
  rw [hLq] at hLqbig hU hzfr
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hTpos : 0 < T := by linarith
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hTne : T ≠ 0 := ne_of_gt hTpos
  -- basic bounds on the two logarithms
  have hA : 1000 ≤ Real.log q := hLqbig
  have hApos : 0 < Real.log q := lt_of_lt_of_le (by norm_num) hA
  have hB : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hBpos : 0 < Real.log T := lt_of_lt_of_le (Real.log_pos (by norm_num)) hB
  have hlog4le : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hqT : Real.log (q * T) = Real.log q + Real.log T := Real.log_mul hqne hTne
  have hSpos : 0 < Real.log q + Real.log T := add_pos hApos hBpos
  have hzfr' : cZ ≤ (P / Real.log q) * (Real.log q + Real.log T) := by
    rw [hqT] at hzfr; exact hzfr
  -- positivity of `P`, forced by the zero-free region
  have hprodpos : 0 < (P / Real.log q) * (Real.log q + Real.log T) := lt_of_lt_of_le hcZ hzfr'
  have hPpos : 0 < P := by
    have hpa : 0 < P / Real.log q := by
      rcases mul_pos_iff.mp hprodpos with ⟨h, _⟩ | ⟨_, h2⟩
      · exact h
      · exact absurd hSpos (not_lt.mpr (le_of_lt h2))
    rcases div_pos_iff.mp hpa with ⟨h, _⟩ | ⟨_, h2⟩
    · exact h
    · exact absurd hApos (not_lt.mpr (le_of_lt h2))
  -- clear the denominator in the zero-free region
  have hPS : cZ * Real.log q ≤ P * (Real.log q + Real.log T) := by
    have h := mul_le_mul_of_nonneg_right hzfr' (le_of_lt hApos)
    have he : ((P / Real.log q) * (Real.log q + Real.log T)) * Real.log q
        = P * (Real.log q + Real.log T) := by field_simp
    linarith [h, he]
  -- clear the denominator in the lower bound for `U`
  have hUmul : (11 / 5) * Real.log q + (11 / 10) * (Real.log T - Real.log 4)
      ≤ U * Real.log q := by
    have h := mul_le_mul_of_nonneg_right hU (le_of_lt hApos)
    have he : (11 / 5 + (11 / 10) * ((Real.log T - Real.log 4) / Real.log q)) * Real.log q
        = (11 / 5) * Real.log q + (11 / 10) * (Real.log T - Real.log 4) := by field_simp
    linarith [h, he]
  have hUpos : 0 < U := by
    have h1 : (0 : ℝ) < (11 / 5) * Real.log q + (11 / 10) * (Real.log T - Real.log 4) := by
      have h2 : 0 ≤ (11 / 10) * (Real.log T - Real.log 4) := by
        have h3 : 0 ≤ Real.log T - Real.log 4 := by linarith
        positivity
      nlinarith [hA]
    have hUA : 0 < U * Real.log q := lt_of_lt_of_le h1 hUmul
    rcases mul_pos_iff.mp hUA with ⟨h, _⟩ | ⟨_, h2'⟩
    · exact h
    · exact absurd hApos (not_lt.mpr (le_of_lt h2'))
  -- the numerical core: `log q + log T ≤ 1000·(log q)·U`
  have hSU : Real.log q + Real.log T ≤ 1000 * (Real.log q * U) := by
    nlinarith [hUmul, hA, hB, hlog4le]
  -- multiply the zero-free region by `(1000/cZ)·U`
  have hstep : 1000 * (Real.log q * U)
      ≤ P * (1000 / cZ) * U * (Real.log q + Real.log T) := by
    have hcoef : (0 : ℝ) ≤ (1000 / cZ) * U := by positivity
    have h := mul_le_mul_of_nonneg_right hPS hcoef
    have h1 : cZ * Real.log q * ((1000 / cZ) * U) = 1000 * (Real.log q * U) := by field_simp
    have h2 : P * (Real.log q + Real.log T) * ((1000 / cZ) * U)
        = P * (1000 / cZ) * U * (Real.log q + Real.log T) := by ring
    linarith [h, h1, h2]
  have hfinal : 1 ≤ P * (1000 / cZ) * U := by
    have hmain : (1 : ℝ) * (Real.log q + Real.log T)
        ≤ (P * (1000 / cZ) * U) * (Real.log q + Real.log T) := by
      rw [one_mul]
      exact le_trans hSU hstep
    exact (mul_le_mul_iff_left₀ hSpos).mp hmain
  -- finally use `1000/cZ ≤ max (1000/cZ) 1000`
  have hmax : P * (1000 / cZ) * U ≤ P * max (1000 / cZ) 1000 * U := by
    have hle : 1000 / cZ ≤ max (1000 / cZ) 1000 := le_max_left _ _
    have h1 : P * (1000 / cZ) ≤ P * max (1000 / cZ) 1000 :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hPpos)
    exact mul_le_mul_of_nonneg_right h1 (le_of_lt hUpos)
  exact le_trans hfinal hmax

end Work.LinnikAreas.BGTZArith
