import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.elim_Xbw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `log (m!) ≤ m log m` for every natural number `m` (from `m! ≤ m^m`). -/
private lemma log_fact_le_mul_log (m : ℕ) :
    Real.log (((m.factorial : ℕ) : ℝ)) ≤ (m : ℝ) * Real.log (m : ℝ) := by
  have h1 : ((m.factorial : ℕ) : ℝ) ≤ (m : ℝ) ^ m := by
    exact_mod_cast Nat.factorial_le_pow m
  have hpos : (0 : ℝ) < ((m.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  calc Real.log ((m.factorial : ℕ) : ℝ) ≤ Real.log ((m : ℝ) ^ m) :=
        Real.log_le_log hpos h1
    _ = (m : ℝ) * Real.log (m : ℝ) := Real.log_pow m m

/-- **BW §11/§13 degree bookkeeping.**  For the intermediate field `F = ℚ(α'₁,…,α'_r) ≤ K`,
`log [F : ℚ]! ≤ [K : ℚ] · (h + 1)` where `h = ⌊h'(L) + v log 2⌋₊`.

Indeed `[F : ℚ] ≤ [K : ℚ]` (`Module.finrank_mul_finrank`), so
`log [F:ℚ]! ≤ [F:ℚ] log [F:ℚ] ≤ [K:ℚ] log [K:ℚ]`, and `log [K:ℚ] ≤ h + 1` because
`log d ≤ Xbw n d` (`elim_Xbw`), `Xbw n d ≤ h'(L)` (standing assumptions) and
`h'(L) ≤ h'(L) + v log 2 < ⌊h'(L) + v log 2⌋₊ + 1` (`Nat.lt_floor_add_one`). -/
theorem log_factorial_le_dK_mul {K : Type*} [Field K] [NumberField K] {n r : ℕ}
    (φ : K →+* ℂ) (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ)
    (α' : Fin r → K)
    (hst : Standing φ α b k c) (v : ℕ) :
    Real.log ((Module.finrank ℚ ↥(auxField α')).factorial : ℝ)
      ≤ (Module.finrank ℚ K : ℝ) * ((ph (hL b (Module.finrank ℚ K)) v : ℝ) + 1) := by
  have hn2 : 2 ≤ n := hst.1
  have hX0 : Xbw n (Module.finrank ℚ K) ≤ hL b (Module.finrank ℚ K) := hst.2.2.2.2.2.2.1
  set dK : ℕ := Module.finrank ℚ K with hdK
  set dF : ℕ := Module.finrank ℚ ↥(auxField α') with hdF
  have hdK1 : 1 ≤ dK := by rw [hdK]; exact Module.finrank_pos (R := ℚ) (M := K)
  have hdF1 : 1 ≤ dF := by rw [hdF]; exact Module.finrank_pos
  -- `auxField α'` is an intermediate field of `K`, hence `[F : ℚ] ≤ [K : ℚ]`.
  have hdFle : dF ≤ dK := by
    have h := Module.finrank_mul_finrank ℚ ↥(auxField α') K
    have h1 : 0 < Module.finrank ↥(auxField α') K := Module.finrank_pos
    have h2 : Module.finrank ℚ ↥(auxField α') ≤
        Module.finrank ℚ ↥(auxField α') * Module.finrank ↥(auxField α') K :=
      Nat.le_mul_of_pos_right _ h1
    rw [hdF, hdK]
    exact le_trans h2 h.le
  -- `log [K:ℚ] ≤ h + 1`
  have hlogdK : Real.log (dK : ℝ) ≤ (ph (hL b dK) v : ℝ) + 1 := by
    have hX : Xbw n dK ≤ hL b dK := by simpa only [hdK] using hX0
    have hlog : Real.log (dK : ℝ) ≤ Xbw n dK := by
      have h := elim_Xbw hn2 hdK1
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        have : (1 : ℕ) ≤ n := by omega
        exact_mod_cast this
      have hmul : (0 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) :=
        mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hn1)
      linarith
    have hfloor : hL b dK + (v : ℝ) * Real.log 2 < (ph (hL b dK) v : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hv : (0 : ℝ) ≤ (v : ℝ) * Real.log 2 :=
      mul_nonneg (Nat.cast_nonneg v) (Real.log_nonneg (by norm_num))
    linarith
  have hdFleR : (dF : ℝ) ≤ (dK : ℝ) := by exact_mod_cast hdFle
  have hlogmono : Real.log (dF : ℝ) ≤ Real.log (dK : ℝ) :=
    Real.log_le_log (by exact_mod_cast hdF1) hdFleR
  have hlogdKnn : (0 : ℝ) ≤ Real.log (dK : ℝ) := Real.log_nonneg (by exact_mod_cast hdK1)
  calc Real.log ((dF.factorial : ℕ) : ℝ)
      ≤ (dF : ℝ) * Real.log (dF : ℝ) := log_fact_le_mul_log dF
    _ ≤ (dK : ℝ) * Real.log (dK : ℝ) := by
        have h1 : (dF : ℝ) * Real.log (dF : ℝ) ≤ (dF : ℝ) * Real.log (dK : ℝ) :=
          mul_le_mul_of_nonneg_left hlogmono (Nat.cast_nonneg dF)
        have h2 : (dF : ℝ) * Real.log (dK : ℝ) ≤ (dK : ℝ) * Real.log (dK : ℝ) :=
          mul_le_mul_of_nonneg_right hdFleR hlogdKnn
        linarith
    _ ≤ (dK : ℝ) * ((ph (hL b dK) v : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlogdK (Nat.cast_nonneg dK)

end Work.BW
