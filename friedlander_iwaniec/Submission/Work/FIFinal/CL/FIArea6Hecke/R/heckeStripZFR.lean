import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.R.heckeZFRoffAxisP
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.heckeZFRrealAxisClean
import Submission.Work.FIArea6Hecke.R.zfrRealAxisPLight

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## The uniform comparison of the two region depths

The target region is `σ ≥ 1 - c/(d^ε·log(|m|+|t|+3))`, whereas *FI* (16.20) gives non-vanishing
only for `σ > 1 - c₀/log(4d+|m|+|t|)`.  The two differ by the factor
`d^ε·log(|m|+|t|+3)/log(4d+|m|+|t|)`, and this factor is bounded *below* by `ε·log 3/4` uniformly
in `d ≥ 1`, `m : ℤ` and `t : ℝ`.  Hence, with `c = c₀·ε·log 3/4`, the target region is contained
in the (16.20) region pointwise — which is what makes the depth-free region (16.20) applicable to
the target. -/

lemma log_twelve_le_four : Real.log 12 ≤ 4 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 12)]
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num) 5
  have hval : (∑ i ∈ Finset.range 5, (4 : ℝ) ^ i / ((i.factorial : ℕ) : ℝ))
      = 1 + 4 + 8 + 64 / 6 + 256 / 24 := by
    norm_num [Finset.sum_range_succ]
  rw [hval] at h
  linarith

/-- **Uniform comparison of the region depths**: for `0 < ε ≤ 1/4`, `cB > 0`, `d ≥ 1`, `m : ℤ` and
`t : ℝ`,

  `cB·(log 3)·ε/4 / (d^ε·log(|m|+|t|+3)) ≤ cB / log(4d + |m| + |t|)`.

Equivalently: `d^ε·log(|m|+|t|+3)/log(4d+|m|+|t|) ≥ ε·log 3/4` for all data.  The proof is the
elementary estimate `d^ε ≥ 1 + ε·log d` together with the monotonicity of `u ↦ u/(K+u)`, which
reduces the statement to `ε·log 12 ≤ 1` — true for `ε ≤ 1/4` because `log 12 ≤ 4`. -/
lemma region_le_offAxis {ε cB : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hcB : 0 < cB)
    (d : ℕ) (hd : 1 ≤ d) (m : ℤ) (t : ℝ) :
    cB * Real.log 3 * ε / 4 / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |t| + 3))
      ≤ cB / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t|) := by
  have hlog12 : ε * Real.log 12 ≤ 1 := by
    have h := log_twelve_le_four
    nlinarith [hε.le, h]
  set M : ℝ := |(m : ℝ)| + |t| + 3 with hM
  have hM3 : 3 ≤ M := by
    have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg t
    simp only [hM]; linarith
  have hMpos : 0 < M := by linarith
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogM : Real.log 3 ≤ Real.log M := Real.log_le_log (by norm_num) hM3
  have hlogMpos : 0 < Real.log M := lt_of_lt_of_le hlog3pos hlogM
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by linarith
  have hdepos : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos hdpos ε
  have hlogdnn : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  have hDpos : 0 < Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t|) := by
    refine Real.log_pos ?_
    have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg t
    linarith
  have hlogD : Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t|)
      ≤ Real.log 4 + Real.log (d : ℝ) + Real.log M := by
    have hle : 4 * (d : ℝ) + |(m : ℝ)| + |t| ≤ 4 * (d : ℝ) * M := by
      have h4 : 4 * (d : ℝ) + |(m : ℝ)| + |t| = 4 * (d : ℝ) + (M - 3) := by
        simp only [hM]; ring
      rw [h4]
      nlinarith [hdR, hM3]
    calc Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t|)
        ≤ Real.log (4 * (d : ℝ) * M) := Real.log_le_log (by positivity) hle
      _ = Real.log 4 + Real.log (d : ℝ) + Real.log M := by
          rw [Real.log_mul (show (4 * (d : ℝ)) ≠ 0 by positivity) (show M ≠ 0 by linarith),
              Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) (show (d : ℝ) ≠ 0 by linarith)]
  have hP : 1 ≤ Real.log M / Real.log 3 := (one_le_div hlog3pos).mpr hlogM
  have hPm : (Real.log M / Real.log 3) * Real.log 3 = Real.log M :=
    div_mul_cancel₀ _ (ne_of_gt hlog3pos)
  have hsum : Real.log 3 + Real.log 4 = Real.log 12 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hA : 0 ≤ 1 + ε * Real.log (d : ℝ) - ε * Real.log 3 := by
    have h1 : ε * Real.log 3 ≤ ε * Real.log 12 := by
      nlinarith [hε.le, Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 12)]
    nlinarith [h1, hlog12, hε.le, hlogdnn]
  have hPA : (1 + ε * Real.log (d : ℝ) - ε * Real.log 3)
      ≤ (Real.log M / Real.log 3) * (1 + ε * Real.log (d : ℝ) - ε * Real.log 3) := by
    nlinarith [hP, hA]
  have hstep : ε * (Real.log 4 + Real.log (d : ℝ) + Real.log M)
      ≤ (1 + ε * Real.log (d : ℝ)) * (Real.log M / Real.log 3) := by
    nlinarith [hPA, hPm, hA, hsum, hlog12]
  have hexp : (1 + ε * Real.log (d : ℝ)) ≤ (d : ℝ) ^ ε := by
    rw [Real.rpow_def_of_pos hdpos]
    have heq : Real.log (d : ℝ) * ε = ε * Real.log (d : ℝ) := by ring
    rw [heq]
    have := Real.add_one_le_exp (ε * Real.log (d : ℝ))
    linarith
  have hstep2 : ε * (Real.log 4 + Real.log (d : ℝ) + Real.log M)
      ≤ (d : ℝ) ^ ε * (Real.log M / Real.log 3) :=
    le_trans hstep (mul_le_mul_of_nonneg_right hexp (by positivity))
  have hstep3 : ε * Real.log 3 * (Real.log 4 + Real.log (d : ℝ) + Real.log M)
      ≤ (d : ℝ) ^ ε * Real.log M := by
    have h1 := mul_le_mul_of_nonneg_right hstep2 hlog3pos.le
    have h2 : (ε * (Real.log 4 + Real.log (d : ℝ) + Real.log M)) * Real.log 3
        = ε * Real.log 3 * (Real.log 4 + Real.log (d : ℝ) + Real.log M) := by ring
    have h3 : ((d : ℝ) ^ ε * (Real.log M / Real.log 3)) * Real.log 3
        = (d : ℝ) ^ ε * Real.log M := by rw [mul_assoc, hPm]
    linarith [h1, h2, h3]
  have hSnn : 0 ≤ Real.log 4 + Real.log (d : ℝ) + Real.log M := by
    have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  have hcore : (ε * Real.log 3 / 4) * Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t|)
      ≤ (d : ℝ) ^ ε * Real.log M := by
    have hmono : (ε * Real.log 3 / 4) * Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t|)
        ≤ (ε * Real.log 3 / 4) * (Real.log 4 + Real.log (d : ℝ) + Real.log M) :=
      mul_le_mul_of_nonneg_left hlogD (by positivity)
    have hle2 : ε * Real.log 3 / 4 ≤ ε * Real.log 3 := by nlinarith [hε.le, hlog3pos]
    have h5 : (ε * Real.log 3 / 4) * (Real.log 4 + Real.log (d : ℝ) + Real.log M)
        ≤ (ε * Real.log 3) * (Real.log 4 + Real.log (d : ℝ) + Real.log M) :=
      mul_le_mul_of_nonneg_right hle2 hSnn
    linarith [hmono, h5, hstep3]
  rw [div_le_div_iff₀ (mul_pos hdepos hlogMpos) hDpos]
  nlinarith [hcore, hcB.le]

/-! ## The assembly -/

/-- **The target from its two classical inputs.**  Given the depth-free region (16.20) off the real
axis (`ZFRoffAxis`) and the Siegel bound (16.21) on the real axis for real `ψ` (`ZFRrealAxis ε`),
the target region `1 - c/(d^ε·log(|m|+|t|+3)) ≤ σ ≤ 2` is zero-free: on the real axis with real `ψ`
the Siegel region `σ > 1 - c_S·d^{-ε}` contains the target region (since `log(...) ≥ log 3 > 1`),
and everywhere else the comparison lemma `region_le_offAxis` contains the target region in (16.20).

The `ψ`-realness in the exceptional set is `PsiRealPrimary` (real-valued on the *primary*
elements, i.e. on the odd ideals of (16.16)), not real-valuedness on all of `Z[i]`: the Hecke
eigenvalues `λ(n) = Σ_{z primary,|z|²=n} ψ(z)` — and hence the whole `L`-function — see only the
primary values, and the exceptional zero occurs exactly when `ψ²` is trivial, i.e. `ψ` real on the
primary elements. -/
theorem heckeStripZFR_of (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hoff : ZFRoffAxis) (hreal : ZFRrealAxisP ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        ∀ s : ℂ,
          1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) ≤ s.re → s.re ≤ 2 →
          Work.FIArea6Hecke.Lval d m Lam s ≠ 0 := by
  obtain ⟨cB, hcB, hB⟩ := hoff
  obtain ⟨cS, hcS, hS⟩ := hreal
  refine ⟨min (min (cB * Real.log 3 * ε / 8) (cS * Real.log 3 / 2)) 1, ?_, ?_⟩
  · refine lt_min (lt_min ?_ ?_) one_pos
    · have h := Real.log_pos (by norm_num : (1 : ℝ) < 3); positivity
    · have h := Real.log_pos (by norm_num : (1 : ℝ) < 3); positivity
  · intro d chi m Lam hd hchi hAn hagr s hreg hs2
    have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hM3 : 3 ≤ |(m : ℝ)| + |s.im| + 3 := by
      have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im; linarith
    have hlogM : Real.log 3 ≤ Real.log (|(m : ℝ)| + |s.im| + 3) :=
      Real.log_le_log (by norm_num) hM3
    have hlogMpos : 0 < Real.log (|(m : ℝ)| + |s.im| + 3) := lt_of_lt_of_le hlog3pos hlogM
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdpos : 0 < (d : ℝ) := by linarith
    have hdepos : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos hdpos ε
    have hDpos : 0 < (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) :=
      mul_pos hdepos hlogMpos
    have hEpos : 0 < Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) := by
      refine Real.log_pos ?_
      have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im
      linarith
    by_cases hrc : s.im = 0 ∧ PsiRealPrimary chi m
    · -- the real axis with real `ψ`: the Siegel bound (16.21)
      have hcle : min (min (cB * Real.log 3 * ε / 8) (cS * Real.log 3 / 2)) 1
          ≤ cS * Real.log 3 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
      have hle1 : min (min (cB * Real.log 3 * ε / 8) (cS * Real.log 3 / 2)) 1 /
            ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
          ≤ (cS * Real.log 3 / 2) / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) :=
        div_le_div_of_nonneg_right hcle hDpos.le
      have hle2 : (cS * Real.log 3 / 2) / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
          ≤ cS / (2 * (d : ℝ) ^ ε) := by
        rw [div_le_div_iff₀ hDpos (by positivity)]
        have hprod : cS * (d : ℝ) ^ ε * Real.log 3
            ≤ cS * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) :=
          mul_le_mul_of_nonneg_left hlogM (mul_nonneg hcS.le hdepos.le)
        nlinarith [hprod]
      have hlt2 : cS / (2 * (d : ℝ) ^ ε) < cS / (d : ℝ) ^ ε := by
        rw [div_lt_div_iff₀ (by positivity) hdepos]
        nlinarith [hcS, hdepos]
      have hlt : 1 - cS / (d : ℝ) ^ ε < s.re := by linarith
      exact hS d chi m Lam hd hchi hAn hagr hrc.2 s hrc.1 hlt hs2
    · -- off the real axis: the de la Vallée Poussin region (16.20)
      have hcle : min (min (cB * Real.log 3 * ε / 8) (cS * Real.log 3 / 2)) 1
          ≤ cB * Real.log 3 * ε / 8 := le_trans (min_le_left _ _) (min_le_left _ _)
      have hcont := region_le_offAxis hε hε4 hcB d hd m s.im
      have hlt : min (min (cB * Real.log 3 * ε / 8) (cS * Real.log 3 / 2)) 1 /
            ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
          < cB / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) := by
        have h3 := div_le_div_of_nonneg_right hcle hDpos.le
        have h4 : (cB * Real.log 3 * ε / 8) /
              ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
            = (1 / 2) * ((cB * Real.log 3 * ε / 4) /
                ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))) := by ring
        have h5 : (1 / 2) * ((cB * Real.log 3 * ε / 4) /
                ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)))
            ≤ (1 / 2) * (cB / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|)) :=
          mul_le_mul_of_nonneg_left hcont (by norm_num)
        have h6 : (1 / 2) * (cB / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|))
            < cB / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) := by
          have h7 := div_pos hcB hEpos
          linarith
        linarith
      exact hB d chi m Lam hd hchi hAn hagr s (by linarith) hs2 hrc

/-- **The zero-free region (*FI* (16.20)/(16.24)) for the completed Hecke `L`-function of `ℚ(i)`**:
for `Lam` an entire completion of `L(·,ψ)` (`Lam s = heckeArch d m s · heckeLSeries χ m s` for
`re s > 1 + |m|/2`) the value `Lval d m Lam s` never vanishes in
`1 - c/(d^ε log(|m|+|s.im|+3)) ≤ re s ≤ 2`.

This is the first conjunct of `StripCore ε` (`StripCoreDefs.lean`), consumed by
`heckeStripCore → heckeStripGlue → heckeLcontInvBound_strip`.

**Why this is the deep input.**  The `d^{-ε}` depth is *stronger* on the real axis than the
effective bound `1 - β ≫ 1/(√q log²q)` that de la Vallée Poussin gives: for `ε < 1/2` one has
`d^{-ε} ≫ 1/(√d log²d)`.  So the classical `3-4-1` inequality gives only the
*exceptional-zero-allowing* region, and the `ε`-form needs the Landau-Siegel/Goldfeld input
(*FI* Lemma 16.1, (16.21)) for the possible real zero.

The proof is assembled in `heckeStripZFR_of` from the two classical statements of *FI* §16:
the depth-free region (16.20) away from the real axis (`ZFRoffAxis`) and Lemma 16.1 (Siegel) on the
real axis for real `ψ` (`ZFRrealAxisP ε`, whose hypothesis `PsiRealPrimary` matches the exceptional
set of `ZFRoffAxis`); see `ZFRStatementDefs.lean`. -/
theorem heckeStripZFR (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        ∀ s : ℂ,
          1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) ≤ s.re → s.re ≤ 2 →
          Work.FIArea6Hecke.Lval d m Lam s ≠ 0 :=
  heckeStripZFR_of ε hε hε4 heckeZFRoffAxisP
    (zfrRealAxisPLight ε hε hε4 (heckeZFRrealAxisClean ε hε hε4))

end

end Work.FIArea6Hecke.R
