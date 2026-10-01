import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_ownRepelNearWindow
import Submission.Work.LinnikAreas.ownRepelFarRange

namespace Work.LinnikAreas

open Work.LinnikContract

/-- **The Deuring–Heilbronn self-repulsion, `λ₁`-uniform form.**

There are absolute constants `c > 0` and `q₀` such that for every `q ≥ q₀`, every *real* character
`χ₀` modulo `q` whose `L`-function has a real zero `ρ₀` of minimal `λ = (1 - Re)·log q` over all
zeros of all non-principal characters (`IsMin1`) with `λ(ρ₀) ≤ 1/2`, every *other* zero `ρ ≠ ρ₀` of
`χ₀` with `|Im ρ| ≤ 1` satisfies `c·log(1/λ(ρ₀)) ≤ λ(ρ)`.

Proof.  Split on `λ(ρ₀)`:

* `λ(ρ₀) ≥ 1/1000`: `IsMin1` alone (and `λ(ρ)` monotone) gives the claim with the tiny constant
  `(1/1000)/log 1000`, because then `log(1/λ(ρ₀)) ≤ log 1000` and `λ(ρ) ≥ λ(ρ₀) ≥ 1/1000`.
* `λ(ρ₀) < 1/1000`, so `λ(ρ₀) ≤ 1/100`: the uncapped repulsion
  `ownRepelUncapped_of_nearWindow ownRepelNearWindow` (the Turán/window half `ownRepelNearWindow`
  plus the Siegel far range `ownRepelFarRange`) applies verbatim.

Taking the minimum of the two constants finishes. -/
theorem repelOwnFinal : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 2 →
    ∀ (ρ : ℂ), Work.LinnikContract.zeroMult χ₀ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₀ →
      c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q ρ := by
  -- the repulsion in the range `λ(ρ₀) ≤ 1/100`, from the Turán/window half and the Siegel far range
  obtain ⟨c₁, hc₁, q₁, hrec⟩ := ownRepelUncapped_of_nearWindow ownRepelNearWindow
  refine ⟨min c₁ ((1 / 1000) / Real.log 1000), lt_min hc₁ (by positivity), max q₁ 3, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hsq him0 hhalf ρ hρ him hne
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hq2 : 2 ≤ q := by omega
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  -- `λ(ρ₀) > 0`, hence `log (1/λ(ρ₀)) ≥ 0`
  have hre : ρ₀.re < 1 := boxMaxZeroAux.zeroMult_re_lt_one χ₀ hmin.1.2.1
  have hlam0pos : 0 < Work.LinnikContract.lamOf q ρ₀ := by
    rw [Work.LinnikContract.lamOf]
    exact mul_pos (by linarith) hlogq
  have hlog0 : 0 ≤ Real.log (1 / Work.LinnikContract.lamOf q ρ₀) := by
    apply Real.log_nonneg
    rw [one_div]
    exact (one_le_inv₀ hlam0pos).mpr (by linarith [hhalf])
  by_cases hbig : 1 / 1000 ≤ Work.LinnikContract.lamOf q ρ₀
  · -- `λ(ρ₀) ≥ 1/1000`: `IsMin1` gives `λ(ρ) ≥ λ(ρ₀)`, and `log (1/λ(ρ₀)) ≤ log 1000`
    have hminle : Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q ρ :=
      hmin.2 χ₀ ρ ⟨hmin.1.1, hρ, him⟩
    have hlogle : Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Real.log 1000 := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hlam0pos]
      nlinarith [hbig]
    have hconst : ((1 / 1000) / Real.log 1000) * Real.log 1000 = 1 / 1000 := by
      rw [div_mul_cancel₀]
      exact ne_of_gt (Real.log_pos (by norm_num))
    calc min c₁ ((1 / 1000) / Real.log 1000) * Real.log (1 / Work.LinnikContract.lamOf q ρ₀)
        ≤ ((1 / 1000) / Real.log 1000) * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hlog0
      _ ≤ ((1 / 1000) / Real.log 1000) * Real.log 1000 :=
          mul_le_mul_of_nonneg_left hlogle (by positivity)
      _ = 1 / 1000 := hconst
      _ ≤ Work.LinnikContract.lamOf q ρ₀ := hbig
      _ ≤ Work.LinnikContract.lamOf q ρ := hminle
  · -- `λ(ρ₀) < 1/1000`, so `≤ 1/100`: the uncapped repulsion applies
    have hbig' : Work.LinnikContract.lamOf q ρ₀ < 1 / 1000 := not_le.mp hbig
    have h100 : Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 := by linarith [hbig']
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hlog0)
      (hrec q hq1 χ₀ ρ₀ hmin hsq him0 h100 ρ hρ him hne)

end Work.LinnikAreas
