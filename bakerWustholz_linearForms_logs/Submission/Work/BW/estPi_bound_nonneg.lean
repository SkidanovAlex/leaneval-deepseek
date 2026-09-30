import Mathlib
import Submission.Work.BW.est15defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Under the standing hypotheses of BW §11 (`ACHyp`), the parameters satisfy `2 ≤ r` and
`0 < σ j`, whence `D = pD r d σ > 0` and `Λ = gamBound K b v σ ≥ 0`. Since `T' = estTp t ≥ 0`,
the `Π`-factor bound `T'(1 + log(1 + Λ/T'))` is nonnegative: for `T' = 0` it vanishes, and for
`T' > 0` one has `Λ/T' ≥ 0`, so `1 + Λ/T' ≥ 1` and `log(1 + Λ/T') ≥ 0`. -/
theorem estPi_bound_nonneg {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (t : Fin (r - 1) → ℕ) :
    0 ≤ estTp t * (1 + Real.log (1 + gamBound K b v σ / estTp t)) := by
  -- σ is positive at every place (component of `BH`)
  have hσ : ∀ j, 0 < σ j := by
    have h := H.hBH; simp only [BH] at h; exact h.2.2.2.2.1
  -- `d = [K:ℚ] ≥ 1`
  have hd1 : (1 : ℝ) ≤ (dK K : ℝ) := by
    have h : 1 ≤ dK K := Module.finrank_pos
    exact_mod_cast h
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast H.hr
  have hd0 : (0 : ℝ) < (dK K : ℝ) := by linarith
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  -- `log (2 r d) > 0`
  have hlogD : 0 < Real.log (2 * (r : ℝ) * (dK K : ℝ)) := by
    apply Real.log_pos
    nlinarith [hr2, hd1]
  have hprod : 0 < ∏ j, σ j := Finset.prod_pos (fun j _ => hσ j)
  -- `D = pD r d σ > 0` and `Λ = gamBound K b v σ ≥ 0`
  have hDpos : 0 < acD K σ := by
    rw [acD, pD]
    positivity
  have hr1 : (0 : ℝ) ≤ (r : ℝ) - 1 := by linarith
  have hgam : 0 ≤ gamBound K b v σ := by
    rw [gamBound]; positivity
  -- `T' = estTp t ≥ 0`
  have hT : 0 ≤ estTp t := Finset.sum_nonneg fun m _ => by positivity
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · -- `T' = 0`: the product vanishes
    rw [← hT0]; simp
  · -- `T' > 0`: the logarithm is nonnegative
    have hdiv : 0 ≤ gamBound K b v σ / estTp t := div_nonneg hgam hTpos.le
    have h1 : 1 ≤ 1 + gamBound K b v σ / estTp t := by linarith
    have hlog : 0 ≤ Real.log (1 + gamBound K b v σ / estTp t) := Real.log_nonneg h1
    exact mul_nonneg hTpos.le (by linarith)

end Work.BW
