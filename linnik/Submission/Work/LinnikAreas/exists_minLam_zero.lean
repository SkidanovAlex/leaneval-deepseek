import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.boxMaxZero

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

/-- **Extraction of the minimal-`λ` zero in a horizontal strip.**  If `ρ ≠ ρ₀` is a zero of a
non-principal `χ` with `|Im ρ| ≤ H`, then among all zeros `z ≠ ρ₀` of `χ` with `|Im z| ≤ H` and
`λ(z) ≤ λ(ρ)` there is one, `u`, of minimal `λ`.

The set in question is contained in the compact region `{0 < Re z < 1, |Im z| ≤ H}` intersected
with `λ(z) ≤ λ(ρ)` (i.e. `Re z ≥ 1 - λ(ρ)/log q` for `q ≥ 2`) and is the support of the divisor of
`completedLFunction χ.primitiveCharacter` on the ball of radius `Real.sqrt (1 + H^2) + 1`, hence
finite (`MeromorphicOn.divisor`'s finite support on `closedBall 0 R`); use
`Commons.NumberTheory.Linnik.completedL_zero_strip` for `0 < Re z < 1`, and note that for `q = 1`
(where `log q = 0`) every `lamOf` vanishes and the claim is trivial. -/
theorem exists_minLam_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (ρ₀ ρ : ℂ) (H : ℝ)
    (hρ : Work.LinnikContract.zeroMult χ ρ ≠ 0) (hH : |ρ.im| ≤ H) (hne : ρ ≠ ρ₀) :
    ∃ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 ∧ u ≠ ρ₀ ∧ |u.im| ≤ H ∧
      Work.LinnikContract.lamOf q u ≤ Work.LinnikContract.lamOf q ρ ∧
      ∀ z : ℂ, Work.LinnikContract.zeroMult χ z ≠ 0 → z ≠ ρ₀ → |z.im| ≤ H →
        Work.LinnikContract.lamOf q z ≤ Work.LinnikContract.lamOf q ρ →
        Work.LinnikContract.lamOf q u ≤ Work.LinnikContract.lamOf q z := by
  classical
  -- A non-principal character mod `q` forces `q ≥ 2` (there is only one character mod `1`).
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq2 : 2 ≤ q := by
    by_contra h
    have hq1 : q = 1 := by omega
    subst hq1
    exact hχ (Subsingleton.elim χ (1 : DirichletCharacter ℂ 1))
  have hlogpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  -- The zero set of `χ` with `Re ≤ 1` and `|Im| ≤ H` (and `Re ≥ ρ.re`) is finite.
  have hfin := boxMaxZeroAux.finite_zeroMult_box χ ρ.re H
  set S := hfin.toFinset with hS
  have hmemS : ∀ u : ℂ, u ∈ S ↔
      zeroMult χ u ≠ 0 ∧ ρ.re ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ H := by
    intro u
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  have hρS : ρ ∈ S := (hmemS ρ).mpr
    ⟨hρ, le_rfl, le_of_lt (boxMaxZeroAux.zeroMult_re_lt_one χ hρ), hH⟩
  -- Pick a minimiser of `lamOf q` over the (nonempty) candidate set.
  have hneS : (S.filter (fun z => z ≠ ρ₀ ∧ lamOf q z ≤ lamOf q ρ)).Nonempty :=
    ⟨ρ, Finset.mem_filter.mpr ⟨hρS, hne, le_rfl⟩⟩
  obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image _ (fun z => lamOf q z) hneS
  obtain ⟨huS, hune, hule⟩ := Finset.mem_filter.mp hu
  obtain ⟨hzu, -, -, himu⟩ := (hmemS u).mp huS
  refine ⟨u, hzu, hune, himu, hule, ?_⟩
  intro z hz hzne himz hzle
  -- `lamOf q z ≤ lamOf q ρ` with `log q > 0` gives `ρ.re ≤ z.re`, so `z` is a candidate too.
  have hzle' : (1 - z.re) * Real.log (q : ℝ) ≤ (1 - ρ.re) * Real.log (q : ℝ) := hzle
  have hzre_le : ρ.re ≤ z.re := by
    have h2 : 1 - z.re ≤ 1 - ρ.re :=
      (mul_le_mul_iff_left₀ hlogpos).mp hzle'
    linarith
  have hzS : z ∈ S := (hmemS z).mpr
    ⟨hz, hzre_le, le_of_lt (boxMaxZeroAux.zeroMult_re_lt_one χ hz), himz⟩
  exact hmin z (Finset.mem_filter.mpr ⟨hzS, hzne, hzle⟩)

end Work.LinnikAreas
