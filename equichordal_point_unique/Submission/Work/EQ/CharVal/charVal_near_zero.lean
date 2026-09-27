import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.charVal_main
import Submission.Work.EQ.walk_count
import Submission.Work.EQ.walk_bounds
import Submission.Work.EQ.charValDefs

/-!
# `Work.EQ.CharVal.charVal_near_zero`

A returning fan word whose last letter is the non-principal one has a characteristic value
bounded away from `1`: the characteristic value of a returning word is the weight product of the
walk it induces (`charVal_of_closed`), which decays like `γ ^ (number of non-principal letters)`
with a uniform `γ < 1` (`walk_count`, Rychlik Lemma 13).  A word ending in `false` has at least
one non-principal letter, so its (positive, real) characteristic value is at most `γ`, hence at
distance at least `1 - γ` from `1`.
-/

namespace Work.EQ.CharVal

/-- **Rychlik's near-zero property of characteristic values.** There is a uniform `γ ∈ (0,1)`
such that the characteristic value of every returning fan word ending in the non-principal
letter lies in the interval `(0, γ]`, hence is at distance at least `1 - γ` from `1`. -/
theorem charVal_near_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∀ ε : List Bool, ε.getLast? = some false →
      Work.EQ.fan a h ε 0 = ((-1 / 2 : ℂ), (0 : ℂ)) → 1 - γ ≤ ‖Work.EQ.charVal a h ε - 1‖ := by
  obtain ⟨γ, hγ0, hγ1, hbnd⟩ := Work.EQ.walk_count (a := a) ha0 ha1
  obtain ⟨-, -, -, -, -, -, -, -, -, w10, -, -, -, -, -⟩ := Work.EQ.walk_bounds (a := a) ha0 ha1
  refine ⟨γ, hγ0, hγ1, fun ε hlast hε => ?_⟩
  -- the characteristic value is the (positive) weight product of the reversed word
  have hcv := Work.EQ.charVal_of_closed ha0 ha1 hh hε
  have hcl := Work.EQ.stAux_eq_zero_of_closed ha0 ha1 hh hε
  have hpos : 0 < Work.EQ.wtAux a ε.reverse 0 := w10 ε.reverse 0
  -- a word ending in `false` contains at least one non-principal letter
  have hmem : false ∈ ε := by
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    simp
  have hcount : 1 ≤ ε.reverse.count false := by
    rw [List.count_reverse]
    exact List.one_le_count_iff.mpr hmem
  -- the returning weight product is at most `γ`
  have hle : Work.EQ.wtAux a ε.reverse 0 ≤ γ := by
    calc Work.EQ.wtAux a ε.reverse 0 ≤ γ ^ (ε.reverse.count false) := hbnd _ hcl
      _ ≤ γ ^ 1 := pow_le_pow_of_le_one hγ0.le hγ1.le hcount
      _ = γ := pow_one γ
  have h1 : Work.EQ.charVal a h ε - 1 = (((Work.EQ.wtAux a ε.reverse 0 - 1 : ℝ)) : ℂ) := by
    rw [hcv]; push_cast; ring
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith

end Work.EQ.CharVal
