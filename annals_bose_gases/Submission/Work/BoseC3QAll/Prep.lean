import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.Statements
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7AK.Prep` — the small scalar facts of the parameter point

Elementary consequences of `FSParamsView` used by the preparation bundle
`SplitQ3A` (`Statements.lean`) and by the assembly `control3QA_of_three`:

* `lille_sq_le_one` — `𝓁² ≤ 1` (FS §9's `𝓁 ≤ δ ≤ 1`; here `𝓁 = X^{97/2}`);
* `lille_pos` — `0 < 𝓁`;
* `eT_nonneg` — `0 ≤ ε_T` (it is `X^{23/4} > 0`);
* `b_pos_of_le` — `b₀ > 0` and `b₀ ≤ b` give `0 < b`;
* `KH_a_pos` — `0 < K_H a`;
* `lille_le_one` — `𝓁 ≤ 1`.

Nothing here uses the Fock system: they are scalar facts about FS's parameters.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- FS `eq:DefLille`: `𝓁 = (μa³)K_H² = X^{97/2}`; in particular `𝓁² = X^{97} ≤ 1`
for `0 < t ≤ 1`. -/
theorem lille_sq_le_one (E : Q3Env Mode) (h : FSParamsView E) : E.lille ^ 2 ≤ 1 := by
  have ht0 : 0 < h.t := h.t_pos
  calc E.lille ^ 2 = Work.BoseBox.fsXp h.t 97 := by
        rw [lille_val E h, ← Real.rpow_natCast, Work.BoseBox.fsXp_rpow ht0.le]
        congr 1
        norm_num
    _ ≤ 1 := Work.BoseBox.fsXp_le_one ht0 h.t_le_one (by norm_num)

/-- `0 < 𝓁` at FS's parameter point. -/
theorem lille_pos (E : Q3Env Mode) (h : FSParamsView E) : 0 < E.lille := by
  rw [lille_val E h]
  exact Work.BoseBox.fsXp_pos h.t_pos

/-- `𝓁 ≤ 1` at FS's parameter point. -/
theorem lille_le_one (E : Q3Env Mode) (h : FSParamsView E) : E.lille ≤ 1 := by
  rw [lille_val E h]
  exact Work.BoseBox.fsXp_le_one h.t_pos h.t_le_one (by norm_num)

/-- `0 ≤ ε_T` (it is `X^{23/4} > 0`). -/
theorem eT_nonneg (E : Q3Env Mode) (h : FSParamsView E) : 0 ≤ E.eT := by
  rw [h.eT_eq]
  exact Work.BoseBox.fsXp_nonneg h.t_pos.le

/-- `0 < ε_T`. -/
theorem eT_pos (E : Q3Env Mode) (h : FSParamsView E) : 0 < E.eT := by
  rw [h.eT_eq]
  exact Work.BoseBox.fsXp_pos h.t_pos

/-- `0 < b` from `b₀ ≤ b` and `0 < b₀`. -/
theorem b_pos_of_le {b₀ b : ℝ} (hb₀ : 0 < b₀) (hb : b₀ ≤ b) : 0 < b :=
  lt_of_lt_of_le hb₀ hb

/-- `0 < K_H a` at FS's parameter point (`K_H ≥ 1`, `a > 0`). -/
theorem KH_a_pos (E : Q3Env Mode) (h : FSParamsView E) : 0 < E.KH * E.aScat :=
  mul_pos (lt_of_lt_of_le zero_lt_one h.one_le_KH) h.a_pos

/-- `0 < K_H`. -/
theorem KH_pos (E : Q3Env Mode) (h : FSParamsView E) : 0 < E.KH :=
  lt_of_lt_of_le zero_lt_one h.one_le_KH

end Work.BoseC3QAll
