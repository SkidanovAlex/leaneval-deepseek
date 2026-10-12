import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.FSEnvDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.fsEnv_lille_val` — the value of `𝓁` at the concrete FS environment

`Work.BoseB7.fsEnv t` (`Submission/Work/BoseB7/FSEnvDefs.lean`) is the concrete
`Q3Env` at FS's parameter point `μ = t`, `a = 1`, whose `K_H` is FS's **full**
`K̃_H(μa³)^{-5/12}` with `K̃_H = X^{-8/3}`, i.e. `K_H = X^{-549/4}`.

FS `eq:DefLille` gives `𝓁 = (μa³)K_H²`; this module evaluates it:

  `𝓁 = t · (X^{-549/4})² = X^{323} · X^{-549/2} = X^{97/2}`,

i.e. `(fsEnv t).lille = fsXp t (97/2)` (the `fsXp` normal form of
`Work.BoseBox.Basic`, `fsXp t c = t^{c/323} = X^c`).

This is the row `𝓁` of the closed-form table in
`Submission/Work/BoseB7/fsEnv_closed.lean` (which imports this module), so the
exponent arithmetic is done here with the `fsXp`-calculus
(`fsXp_mul`, `fsXp_rpow`, `fsXp_pow`, `delta_eq_fsXp`) rather than through the
`FSParamsView` bundle (`lille_val` of
`Submission/Work/BoseB7/FSParamsVals.lean`), which would be circular.

The intermediate value `K_H = X^{-549/4}` is kept as a local `have` (it is the
`fsKHVal_eq` lemma of `fsEnv_closed.lean`, which cannot be imported here).

## Contents

* `fsEnv_lille_val` — the target, `𝓁 = X^{97/2}`.
-/

namespace Work.BoseB7

open Work.BoseBox

/-- **`𝓁 = (μa³)K_H² = X^{97/2}` at the concrete environment `fsEnv t`.**

`K_H = K̃_H(μa³)^{-5/12} = X^{-8/3}·X^{-1615/12} = X^{-549/4}`, so
`(μa³)K_H² = X^{323}·X^{-549/2} = X^{97/2}` in the `fsXp` normal form of
`Work.BoseBox.Basic`. -/
theorem fsEnv_lille_val {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] {t : ℝ} (h0 : 0 < t) :
    (Work.BoseB7.fsEnv (Mode := Mode) t).lille = Work.BoseBox.fsXp t (97 / 2) := by
  have ht : 0 ≤ t := h0.le
  -- FS's full `K_H` at `μ = t`, `a = 1` is `X^{-549/4}`.
  have hKH : fsKHVal t = fsXp t (-(549 / 4)) := by
    rw [fsKHVal, KH, one_pow, mul_one, rpow_eq_fsXp ht, fsXp_mul h0]
    norm_num
  have h2 : (fsXp t (-(549 / 4)) : ℝ) ^ 2 = fsXp t (-(549 / 2)) := by
    rw [← Real.rpow_natCast, fsXp_rpow ht]
    norm_num
  have hproj : (fsEnv (Mode := Mode) t).lille = lille t 1 (fsKHVal t) := rfl
  rw [hproj, lille, hKH]
  simp only [one_pow, mul_one]
  rw [h2]
  calc t * fsXp t (-(549 / 2))
      = fsXp t 323 * fsXp t (-(549 / 2)) :=
        congr_arg (· * fsXp t (-(549 / 2))) (delta_eq_fsXp ht)
    _ = fsXp t (323 + -(549 / 2)) := fsXp_mul h0 _ _
    _ = fsXp t (97 / 2) := by congr 1; norm_num

end Work.BoseB7
