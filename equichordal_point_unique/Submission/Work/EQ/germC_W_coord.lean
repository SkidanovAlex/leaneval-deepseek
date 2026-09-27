import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.ugermC_snd_eq_neg_mul

/-! # The `W`-coordinate of the stable germ curve

The meromorphic coordinate `W(x, y) = y / (x - a/2)` of the second focus `O₂ = (a/2, 0)`, read on
the stable germ curve `germC a h ·`, is the *linearising parameter* of the germ:

  `W (germC a h u) = h (λ u)`.

Cleared of division (multiplying by the third `dslope` of `germC`), this is

  `(germC a h u).2 = h (λu) · ((germC a h u).1 - a/2)`,

which is an identity of rational functions of the three `dslope`s; it is proved here directly
from `sub_smul_dslope` (`u · dslope f 0 u = f u - f 0`) with the hypothesis that the third
`dslope` does not vanish at `u` (it equals `1 - λ ≠ 0` at `u = 0`, so it holds for `u` in a
neighbourhood of `0`).

The companion identity for the first focus `O₁ = (-a/2, 0)`,
`W₊ (germC a h u) = h u` with `W₊(x,y) = y/(x + a/2)`, follows immediately from the mirror
identity `Work.EQ.ugermC_snd_eq_neg_mul`, since `ugermC = eqMirror ∘ germC`. -/

set_option linter.unusedVariables false

namespace Work.EQ

open Complex

/-- **The `W`-coordinate of the stable germ is the germ parameter**: cleared of division,
`(germC a h u).2 = h (λu) · ((germC a h u).1 - a/2)`, as long as the third `dslope` of `germC`
does not vanish at `u` (true for `u` near `0`, where it equals `1 - λ ≠ 0`). -/
theorem germC_snd_eq_h_mul {a : ℝ} {h : ℂ → ℂ} (h0 : h 0 = 0) {u : ℂ}
    (hu : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u ≠ 0) :
    (germC a h u).2 = h ((eqLam a : ℂ) * u) * ((germC a h u).1 - ((a / 2 : ℝ) : ℂ)) := by
  have hcast : ((a / 2 : ℝ) : ℂ) = (a : ℂ) / 2 := by push_cast; ring
  simp only [germC]
  rw [hcast]
  set A := dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 u with hAdef
  set H := dslope h 0 u with hHdef
  set B := dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u with hBdef
  have huB : B ≠ 0 := hu
  have hA : u * A = h ((eqLam a : ℂ) * u) := by
    have hh := sub_smul_dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) (0 : ℂ) u
    simp only [sub_zero, smul_eq_mul] at hh
    simpa [h0, hAdef] using hh
  have hH : u * H = h u := by
    have hh := sub_smul_dslope h (0 : ℂ) u
    simp only [sub_zero, smul_eq_mul] at hh
    simpa [h0, hHdef] using hh
  have hB : u * B = h ((eqLam a : ℂ) * u) - h u := by
    have hh := sub_smul_dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) (0 : ℂ) u
    simp only [sub_zero, smul_eq_mul] at hh
    rw [hBdef]
    rw [hh, mul_zero, h0, sub_zero, sub_zero]
  rcases eq_or_ne u 0 with rfl | hu0
  · simp [h0]
  · have hAB : A - B = H := by
      have h1 : u * (A - B) = u * H := by rw [mul_sub, hA, hB, hH]; ring
      exact mul_left_cancel₀ hu0 h1
    have hclear : (a : ℂ) * u * H * A = h ((eqLam a : ℂ) * u) * ((a : ℂ) * A - (a : ℂ) * B) := by
      rw [← hAB]
      rw [show (a : ℂ) * u * (A - B) * A = (a : ℂ) * (A - B) * (u * A) by ring, hA]
      ring
    rw [show (a : ℂ) * A / B - (a : ℂ) / 2 - (a : ℂ) / 2 = (a : ℂ) * A / B - (a : ℂ) by ring]
    rw [show h (↑(eqLam a) * u) * ((a : ℂ) * A / B - (a : ℂ))
          = h (↑(eqLam a) * u) * ((a : ℂ) * A - (a : ℂ) * B) / B by
        rw [show (a : ℂ) * A / B - (a : ℂ) = ((a : ℂ) * A - (a : ℂ) * B) / B by
          field_simp]
        ring]
    rw [div_eq_div_iff huB huB, hclear]

/-- **The companion identity for the first focus**: `(germC a h u).2 = h u · ((germC a h u).1 +
a/2)`, i.e. `W₊ (germC a h u) = h u` for `W₊(x,y) = y/(x + a/2)`. -/
theorem germC_snd_eq_h_mul_add {a : ℝ} {h : ℂ → ℂ} (h0 : h 0 = 0) (u : ℂ) :
    (germC a h u).2 = h u * ((germC a h u).1 + ((a / 2 : ℝ) : ℂ)) := by
  have h := ugermC_snd_eq_neg_mul a h0 u
  simp only [ugermC, eqMirror] at h
  rw [h]; ring

end Work.EQ
