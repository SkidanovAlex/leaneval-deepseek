import Mathlib
import Submission.Work.CNum.PtC1bAux
import Submission.Work.CNum.ratIvMem

/-!
# `Work.CNum.Q1bMem`

Soundness of the named interval `Q1b k = IvM (629/50) (expI k).im`, which encloses
`QR θ_k = 2(1+c²) sin(θ_k/2)` for `θ_k = 2πk/1024` (`k ≤ 1024`).

The two inputs are `ExpISpec` (the table `expI k` encloses `e^{i k π/1024}`, hence its
imaginary part encloses `sin (kπ/1024)`) and the rational enclosure `ratIvMem` of
`2(1+c²) = 629/50`; the interval multiplication is the four-corner rule `IvMSpec`.
-/

namespace Work.CNum

open Work.ANum

theorem Q1bMem {k : ℕ} (hk : k ≤ 1024) :
    (Work.CNum.Q1b k).Mem (Work.CNum.QR ((k : ℝ) * Real.pi / 512)) := by
  -- the imaginary part of the table entry encloses `sin (kπ/1024)`
  have hEim : (expI k).im.Mem (Real.sin ((k : ℝ) * Real.pi / 1024)) := by
    have h := (ExpISpec hk).2
    rw [show Complex.I * ((k : ℂ) * ↑Real.pi / 1024)
          = (((k : ℝ) * Real.pi / 1024 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_im] at h
    exact h
  -- the rational enclosure of `2(1+c²) = 629/50`
  have hq : (ratIv 629 50).Mem (2 * (1 + cR ^ 2)) := by
    have h := ratIvMem (p := 629) (q := 50) (by norm_num)
    convert h using 1
    norm_num [cR]
  -- half-angle rewrite
  have harg : ((k : ℝ) * Real.pi / 512) / 2 = (k : ℝ) * Real.pi / 1024 := by ring
  have hmain := IvMSpec hq hEim
  rw [QR, harg]
  exact hmain

end Work.CNum
