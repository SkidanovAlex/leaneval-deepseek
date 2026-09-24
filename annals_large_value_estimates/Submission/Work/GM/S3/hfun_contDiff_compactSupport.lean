import Mathlib
import Submission.Work.GM.S3.hhat_defs

/-!
# `h_t(u) = w(u)² u^{it}` is `C^∞` with compact support (GM (4.4))

`Submission.GM.hfun t u = (w u)² u^{it}`, where `w = Submission.LargeValues.bumpW` is a
smooth bump function supported in `[1,2]`.  We prove

* `hfun t` is `ContDiff ℝ ∞` (the regularity index has to be `((⊤ : ℕ∞) : WithTop ℕ∞)`,
  i.e. smooth; `⊤ : WithTop ℕ∞` would mean *analytic*, which no bump function is);
* `hfun t` has compact support, indeed its support is contained in `[1,2]`.

Route: write `hfun t = w2C · phi t` everywhere (`hfun_eq_w2C_mul_phi`), where
`w2C u = (w u)²` seen in `ℂ` and `phi t u = exp(i t log u)`.  At a point `u < 1` the function
`w2C` vanishes identically on a neighbourhood of `u`, so `hfun t` is *eventually* `0` there;
at `u ≥ 1 > 0` both factors are smooth (`w2C_contDiff`, `contDiffAt_phi`).
-/

namespace Work.GM.S3

open Complex
open scoped Topology

open Submission.GM (hfun)

/-- `w2C u = (w u)²` (with `w = bumpW`) is smooth. -/
theorem w2C_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w2C := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => ((Submission.LargeValues.bumpW u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Submission.LargeValues.bumpW_contDiff
  exact h.pow 2

/-- `phi t u = exp(i t log u)` is smooth at every `u > 0`. -/
theorem contDiffAt_phi (t : ℝ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (phi t) u := by
  have hcast0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((↑) : ℝ → ℂ) (Real.log u) :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => (Real.log x : ℂ)) u :=
    ContDiffAt.comp u hcast0 (Real.contDiffAt_log.2 hu.ne')
  have hphase : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => Complex.I * (t : ℂ) * (Real.log x : ℂ)) u :=
    (contDiffAt_const (c := Complex.I * (t : ℂ))).mul hlog
  exact ContDiffAt.comp u (Complex.contDiff_exp.contDiffAt) hphase

/-- `hfun t = w² u^{it}` is smooth: off `[1,2]` it vanishes on a neighbourhood, and on
`[1,∞)` the point is positive so that `log` is smooth. -/
theorem hfun_contDiff (t : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hfun t) := by
  rw [hfun_eq_mul]
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_or_ge u 1 with hu | hu
  · have hev : (w2C * phi t) =ᶠ[𝓝 u] fun _ => (0 : ℂ) := by
      filter_upwards [isOpen_Iio.mem_nhds hu] with x hx
      have hx' : x ∉ Set.Icc (1 : ℝ) 2 := by
        simp only [Set.mem_Iio] at hx
        intro h
        linarith [h.1]
      rw [Pi.mul_apply, w2C_eq_zero_of_notMem hx', zero_mul]
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hev
  · exact w2C_contDiff.contDiffAt.mul (contDiffAt_phi t (lt_of_lt_of_le one_pos hu))

/-- `hfun t = w² u^{it}` vanishes off the compact interval `[1,2]`. -/
theorem hfun_hasCompactSupport (t : ℝ) : HasCompactSupport (hfun t) := by
  refine HasCompactSupport.intro (K := Set.Icc (1 : ℝ) 2) isCompact_Icc (fun x hx => ?_)
  have hb : Submission.LargeValues.bumpW x = 0 :=
    Submission.LargeValues.bumpW_eq_zero_of_notMem hx
  rw [hfun, hb]
  simp

theorem hfun_contDiff_compactSupport (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Submission.GM.hfun t) ∧
      HasCompactSupport (Submission.GM.hfun t) :=
  ⟨hfun_contDiff t, hfun_hasCompactSupport t⟩

end Work.GM.S3
