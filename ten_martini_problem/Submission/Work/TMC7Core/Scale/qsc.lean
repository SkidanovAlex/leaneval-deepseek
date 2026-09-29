import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Scale.qscDefs
import Submission.Work.TMC7Core.Scale.spectral_continuity
import Submission.Work.TMC7Core.Scale.qscAux

/-!
# TMC7Core / Scale — S4: quantitative spectral closeness at a free phase

`qsc` is S4 of the lead's C7 design (`Submission/Work/TMC7Core/Scale/S4_GUIDE.md`):
Avila–Malmud–Shen windowing produces, from a finitely supported quasimode of `H_{α,λ,θ}`
at a spectral point `E`, a `(9/Lw)`-quasimode supported in a window of length `2 Lw`.
Shifting the phase by `k α` moves that window to `(0, 2Lw)` without changing the
quasimode error; on that window the potential is `8 π |λ| Lw |α - α'|`-Lipschitz in the
frequency, which gives a spectral point of an almost Mathieu operator at frequency `α'`.

The two analytic inputs are proved in sibling files:

* `tent_window` — the windowing/pigeonhole step (tent functions, `Σ_n χ_n(k)² ≥ Lw/3`);
* `amo_shift`   — covariance of the almost Mathieu operator under the shift `ℓ²(ℤ) → ℓ²(ℤ)`;
* `perturb_win`— the frequency-perturbation bound on the window `(0, 2 Lw)`.
-/

open scoped ENNReal BigOperators
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Scale

/-- **S4** of the lead's C7 design (see `Submission/Work/TMC7Core/Scale/S4_GUIDE.md`):
quantitative spectral closeness at a *free* phase (AvMS windowing). -/
theorem qsc (h1 : Work.TMC7Core.P_OpBasics) (lam α α' θ E : ℝ)
    (H : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo)
    (hH : LeanEval.Analysis.TenMartini.IsAlmostMathieuOperator α lam θ H)
    (hE : (E : ℂ) ∈ spectrum ℂ H) (Lw : ℕ) (hL : 3 ≤ Lw) :
    ∃ (θ' E' : ℝ)
      (H' : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo),
      LeanEval.Analysis.TenMartini.IsAlmostMathieuOperator α' lam θ' H' ∧
      (E' : ℂ) ∈ spectrum ℂ H' ∧
      |E - E'| ≤ 9 / (Lw : ℝ) + 8 * Real.pi * |lam| * (Lw : ℝ) * |α - α'| := by
  have hHsa : IsSelfAdjoint H := h1.2.1 α lam θ H hH
  -- S4.a–S4.d: windowing.  A window-localised `9 / Lw` quasimode.
  obtain ⟨n, u, hu_ne, hu_approx, hu_supp⟩ := tent_window_alt lam α θ E H hH hHsa hE Lw hL
  -- S4.e: shift the window to `(0, 2 Lw)`; the phase moves to `θ' = θ + k α`.
  let k : ℤ := n - (Lw : ℤ)
  let θ' : ℝ := θ + (k : ℝ) * α
  obtain ⟨H₂, hH₂⟩ := h1.1 α lam θ'
  obtain ⟨H', hH'⟩ := h1.1 α' lam θ'
  have hH'sa : IsSelfAdjoint H' := h1.2.1 α' lam θ' H' hH'
  let w : EllTwo := shift k u
  have hw_norm : ‖w‖ = ‖u‖ := shift_norm k u
  have hw_ne : w ≠ 0 := by
    intro h0
    have h0' : ‖w‖ = 0 := by rw [h0]; simp
    rw [hw_norm] at h0'
    exact hu_ne (norm_eq_zero.mp h0')
  -- the support of the shifted vector lies in the window `(0, 2 Lw)`
  have hw_supp : ∀ m : ℤ, w m ≠ 0 → 0 < (m : ℝ) ∧ (m : ℝ) < 2 * (Lw : ℝ) := by
    intro m hm
    have hm' : u (m + k) ≠ 0 := by
      intro hc
      apply hm
      show shift k u m = 0
      rw [shift_apply]; exact hc
    have hb := hu_supp (m + k) hm'
    have hcast : (((m + k : ℤ)) : ℝ) = (m : ℝ) + (n : ℝ) - (Lw : ℝ) := by
      simp only [k]; push_cast; ring
    rw [hcast] at hb
    have habs : |(m : ℝ) - (Lw : ℝ)| < (Lw : ℝ) := by
      have he : (m : ℝ) + (n : ℝ) - (Lw : ℝ) - (n : ℝ) = (m : ℝ) - (Lw : ℝ) := by ring
      rw [← he]; exact hb
    rw [abs_lt] at habs
    constructor <;> linarith [habs.1, habs.2]
  -- the shifted vector is a `9 / Lw` quasimode at phase `θ'`
  have hcov : ‖(H₂ - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) w‖
      = ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) u‖ :=
    amo_shift_alt (k := k) (E := E) (H := H) (H' := H₂) hH hH₂ u
  have hq₂ : ‖(H₂ - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) w‖ ≤ 9 / (Lw : ℝ) * ‖w‖ := by
    rw [hcov, hw_norm]
    exact hu_approx
  -- S4.f: perturbing the frequency on the window costs `8 π |λ| Lw |α - α'|`
  have hpert : ‖(H' - H₂) w‖
      ≤ 8 * Real.pi * |lam| * (Lw : ℝ) * |α - α'| * ‖w‖ :=
    perturb_win_alt lam α α' θ' H₂ H' hH₂ hH' Lw (by omega) w hw_supp
  have hfinal : ‖(H' - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) w‖
      ≤ (9 / (Lw : ℝ) + 8 * Real.pi * |lam| * (Lw : ℝ) * |α - α'|) * ‖w‖ := by
    have hdec : (H' - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) w
        = (H' - H₂) w + (H₂ - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) w := by
      simp only [sub_apply, add_apply, smul_apply]; abel
    rw [hdec]
    calc ‖(H' - H₂) w + (H₂ - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) w‖
        ≤ ‖(H' - H₂) w‖ + ‖(H₂ - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) w‖ :=
          norm_add_le _ _
      _ ≤ 8 * Real.pi * |lam| * (Lw : ℝ) * |α - α'| * ‖w‖ + 9 / (Lw : ℝ) * ‖w‖ :=
          add_le_add hpert hq₂
      _ = (9 / (Lw : ℝ) + 8 * Real.pi * |lam| * (Lw : ℝ) * |α - α'|) * ‖w‖ := by ring
  -- S4.g: a quasimode produces a spectral point
  obtain ⟨z, hzmem, hzle⟩ := spectrum_close H' hH'sa E w hw_ne
  have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw_ne
  have hz_bound : ‖z - (E : ℂ)‖
      ≤ 9 / (Lw : ℝ) + 8 * Real.pi * |lam| * (Lw : ℝ) * |α - α'| := by
    have h1' : ‖(H' - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) w‖ / ‖w‖
        ≤ (9 / (Lw : ℝ) + 8 * Real.pi * |lam| * (Lw : ℝ) * |α - α'|) * ‖w‖ / ‖w‖ := by
      gcongr
    rw [mul_div_cancel_right₀ _ (ne_of_gt hwn)] at h1'
    linarith [hzle, h1']
  have hnorm : ‖z - (E : ℂ)‖ = |z.re - E| := by
    have h1 : z - (E : ℂ) = ((z.re : ℝ) : ℂ) - (E : ℂ) := by
      conv_lhs => rw [hH'sa.mem_spectrum_eq_re hzmem]
    rw [h1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨θ', z.re, H', hH', ?_, ?_⟩
  · rw [← hH'sa.mem_spectrum_eq_re hzmem]; exact hzmem
  · have : |E - z.re| = ‖z - (E : ℂ)‖ := by rw [abs_sub_comm, hnorm]
    rw [this]; exact hz_bound

end Work.TMC7Core.Scale
