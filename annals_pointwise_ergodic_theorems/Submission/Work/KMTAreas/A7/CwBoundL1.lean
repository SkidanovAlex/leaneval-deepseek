import Mathlib
import Submission.Work.KMTAreas.A7.cw_etaCut_decay

namespace Work.KMTAreas.A7

open MeasureTheory

/-- The modulation `ee x = exp (2 π i x)` has modulus one. -/
private lemma ee_norm_eq_one (x : ℝ) : ‖ee x‖ = 1 := by
  rw [ee, show (2 : ℂ) * ↑Real.pi * Complex.I * ↑x = ↑(2 * Real.pi * x) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **The trivial `L¹` bound for `cw`.**  If `m` is bounded by `C0` and vanishes off the interval
`[-1/R, 1/R]`, then `‖cw m j‖ ≤ 2 C0 / R` for every frequency `j`.

The proof is pure measure theory: the integrand `θ ↦ m θ e(-jθ)` is supported in
`[-1/R, 1/R]` (a set of measure `2/R`), and `|e(-jθ)| = 1`, so its integral is at most
`C0 · (2/R)`.  No smoothness of `m` is used. -/
private lemma norm_cw_le (m : ℝ → ℂ) (C0 R : ℝ) (hR : 0 < R)
    (hb : ∀ θ, ‖m θ‖ ≤ C0) (hsupp : ∀ θ, 1 / R < |θ| → m θ = 0) (j : ℤ) :
    ‖cw m j‖ ≤ 2 * C0 / R := by
  rw [cw]
  have hmem : ∀ θ, θ ∉ Set.Icc (-(1/R)) (1/R) → m θ * ee (-(j:ℝ) * θ) = 0 := by
    intro θ hθ
    have h' : ¬ (-(1/R) ≤ θ ∧ θ ≤ 1/R) := by
      simpa [Set.mem_Icc] using hθ
    have hlt : 1 / R < |θ| := lt_of_not_ge (fun hf => h' (abs_le.mp hf))
    rw [hsupp θ hlt, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hmem]
  have hbd : ‖∫ θ in Set.Icc (-(1/R)) (1/R), m θ * ee (-(j:ℝ) * θ)‖
      ≤ C0 * volume.real (Set.Icc (-(1/R)) (1/R)) :=
    norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top (fun θ _ => by
      rw [norm_mul, ee_norm_eq_one, mul_one]
      exact hb θ)
  have hvol : volume.real (Set.Icc (-(1/R)) (1/R)) = 2 / R := by
    rw [Real.volume_real_Icc_of_le (by
      have h : (0:ℝ) < 1/R := one_div_pos.mpr hR
      linarith)]
    ring
  calc ‖∫ θ in Set.Icc (-(1/R)) (1/R), m θ * ee (-(j:ℝ) * θ)‖
      ≤ C0 * volume.real (Set.Icc (-(1/R)) (1/R)) := hbd
    _ = 2 * C0 / R := by rw [hvol]; ring

/-- The trivial `L¹` bound for the coefficient kernel `cw m j = ∫_ℝ m(θ)e(-jθ)dθ`
(`Work.KMTAreas.A7.cw`, `Submission/Work/KMTAreas/A7/Large/Defs.lean`): if `m` is `C²` and vanishes
off `[-1/R,1/R]` for some `R > 0`, with `‖m‖_∞ ≤ C₀`, then `‖cw m j‖ ≤ C·C₀/R` for every `j : ℤ`,
the constant `C` being absolute. -/
theorem CwBoundL1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ) (C0 R : ℝ),
      0 < R → 0 ≤ C0 → ContDiff ℝ 2 m →
      (∀ θ, ‖m θ‖ ≤ C0) →
      (∀ θ, 1 / R < |θ| → m θ = 0) →
      ∀ j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ ≤ C * C0 / R :=
  ⟨2, by norm_num, fun m C0 R hR _hC0 _hm hb hsupp j => norm_cw_le m C0 R hR hb hsupp j⟩

end Work.KMTAreas.A7
