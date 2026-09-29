import Mathlib
import Submission.Work.CPhi.exists_differentiableOn_log_ball

namespace Work.CPull

/-- **Holomorphic square-root lift of `Φ²/(Φ−1) − 4`.**
If `Φ` is holomorphic on the unit disc and never takes the value `1` there, then `Φ²/(Φ−1) − 4`
has a holomorphic square root `K` on the disc.  Indeed
`Φ²/(Φ−1) − 4 = (Φ−2)²/(Φ−1) = ((Φ−2)·exp(−L/2))²` where `L` is a holomorphic logarithm of
`Φ − 1` (which exists since `Φ − 1` is holomorphic and nonvanishing on the simply connected disc,
see `Work.CPhi.exists_differentiableOn_log_ball`). -/
theorem exists_K_lift (Φ : ℂ → ℂ) (hΦ : DifferentiableOn ℂ Φ (Metric.ball 0 1))
    (hΦneq : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ z ≠ 1) :
    ∃ K : ℂ → ℂ, DifferentiableOn ℂ K (Metric.ball 0 1) ∧
      ∀ z ∈ Metric.ball (0:ℂ) 1, K z ^ 2 + 4 = (Φ z) ^ 2 / (Φ z - 1) := by
  have hV : DifferentiableOn ℂ (fun z => Φ z - 1) (Metric.ball (0:ℂ) 1) := hΦ.sub_const 1
  have hne : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ z - 1 ≠ 0 :=
    fun z hz => sub_ne_zero.mpr (hΦneq z hz)
  obtain ⟨L, hLdiff, hLexp⟩ :=
    Work.CPhi.exists_differentiableOn_log_ball (c := (0:ℂ)) (r := 1) hV hne
  refine ⟨fun z => (Φ z - 2) * Complex.exp (-(L z) / 2), ?_, ?_⟩
  · exact (hΦ.sub_const 2).mul ((hLdiff.neg.div_const 2).cexp)
  · intro z hz
    have hz0 : Φ z - 1 ≠ 0 := hne z hz
    have hexp : Complex.exp (-(L z) / 2) ^ 2 = (Φ z - 1)⁻¹ := by
      rw [sq, ← Complex.exp_add,
        show -(L z) / 2 + (-(L z) / 2) = -(L z) by ring, Complex.exp_neg, hLexp z hz]
    rw [mul_pow, hexp, div_eq_mul_inv]
    field_simp
    ring

end Work.CPull
