import Mathlib

/-!
# Descending a `2πi`-periodic holomorphic function from a half-plane to a punctured disc

Let `G` be holomorphic on the half-plane `{ζ : ℂ | ζ.re < L}` and `2πi`-periodic there.  Writing
`ρ = exp L`, the exponential map sends the half-plane onto the punctured disc `{z | 0 < ‖z‖ < ρ}`
(and is onto it), and the periodicity of `G` means that `G` factors through `Complex.exp`: there is
`H` analytic on the punctured disc with `H (exp ζ) = G ζ` for `ζ.re < L`.

The function used is `H z = G (Complex.log z)` for the principal branch `Complex.log`.  On a small
neighbourhood of a point `z₀ ≠ 0` of the punctured disc one replaces `Complex.log` by the local
branch `z ↦ Complex.log z₀ + Complex.log (z / z₀)`, which is analytic near `z₀` because `z / z₀` is
close to `1` (off the branch cut); the two branches differ by an integral multiple of `2πi`, and `G`
is invariant under those shifts, which is the content of `periodic_intCast`.

## Main results

* `Work.Potential.descend_periodic_halfplane`
-/

namespace Work.Potential

open Filter Metric

private lemma period_re (w : ℂ) (n : ℤ) :
    (w + (n : ℂ) * (2 * Real.pi * Complex.I)).re = w.re := by
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]

private lemma period_nat_re (w : ℂ) (n : ℕ) :
    (w + (n : ℂ) * (2 * Real.pi * Complex.I)).re = w.re := by
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- Periodicity of `G` on the half-plane extends from the single period `2πi` to every integral
multiple of it. -/
private lemma periodic_intCast {L : ℝ} {G : ℂ → ℂ}
    (hper : ∀ ζ : ℂ, ζ.re < L → G (ζ + 2 * Real.pi * Complex.I) = G ζ) :
    ∀ (n : ℤ) (w : ℂ), w.re < L →
      G (w + (n : ℂ) * (2 * Real.pi * Complex.I)) = G w := by
  intro n
  refine Int.induction_on (motive := fun m => ∀ w : ℂ, w.re < L →
      G (w + (m : ℂ) * (2 * Real.pi * Complex.I)) = G w) n ?_ ?_ ?_
  · intro w _
    simp
  · intro i ih w hw
    have h1 : w + (((i : ℤ) + 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
        = (w + (i : ℂ) * (2 * Real.pi * Complex.I)) + 2 * Real.pi * Complex.I := by
      push_cast; ring
    rw [h1, hper (w + (i : ℂ) * (2 * Real.pi * Complex.I)) (by rw [period_nat_re]; exact hw)]
    exact ih w hw
  · intro i ih w hw
    have h1 : (w + ((-(i : ℤ) - 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I))
          + 2 * Real.pi * Complex.I
        = w + ((-(i : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    have h2 : G (w + ((-(i : ℤ) - 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I))
        = G (w + ((-(i : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
      rw [← h1, hper (w + ((-(i : ℤ) - 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I))
        (by rw [period_re]; exact hw)]
    exact h2.trans (ih w hw)

theorem descend_periodic_halfplane {L ρ : ℝ} (hL : Real.exp L = ρ) {G : ℂ → ℂ}
    (hG : ∀ ζ : ℂ, ζ.re < L → AnalyticAt ℂ G ζ)
    (hper : ∀ ζ : ℂ, ζ.re < L → G (ζ + 2 * Real.pi * Complex.I) = G ζ) :
    ∃ H : ℂ → ℂ, (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → AnalyticAt ℂ H z) ∧
      ∀ ζ : ℂ, ζ.re < L → H (Complex.exp ζ) = G ζ := by
  refine ⟨fun z => G (Complex.log z), ?_, ?_⟩
  · intro z0 hz0pos hz0lt
    have hz0 : z0 ≠ 0 := by rintro rfl; simp at hz0pos
    have hlogρ : Real.log ρ = L := by rw [← hL, Real.log_exp]
    have hrelog : (Complex.log z0).re < L := by
      rw [Complex.log_re]
      have h1 : Real.log ‖z0‖ < Real.log ρ := Real.log_lt_log hz0pos hz0lt
      rwa [hlogρ] at h1
    have hA : AnalyticAt ℂ (fun z => Complex.log z0 + Complex.log (z / z0)) z0 := by
      have hdiv : AnalyticAt ℂ (fun z => z / z0) z0 := by
        simpa using (analyticAt_id (𝕜 := ℂ) (z := z0)).div_const (c := z0)
      have hlog : AnalyticAt ℂ (fun z => Complex.log (z / z0)) z0 := by
        refine hdiv.clog ?_
        rw [div_self hz0]
        exact Complex.one_mem_slitPlane
      exact (analyticAt_const (v := Complex.log z0)).add hlog
    have hcomp : AnalyticAt ℂ (fun z => G (Complex.log z0 + Complex.log (z / z0))) z0 := by
      refine AnalyticAt.comp ?_ hA
      have hpt : Complex.log z0 + Complex.log (z0 / z0) = Complex.log z0 := by
        rw [div_self hz0, Complex.log_one, add_zero]
      rw [hpt]
      exact hG (Complex.log z0) hrelog
    refine hcomp.congr ?_
    have hball : Metric.ball 0 ρ ∈ nhds z0 :=
      Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hz0lt)
    filter_upwards [eventually_ne_nhds hz0, hball] with z hz hzball
    have hzlt : ‖z‖ < ρ := by rwa [Metric.mem_ball, dist_zero_right] at hzball
    have hzlog : (Complex.log z).re < L := by
      rw [Complex.log_re]
      have h1 : Real.log ‖z‖ < Real.log ρ := Real.log_lt_log (norm_pos_iff.mpr hz) hzlt
      rwa [hlogρ] at h1
    have hexp1 : Complex.exp (Complex.log z0 + Complex.log (z / z0)) = z := by
      rw [Complex.exp_add, Complex.exp_log hz0, Complex.exp_log (div_ne_zero hz hz0),
        mul_div_cancel₀ _ hz0]
    have hexp2 : Complex.exp (Complex.log z) = z := Complex.exp_log hz
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexp1.trans hexp2.symm)
    show G (Complex.log z0 + Complex.log (z / z0)) = G (Complex.log z)
    rw [hn]
    exact periodic_intCast hper n (Complex.log z) hzlog
  · intro ζ hζ
    have hexp : Complex.exp (Complex.log (Complex.exp ζ)) = Complex.exp ζ :=
      Complex.exp_log (Complex.exp_ne_zero ζ)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    show G (Complex.log (Complex.exp ζ)) = G ζ
    rw [hn]
    exact periodic_intCast hper n ζ hζ

end Work.Potential
