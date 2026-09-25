import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace Commons.NumberTheory.Zeta

noncomputable section

/-- The complex-valued correlation function `Chebyshev.psi t - t`, supported on `[1, ∞)`. -/
private def psiSubIdCorr (t : ℝ) : ℂ :=
  if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0

private lemma psi_complex_measurable : Measurable (fun t : ℝ => (Chebyshev.psi t : ℂ)) := by
  let s : ℕ → ℂ := fun k => (Chebyshev.psi (k : ℝ) : ℂ)
  have hs : Measurable s := by fun_prop
  have hf : Measurable (fun t : ℝ => (⌊t⌋₊ : ℕ)) := by fun_prop
  have hcong : (fun t : ℝ => (Chebyshev.psi t : ℂ)) = fun t : ℝ => s (⌊t⌋₊) := by
    funext t
    exact congrArg (fun z : ℝ => (z : ℂ)) (Chebyshev.psi_eq_psi_coe_floor t)
  rw [hcong]
  exact hs.comp hf

private lemma psiSubIdCorr_measurable : Measurable psiSubIdCorr := by
  unfold psiSubIdCorr
  apply Measurable.ite measurableSet_Ici
  · exact psi_complex_measurable.sub (by fun_prop : Measurable (fun t : ℝ => (t : ℂ)))
  · fun_prop

private lemma psiSubIdCorr_aestronglyMeasurable :
    AEStronglyMeasurable psiSubIdCorr (volume : Measure ℝ) :=
  psiSubIdCorr_measurable.aestronglyMeasurable

private lemma psiSubIdCorr_integrableOn_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn psiSubIdCorr (Icc a b) := by
  refine Measure.integrableOn_of_bounded (s := Icc a b) (M := Chebyshev.psi b + b) ?_ ?_ ?_
  · exact measure_Icc_lt_top.ne
  · exact psiSubIdCorr_aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Icc]
    apply ae_of_all _ _
    intro t ht
    have hb0 : 0 ≤ b := by linarith
    have hta : a ≤ t := (mem_Icc.mp ht).1
    have ht_le_b : t ≤ b := (mem_Icc.mp ht).2
    have ht0 : 0 ≤ t := by linarith
    by_cases h1 : 1 ≤ t
    · simp only [psiSubIdCorr, h1, ↓reduceIte]
      have hpsi : Chebyshev.psi t ≤ Chebyshev.psi b := Chebyshev.psi_mono ht_le_b
      have hpsi0 : 0 ≤ Chebyshev.psi t := Chebyshev.psi_nonneg t
      calc
        ‖(Chebyshev.psi t : ℂ) - (t : ℂ)‖ ≤ ‖(Chebyshev.psi t : ℂ)‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
        _ = Chebyshev.psi t + t := by
          have hψn : ‖(Chebyshev.psi t : ℂ)‖ = Chebyshev.psi t := by
            simpa [abs_of_nonneg hpsi0] using (RCLike.norm_ofReal (Chebyshev.psi t))
          have htn : ‖(t : ℂ)‖ = t := by
            simpa [abs_of_nonneg ht0] using (RCLike.norm_ofReal t)
          rw [hψn, htn]
        _ ≤ Chebyshev.psi b + b := by linarith
    · simp only [psiSubIdCorr, h1, ↓reduceIte, norm_zero]
      exact add_nonneg (Chebyshev.psi_nonneg b) hb0

private lemma psiSubIdCorr_locallyIntegrableOn_Ioi :
    LocallyIntegrableOn psiSubIdCorr (Ioi 0) := by
  intro x0 hx0
  have hx0pos : 0 < x0 := hx0
  let r : ℝ := x0 / 2
  have hr : 0 < r := by dsimp [r]; linarith
  refine ⟨Metric.ball x0 r, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x0 hr)
  · have ha : 0 < x0 - r := by dsimp [r]; linarith
    have hab : x0 - r ≤ x0 + r := by linarith
    exact (psiSubIdCorr_integrableOn_Icc (a := x0 - r) (b := x0 + r) ha hab).mono_set
      (by
        intro y hy
        have hyr : |y - x0| < r := by
          simpa [Real.dist_eq] using hy
        constructor <;> linarith [abs_lt.mp hyr])

private lemma psiSubIdCorr_isBigO_top {θ C : ℝ}
    (hbig : ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ C * x ^ θ) :
    psiSubIdCorr =O[atTop] (fun x : ℝ => x ^ θ) := by
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [hbig, (eventually_ge_atTop 1)] with x hx hx1
  have hxpos : 0 < x := by linarith
  have hnorm : ‖psiSubIdCorr x‖ = |Chebyshev.psi x - x| := by
    dsimp [psiSubIdCorr]
    rw [if_pos hx1]
    simpa using (RCLike.norm_ofReal (Chebyshev.psi x - x) :
      ‖((Chebyshev.psi x - x : ℝ) : ℂ)‖ = |Chebyshev.psi x - x|)
  calc
    ‖psiSubIdCorr x‖ = |Chebyshev.psi x - x| := hnorm
    _ ≤ C * x ^ θ := hx
    _ = C * ‖x ^ θ‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxpos.le θ)]

private lemma psiSubIdCorr_isBigO_bot (b : ℝ) :
    psiSubIdCorr =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  have hset : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsWithin]
    refine ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo, by simp, ?_⟩
    intro t ht
    exact ⟨ht.2, ht.1.2⟩
  filter_upwards [hset] with t ht
  have ht1 : t < 1 := ht.2
  have hnorm : ‖psiSubIdCorr t‖ = 0 := by
    dsimp [psiSubIdCorr]
    simp [ht1]
  calc
    ‖psiSubIdCorr t‖ = 0 := hnorm
    _ ≤ 1 * ‖t ^ (-b)‖ := by
      rw [Real.norm_eq_abs]
      exact mul_nonneg zero_le_one (abs_nonneg _)

private lemma mellin_psiSubIdCorr_differentiableAt {θ C : ℝ}
    (hbig : ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ C * x ^ θ) {s : ℂ}
    (hs : s.re < -θ) : DifferentiableAt ℂ (mellin psiSubIdCorr) s := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := -θ) (b := s.re - 1) ?_ ?_ ?_ ?_ ?_
  · exact psiSubIdCorr_locallyIntegrableOn_Ioi
  · simpa [neg_neg] using (psiSubIdCorr_isBigO_top (θ := θ) hbig)
  · exact hs
  · exact psiSubIdCorr_isBigO_bot (s.re - 1)
  · linarith

private lemma psiSubIdCorr_mellin_analyticOnNhd {θ C : ℝ} (hC : 0 < C)
    (hbig : ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ C * x ^ θ) :
    AnalyticOnNhd ℂ (fun w : ℂ => w * mellin psiSubIdCorr (-w)) {w : ℂ | θ < w.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ ?_
  · intro w hw
    have hw' : θ < w.re := hw
    have hA : DifferentiableAt ℂ (fun z : ℂ => z) w := differentiableAt_id (𝕜 := ℂ)
    have hB : DifferentiableAt ℂ (fun z : ℂ => mellin psiSubIdCorr (-z)) w := by
      have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) w :=
        (differentiableAt_id (𝕜 := ℂ) (x := w)).neg
      have hmell : DifferentiableAt ℂ (mellin psiSubIdCorr) (-w) := by
        exact mellin_psiSubIdCorr_differentiableAt (θ := θ) hbig (s := -w) (by
          rw [Complex.neg_re]
          linarith)
      exact hmell.comp w hneg
    exact (hA.mul hB).differentiableWithinAt
  · exact isOpen_lt (f := fun _ : ℂ => θ) (g := fun z : ℂ => z.re) continuous_const Complex.continuous_re

/-- If `Chebyshev.psi (x) - x = O (x ^ θ)` as `x → ∞`, then the Mellin-transform function
`w ↦ w * mellin (ψ - id) (-w)` is holomorphic on the half-plane `θ < Re w`. -/
theorem psi_sub_id_mellin_analytic {θ C : ℝ} (hC : 0 < C)
    (hbig : ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ C * x ^ θ) :
    AnalyticOnNhd ℂ
      (fun w : ℂ => w * mellin (fun t : ℝ => if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0) (-w))
      {w : ℂ | θ < w.re} := by
  have hmain := psiSubIdCorr_mellin_analyticOnNhd (θ := θ) hC hbig
  have hEq : psiSubIdCorr =
      (fun t : ℝ => if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0) := rfl
  rw [← hEq]
  exact hmain

end

end Commons.NumberTheory.Zeta
