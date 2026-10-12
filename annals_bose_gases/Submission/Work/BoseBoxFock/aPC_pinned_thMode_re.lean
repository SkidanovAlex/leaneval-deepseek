import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.aPCPairAlg
import Submission.Work.BoseBoxFock.chiRowDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-
# `Work.BoseBoxFock.aPC_pinned_thMode_re` — the real part of the pinned `thMode` slot mean

The state `G : X n → ℂ` of the left-hand side is `y ↦ conj (thMode (y j)) · ↑(Σᵢ PᵢΦ (y))`, and
the claim is that its `j`-th complex slot mean has real part the `j`-th real slot mean of the
weight `thW = χ_Λ² − 1 − Re θ_tail` times the same sum.  Three ingredients:

* `aPC_re` reduces the real part of the complex slot mean to the real slot mean of the real part,
  at the price of the integrability of the peeled fibre; that integrability is a boundedness
  statement, and the bound `n·(sup_{abox}|Φ|)` for the sum `Σᵢ PᵢΦ` comes from the sup-norm
  contraction `aP_abs_le` on the centred box (together with `hthb` for `thMode`);
* on the peeled fibre the `j`-th coordinate of `update x j y` is `y`, and for `y` in the cube the
  `θ`-weight is `1`, so `Re (thMode y) = thW y` (`thMode_re_of_theta_eq_one`);
* the resulting *pointwise-on-the-box* identity between real states is then transported through the
  slot mean by the box-locality fact of `chiRow_aP_abox_facts`.
-/

open MeasureTheory

namespace Work.BoseBoxFock

set_option maxHeartbeats 800000

theorem aPC_pinned_thMode_re {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    {Cth : ℝ} (hCth0 : 0 ≤ Cth)
    (hthm : Measurable (Work.BoseBoxFock.thMode ℓ N))
    (hthb : ∀ z : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.thMode ℓ N z‖ ≤ Cth) :
    ∀ x ∈ Submission.BoseGases.abox n ℓ,
      (Work.BoseBoxFock.aPC ℓ j (fun y : Submission.BoseGases.X n =>
          (starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) *
            ((∑ i : Fin n, ((Submission.BoseGases.aP ℓ i Φ y : ℝ) : ℂ)))) x).re
      = Submission.BoseGases.aP ℓ j (fun y : Submission.BoseGases.X n =>
          Work.BoseBoxFock.thW ℓ N (y j) * (∑ i : Fin n, Submission.BoseGases.aP ℓ i Φ y)) x := by
  intro x hx
  -- the real state `W = Σᵢ PᵢΦ` whose slot mean appears on both sides
  set W : Submission.BoseGases.X n → ℝ := fun y => ∑ i : Fin n, Submission.BoseGases.aP ℓ i Φ y with hW
  have hWu : ∀ y, W y = ∑ i : Fin n, Submission.BoseGases.aP ℓ i Φ y := fun y => by rw [hW]
  have hWm : Measurable W := by
    rw [hW]
    exact Finset.measurable_sum _ (fun i _ => Weak.aP_measurable i hΦc.measurable)
  -- a sup-norm bound for `Φ` and for `W` on the centred box
  obtain ⟨C0, hC0⟩ :=
    (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn (f := Φ) hΦc.continuousOn
  set B := max C0 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hΦB : ∀ z ∈ Submission.BoseGases.abox n ℓ, |Φ z| ≤ B := by
    intro z hz
    have h1 : |Φ z| ≤ C0 := by simpa [Real.norm_eq_abs] using hC0 z hz
    exact h1.trans (le_max_left _ _)
  have hWB : ∀ z ∈ Submission.BoseGases.abox n ℓ, |W z| ≤ (n : ℝ) * B := by
    intro z hz
    rw [hW]
    calc |∑ i : Fin n, Submission.BoseGases.aP ℓ i Φ z|
        ≤ ∑ i : Fin n, |Submission.BoseGases.aP ℓ i Φ z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, B :=
          Finset.sum_le_sum (fun i _ => Submission.BoseGases.aP_abs_le hℓ i hΦc hB0 hΦB z hz)
      _ = (n : ℝ) * B := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- integrability of the peeled fibre of the complex state, from the box bounds
  have hInt : IntegrableOn (fun y : EuclideanSpace ℝ (Fin 3) =>
      (starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N ((Function.update x j y) j)) *
        ((W (Function.update x j y) : ℝ) : ℂ))
      (Submission.BoseGases.acube ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le) ?_
      (Cth * ((n : ℝ) * B)) ?_
    · exact ((Complex.continuous_conj.measurable.comp
        (hthm.comp ((measurable_pi_apply j).comp (measurable_update x (a := j))))).mul
        (Complex.continuous_ofReal.measurable.comp
          (hWm.comp (measurable_update x (a := j))))).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)] with y hy
      rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hthb _) (hWB _ (Submission.BoseGases.update_mem_abox j hx hy))
        (abs_nonneg _) hCth0
  -- the pointwise identity on the box: `Re (conj (thMode y)) = thW y`
  have hGpoint : ∀ y ∈ Submission.BoseGases.abox n ℓ,
      ((starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) * ((W y : ℝ) : ℂ)).re
        = Work.BoseBoxFock.thW ℓ N (y j) * (∑ i : Fin n, Submission.BoseGases.aP ℓ i Φ y) := by
    intro y hy
    have hyj : y j ∈ Submission.BoseGases.acube ℓ :=
      (Submission.BoseGases.mem_abox_iff n ℓ y).mp hy j
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, hWu y,
      Work.BoseBoxFock.thMode_re_of_theta_eq_one ℓ N
        (Work.BoseBoxFock.thetaFun_eq_one_of_mem_acube hℓ hyj)]
  -- the left-hand state, with the cast of the sum pulled out
  have hstateeq : (fun y : Submission.BoseGases.X n =>
        (starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) *
          ((∑ i : Fin n, ((Submission.BoseGases.aP ℓ i Φ y : ℝ) : ℂ))))
      = fun y : Submission.BoseGases.X n =>
        (starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) * ((W y : ℝ) : ℂ) := by
    funext y
    rw [hWu y]
    simp only [Complex.ofReal_sum]
  have hmain : (Work.BoseBoxFock.aPC ℓ j (fun y : Submission.BoseGases.X n =>
        (starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) * ((W y : ℝ) : ℂ)) x).re
      = Submission.BoseGases.aP ℓ j (fun y : Submission.BoseGases.X n =>
          Work.BoseBoxFock.thW ℓ N (y j) * (∑ i : Fin n, Submission.BoseGases.aP ℓ i Φ y)) x := by
    calc (Work.BoseBoxFock.aPC ℓ j (fun y : Submission.BoseGases.X n =>
          (starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) * ((W y : ℝ) : ℂ)) x).re
        = Submission.BoseGases.aP ℓ j (fun y : Submission.BoseGases.X n =>
            ((starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) * ((W y : ℝ) : ℂ)).re) x :=
          Work.BoseBoxFock.aPC_re ℓ j _ x hInt
      _ = Submission.BoseGases.aP ℓ j (fun y : Submission.BoseGases.X n =>
            Work.BoseBoxFock.thW ℓ N (y j) * (∑ i : Fin n, Submission.BoseGases.aP ℓ i Φ y)) x :=
          (Work.BoseBoxFock.chiRow_aP_abox_facts hℓ).2.2 j hGpoint x hx
  rw [hstateeq]
  exact hmain

end Work.BoseBoxFock
