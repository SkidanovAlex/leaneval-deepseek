import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Final.holderNorm_comp_linear
import Submission.Work.NN.Newton.FTfibre.holderNorm_comp_right_le_of_contDiff

noncomputable section

open scoped NNReal ENNReal Topology
open Set

namespace Work.NN.Newton.FTfibre

/-- **Comparison of the `C^{k,α}` norm of the coordinate slice with that of the function on a
ball.**

For the coordinate projection `Φ z = z s`, the composition `z ↦ f (z s)` is `f ∘ Φ`.  Since
`‖Φ‖ = 1`, the general right-composition estimate
`holderNorm_comp_right_le_of_contDiff` loses no constant.  Every point of the polydisc
`polydisc 0 Q` has `‖z s‖ < Q s ≤ R`, so its image under `Φ` lies in the *open* ball `ball 0 R`,
hence `Φ` maps the polydisc into the interior of `closedBall 0 R`, which is exactly the
neighbourhood hypothesis `ht` of the general lemma. -/
theorem holderNorm_comp_apply_le {n : ℕ} {α : ℝ} {k : ℕ} (s : Fin n) {Q : Fin n → ℝ} {R : ℝ}
    (hQR : Q s ≤ R) (hQ : ∀ j, 0 < Q j) {f : ℂ → ℂ} (hf : ContDiff ℝ k f) (hα0 : 0 ≤ α) :
    Work.CR.Flat.holderNorm k α (fun z : Fin n → ℂ => f (z s)) (Work.CR.Flat.polydisc 0 Q)
      ≤ Work.CR.Flat.holderNorm k α f (Metric.closedBall (0 : ℂ) R) := by
  let Φ : (Fin n → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) s
  have hΦapp : ∀ z : Fin n → ℂ, Φ z = z s := fun z => ContinuousLinearMap.proj_apply s z
  have hnorm : ‖Φ‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound Φ zero_le_one (fun z => ?_)
    rw [one_mul, hΦapp z]
    exact norm_le_pi_norm z s
  have hΩ : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q,
      Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q ∈ nhds x :=
    fun x hx => (Work.CR.Flat.isOpen_polydisc 0 Q).mem_nhds hx
  have ht : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q,
      Metric.closedBall (0 : ℂ) R ∈ nhds (Φ x) := by
    intro x hx
    have hxs : ‖x s‖ < Q s := by simpa using hx s
    have hxR : ‖x s‖ < R := lt_of_lt_of_le hxs hQR
    have hmem : Φ x ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_eq_norm, hΦapp x, sub_zero]
      exact hxR
    exact Filter.mem_of_superset ((Metric.isOpen_ball).mem_nhds hmem) Metric.ball_subset_closedBall
  have hmain := holderNorm_comp_right_le_of_contDiff Φ k hα0 hf hΩ ht
  have hmax : ENNReal.ofReal (max 1 (‖Φ‖ ^ ((k : ℝ) + α))) = 1 := by
    rw [max_eq_left, ENNReal.ofReal_one]
    exact Real.rpow_le_one (norm_nonneg Φ) hnorm (add_nonneg (Nat.cast_nonneg k) hα0)
  rw [hmax, one_mul] at hmain
  rw [show (fun z : Fin n → ℂ => f (z s)) = (fun z => f (Φ z)) from
        funext (fun z => by rw [hΦapp z])]
  exact hmain

end Work.NN.Newton.FTfibre
