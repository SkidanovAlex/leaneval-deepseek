import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.EWindowAux
import Submission.Work.Asymptotics.SpikeCircle.spike_KPlus8_bound
import Submission.Work.Asymptotics.SpikeCircle.spike_KMinus8_bound
import Submission.Work.Asymptotics.SpikeCircle.spike_KPlus24_bound
import Submission.Work.Asymptotics.SpikeCircle.spike_KMinus24_bound
import Submission.Work.Asymptotics.SpikeCircle.divisorLowerDisc
import Submission.Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf
import Submission.Work.Asymptotics.SpikeCircle.jInvariantFunUpperDisc
import Submission.Work.Asymptotics.SpikeCircle.jInvariantFun_eq_iff_disc
import Submission.Work.Asymptotics.SpikeCircle.spikeStripBound
import Submission.Work.Analysis.ThreeZeros.three_zeros_bound_ball
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.Funnel_Kfun_diag_bound
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Residues.KPlusClear_T
import Submission.Work.Residues.KMinusClear_T
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Asymptotics.HalfFunnel.funnelFlat
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence

namespace Work.Asymptotics

noncomputable section

open UpperHalfPlane ModularGroup Work.Kernels Metric
open scoped Manifold Topology

/-! ### Prepared ingredients for the window bound at the pole height

The three-zero (Schwarz) route to `EWindow_pole`: the *cleared* kernel
`KhatClear = (KPlusClear - KMinusClear)/2` is holomorphic, equals
`growthPrefactor · Khat` off the coincidence, and vanishes at the three poles
`ζ = τ, τ - 1, τ + 1` of the spike disc `‖ζ - τ‖ ≤ 29/20`; the divisor lower bound of
`SpikeCircle.divisorLowerDisc` cancels the product of distances produced by the three-zero
estimate, and the exponential factors of `Δ` cancel.  The lemmas below are the verified
part of that route. -/

/-- The cleared kernel `K̄` is the `growthPrefactor` times `K̄` off the coincidence. -/
lemma KhatClear_eq_growthPrefactor_mul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ z : ℍ}
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.KhatClear ℓ d τ z = Work.Kernels.growthPrefactor d τ z * Work.Kernels.Khat ℓ d τ z := by
  have h1 := Work.Kernels.ClearLink.KPlusClear_eq_smul d hd τ z h
  have h2 := Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ d hd τ z h
  rw [Work.Kernels.KhatClear, h1, h2, Work.Kernels.Khat]
  ring

/-- The cleared kernel vanishes on the diagonal. -/
lemma KhatClear_self_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    Work.Kernels.KhatClear ℓ d z z = 0 := by
  rw [Work.Kernels.KhatClear, Work.Residues.KPlusClear_diag d hd z,
    Work.Residues.KMinusClear_diag ℓ d hd z]
  ring

/-- The cleared kernel vanishes at the `T⁻¹` translate. -/
lemma KhatClear_vadd_one_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) : Work.Kernels.KhatClear ℓ d ((1 : ℝ) +ᵥ z) z = 0 := by
  rw [Work.Kernels.KhatClear, Work.Residues.KPlusClear_T d hd z,
    Work.Residues.KMinusClear_T ℓ d hd z]
  ring

/-- The `τ`-affinity of the cleared kernel. -/
lemma KhatClear_T2_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.KhatClear ℓ d τ z) = 0 := by
  have hp := HalfFunnel.KPlusClear_T2' d hd z
  have hm := HalfFunnel.KMinusClear_T2' ℓ d hd z
  have hsplit : (fun τ : ℍ => Work.Kernels.KhatClear ℓ d τ z)
      = fun τ : ℍ => (2 : ℂ)⁻¹ * Work.Kernels.KPlusClear d τ z
          - (2 : ℂ)⁻¹ * Work.Kernels.KMinusClear ℓ d τ z := by
    funext τ; rw [Work.Kernels.KhatClear]; ring
  rw [hsplit]
  have hsub : Work.Kernels.T2op (fun τ : ℍ => (2 : ℂ)⁻¹ * Work.Kernels.KPlusClear d τ z
        - (2 : ℂ)⁻¹ * Work.Kernels.KMinusClear ℓ d τ z)
      = Work.Kernels.T2op (fun τ : ℍ => (2 : ℂ)⁻¹ * Work.Kernels.KPlusClear d τ z)
        - Work.Kernels.T2op (fun τ : ℍ => (2 : ℂ)⁻¹ * Work.Kernels.KMinusClear ℓ d τ z) := by
    funext τ; simp only [Work.Kernels.T2op, Pi.sub_apply]; ring
  rw [hsub, HalfFunnel.T2op_const_mul, HalfFunnel.T2op_const_mul, hp, hm]
  ext τ; simp

/-- The cleared kernel vanishes at the `T` translate. -/
lemma KhatClear_vadd_neg_one_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) : Work.Kernels.KhatClear ℓ d z ((1 : ℝ) +ᵥ z) = 0 := by
  have h := congr_fun (KhatClear_T2_zero ℓ d hd ((1 : ℝ) +ᵥ z)) z
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h
  have h1 : Work.Kernels.KhatClear ℓ d ((2 : ℝ) +ᵥ z) ((1 : ℝ) +ᵥ z) = 0 := by
    have : ((2 : ℝ) +ᵥ z) = (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z) := by rw [← add_vadd]; norm_num
    rw [this]
    exact KhatClear_vadd_one_zero ℓ d hd ((1 : ℝ) +ᵥ z)
  have h2 : Work.Kernels.KhatClear ℓ d ((1 : ℝ) +ᵥ z) ((1 : ℝ) +ᵥ z) = 0 :=
    KhatClear_self_zero ℓ d hd _
  rw [h1, h2] at h
  simpa using h

/-- The closed Euclidean ball of radius `ρ` about `τ` stays in `ℍ` when `ρ < Im τ`. -/
lemma closedBall_subset_upper' {c : ℍ} {ρ : ℝ} (h : ρ < c.im) :
    Metric.closedBall (c : ℂ) ρ ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have h1 : ‖w - (c : ℂ)‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have h2 : ((w - (c : ℂ)).im) = w.im - (c : ℂ).im := by simp
  have h3 : |((w - (c : ℂ)).im)| ≤ ‖w - (c : ℂ)‖ := Complex.abs_im_le_norm _
  have h4 := (abs_le.mp (le_trans h3 h1)).1
  simp only [UpperHalfPlane.coe_im] at h2
  show (0 : ℝ) < w.im
  linarith

/-- The cleared kernel, lifted to the disc about `τ`, is holomorphic with continuous
extension to the boundary. -/
lemma diffContOnCl_KhatClear (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : ℍ} (hτ : 2 ≤ τ.im) :
    DiffContOnCl ℂ (fun u : ℂ => Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u))
      (Metric.ball ((τ : ℂ)) (29 / 20)) := by
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => Work.Kernels.KhatClear ℓ d τ z) :=
    (Work.Kernels.KernelClear_growth_z ℓ d hd τ).2.1
  have hdiff : DifferentiableOn ℂ
      (fun u : ℂ => Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u))
      {u : ℂ | 0 < u.im} := (UpperHalfPlane.mdifferentiable_iff).mp hmd
  exact hdiff.diffContOnCl_ball (closedBall_subset_upper' (by linarith : (29:ℝ)/20 < τ.im))

/-- **The spike-circle bound for `K̂` for `Im τ ≥ 3`** (assembly of the four proven
componentwise spike bounds). -/
theorem Khat_spike_circle_high (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N H₀ : ℝ, 0 < C ∧ 0 ≤ N ∧ 3 ≤ H₀ ∧
      ∀ (τ ζ : UpperHalfPlane), Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → H₀ ≤ τ.im →
        ‖Work.Kernels.Khat ℓ d τ ζ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  rcases hd with rfl | rfl
  · obtain ⟨C1, N1, hC1, hN1, hb1⟩ := SpikeCircle.spike_KPlus8_bound
    obtain ⟨C2, N2, hC2, hN2, hb2⟩ := SpikeCircle.spike_KMinus8_bound ℓ
    refine ⟨C1 + C2, max N1 N2, 3, by linarith, le_max_of_le_left hN1, le_refl 3, ?_⟩
    intro τ ζ hτ hζ h3
    have hK : Khat ℓ 8 τ ζ = (KPlus 8 τ ζ - KMinus ℓ 8 τ ζ) / 2 := rfl
    rw [hK, norm_div, show ‖(2:ℂ)‖ = 2 from by norm_num]
    have h1 := hb1 τ ζ hτ hζ h3
    have h2 := hb2 τ ζ hτ hζ h3
    have hs : (1:ℝ) ≤ scale τ := one_le_scale τ
    have hN1' : scale τ ^ N1 ≤ scale τ ^ max N1 N2 :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
    have hN2' : scale τ ^ N2 ≤ scale τ ^ max N1 N2 :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _)
    have hC1' : C1 * scale τ ^ N1 ≤ (C1 + C2) * scale τ ^ max N1 N2 :=
      mul_le_mul (by linarith) hN1' (Real.rpow_nonneg (scale_pos τ).le _) (by linarith)
    have hC2' : C2 * scale τ ^ N2 ≤ (C1 + C2) * scale τ ^ max N1 N2 :=
      mul_le_mul (by linarith) hN2' (Real.rpow_nonneg (scale_pos τ).le _) (by linarith)
    have hsum : ‖KPlus 8 τ ζ - KMinus ℓ 8 τ ζ‖ ≤ 2 * ((C1 + C2) * scale τ ^ max N1 N2) :=
      le_trans (norm_sub_le _ _) (by linarith)
    linarith
  · obtain ⟨H1, hSB1⟩ := SpikeCircle.SBs_KPlus24
    obtain ⟨H2, hSB2⟩ := SpikeCircle.SBs_KMinus24 ℓ
    obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hSB1
    obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hSB2
    refine ⟨C1 + C2, max N1 N2, max 3 (max H1 H2),
      by linarith, le_max_of_le_left hN1, le_max_left 3 (max H1 H2), ?_⟩
    intro τ ζ hτ hζ hH₀
    have hA : H1 ≤ τ.im := le_trans (le_trans (le_max_left H1 H2) (le_max_right 3 (max H1 H2))) hH₀
    have hB : H2 ≤ τ.im := le_trans (le_trans (le_max_right H1 H2) (le_max_right 3 (max H1 H2))) hH₀
    have h1 := hb1 τ ζ hτ hζ hA
    have h2 := hb2 τ ζ hτ hζ hB
    simp only [Real.rpow_zero, mul_one] at h1 h2
    have hK : Khat ℓ 24 τ ζ = (KPlus 24 τ ζ - KMinus ℓ 24 τ ζ) / 2 := rfl
    rw [hK, norm_div, show ‖(2:ℂ)‖ = 2 from by norm_num]
    have hs : (1:ℝ) ≤ scale τ := one_le_scale τ
    have hN1' : scale τ ^ N1 ≤ scale τ ^ max N1 N2 :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
    have hN2' : scale τ ^ N2 ≤ scale τ ^ max N1 N2 :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _)
    have hC1' : C1 * scale τ ^ N1 ≤ (C1 + C2) * scale τ ^ max N1 N2 :=
      mul_le_mul (by linarith) hN1' (Real.rpow_nonneg (scale_pos τ).le _) (by linarith)
    have hC2' : C2 * scale τ ^ N2 ≤ (C1 + C2) * scale τ ^ max N1 N2 :=
      mul_le_mul (by linarith) hN2' (Real.rpow_nonneg (scale_pos τ).le _) (by linarith)
    have hsum : ‖KPlus 24 τ ζ - KMinus ℓ 24 τ ζ‖ ≤ 2 * ((C1 + C2) * scale τ ^ max N1 N2) :=
      le_trans (norm_sub_le _ _) (by linarith)
    linarith


/-! ### Proof route (completed)

The window bound is obtained in the *funnel* picture, i.e. for `τ = S • w ∈ 𝔽` and
`ζ = i t ∈ ℍ` with `|t - Im τ| ≤ 1`; by `imagAxis_dist_lt` the whole window lies strictly
inside the disc `‖ζ - τ‖ < 29/20`, the only `j`-coincidences of which are the three poles
`τ, τ - 1, τ + 1` (`SpikeCircle.jInvariantFun_eq_iff_disc`).

* `KhatClear_ball_decay` : the sharp ball bound
  `‖K̄(τ,ζ)‖ ≤ C (scale τ)^N e^{-2πe Im τ}` (`e = Epow d ∈ {1,2}`).  For `Im τ ≥ H₀` it is the
  maximum modulus principle (`Complex.norm_le_of_forall_mem_frontier_norm_le`) applied to the
  holomorphic `K̄` with the sphere bound `‖K̄‖ = ‖gp · K̂‖` obtained from
  `Khat_spike_circle_high`, `SpikeCircle.jInvariantFunUpperDisc` and
  `SpikeCircle.DeltaFunBoundsHalf`; for `2 ≤ Im τ ≤ H₀` it is the crude two-variable bound
  `Work.Asymptotics.KClear_mg2`.
* `Khat_window_bound` : `‖K̂(τ, i t)‖ ≤ C (scale τ)^N`.  On the coincidence locus (`ζ = τ`, so
  `τ` is purely imaginary) `KMinus_eq_zero_of_coincidence` leaves `K̂ τ τ = 0` for `d = 8` and
  `K̂ τ τ = Kfun τ τ` for `d = 24`, bounded by `Funnel_Kfun_diag_bound`.  Otherwise
  `three_zeros_bound_ball` applied to `u ↦ K̄(τ, ofComplex u)` (zeros at `τ, τ±1`, product of
  distances bounded below on the sphere by `sphere_prod_lower`) gives
  `‖K̄(τ,ζ)‖ ≤ (M/δ)‖ζ-τ‖‖ζ-(τ-1)‖‖ζ-(τ+1)‖`, the product of distances is cancelled by the
  divisor lower bound `SpikeCircle.divisorLowerDisc` inside
  `growthPrefactor_lower`, and `K̂ = K̄/gp` converts this into the desired bound.
* `scale_S_smul_le_of_mem_KEpsilon` and the `S`-transport `Kfun_S_smul`
  (`Kfun ℓ d w z = -(S•w)^{d/2} K̂ (S•w) z`) then give `EWindow_pole`: the factor
  `(1 + e^{2πt})` is not even needed -- the bound obtained is polynomial in `scale w`.
-/

/-! ### Geometry of the window and the two-variable bounds -/

/-- The exponent `e` of `Δ(z)` in the growth prefactor `Δ(τ)Δ(z)^e(jτ − jz)`. -/
def Epow (d : ℕ) : ℕ := if d = 8 then 1 else 2

lemma growthPrefactor_eq (d : ℕ) (τ z : ℍ) :
    Work.Kernels.growthPrefactor d τ z
      = Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z ^ Epow d
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) := rfl

lemma Epow_disj {d : ℕ} (hd : d = 8 ∨ d = 24) : Epow d = 1 ∨ Epow d = 2 := by
  rcases hd with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma one_le_Epow {d : ℕ} (hd : d = 8 ∨ d = 24) : (1 : ℝ) ≤ (Epow d : ℝ) := by
  rcases Epow_disj hd with h | h <;> rw [h] <;> norm_num

lemma Epow_pos (d : ℕ) : (0 : ℝ) < (Epow d : ℝ) := by
  unfold Epow; split_ifs <;> norm_num

/-- The window point `i t` lies strictly inside the disc of radius `29/20` about `τ` when
`Im τ - 1 ≤ t ≤ Im τ + 1` and `|Re τ| < 1`. -/
lemma imagAxis_dist_lt {τ : ℍ} {t : ℝ} (ht : 0 < t) (hre : |τ.re| < 1)
    (h1 : τ.im - 1 ≤ t) (h2 : t ≤ τ.im + 1) :
    ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (τ : ℂ)‖ < 29 / 20 := by
  set ζ : ℍ := Work.Kernels.imagAxis t ht with hζdef
  have hζcoe : (ζ : ℂ) = (t : ℂ) * Complex.I := rfl
  have him : |t - τ.im| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hsq : ‖(ζ : ℂ) - (τ : ℂ)‖ ^ 2
      = ((ζ : ℂ) - (τ : ℂ)).re ^ 2 + ((ζ : ℂ) - (τ : ℂ)).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hre' : ((ζ : ℂ) - (τ : ℂ)).re = -τ.re := by
    rw [Complex.sub_re, hζcoe, UpperHalfPlane.coe_re]; simp
  have him' : ((ζ : ℂ) - (τ : ℂ)).im = t - τ.im := by
    rw [Complex.sub_im, hζcoe, UpperHalfPlane.coe_im]; simp
  have h1' : τ.re ^ 2 < 1 := by nlinarith [abs_lt.mp hre, sq_abs τ.re]
  have h2' : (t - τ.im) ^ 2 ≤ 1 := by nlinarith [abs_le.mp him, sq_abs (t - τ.im)]
  have hkey : ‖(ζ : ℂ) - (τ : ℂ)‖ ^ 2 < 2 := by
    rw [hsq, hre', him']; nlinarith
  have h29 : (2 : ℝ) < (29 / 20) ^ 2 := by norm_num
  nlinarith [norm_nonneg ((ζ : ℂ) - (τ : ℂ)), hkey, h29]

/-- Points of the disc of radius `29/20` about a funnel point have height `≥ 11/20`. -/
lemma disc_im_ge {τ ζ : ℍ} (hτ : 2 ≤ τ.im) (h : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20) :
    11 / 20 ≤ ζ.im := by
  have h2 : |(ζ : ℂ).im - (τ : ℂ).im| ≤ ‖(ζ : ℂ) - (τ : ℂ)‖ := by
    rw [show (ζ : ℂ).im - (τ : ℂ).im = ((ζ : ℂ) - (τ : ℂ)).im by simp]
    exact Complex.abs_im_le_norm _
  have h3 := (abs_le.mp (le_trans h2 h)).1
  simp only [UpperHalfPlane.coe_im] at h3
  linarith

/-- The height of a disc point is at least `Im τ - 29/20`. -/
lemma disc_im_lower {τ ζ : ℍ} (h : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20) :
    τ.im - 29 / 20 ≤ ζ.im := by
  have h2 : |(ζ : ℂ).im - (τ : ℂ).im| ≤ ‖(ζ : ℂ) - (τ : ℂ)‖ := by
    rw [show (ζ : ℂ).im - (τ : ℂ).im = ((ζ : ℂ) - (τ : ℂ)).im by simp]
    exact Complex.abs_im_le_norm _
  have h3 := (abs_le.mp (le_trans h2 h)).1
  simp only [UpperHalfPlane.coe_im] at h3
  linarith

/-- The height of a disc point is at most `Im τ + 29/20`. -/
lemma disc_im_le {τ ζ : ℍ} (h : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20) :
    ζ.im ≤ τ.im + 29 / 20 := by
  have h2 : |(ζ : ℂ).im - (τ : ℂ).im| ≤ ‖(ζ : ℂ) - (τ : ℂ)‖ := by
    rw [show (ζ : ℂ).im - (τ : ℂ).im = ((ζ : ℂ) - (τ : ℂ)).im by simp]
    exact Complex.abs_im_le_norm _
  have h3 := (abs_le.mp (le_trans h2 h)).2
  simp only [UpperHalfPlane.coe_im] at h3
  linarith

/-- Points of the disc of radius `29/20` about a funnel point have `scale` at most `4 scale τ`. -/
lemma disc_scale_le {τ ζ : ℍ} (hτ : 2 ≤ τ.im) (h : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20) :
    Work.Kernels.scale ζ ≤ 4 * Work.Kernels.scale τ := by
  have h1 : (11 : ℝ) / 20 ≤ ζ.im := disc_im_ge hτ h
  have h2 : (ζ.im)⁻¹ ≤ 20 / 11 := by
    have hh : ((11 : ℝ) / 20)⁻¹ = 20 / 11 := by norm_num
    rw [← hh]
    exact inv_anti₀ (by norm_num) h1
  have h3 : ‖(ζ : ℂ)‖ ≤ ‖(τ : ℂ)‖ + 29 / 20 := by
    have := norm_add_le ((τ : ℂ)) ((ζ : ℂ) - (τ : ℂ))
    have he : (τ : ℂ) + ((ζ : ℂ) - (τ : ℂ)) = (ζ : ℂ) := by ring
    rw [he] at this
    linarith
  have h4 : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
  have h5 : (2 : ℝ) ≤ ‖(τ : ℂ)‖ := by
    have := Work.Kernels.im_le_coe_norm τ; linarith
  have h6 : 0 ≤ (ζ.im)⁻¹ := inv_nonneg.mpr ζ.im_pos.le
  have h7 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le
  rw [Work.Kernels.scale, Work.Kernels.scale]
  nlinarith [h2, h3, h4, h5, h6, h7]

/-! ### Basic algebra of the growth prefactor -/

/-- Combine three exponentials into one. -/
lemma exp3 (a b c : ℝ) : Real.exp a * Real.exp b * Real.exp c = Real.exp (a + b + c) := by
  rw [← Real.exp_add, ← Real.exp_add]

/-- The product of distances to the three poles is bounded below on the spike sphere. -/
lemma sphere_prod_lower {c z : ℂ} (h : ‖z - c‖ = 29 / 20) :
    (29 / 20) * (9 / 20) * (9 / 20) ≤ ‖z - c‖ * ‖z - (c - 1)‖ * ‖z - (c + 1)‖ := by
  have key := SpikeCircle.norm_mul_succ_pred_lower (a := z - c) h
  have hP : ‖(z - c) + 1‖ = ‖z - (c - 1)‖ := by congr 1; ring
  have hQ : ‖(z - c) - 1‖ = ‖z - (c + 1)‖ := by congr 1; ring
  rw [norm_mul, norm_mul] at key
  rw [hP, hQ] at key
  exact key

/-- The identity `K̂ = K̄ / gp` in norm form, away from the coincidence `j τ = j ζ`. -/
lemma norm_Khat_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {τ ζ : ℍ}
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ) :
    ‖Work.Kernels.Khat ℓ d τ ζ‖
      = ‖Work.Kernels.KhatClear ℓ d τ ζ‖ / ‖Work.Kernels.growthPrefactor d τ ζ‖ := by
  have hgp : Work.Kernels.growthPrefactor d τ ζ ≠ 0 := by
    rw [growthPrefactor_eq]
    exact mul_ne_zero (mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
      (pow_ne_zero _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero ζ))) (sub_ne_zero.mpr h)
  have hK : Work.Kernels.Khat ℓ d τ ζ
      = Work.Kernels.KhatClear ℓ d τ ζ / Work.Kernels.growthPrefactor d τ ζ := by
    rw [KhatClear_eq_growthPrefactor_mul ℓ d hd h, mul_div_cancel_left₀ _ hgp]
  rw [hK, norm_div]

/-- At distance `29/20` the coincidence `j τ = j ζ` is impossible. -/
lemma disc_jne {τ ζ : ℍ} (hτ : Funnel τ) (h : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ := by
  intro hc
  rcases (SpikeCircle.jInvariantFun_eq_iff_disc hτ (le_of_eq h)).mp hc with h1 | h1 | h1
  · rw [h1, sub_self, norm_zero] at h; norm_num at h
  · have h2 : ‖(ζ : ℂ) - (τ : ℂ)‖ = 1 := by
      rw [h1, UpperHalfPlane.coe_vadd]
      have h3 : ((1 : ℝ) : ℂ) + (τ : ℂ) - (τ : ℂ) = 1 := by push_cast; ring
      rw [h3]; norm_num
    rw [h2] at h; norm_num at h
  · have h2 : ‖(ζ : ℂ) - (τ : ℂ)‖ = 1 := by
      rw [h1, UpperHalfPlane.coe_vadd]
      have h3 : ((-1 : ℝ) : ℂ) + (τ : ℂ) - (τ : ℂ) = -1 := by push_cast; ring
      rw [h3]; norm_num
    rw [h2] at h; norm_num at h

/-- Upper bound for the growth prefactor on the disc. -/
lemma growthPrefactor_upper {d : ℕ} {τ ζ : ℍ} {Cz Cj : ℝ} (hCz : 0 < Cz) (hCj : 0 < Cj)
    (hΔτ : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)))
    (hΔζ : ‖Work.Kernels.DeltaFun ζ‖ ≤ Cz * Real.exp (-(2 * Real.pi * ζ.im)))
    (hjj : ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖
      ≤ Cj * Real.exp (2 * Real.pi * τ.im))
    (hζ : τ.im - 29 / 20 ≤ ζ.im) :
    ‖Work.Kernels.growthPrefactor d τ ζ‖
      ≤ (2 * Cz ^ (Epow d : ℝ) * Cj * Real.exp (2 * Real.pi * (Epow d : ℝ) * (29 / 20)))
          * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)) := by
  rw [growthPrefactor_eq, norm_mul, norm_mul]
  rw [norm_pow, ← Real.rpow_natCast (‖Work.Kernels.DeltaFun ζ‖) (Epow d)]
  have h1 : ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun ζ‖ ^ (Epow d : ℝ)
        * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖
      ≤ (2 * Real.exp (-(2 * Real.pi * τ.im)))
        * (Cz * Real.exp (-(2 * Real.pi * ζ.im))) ^ (Epow d : ℝ)
        * (Cj * Real.exp (2 * Real.pi * τ.im)) := by
    gcongr
  refine h1.trans ?_
  have hstep : (2 * Real.exp (-(2 * Real.pi * τ.im)))
        * (Cz * Real.exp (-(2 * Real.pi * ζ.im))) ^ (Epow d : ℝ)
        * (Cj * Real.exp (2 * Real.pi * τ.im))
      = 2 * Cz ^ (Epow d : ℝ) * Cj
          * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * ζ.im)) := by
    rw [Real.mul_rpow hCz.le (Real.exp_pos _).le, ← Real.exp_mul]
    rw [show 2 * Real.exp (-(2 * Real.pi * τ.im))
          * (Cz ^ (Epow d : ℝ) * Real.exp (-(2 * Real.pi * ζ.im) * (Epow d : ℝ)))
          * (Cj * Real.exp (2 * Real.pi * τ.im))
        = 2 * Cz ^ (Epow d : ℝ) * Cj
          * (Real.exp (-(2 * Real.pi * τ.im))
            * Real.exp (-(2 * Real.pi * ζ.im) * (Epow d : ℝ))
            * Real.exp (2 * Real.pi * τ.im)) by ring]
    rw [exp3]
    congr 1
    ring
  rw [hstep]
  have hA : (2 * Real.pi * (Epow d : ℝ)) * (τ.im - 29 / 20)
      ≤ (2 * Real.pi * (Epow d : ℝ)) * ζ.im :=
    mul_le_mul_of_nonneg_left hζ (by positivity)
  have hexp : Real.exp (-(2 * Real.pi * (Epow d : ℝ) * ζ.im))
      ≤ Real.exp (-(2 * Real.pi * (Epow d : ℝ) * (τ.im - 29 / 20))) :=
    Real.exp_le_exp.mpr (by nlinarith [hA])
  calc 2 * Cz ^ (Epow d : ℝ) * Cj * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * ζ.im))
      ≤ 2 * Cz ^ (Epow d : ℝ) * Cj
          * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * (τ.im - 29 / 20))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 2 * Cz ^ (Epow d : ℝ) * Cj
          * (Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im))
            * Real.exp (2 * Real.pi * (Epow d : ℝ) * (29 / 20))) := by
        rw [show -(2 * Real.pi * (Epow d : ℝ) * (τ.im - 29 / 20))
            = -(2 * Real.pi * (Epow d : ℝ) * τ.im) + 2 * Real.pi * (Epow d : ℝ) * (29 / 20) by ring,
          Real.exp_add]
    _ = (2 * Cz ^ (Epow d : ℝ) * Cj * Real.exp (2 * Real.pi * (Epow d : ℝ) * (29 / 20)))
          * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)) := by ring_nf

/-- Lower bound for the growth prefactor on the disc. -/
lemma growthPrefactor_lower {d : ℕ} {τ ζ : ℍ} {cd cz P : ℝ} (hcd : 0 < cd) (hcz : 0 < cz)
    (hP : 0 ≤ P)
    (hΔτ : (1 / 2) * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖Work.Kernels.DeltaFun τ‖)
    (hΔζ : (cz * Real.exp (-(2 * Real.pi * ζ.im))) ^ (Epow d : ℝ)
      ≤ ‖Work.Kernels.DeltaFun ζ‖ ^ (Epow d : ℝ))
    (hjj : cd * Real.exp (2 * Real.pi * τ.im) * P
      ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖) :
    (cd * cz ^ (Epow d : ℝ) / 2) * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * ζ.im)) * P
      ≤ ‖Work.Kernels.growthPrefactor d τ ζ‖ := by
  rw [growthPrefactor_eq, norm_mul, norm_mul]
  rw [norm_pow, ← Real.rpow_natCast (‖Work.Kernels.DeltaFun ζ‖) (Epow d)]
  have hstep : (cd * cz ^ (Epow d : ℝ) / 2) * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * ζ.im)) * P
      = ((1 / 2) * Real.exp (-(2 * Real.pi * τ.im)))
        * (cz * Real.exp (-(2 * Real.pi * ζ.im))) ^ (Epow d : ℝ)
        * (cd * Real.exp (2 * Real.pi * τ.im) * P) := by
    rw [Real.mul_rpow hcz.le (Real.exp_pos _).le, ← Real.exp_mul]
    rw [show (1 / 2 * Real.exp (-(2 * Real.pi * τ.im)))
          * (cz ^ (Epow d : ℝ) * Real.exp (-(2 * Real.pi * ζ.im) * (Epow d : ℝ)))
          * (cd * Real.exp (2 * Real.pi * τ.im) * P)
        = (cd * cz ^ (Epow d : ℝ) / 2)
          * (Real.exp (-(2 * Real.pi * τ.im))
            * Real.exp (-(2 * Real.pi * ζ.im) * (Epow d : ℝ))
            * Real.exp (2 * Real.pi * τ.im)) * P by ring_nf]
    rw [exp3]
    congr 1
    ring
  rw [hstep]
  have h1 : ((1 / 2) * Real.exp (-(2 * Real.pi * τ.im)))
        * (cz * Real.exp (-(2 * Real.pi * ζ.im))) ^ (Epow d : ℝ)
      ≤ ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun ζ‖ ^ (Epow d : ℝ) :=
    mul_le_mul hΔτ hΔζ (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
  exact mul_le_mul h1 hjj (mul_nonneg (mul_nonneg hcd.le (Real.exp_pos _).le) hP)
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))

/-- **The sharp ball bound for `K̄`.** -/
lemma KhatClear_ball_decay (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ ζ : ℍ), Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ < 29 / 20 →
      ‖Work.Kernels.KhatClear ℓ d τ ζ‖
        ≤ C * (Work.Kernels.scale τ) ^ N
            * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)) := by
  obtain ⟨C0, N0, H0, hC0, hN0, hH0, hspike⟩ := Khat_spike_circle_high ℓ d hd
  obtain ⟨cz, Cz, hcz, hCz, hΔb⟩ := SpikeCircle.DeltaFunBoundsHalf
  obtain ⟨Cj, hCj, hju⟩ := SpikeCircle.jInvariantFunUpperDisc
  obtain ⟨_, hmono2⟩ := KClear_mg2 ℓ d hd
  obtain ⟨α, Na, Mb, hα, hNa, hMb, hmgb⟩ := hmono2
  set Kbig : ℝ := max
    (C0 * (2 * Cz ^ (Epow d : ℝ) * Cj * Real.exp (2 * Real.pi * (Epow d : ℝ) * (29 / 20))))
    (α * 4 ^ (Mb : ℝ) * Real.exp (2 * Real.pi * (Epow d : ℝ) * H0)) with hKbig
  have hK0 : 0 < Kbig := by
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    exact mul_pos hC0 (by positivity)
  refine ⟨Kbig, max N0 (Na + Mb), hK0, le_max_of_le_left hN0, ?_⟩
  intro τ ζ hτ hdist
  have hτ2 : 2 ≤ τ.im := hτ.2
  have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  by_cases hH : H0 ≤ τ.im
  · -- large height: the maximum modulus principle on the disc
    have hfr : ∀ u ∈ frontier (Metric.ball ((τ : ℂ)) (29 / 20)),
        ‖Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u)‖
          ≤ (C0 * (2 * Cz ^ (Epow d : ℝ) * Cj * Real.exp (2 * Real.pi * (Epow d : ℝ) * (29 / 20))))
            * (Work.Kernels.scale τ) ^ N0
            * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)) := by
      intro u hu
      have hsp : u ∈ Metric.sphere ((τ : ℂ)) (29 / 20) := Metric.frontier_ball_subset_sphere hu
      have hud : ‖u - (τ : ℂ)‖ = 29 / 20 := by
        have hh := Metric.mem_sphere.mp hsp
        rwa [dist_eq_norm] at hh
      have huim : 0 < u.im := by
        have h2 : |u.im - τ.im| ≤ 29 / 20 := by
          have h3 : |(u - (τ : ℂ)).im| ≤ ‖u - (τ : ℂ)‖ := Complex.abs_im_le_norm _
          rw [show (u - (τ : ℂ)).im = u.im - τ.im by simp, hud] at h3
          exact h3
        linarith [(abs_le.mp h2).1, hτ2]
      have hζc : ((⟨u, huim⟩ : ℍ) : ℂ) = u := rfl
      have hζd : ‖((⟨u, huim⟩ : ℍ) : ℂ) - (τ : ℂ)‖ = 29 / 20 := by rw [hζc]; exact hud
      have hjne := disc_jne hτ hζd
      have hΔτ : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)) :=
        DeltaFun_upper_sharp τ (by linarith)
      have hΔζ : ‖Work.Kernels.DeltaFun (⟨u, huim⟩ : ℍ)‖
          ≤ Cz * Real.exp (-(2 * Real.pi * (⟨u, huim⟩ : ℍ).im)) :=
        (hΔb ⟨u, huim⟩ (by have := disc_im_ge hτ2 (le_of_eq hζd); linarith)).2
      have hjj : ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (⟨u, huim⟩ : ℍ)‖
          ≤ Cj * Real.exp (2 * Real.pi * τ.im) := hju τ ⟨u, huim⟩ hτ (le_of_eq hζd)
      have hgpup := growthPrefactor_upper (d := d) hCz hCj hΔτ hΔζ hjj
        (disc_im_lower (le_of_eq hζd))
      have hKup : ‖Work.Kernels.Khat ℓ d τ (⟨u, huim⟩ : ℍ)‖
          ≤ C0 * (Work.Kernels.scale τ) ^ N0 := hspike τ ⟨u, huim⟩ hτ hζd hH
      rw [show UpperHalfPlane.ofComplex u = (⟨u, huim⟩ : ℍ) from
          UpperHalfPlane.ofComplex_apply_of_im_pos huim,
        KhatClear_eq_growthPrefactor_mul ℓ d hd hjne, norm_mul]
      calc ‖Work.Kernels.growthPrefactor d τ (⟨u, huim⟩ : ℍ)‖
            * ‖Work.Kernels.Khat ℓ d τ (⟨u, huim⟩ : ℍ)‖
          ≤ (2 * Cz ^ (Epow d : ℝ) * Cj * Real.exp (2 * Real.pi * (Epow d : ℝ) * (29 / 20)))
              * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im))
              * (C0 * (Work.Kernels.scale τ) ^ N0) :=
            mul_le_mul hgpup hKup (norm_nonneg _) (by positivity)
        _ = (C0 * (2 * Cz ^ (Epow d : ℝ) * Cj * Real.exp (2 * Real.pi * (Epow d : ℝ) * (29 / 20))))
              * (Work.Kernels.scale τ) ^ N0
              * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)) := by ring
    have hmain : ∀ z ∈ closure (Metric.ball ((τ : ℂ)) (29 / 20)),
        ‖Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex z)‖
          ≤ (C0 * (2 * Cz ^ (Epow d : ℝ) * Cj * Real.exp (2 * Real.pi * (Epow d : ℝ) * (29 / 20))))
            * (Work.Kernels.scale τ) ^ N0
            * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)) :=
      fun z hz => Complex.norm_le_of_forall_mem_frontier_norm_le
        (f := fun u : ℂ => Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u))
        (U := Metric.ball ((τ : ℂ)) (29 / 20)) Metric.isBounded_ball
        (diffContOnCl_KhatClear ℓ d hd hτ2) hfr hz
    have hmem : (ζ : ℂ) ∈ Metric.ball ((τ : ℂ)) (29 / 20) := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hdist
    have hres := hmain (ζ : ℂ) (subset_closure hmem)
    rw [UpperHalfPlane.ofComplex_apply] at hres
    refine hres.trans ?_
    have h1 : C0 * (2 * Cz ^ (Epow d : ℝ) * Cj
        * Real.exp (2 * Real.pi * (Epow d : ℝ) * (29 / 20))) ≤ Kbig := by
      rw [hKbig]; exact le_max_left _ _
    have h2 : (Work.Kernels.scale τ) ^ N0 ≤ (Work.Kernels.scale τ) ^ (max N0 (Na + Mb)) :=
      Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_left _ _)
    have hA : C0 * (2 * Cz ^ (Epow d : ℝ) * Cj
          * Real.exp (2 * Real.pi * (Epow d : ℝ) * (29 / 20)))
          * (Work.Kernels.scale τ) ^ N0
        ≤ Kbig * (Work.Kernels.scale τ) ^ (max N0 (Na + Mb)) :=
      mul_le_mul h1 h2 (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _) hK0.le
    exact mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
  · -- small height: the crude two-variable bound
    have hlt : τ.im < H0 := not_le.mp hH
    have hsc : Work.Kernels.scale ζ ≤ 4 * Work.Kernels.scale τ := disc_scale_le hτ2 (le_of_lt hdist)
    have hnum : ‖Work.Kernels.KhatClear ℓ d τ ζ‖
        ≤ α * (Work.Kernels.scale τ) ^ Na * (4 * Work.Kernels.scale τ) ^ Mb := by
      refine (hmgb τ ζ).trans ?_
      have hinner : (Work.Kernels.scale ζ) ^ Mb ≤ (4 * Work.Kernels.scale τ) ^ Mb :=
        Real.rpow_le_rpow (Work.Kernels.scale_pos ζ).le hsc hMb
      exact mul_le_mul_of_nonneg_left hinner
        (mul_nonneg hα (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _))
    have h4pow : (4 * Work.Kernels.scale τ) ^ Mb
        = 4 ^ Mb * (Work.Kernels.scale τ) ^ Mb :=
      Real.mul_rpow (by norm_num) (Work.Kernels.scale_pos τ).le
    have hpowadd : (Work.Kernels.scale τ) ^ Na * (Work.Kernels.scale τ) ^ Mb
        = (Work.Kernels.scale τ) ^ (Na + Mb) :=
      (Real.rpow_add (Work.Kernels.scale_pos τ) Na Mb).symm
    have hnum' : α * (Work.Kernels.scale τ) ^ Na * (4 * Work.Kernels.scale τ) ^ Mb
        = α * 4 ^ (Mb : ℝ) * (Work.Kernels.scale τ) ^ (Na + Mb) := by
      rw [h4pow, ← hpowadd]; ring
    have h5 : α * 4 ^ (Mb : ℝ) * Real.exp (2 * Real.pi * (Epow d : ℝ) * H0) ≤ Kbig := by
      rw [hKbig]; exact le_max_right _ _
    have hfac : (1 : ℝ) ≤ Real.exp (2 * Real.pi * (Epow d : ℝ) * H0)
        * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      rw [show 2 * Real.pi * (Epow d : ℝ) * H0 + -(2 * Real.pi * (Epow d : ℝ) * τ.im)
          = (2 * Real.pi * (Epow d : ℝ)) * (H0 - τ.im) by ring]
      exact mul_nonneg (by positivity) (by linarith)
    have hNaMb : (Work.Kernels.scale τ) ^ (Na + Mb)
        ≤ (Work.Kernels.scale τ) ^ (max N0 (Na + Mb)) :=
      Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_right _ _)
    have hmid : α * 4 ^ (Mb : ℝ) * (Work.Kernels.scale τ) ^ (Na + Mb)
        ≤ α * 4 ^ (Mb : ℝ)
          * ((Real.exp (2 * Real.pi * (Epow d : ℝ) * H0)
              * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)))
            * (Work.Kernels.scale τ) ^ (Na + Mb)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc (Work.Kernels.scale τ) ^ (Na + Mb)
          = 1 * (Work.Kernels.scale τ) ^ (Na + Mb) := by rw [one_mul]
        _ ≤ (Real.exp (2 * Real.pi * (Epow d : ℝ) * H0)
              * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)))
            * (Work.Kernels.scale τ) ^ (Na + Mb) :=
            mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _)
    calc ‖Work.Kernels.KhatClear ℓ d τ ζ‖
        ≤ α * (Work.Kernels.scale τ) ^ Na * (4 * Work.Kernels.scale τ) ^ Mb := hnum
      _ = α * 4 ^ (Mb : ℝ) * (Work.Kernels.scale τ) ^ (Na + Mb) := hnum'
      _ ≤ α * 4 ^ (Mb : ℝ) * ((Real.exp (2 * Real.pi * (Epow d : ℝ) * H0)
              * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)))
            * (Work.Kernels.scale τ) ^ (Na + Mb)) := hmid
      _ = (α * 4 ^ (Mb : ℝ) * Real.exp (2 * Real.pi * (Epow d : ℝ) * H0))
            * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im))
            * (Work.Kernels.scale τ) ^ (Na + Mb) := by ring
      _ ≤ Kbig * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im))
            * (Work.Kernels.scale τ) ^ (Na + Mb) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le)
            (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _)
      _ ≤ Kbig * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im))
            * (Work.Kernels.scale τ) ^ (max N0 (Na + Mb)) :=
          mul_le_mul_of_nonneg_left hNaMb (by positivity)
      _ = Kbig * (Work.Kernels.scale τ) ^ (max N0 (Na + Mb))
            * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)) := by ring

/-- `scale (S • w) ≤ 3 scale w` on the cusp-`0` tile `E`. -/
lemma scale_S_smul_le_of_mem_KEpsilon {w : ℍ} (hw : w ∈ KEpsilon) :
    Work.Kernels.scale (ModularGroup.S • w) ≤ 3 * Work.Kernels.scale w := by
  have hnormS : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ = (‖(w : ℂ)‖)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [norm_inv]
  have him : 2 * ‖(w : ℂ)‖ ^ 2 ≤ w.im := by
    have hS : 2 ≤ (ModularGroup.S • w).im := hw.2
    rw [E_S_im] at hS
    have hn : 0 < ‖(w : ℂ)‖ ^ 2 := pow_pos (E_norm_pos w) 2
    rw [le_div_iff₀ hn] at hS
    linarith
  have h1 : Work.Kernels.scale (ModularGroup.S • w)
      = 1 + ‖(w : ℂ)‖ ^ 2 / w.im + (‖(w : ℂ)‖)⁻¹ := by
    rw [Work.Kernels.scale, E_S_im, inv_div, hnormS]
  have h2 : ‖(w : ℂ)‖ ^ 2 / w.im ≤ 1 / 2 := by
    rw [div_le_iff₀ w.im_pos]; linarith
  have h3 : (‖(w : ℂ)‖)⁻¹ ≤ Work.Kernels.scale w :=
    le_trans (inv_anti₀ w.im_pos (Work.Kernels.im_le_coe_norm w)) (Work.Kernels.inv_im_le_scale w)
  have h4 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  rw [h1]
  linarith

/-- **The `K̂` window bound in the funnel picture.** -/
lemma Khat_window_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t),
      Funnel τ → τ.im - 1 ≤ t → t ≤ τ.im + 1 →
      ‖Work.Kernels.Khat ℓ d τ (Work.Kernels.imagAxis t ht)‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨Cb, Nb, hCb, hNb, hball⟩ := KhatClear_ball_decay ℓ d hd
  obtain ⟨cd, hcd, hdiv⟩ := SpikeCircle.divisorLowerDisc
  obtain ⟨cz, Cz, hcz, hCz, hΔb⟩ := SpikeCircle.DeltaFunBoundsHalf
  obtain ⟨C24, N24, hC24, hN24, hdiag⟩ := Funnel_Kfun_diag_bound ℓ 24 (Or.inr rfl)
  have hE0 : (0 : ℝ) < (Epow d : ℝ) := Epow_pos d
  set δ : ℝ := (29 / 20) * (9 / 20) * (9 / 20) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; norm_num
  set Cf : ℝ := Cb * 2 * Real.exp (2 * Real.pi * (Epow d : ℝ)) / (δ * cd * cz ^ (Epow d : ℝ))
    with hCf
  have hCf0 : 0 < Cf := by
    rw [hCf]
    exact div_pos (mul_pos (mul_pos hCb (by norm_num)) (Real.exp_pos _))
      (mul_pos (mul_pos hδ0 hcd) (Real.rpow_pos_of_pos hcz _))
  set Cw : ℝ := max Cf C24 with hCw
  refine ⟨Cw, max Nb N24, lt_max_of_lt_left hCf0, le_max_of_le_left hNb, ?_⟩
  intro τ t ht hτ h1 h2
  have hτre : |τ.re| < 1 := Funnel.re_abs_lt_one hτ
  have hτ2 : 2 ≤ τ.im := hτ.2
  have hdist : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (τ : ℂ)‖ < 29 / 20 :=
    imagAxis_dist_lt ht hτre h1 h2
  have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  set ζ : ℍ := Work.Kernels.imagAxis t ht with hζdef
  have hζcoe : (ζ : ℂ) = (t : ℂ) * Complex.I := rfl
  have hζim : ζ.im = t := by simp [hζdef, Work.Kernels.imagAxis]
  have hζre : (ζ : ℂ).re = 0 := by rw [hζcoe]; simp
  have hτre_ne_one : τ.re ≠ 1 := ne_of_lt (abs_lt.mp hτre).2
  have hτre_ne_neg_one : τ.re ≠ -1 := ne_of_gt (abs_lt.mp hτre).1
  by_cases hcoin : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun ζ
  · -- the coincidence case
    rcases (SpikeCircle.jInvariantFun_eq_iff_disc hτ (le_of_lt hdist)).mp hcoin with h | h | h
    · -- `ζ = τ`, so `τ` is purely imaginary
      have h0 : Work.Kernels.Khat ℓ d τ ζ = Work.Kernels.Khat ℓ d τ τ := by rw [h]
      rw [h0]
      rcases hd with rfl | rfl
      · have hz : Work.Kernels.Khat ℓ 8 τ τ = 0 := by
          rw [Work.Kernels.Khat_eq, Work.Asymptotics.MiddleRange.KPlus_eight_eq_zero rfl,
            Work.Asymptotics.MiddleRange.KMinus_eq_zero_of_coincidence ℓ (Or.inl rfl) rfl]
          ring
        rw [hz, norm_zero]
        exact mul_nonneg (le_of_lt (lt_of_lt_of_le hCf0 (le_max_left _ _)))
          (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _)
      · have hτre0 : τ.re = 0 := by
          have h2' : (τ : ℂ) = (t : ℂ) * Complex.I := by rw [← hζcoe, h]
          have h3 : (τ : ℂ).re = 0 := by rw [h2']; simp
          rwa [UpperHalfPlane.coe_re] at h3
        have hKH : Work.Kernels.Khat ℓ 24 τ τ = Work.Kernels.Kfun ℓ 24 τ τ := by
          rw [Work.Kernels.Khat_eq, Work.Kernels.Kfun_eq,
            Work.Asymptotics.MiddleRange.KMinus_eq_zero_of_coincidence ℓ (Or.inr rfl) rfl]
          ring
        rw [hKH]
        have h4 : C24 ≤ Cw := by rw [hCw]; exact le_max_right _ _
        have h5 : (Work.Kernels.scale τ) ^ N24 ≤ (Work.Kernels.scale τ) ^ (max Nb N24) :=
          Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_right _ _)
        exact (hdiag τ hτre0 hτ2).trans (mul_le_mul h4 h5
          (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _) (le_trans hC24.le h4))
    · exfalso
      have h2' : (ζ : ℂ) = (τ : ℂ) + 1 := by rw [h, UpperHalfPlane.coe_vadd]; push_cast; ring
      have h3 : (ζ : ℂ).re = τ.re + 1 := by
        rw [h2', Complex.add_re, UpperHalfPlane.coe_re]
        norm_num
      rw [hζre] at h3
      exact hτre_ne_neg_one (by linarith)
    · exfalso
      have h2' : (ζ : ℂ) = (τ : ℂ) - 1 := by rw [h, UpperHalfPlane.coe_vadd]; push_cast; ring
      have h3 : (ζ : ℂ).re = τ.re - 1 := by
        rw [h2', Complex.sub_re, UpperHalfPlane.coe_re]
        norm_num
      rw [hζre] at h3
      exact hτre_ne_one (by linarith)
  · -- the generic case
    set M : ℝ := Cb * (Work.Kernels.scale τ) ^ Nb
      * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)) with hMdef
    have hM0 : 0 ≤ M := by rw [hMdef]; positivity
    set P : ℝ := ‖(ζ : ℂ) - (τ : ℂ)‖ * ‖(ζ : ℂ) - ((τ : ℂ) - 1)‖ * ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖
      with hPdef
    have hPpos : 0 < P := by
      have h1' : (0 : ℝ) < ‖(ζ : ℂ) - (τ : ℂ)‖ := by
        rw [norm_pos_iff]
        intro hh
        exact hcoin (by rw [UpperHalfPlane.ext (sub_eq_zero.mp hh)])
      have h2' : (0 : ℝ) < ‖(ζ : ℂ) - ((τ : ℂ) - 1)‖ := by
        rw [norm_pos_iff]
        intro hh
        have he : (ζ : ℂ) = (τ : ℂ) - 1 := sub_eq_zero.mp hh
        have hre : (0 : ℝ) = τ.re - 1 := by
          have h1'' := congrArg Complex.re he
          rw [hζre, Complex.sub_re, UpperHalfPlane.coe_re] at h1''
          norm_num at h1''
          exact h1''
        exact hτre_ne_one (by linarith)
      have h3' : (0 : ℝ) < ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖ := by
        rw [norm_pos_iff]
        intro hh
        have he : (ζ : ℂ) = (τ : ℂ) + 1 := sub_eq_zero.mp hh
        have hre : (0 : ℝ) = τ.re + 1 := by
          have h1'' := congrArg Complex.re he
          rw [hζre, Complex.add_re, UpperHalfPlane.coe_re] at h1''
          norm_num at h1''
          exact h1''
        exact hτre_ne_neg_one (by linarith)
      rw [hPdef]; positivity
    have hbd : ∀ z ∈ Metric.ball ((τ : ℂ)) (29 / 20),
        ‖Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex z)‖ ≤ M := by
      intro z hz
      have hz' : ‖((UpperHalfPlane.ofComplex z : ℍ) : ℂ) - (τ : ℂ)‖ < 29 / 20 := by
        have hh := Metric.mem_ball.mp hz
        rw [dist_eq_norm] at hh
        have hz1 : 0 < z.im := by
          have h2'' : |z.im - τ.im| ≤ 29 / 20 := by
            have h3'' : |(z - (τ : ℂ)).im| ≤ ‖z - (τ : ℂ)‖ := Complex.abs_im_le_norm _
            have h4'' : |(z - (τ : ℂ)).im| = |z.im - τ.im| := by
              rw [Complex.sub_im, UpperHalfPlane.coe_im]
            rw [h4''] at h3''
            exact le_trans h3'' hh.le
          linarith [(abs_le.mp h2'').1, hτ2]
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz1, UpperHalfPlane.coe_mk]
        exact hh
      exact hball τ (UpperHalfPlane.ofComplex z) hτ hz'
    have hz1 : (fun u : ℂ => Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u)) (τ : ℂ) = 0 := by
      show Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex (τ : ℂ)) = 0
      rw [UpperHalfPlane.ofComplex_apply]
      exact KhatClear_self_zero ℓ d hd τ
    have hofm1 : UpperHalfPlane.ofComplex ((τ : ℂ) - 1) = ((-1 : ℝ) +ᵥ τ) := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by
            have hh : ((τ : ℂ) - 1).im = τ.im := by
              rw [Complex.sub_im, UpperHalfPlane.coe_im]
              norm_num
            rw [hh]; exact τ.im_pos),
        UpperHalfPlane.coe_vadd]
      push_cast; ring
    have hofp1 : UpperHalfPlane.ofComplex ((τ : ℂ) + 1) = ((1 : ℝ) +ᵥ τ) := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by
            have hh : ((τ : ℂ) + 1).im = τ.im := by
              rw [Complex.add_im, UpperHalfPlane.coe_im]
              norm_num
            rw [hh]; exact τ.im_pos),
        UpperHalfPlane.coe_vadd]
      push_cast; ring
    have hz2 : (fun u : ℂ => Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u)) ((τ : ℂ) - 1) = 0 := by
      show Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex ((τ : ℂ) - 1)) = 0
      rw [hofm1]
      have hh := KhatClear_vadd_one_zero ℓ d hd ((-1 : ℝ) +ᵥ τ)
      rwa [show ((1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ)) = τ from by rw [← add_vadd]; norm_num] at hh
    have hz3 : (fun u : ℂ => Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u)) ((τ : ℂ) + 1) = 0 := by
      show Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex ((τ : ℂ) + 1)) = 0
      rw [hofp1]
      exact KhatClear_vadd_neg_one_zero ℓ d hd τ
    have hne12 : (τ : ℂ) ≠ (τ : ℂ) - 1 := by
      intro hh
      have h2' : (1 : ℂ) = 0 := by
        have := congrArg (fun w : ℂ => w - ((τ : ℂ) - 1)) hh
        ring_nf at this
        exact this
      exact one_ne_zero h2'
    have hne13 : (τ : ℂ) ≠ (τ : ℂ) + 1 := by
      intro hh
      have h2' : (-1 : ℂ) = 0 := by
        have := congrArg (fun w : ℂ => w - ((τ : ℂ) + 1)) hh
        ring_nf at this
        exact this
      norm_num at h2'
    have hne23 : (τ : ℂ) - 1 ≠ (τ : ℂ) + 1 := by
      intro hh
      have h2' : (-2 : ℂ) = 0 := by
        have := congrArg (fun w : ℂ => w - ((τ : ℂ) + 1)) hh
        ring_nf at this
        exact this
      norm_num at h2'
    have hbound : ∀ z ∈ Metric.sphere ((τ : ℂ)) (29 / 20),
        δ ≤ ‖z - (τ : ℂ)‖ * ‖z - ((τ : ℂ) - 1)‖ * ‖z - ((τ : ℂ) + 1)‖ := by
      intro z hz
      have ha : ‖z - (τ : ℂ)‖ = 29 / 20 := by
        have hh := Metric.mem_sphere.mp hz
        rwa [dist_eq_norm] at hh
      exact sphere_prod_lower ha
    have h3z := Analysis.ThreeZeros.three_zeros_bound_ball
      (f := fun u : ℂ => Work.Kernels.KhatClear ℓ d τ (UpperHalfPlane.ofComplex u))
      (c := (τ : ℂ)) (ρ := 29 / 20) (M := M) (δ := δ)
      (by norm_num) hM0 hδ0 (diffContOnCl_KhatClear ℓ d hd hτ2) hbd
      hne12 hne13 hne23 hz1 hz2 hz3 hbound
    have hballmem : (ζ : ℂ) ∈ Metric.ball ((τ : ℂ)) (29 / 20) := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hdist
    have h3 := h3z (ζ : ℂ) hballmem
    rw [UpperHalfPlane.ofComplex_apply] at h3
    have h3' : ‖Work.Kernels.KhatClear ℓ d τ ζ‖ ≤ (M / δ) * P := by
      refine h3.trans (le_of_eq ?_)
      rw [hPdef]; ring
    -- the divisor lower bound
    have hΔτ : (1 / 2) * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖Work.Kernels.DeltaFun τ‖ :=
      DeltaFun_funnel_lower_sharp hτ2
    have hζhalf : (1 : ℝ) / 2 ≤ ζ.im := by rw [hζim]; linarith
    have hΔζ : (cz * Real.exp (-(2 * Real.pi * ζ.im))) ^ (Epow d : ℝ)
        ≤ ‖Work.Kernels.DeltaFun ζ‖ ^ (Epow d : ℝ) :=
      Real.rpow_le_rpow (by positivity) (hΔb ζ hζhalf).1 (by positivity)
    have hjj : cd * Real.exp (2 * Real.pi * τ.im) * P
        ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := by
      have hh := hdiv τ ζ hτ (le_of_lt hdist)
      rw [norm_mul, norm_mul] at hh
      rw [hPdef]
      exact hh
    have hlow : (cd * cz ^ (Epow d : ℝ) / 2) * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * ζ.im)) * P
        ≤ ‖Work.Kernels.growthPrefactor d τ ζ‖ :=
      growthPrefactor_lower (d := d) hcd hcz hPpos.le hΔτ hΔζ hjj
    have hlow' : (cd * cz ^ (Epow d : ℝ) / 2) * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * t)) * P
        ≤ ‖Work.Kernels.growthPrefactor d τ ζ‖ := by
      rwa [hζim] at hlow
    have hDpos : 0 < (cd * cz ^ (Epow d : ℝ) / 2) * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * t)) * P :=
      mul_pos (mul_pos (div_pos (mul_pos hcd (Real.rpow_pos_of_pos hcz _)) (by norm_num))
        (Real.exp_pos _)) hPpos
    have hstep : ‖Work.Kernels.KhatClear ℓ d τ ζ‖ / ‖Work.Kernels.growthPrefactor d τ ζ‖
        ≤ ((M / δ) * P)
          / ((cd * cz ^ (Epow d : ℝ) / 2) * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * t)) * P) :=
      div_le_div₀ (mul_nonneg (div_nonneg hM0 hδ0.le) hPpos.le) h3' hDpos hlow'
    have hexp : Real.exp (2 * Real.pi * (Epow d : ℝ) * t)
          * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im))
        ≤ Real.exp (2 * Real.pi * (Epow d : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hA : (2 * Real.pi * (Epow d : ℝ)) * t ≤ (2 * Real.pi * (Epow d : ℝ)) * (τ.im + 1) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith [hA]
    have hE : Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im))
        ≤ Real.exp (2 * Real.pi * (Epow d : ℝ)) * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * t)) := by
      have h1 : Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im))
          * Real.exp (2 * Real.pi * (Epow d : ℝ) * t) ≤ Real.exp (2 * Real.pi * (Epow d : ℝ)) := by
        rw [mul_comm]; exact hexp
      have h2 := (le_div_iff₀ (Real.exp_pos (2 * Real.pi * (Epow d : ℝ) * t))).mpr h1
      rw [div_eq_mul_inv, ← Real.exp_neg] at h2
      exact h2
    have hδne : δ ≠ 0 := hδ0.ne'
    have hcdne : cd ≠ 0 := hcd.ne'
    have hczne : cz ^ (Epow d : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hcz _).ne'
    have hsc : M / δ ≤ Cf * (Work.Kernels.scale τ) ^ Nb
        * (cd * cz ^ (Epow d : ℝ) / 2) * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * t)) := by
      rw [hMdef, hCf]
      calc Cb * (Work.Kernels.scale τ) ^ Nb
              * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)) / δ
          = (Cb / δ) * (Work.Kernels.scale τ) ^ Nb
              * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * τ.im)) := by ring
        _ ≤ (Cb / δ) * (Work.Kernels.scale τ) ^ Nb
              * (Real.exp (2 * Real.pi * (Epow d : ℝ))
                * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * t))) :=
            mul_le_mul_of_nonneg_left hE (by positivity)
        _ = (Cb * 2 * Real.exp (2 * Real.pi * (Epow d : ℝ)) / (δ * cd * cz ^ (Epow d : ℝ)))
              * (Work.Kernels.scale τ) ^ Nb * (cd * cz ^ (Epow d : ℝ) / 2)
              * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * t)) := by
            field_simp
    have hgoal : (M / δ) * P
          / ((cd * cz ^ (Epow d : ℝ) / 2) * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * t)) * P)
        ≤ Cf * (Work.Kernels.scale τ) ^ Nb := by
      rw [div_le_iff₀ hDpos]
      rw [show Cf * (Work.Kernels.scale τ) ^ Nb
            * ((cd * cz ^ (Epow d : ℝ) / 2) * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * t)) * P)
          = (Cf * (Work.Kernels.scale τ) ^ Nb * (cd * cz ^ (Epow d : ℝ) / 2)
              * Real.exp (-(2 * Real.pi * (Epow d : ℝ) * t))) * P from by ring]
      exact mul_le_mul_of_nonneg_right hsc hPpos.le
    have h4 : Cf ≤ Cw := by rw [hCw]; exact le_max_left _ _
    have h5 : (Work.Kernels.scale τ) ^ Nb ≤ (Work.Kernels.scale τ) ^ (max Nb N24) :=
      Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_left _ _)
    rw [norm_Khat_eq ℓ d hd hcoin]
    exact hstep.trans (hgoal.trans (mul_le_mul h4 h5
      (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _) (le_trans hCf0.le h4)))

/-- **The CKMRV kernel on `E` in the two-unit window around the pole height.**

For `w ∈ E = KEpsilon` and `Im (S • w) - 1 ≤ t ≤ Im (S • w) + 1`, the kernel is bounded by
`C (scale w)^N (1+t)^M (1 + e^{2πt})`.  This is the "top interval" brick of `E_window_exp`
(whose range `1 ≤ t ≤ Im(S•w)+1` splits as `[1, Im-1] ∪ [Im-1, Im+1]`), with a deliberate
overlap; the factor `1 + e^{2πt}` is essential for `d = 24`.-/
theorem EWindow_pole (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (ModularGroup.S • w).im - 1 ≤ t →
        t ≤ (ModularGroup.S • w).im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
              * (1 + Real.exp (2 * Real.pi * t)) := by
  obtain ⟨Cw, Nw, hCw, hNw, hwin⟩ := Khat_window_bound ℓ d hd
  have hd2 : ((d : ℤ) / 2) = ((d / 2 : ℕ) : ℤ) := by
    rcases hd with rfl | rfl <;> norm_num
  refine ⟨Cw * 3 ^ (d / 2) * 3 ^ Nw, Nw + ((d / 2 : ℕ) : ℝ), Nw + ((d / 2 : ℕ) : ℝ),
    by positivity, by positivity, by positivity, ?_⟩
  intro w t hw h1 h2
  have ht : 0 < t := by have h := hw.2; linarith
  have hτ : Funnel (ModularGroup.S • w) := S_smul_mem_funnel hw
  have hK := Kfun_S_smul ℓ d hd (ModularGroup.S • w) (Work.Kernels.imagAxis t ht)
  rw [S_smul_S_smul] at hK
  have hwin' := hwin (ModularGroup.S • w) t ht hτ h1 h2
  have hnormτ : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 3 * Work.Kernels.scale w :=
    le_trans (Work.Kernels.coe_norm_le_scale _) (scale_S_smul_le_of_mem_KEpsilon hw)
  have hsm : ‖((ModularGroup.S • w : ℍ) : ℂ) ^ ((d : ℤ) / 2)‖
      = ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ^ (d / 2) := by
    rw [norm_zpow, hd2, zpow_natCast]
  rw [Work.Kernels.Kaxis, dif_pos ht, hK, norm_mul, norm_neg, hsm]
  calc ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ^ (d / 2)
        * ‖Work.Kernels.Khat ℓ d (ModularGroup.S • w) (Work.Kernels.imagAxis t ht)‖
      ≤ (3 * Work.Kernels.scale w) ^ (d / 2)
          * (Cw * (Work.Kernels.scale (ModularGroup.S • w)) ^ Nw) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnormτ (d / 2)) hwin' (norm_nonneg _)
          (pow_nonneg (mul_nonneg (by norm_num) (Work.Kernels.scale_pos w).le) _)
    _ ≤ (3 * Work.Kernels.scale w) ^ (d / 2) * (Cw * (3 * Work.Kernels.scale w) ^ Nw) := by
        have h2' : (Work.Kernels.scale (ModularGroup.S • w)) ^ Nw ≤ (3 * Work.Kernels.scale w) ^ Nw :=
          Real.rpow_le_rpow (Work.Kernels.scale_pos _).le (scale_S_smul_le_of_mem_KEpsilon hw) hNw
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2' hCw.le)
          (pow_nonneg (mul_nonneg (by norm_num) (Work.Kernels.scale_pos w).le) _)
    _ = Cw * 3 ^ (d / 2) * 3 ^ Nw * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ)) := by
        have hx : (Work.Kernels.scale w) ^ (d / 2) * (Work.Kernels.scale w) ^ Nw
            = (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast (Work.Kernels.scale w) (d / 2),
            ← Real.rpow_add (Work.Kernels.scale_pos w)]
          congr 1
          ring
        rw [mul_pow, Real.mul_rpow (by norm_num) (Work.Kernels.scale_pos w).le]
        rw [show 3 ^ (d / 2) * (Work.Kernels.scale w) ^ (d / 2)
              * (Cw * (3 ^ Nw * (Work.Kernels.scale w) ^ Nw))
            = (3 ^ (d / 2) * 3 ^ Nw * Cw)
              * ((Work.Kernels.scale w) ^ (d / 2) * (Work.Kernels.scale w) ^ Nw) by ring]
        rw [hx]
        ring
    _ ≤ Cw * 3 ^ (d / 2) * 3 ^ Nw * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ))
          * (1 + t) ^ (Nw + ((d / 2 : ℕ) : ℝ)) * (1 + Real.exp (2 * Real.pi * t)) := by
        have hY : (1 : ℝ) ≤ (1 + t) ^ (Nw + ((d / 2 : ℕ) : ℝ)) :=
          Real.one_le_rpow (by linarith) (add_nonneg hNw (Nat.cast_nonneg _))
        have hZ : (1 : ℝ) ≤ 1 + Real.exp (2 * Real.pi * t) := by
          have := Real.exp_pos (2 * Real.pi * t); linarith
        have hX : 0 ≤ Cw * 3 ^ (d / 2) * 3 ^ Nw
            * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ)) :=
          mul_nonneg (mul_nonneg (mul_nonneg hCw.le (pow_nonneg (by norm_num) _))
            (Real.rpow_pos_of_pos (by norm_num) Nw).le)
            (Real.rpow_pos_of_pos (Work.Kernels.scale_pos w) _).le
        have hYZ : (1 : ℝ) ≤ (1 + t) ^ (Nw + ((d / 2 : ℕ) : ℝ))
            * (1 + Real.exp (2 * Real.pi * t)) := by
          have h1 := mul_le_mul hY hZ (by norm_num : (0 : ℝ) ≤ 1)
            (by linarith : (0 : ℝ) ≤ (1 + t) ^ (Nw + ((d / 2 : ℕ) : ℝ)))
          simpa using h1
        calc Cw * 3 ^ (d / 2) * 3 ^ Nw * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ))
            = (Cw * 3 ^ (d / 2) * 3 ^ Nw
                * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ))) * 1 := by ring
          _ ≤ (Cw * 3 ^ (d / 2) * 3 ^ Nw
                * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ)))
                * ((1 + t) ^ (Nw + ((d / 2 : ℕ) : ℝ)) * (1 + Real.exp (2 * Real.pi * t))) :=
              mul_le_mul_of_nonneg_left hYZ hX
          _ = Cw * 3 ^ (d / 2) * 3 ^ Nw * (Work.Kernels.scale w) ^ (Nw + ((d / 2 : ℕ) : ℝ))
                * (1 + t) ^ (Nw + ((d / 2 : ℕ) : ℝ)) * (1 + Real.exp (2 * Real.pi * t)) := by ring

end

end Work.Asymptotics
