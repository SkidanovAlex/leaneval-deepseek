import Mathlib
import Submission.Work.Asymptotics.MFix.Cusp0Flat
import Submission.Work.Asymptotics.MFix.KXiDefs

namespace Work.Asymptotics.HalfFunnel

namespace Work.Asymptotics.HalfFunnel

/-- **The cusp-`0` bound for the CKMRV kernel along the contour, on an arbitrary bounded set of
parameters.**

For any bounded `K ⊆ ℍ` there is `δ > 0` such that for every `N ≥ 0` there is `c > 0` with
`‖Kaxis (Kfun ℓ d) τ t‖ ≤ c · t^N` for all `τ ∈ K` and `0 < t ≤ δ`: the kernel is
"super-polynomially flat" at the cusp `z = 0`, uniformly on bounded parameter sets (the size of
`δ` only has to be small enough that the contour lies below all poles, and the constants are
uniform because every atom of `Kfun` depends continuously on `τ`).

This is the `t → 0` part of `Work.Asymptotics.Kaxis_local_flat` with the hypotheses "`K` compact"
and "`K ⊆ 𝒟`" removed.  The proof of the source statement has two regimes:

* `t ≤ min δ₁ δ₂`: `‖KPlus‖ ≤ C₁ t^{-M₁} e^{-π/t}` and `‖KMinus‖ ≤ C₂ t^{-M₂} e^{-π/t}`
  (`KPlus_cusp_bound`, `KMinus_cusp_bound`: their proofs use only `K ⊆ closedBall i R` and
  boundedness of `j` there, never `hsub` nor the finite-subcover step), combined with
  `exp_neg_div_le_mul_rpow`;
* `min δ₁ δ₂ < t ≤ 1`: the middle-range bound `Kaxis_local_middle`, which *does* use compactness
  and `K ⊆ 𝒟` (its coincidence case needs the classification `z = τ` or `z = Sτ` of the removable
  poles).  That regime is therefore *excluded* here, which is why the conclusion is restricted to
  `t ≤ δ` for a suitable `δ`; the claim below is exactly the part that is uniformly true on
  bounded parameter sets. -/
theorem Kaxis_cusp_of_bounded (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : Bornology.IsBounded K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 0 < t → t ≤ δ →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N := by
  -- Boundedness of `K` puts it inside a ball `closedBall i R'`.
  set τ₁ : UpperHalfPlane := ⟨Complex.I, by simp⟩ with hτ₁
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall τ₁).mp hK
  set R' : ℝ := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hKR : ∀ τ : UpperHalfPlane, τ ∈ K → dist τ τ₁ ≤ R' := fun τ hτ =>
    le_trans (Metric.mem_closedBall.mp (hR hτ)) (le_max_left R 1)
  -- The CKMRV slash bounds (Lemma 4.12) on that ball, for `K_+` and `K_-`.
  obtain ⟨Cp1, hCp1, hslashp⟩ := Work.Asymptotics.MFix.KPlus_slash_ball d hd hR'pos
  obtain ⟨Cm1, hCm1, hslashm⟩ := Work.Asymptotics.MFix.KMinus_slash_ball ℓ d hd hR'pos
  -- `j` is bounded on the ball, and the divisor factor is bounded below by `1/4` far out.
  obtain ⟨M, hMpos, hjM⟩ := Work.Asymptotics.MFix.exists_bound_on_closedBall
    Work.Asymptotics.MFix.continuous_jInvariantFun τ₁ R'
  obtain ⟨Y, hYpos, hdiv⟩ := Work.Asymptotics.MFix.divisor_factor_lower M hMpos.le
  -- The cusp bounds `‖K_±‖ ≤ C t^{-M} e^{-π/t}` on the ball.
  obtain ⟨Cp2, Mp, δp, hCp2, hMp, hδp, hbp⟩ := Work.Asymptotics.MFix.cusp_bound_of_slash
    (Work.Kernels.KPlus d) d hd hCp1.le hslashp (fun τ hτ => hjM τ hτ) hYpos hdiv
  obtain ⟨Cm2, Mm, δm, hCm2, hMm, hδm, hbm⟩ := Work.Asymptotics.MFix.cusp_bound_of_slash
    (Work.Kernels.KMinus ℓ d) d hd hCm1.le hslashm (fun τ hτ => hjM τ hτ) hYpos hdiv
  refine ⟨min (min δp δm) 1, lt_min (lt_min hδp hδm) one_pos, fun N hN => ?_⟩
  -- Exponential decay dominates every power.
  obtain ⟨Kp, hKp, hbKp⟩ := Work.Asymptotics.MFix.rpow_neg_mul_exp_le Mp N
  obtain ⟨Km, hKm, hbKm⟩ := Work.Asymptotics.MFix.rpow_neg_mul_exp_le Mm N
  refine ⟨Cp2 * Kp + Cm2 * Km, by positivity, fun τ t hτ ht htδ => ?_⟩
  have htδp : t ≤ δp := le_trans htδ (le_trans (min_le_left (min δp δm) 1) (min_le_left δp δm))
  have htδm : t ≤ δm := le_trans htδ (le_trans (min_le_left (min δp δm) 1) (min_le_right δp δm))
  have ht1 : t ≤ 1 := le_trans htδ (min_le_right (min δp δm) 1)
  have hb1 := hbp τ t ht (hKR τ hτ) htδp
  have hb2 := hbm τ t ht (hKR τ hτ) htδm
  rw [Work.Kernels.Kaxis, dif_pos ht]
  have hsplit : ‖Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)‖ ≤
      (‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖ +
        ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖) / 2 := by
    rw [Work.Kernels.Kfun, norm_div, show ‖((2 : ℂ))‖ = 2 from by norm_num]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  have h1 : ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖ ≤ Cp2 * Kp * t ^ N := by
    refine le_trans hb1 ?_
    calc Cp2 * t ^ (-Mp) * Real.exp (-(Real.pi / t))
        = Cp2 * (t ^ (-Mp) * Real.exp (-(Real.pi / t))) := by ring
      _ ≤ Cp2 * (Kp * t ^ N) := mul_le_mul_of_nonneg_left (hbKp t ht ht1) hCp2.le
      _ = Cp2 * Kp * t ^ N := by ring
  have h2 : ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖ ≤ Cm2 * Km * t ^ N := by
    refine le_trans hb2 ?_
    calc Cm2 * t ^ (-Mm) * Real.exp (-(Real.pi / t))
        = Cm2 * (t ^ (-Mm) * Real.exp (-(Real.pi / t))) := by ring
      _ ≤ Cm2 * (Km * t ^ N) := mul_le_mul_of_nonneg_left (hbKm t ht ht1) hCm2.le
      _ = Cm2 * Km * t ^ N := by ring
  have hfin : (‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖ +
        ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖) / 2 ≤
      (Cp2 * Kp + Cm2 * Km) * t ^ N := by
    have h3 : (‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖ +
          ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖) / 2 ≤
        (Cp2 * Kp * t ^ N + Cm2 * Km * t ^ N) / 2 :=
      div_le_div_of_nonneg_right (add_le_add h1 h2) (by norm_num)
    have hNn : 0 ≤ t ^ N := Real.rpow_nonneg ht.le N
    have h5 : (Cp2 * Kp * t ^ N + Cm2 * Km * t ^ N) / 2
        ≤ Cp2 * Kp * t ^ N + Cm2 * Km * t ^ N := by
      have ha : 0 ≤ Cp2 * Kp * t ^ N := mul_nonneg (mul_nonneg hCp2.le hKp.le) hNn
      have hb : 0 ≤ Cm2 * Km * t ^ N := mul_nonneg (mul_nonneg hCm2.le hKm.le) hNn
      linarith
    have h6 : Cp2 * Kp * t ^ N + Cm2 * Km * t ^ N = (Cp2 * Kp + Cm2 * Km) * t ^ N := by ring
    linarith [h3, h5, h6.le, h6.ge]
  linarith [hsplit, hfin]

end Work.Asymptotics.HalfFunnel

/-- **The cusp-`0` bound for the CKMRV kernel along the contour, on an arbitrary bounded set of
parameters** — the same statement as
`Work.Asymptotics.HalfFunnel.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded`, restated at the
namespace level `Work.Asymptotics.HalfFunnel` recorded for this module. -/
theorem Kaxis_cusp_of_bounded (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : Bornology.IsBounded K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 0 < t → t ≤ δ →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N :=
  _root_.Work.Asymptotics.HalfFunnel.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded ℓ d hd hK

end Work.Asymptotics.HalfFunnel
