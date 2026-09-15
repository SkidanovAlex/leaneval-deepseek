import Submission.FUP.ModifyWeightAssemble
import Submission.Commons.Analysis.Calculus.sphProj_second_deriv_identity

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Section 4 of the paper, VII: the cancellation identity `∫_ℝ⟨D²ω̃_k(ty)v,v⟩dt = 2q_k`

This is the identity at the heart of §4 of Cohen's paper: because the modified pieces are
designed so that `π_{S^{d-1}} ω̃_k ≡ q_k` is *constant* on the unit sphere, Lemma
`lem:second_deriv_spherical_prj` (our `Commons.Analysis.Calculus.sphProj_second_deriv_identity`)
gives

  `∫_0^∞ ⟨D²ω̃_k(ty)v,v⟩ dt = π ω̃_k(y) + d²/dθ²|_0 π ω̃_k(ycos θ + v sin θ) = q_k`,

the second term vanishing because `π ω̃_k` is constant on the sphere, and applying the same
identity to `-y` gives the other half-line, so that

  `∫_ℝ ⟨D²ω̃_k(ty)v,v⟩ dt = 2 q_k`.

This is the only step of §4 where the *design* of the correction `g_k` (rather than its size) is
used; the absolute values `∑_k |q_k| ≲ C_gr` are estimated in `GrowthSum.lean`
(`sum_abs_qk_le_growth`).
-/

section Basic

/-- The dyadic pieces of the modified weight are compactly supported (in the annulus
`‖x‖ ≤ 2^{k+1}`). -/
lemma hasCompactSupport_omegaTildePiece (k : ℕ) (w : ℝᵈ → ℝ) :
    HasCompactSupport (omegaTildePiece (d := d) k w) := by
  have hsub : tsupport (omegaTildePiece (d := d) k w) ⊆
      Metric.closedBall (0 : ℝᵈ) ((2 : ℝ) ^ (k + 1)) := by
    rw [tsupport]
    refine closure_minimal ?_ (isClosed_closedBall)
    intro x hx
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_not_gt fun h => hx (omegaTildePiece_eq_zero_of_norm_ge k w h.le)
  exact (isCompact_closedBall (0 : ℝᵈ) _).of_isClosed_subset (isClosed_tsupport _) hsub

/-- All derivatives of `ω̃_k` vanish outside the closed annulus `‖x‖ ≤ 2^{k+1}`. -/
lemma iteratedFDeriv_omegaTildePiece_eq_zero_of_norm_gt (k : ℕ) (w : ℝᵈ → ℝ) {z : ℝᵈ}
    (hz : (2 : ℝ) ^ (k + 1) < ‖z‖) (n : ℕ) :
    iteratedFDeriv ℝ n (omegaTildePiece (d := d) k w) z = 0 := by
  have hε : 0 < ‖z‖ - (2 : ℝ) ^ (k + 1) := sub_pos.mpr hz
  have hev : omegaTildePiece (d := d) k w =ᶠ[𝓝 z] 0 := by
    filter_upwards [Metric.ball_mem_nhds z hε] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    refine omegaTildePiece_eq_zero_of_norm_ge k w ?_
    have hsub : ‖z‖ - ‖y - z‖ ≤ ‖y‖ := by
      have h := dist_triangle z y 0
      simp only [dist_eq_norm, sub_zero] at h
      have h2 : ‖z - y‖ = ‖y - z‖ := norm_sub_rev z y
      linarith
    linarith
  have h1 := (hev.iteratedFDeriv ℝ n).self_of_nhds
  rw [h1]; simp

/-- `‖cos θ • y + sin θ • v‖ = 1` for orthonormal unit vectors `y, v`. -/
lemma norm_cos_smul_add_sin_smul (y v : ℝᵈ) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hperp : inner ℝ y v = 0) (θ : ℝ) : ‖Real.cos θ • y + Real.sin θ • v‖ = 1 := by
  have hsq : ‖Real.cos θ • y + Real.sin θ • v‖ ^ 2 = 1 := by
    rw [norm_add_sq_real]
    have hy2 : ‖Real.cos θ • y‖ ^ 2 = Real.cos θ ^ 2 := by
      rw [norm_smul, hy, mul_one, Real.norm_eq_abs, sq_abs]
    have hv2 : ‖Real.sin θ • v‖ ^ 2 = Real.sin θ ^ 2 := by
      rw [norm_smul, hv, mul_one, Real.norm_eq_abs, sq_abs]
    have hi : inner ℝ (Real.cos θ • y) (Real.sin θ • v) = 0 := by
      simp [inner_smul_left, inner_smul_right, hperp]
    rw [hy2, hv2, hi]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  have hnn := norm_nonneg (Real.cos θ • y + Real.sin θ • v)
  nlinarith [hsq, hnn]

end Basic

section HalfLine

/-- **The cancellation identity on a half-line.**  For `k ≥ 2` and orthonormal `y ⊥ v`,
`∫_0^∞ ⟨D²ω̃_k(ty)v,v⟩dt = q_k`. -/
theorem integral_Ioi_iteratedFDeriv_two_omegaTildePiece (k : ℕ) (hk : 2 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (y v : ℝᵈ) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hperp : inner ℝ y v = 0) :
    (∫ t in Set.Ioi (0 : ℝ),
        (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) (t • y)) (fun _ : Fin 2 => v))
      = qk k w := by
  set f := omegaTildePiece (d := d) k w with hf
  have hk1 : 1 ≤ k := by omega
  have hfcd : ContDiff ℝ 2 f := (contDiff_omegaTildePiece k hw hk1).of_le (by norm_num)
  have hsupp : HasCompactSupport f := hasCompactSupport_omegaTildePiece k w
  have havoid : ∀ x : ℝᵈ, ‖x‖ ≤ 1 → f x = 0 := by
    intro x hx
    refine omegaTildePiece_eq_zero_of_norm_le_pred k hk1 w ?_
    calc ‖x‖ ≤ 1 := hx
      _ ≤ (2 : ℝ) ^ (k - 1) := by
          calc (1 : ℝ) = (2 : ℝ) ^ 0 := (pow_zero 2).symm
            _ ≤ (2 : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hid := Commons.Analysis.Calculus.sphProj_second_deriv_identity f hfcd hsupp havoid y v hy hv hperp
  have hfirst : (∫ t in Set.Ioi (0 : ℝ), f (t • y) * (t ^ 2)⁻¹) = qk k w := by
    have h := sphProj_omegaTilde k hk1 hw.continuous hy
    simp only [sphProj] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [hf, omegaTildePiece_of_le k w hk]
  have hsecond : iteratedDeriv 2 (fun θ : ℝ => ∫ t in Set.Ioi (0 : ℝ),
      f (t • (Real.cos θ • y + Real.sin θ • v)) * (t ^ 2)⁻¹) 0 = 0 := by
    have hconst : (fun θ : ℝ => ∫ t in Set.Ioi (0 : ℝ),
        f (t • (Real.cos θ • y + Real.sin θ • v)) * (t ^ 2)⁻¹) = fun _ => qk k w := by
      funext θ
      have hu : ‖Real.cos θ • y + Real.sin θ • v‖ = 1 :=
        norm_cos_smul_add_sin_smul y v hy hv hperp θ
      have h := sphProj_omegaTilde k hk1 hw.continuous hu
      simp only [sphProj] at h
      rw [← h]
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      rw [hf, omegaTildePiece_of_le k w hk]
    rw [hconst, iteratedDeriv_const]
    norm_num
  rw [hid, hfirst, hsecond, add_zero]

end HalfLine

section FullLine

/-- The integrand `t ↦ ⟨D²ω̃_k(ty)v,v⟩` is continuous. -/
lemma continuous_line_second_deriv (k : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (hk1 : 1 ≤ k)
    (y v : ℝᵈ) :
    Continuous (fun t : ℝ =>
      (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) (t • y)) (fun _ : Fin 2 => v)) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝᵈ) ℝ (fun _ : Fin 2 => v)).continuous.comp
    ((ContDiff.continuous_iteratedFDeriv (𝕜 := ℝ) (f := omegaTildePiece (d := d) k w)
        (n := (3 : ℕ∞ω)) (m := 2) (by norm_num) (contDiff_omegaTildePiece k hw hk1)).comp
      (continuous_id.smul continuous_const))

/-- The integrand `t ↦ ⟨D²ω̃_k(ty)v,v⟩` is compactly supported. -/
lemma hasCompactSupport_line_second_deriv (k : ℕ) (w : ℝᵈ → ℝ) (y v : ℝᵈ) (hy : ‖y‖ = 1) :
    HasCompactSupport (fun t : ℝ =>
      (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) (t • y)) (fun _ : Fin 2 => v)) := by
  have hsub : tsupport (fun t : ℝ =>
      (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) (t • y)) (fun _ : Fin 2 => v)) ⊆
      Set.Icc (-(2 : ℝ) ^ (k + 1)) ((2 : ℝ) ^ (k + 1)) := by
    rw [tsupport]
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    rw [Function.mem_support] at ht
    rw [Set.mem_Icc]
    have hnorm : ‖t • y‖ = |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
    constructor
    · by_contra hc
      push Not at hc
      have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
      have htneg : t < 0 := by linarith
      exact ht (by
        rw [iteratedFDeriv_omegaTildePiece_eq_zero_of_norm_gt k w (z := t • y) (by
          rw [hnorm, abs_of_neg htneg]; linarith) 2]
        simp)
    · by_contra hc
      push Not at hc
      have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
      have htpos : 0 < t := by linarith
      exact ht (by
        rw [iteratedFDeriv_omegaTildePiece_eq_zero_of_norm_gt k w (z := t • y) (by
          rw [hnorm, abs_of_pos htpos]; linarith) 2]
        simp)
  exact (isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hsub

/-- **The cancellation identity of §4.**  For `k ≥ 2` and orthonormal `y ⊥ v`,
`∫_ℝ ⟨D²ω̃_k(ty)v,v⟩ dt = 2 q_k`. -/
theorem integral_iteratedFDeriv_two_omegaTildePiece (k : ℕ) (hk : 2 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (y v : ℝᵈ) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hperp : inner ℝ y v = 0) :
    (∫ t : ℝ,
        (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) (t • y)) (fun _ : Fin 2 => v))
      = 2 * qk k w := by
  have hk1 : 1 ≤ k := by omega
  set G : ℝ → ℝ := fun t : ℝ =>
    (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) (t • y)) (fun _ : Fin 2 => v) with hG
  set G' : ℝ → ℝ := fun t : ℝ =>
    (iteratedFDeriv ℝ 2 (omegaTildePiece (d := d) k w) (t • (-y))) (fun _ : Fin 2 => v) with hG'
  have hGcont : Continuous G := by
    rw [hG]; exact continuous_line_second_deriv k hw hk1 y v
  have hGcs : HasCompactSupport G := by
    rw [hG]; exact hasCompactSupport_line_second_deriv k w y v hy
  have hGint : Integrable G := hGcont.integrable_of_hasCompactSupport hGcs
  have h1 : (∫ t in Set.Ioi (0 : ℝ), G t) = qk k w := by
    rw [hG]
    exact integral_Ioi_iteratedFDeriv_two_omegaTildePiece k hk hw y v hy hv hperp
  have h2 : (∫ t in Set.Ioi (0 : ℝ), G' t) = qk k w := by
    rw [hG']
    exact integral_Ioi_iteratedFDeriv_two_omegaTildePiece k hk hw (-y) v (by simpa using hy)
      hv (by simpa using hperp)
  have h3 : (∫ t in Set.Ioi (0 : ℝ), G' t) = ∫ t in Set.Iic (0 : ℝ), G t := by
    have hneg := integral_comp_neg_Ioi (0 : ℝ) G
    simp only [neg_zero] at hneg
    rw [← hneg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [hG', hG]
    simp only [smul_neg, neg_smul]
  rw [← integral_add_compl measurableSet_Ioi hGint,
    show (Set.Ioi (0 : ℝ))ᶜ = Set.Iic 0 from compl_Ioi, ← h3]
  rw [h2, h1]
  ring

end FullLine


end Submission.FUP
