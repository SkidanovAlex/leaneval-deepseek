import Submission.NBody.MarchalBumpAssembly

/-!
# The two-sided assembly of the symmetric-bump argument

The competitor `γ̃ = bumpCurve m k i₀ δ T λ t₀ γ` is symmetric about the collision time `t₀`; the
symmetric-bump argument therefore runs on both windows `[t₀, t₀ + λT]` and `[t₀ - λT, t₀]`.  The
second window is the first for the reflected curve `u ↦ γ (t₀ - u)` (the derivative relation is
`deriv (γ (t₀ - ·)) u = -deriv γ (t₀ - u)`, and `lagR` is even in the velocity), so one single
window bound suffices.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- `lagR` is even in the velocity. -/
lemma lagR_neg (m : Fin N → ℝ) (hm : ∀ i, 0 ≤ m i) (h : ℝ) (x v : EN E N) :
    lagR m h x (-v) = lagR m h x v := by
  rw [lagR_eq hm, lagR_eq hm]
  congr 2
  rw [show (-v : EN E N) = (-1 : ℝ) • v by rw [neg_one_smul],
    weightedNorm_smul hm, abs_neg, abs_one, one_mul]

/-- The curve reflected about the collision time `t₀`. -/
noncomputable def reflectCurve (γ : ℝ → EN E N) (t₀ : ℝ) : ℝ → EN E N := fun u => γ (t₀ - u)

@[simp] lemma reflectCurve_apply (γ : ℝ → EN E N) (t₀ u : ℝ) :
    reflectCurve γ t₀ u = γ (t₀ - u) := rfl

lemma deriv_reflectCurve (γ : ℝ → EN E N) (t₀ u : ℝ) :
    deriv (reflectCurve γ t₀) u = -deriv γ (t₀ - u) := by
  have h : reflectCurve γ t₀ = fun x : ℝ => γ (t₀ - x) := rfl
  rw [h]
  exact deriv_comp_const_sub γ t₀ u

/-- The symmetric bump commutes with the reflection about `t₀`. -/
lemma bumpCurve_reflect {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} (δ : E) (T lam t₀ : ℝ)
    (γ : ℝ → EN E N) (u : ℝ) :
    bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀) u = bumpCurve m k i₀ δ T lam t₀ γ (t₀ - u) := by
  have h1 : (|u - 0| : ℝ) = |t₀ - u - t₀| := by
    rw [sub_zero, show t₀ - u - t₀ = -u by ring, abs_neg]
  rw [bumpCurve, bumpCurve, reflectCurve, bumpPert, bumpPert, h1]

/-- The derivative of the reflected bump. -/
lemma deriv_bumpCurve_reflect {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} (δ : E)
    (T lam t₀ : ℝ) (γ : ℝ → EN E N) (u : ℝ) :
    deriv (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀)) u
      = -deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ - u) := by
  have hfun : bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀)
      = fun v : ℝ => bumpCurve m k i₀ δ T lam t₀ γ (t₀ - v) :=
    funext fun v => bumpCurve_reflect δ T lam t₀ γ v
  rw [hfun]
  exact deriv_comp_const_sub (bumpCurve m k i₀ δ T lam t₀ γ) t₀ u

/-- The integral over `[t₀ - λT, t₀]` as an integral over `[0, λT]` of the reflected function. -/
lemma intervalIntegral_reflect (F : ℝ → ℝ) (t₀ lam T : ℝ) :
    ∫ u in (t₀ - lam * T)..t₀, F u = ∫ u in (0:ℝ)..(lam * T), F (t₀ - u) := by
  have h := intervalIntegral.integral_comp_mul_add (f := F) (c := (-1 : ℝ)) (by norm_num) t₀
    (a := (0:ℝ)) (b := lam * T)
  simp only [neg_mul, one_mul, neg_zero, zero_add] at h
  have h2 : ∫ u in (0:ℝ)..(lam * T), F (t₀ - u) = ∫ u in (0:ℝ)..(lam * T), F (-u + t₀) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [sub_eq_neg_add]
  rw [h2, h, show ((-1:ℝ)⁻¹) = -1 by norm_num, neg_smul, one_smul,
    show -(lam * T) + t₀ = t₀ - lam * T by ring,
    intervalIntegral.integral_symm (a := t₀ - lam * T) (b := t₀)]
  ring

/-! ## The `∀ᶠ λ` form of the window bound -/

theorem bump_window_action_le_eventually {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0)
    {T t₀ h : ℝ} (hT : 0 < T) (hδT : ‖δ‖ ≤ T / 2) {γ : ℝ → EN E N} {Cd Cp ν Pb : ℝ}
    (hCd : 0 ≤ Cd) (hCp : 0 ≤ Cp) (hν : 0 < ν)
    (hac : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T))
    (hncI : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      ∀ u ∈ Ioo t₀ (t₀ + lam * T), WithoutCollisions (γ u))
    (hvel : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (bumpRescaled m k γ t₀ lam) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3))
    (hUpot : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (bumpRescaled m k γ t₀ lam t) ≤ Cp * t ^ (-(2:ℝ)/3))
    (hsgn : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T, ∀ j ∈ k.erase i₀,
      0 ≤ inner ℝ (bumpRescaled m k γ t₀ lam t i₀ - bumpRescaled m k γ t₀ lam t j) δ)
    (hsep : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∀ t ∈ Ioc (0:ℝ) T,
      ClusterSeparated k (γ (t₀ + lam * t)) ν)
    (hpot : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), ∫ t in (0:ℝ)..T,
      (clusterPotential m k (bumpRescaled m k γ t₀ lam t + stdVarVec m k i₀ δ T t)
        - clusterPotential m k (bumpRescaled m k γ t₀ lam t)) ≤ Pb) :
    ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      ∫ u in t₀..(t₀ + lam * T),
          (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
            (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u))
        ≤ lam ^ ((1:ℝ)/3) * ((Cd * ‖stdPertVec m k i₀ δ‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
              + ‖stdPertVec m k i₀ δ‖_[m] ^ 2 / (2 * ‖δ‖)) + Pb)
          + lam * (T * ((∑ p ∈ (pairFinset N).filter
                (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2)
              * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2))) := by
  have hsmall : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), 4 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν := by
    have hb : Tendsto (fun lam : ℝ => 4 * (lam ^ ((2:ℝ)/3) * ‖δ‖))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
      have h := tendsto_rpow_two_thirds_nhdsWithin_zero.const_mul (4 * ‖δ‖)
      have h2 : (fun lam : ℝ => 4 * (lam ^ ((2:ℝ)/3) * ‖δ‖))
          = fun lam : ℝ => (4 * ‖δ‖) * lam ^ ((2:ℝ)/3) := by
        funext lam; ring
      rw [h2]
      simpa using h
    exact hb.eventually (eventually_le_nhds hν)
  filter_upwards [hac, hncI, hvel, hUpot, hsgn, hsep, hpot, hsmall, self_mem_nhdsWithin]
    with lam hac hncI hvel hUpot hsgn hsep hpot hsmall hlam
  exact bump_window_action_le hm hi₀ hδ hlam hT hδT hac hncI hCd hCp hν hvel hUpot hsgn hsep
    hsmall hpot

/-! ## The two-sided negative bound -/

theorem exists_bump_window_negative {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {k : Finset (Fin N)}
    {i₀ : Fin N} {δ : E} {T t₀ h : ℝ} (hT : 0 < T) {γ : ℝ → EN E N} {BR BL : ℝ → ℝ}
    (hboundR : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      ∫ u in t₀..(t₀ + lam * T), (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
          (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u)) ≤ BR lam)
    (hboundL : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      ∫ u in (0:ℝ)..(lam * T), (lagR m h (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀) u)
          (deriv (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀)) u)
        - lagR m h (reflectCurve γ t₀ u) (deriv (reflectCurve γ t₀) u)) ≤ BL lam)
    (hneg : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), BR lam + BL lam < 0)
    (hint : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0), IntervalIntegrable
      (fun u => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
          (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u))
      volume (t₀ - lam * T) (t₀ + lam * T)) :
    ∃ lam ∈ Ioi (0:ℝ), ∫ u in (t₀ - lam * T)..(t₀ + lam * T),
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
          (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u)) < 0 := by
  have hall : ∀ᶠ lam in nhdsWithin (0:ℝ) (Ioi 0),
      (∫ u in t₀..(t₀ + lam * T), (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
          (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u)) ≤ BR lam)
      ∧ (∫ u in (0:ℝ)..(lam * T), (lagR m h (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀) u)
          (deriv (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀)) u)
        - lagR m h (reflectCurve γ t₀ u) (deriv (reflectCurve γ t₀) u)) ≤ BL lam)
      ∧ (BR lam + BL lam < 0)
      ∧ IntervalIntegrable (fun u => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
          (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u))
        volume (t₀ - lam * T) (t₀ + lam * T)
      ∧ (0 < lam) := by
    filter_upwards [hboundR, hboundL, hneg, hint, self_mem_nhdsWithin]
      with lam h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨lam, hR, hL, hneg', hint', hlam⟩ := hall.exists
  refine ⟨lam, hlam, ?_⟩
  have hle : t₀ - lam * T ≤ t₀ := by
    have : 0 < lam * T := mul_pos hlam hT
    linarith
  have hle' : t₀ ≤ t₀ + lam * T := by
    have : 0 < lam * T := mul_pos hlam hT
    linarith
  -- the two windows agree
  have hrefl : (∫ u in (t₀ - lam * T)..t₀, (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u)))
      = ∫ u in (0:ℝ)..(lam * T), (lagR m h (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀) u)
          (deriv (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀)) u)
        - lagR m h (reflectCurve γ t₀ u) (deriv (reflectCurve γ t₀) u)) := by
    rw [intervalIntegral_reflect]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [deriv_bumpCurve_reflect δ T lam t₀ γ u, bumpCurve_reflect δ T lam t₀ γ u,
      deriv_reflectCurve γ t₀ u]
    simp only [lagR_neg m hm h, reflectCurve_apply]
  -- split the big window
  have hmono1 : IntervalIntegrable (fun u => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
      (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u))
      volume (t₀ - lam * T) t₀ :=
    hint'.mono_set (by
      rw [Set.uIcc_of_le hle, Set.uIcc_of_le (by linarith : t₀ - lam * T ≤ t₀ + lam * T)]
      exact Set.Icc_subset_Icc le_rfl hle')
  have hmono2 : IntervalIntegrable (fun u => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
      (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u))
      volume t₀ (t₀ + lam * T) :=
    hint'.mono_set (by
      rw [Set.uIcc_of_le hle', Set.uIcc_of_le (by linarith : t₀ - lam * T ≤ t₀ + lam * T)]
      exact Set.Icc_subset_Icc hle (le_refl _))
  have hsplit : (∫ u in (t₀ - lam * T)..(t₀ + lam * T), (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u)))
      = (∫ u in (t₀ - lam * T)..t₀, (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
          (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u)))
        + (∫ u in t₀..(t₀ + lam * T), (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ u)
          (deriv (bumpCurve m k i₀ δ T lam t₀ γ) u) - lagR m h (γ u) (deriv γ u))) :=
    (intervalIntegral.integral_add_adjacent_intervals hmono1 hmono2).symm
  rw [hsplit, hrefl]
  linarith [hR, hL, hneg']

end Submission.NBody
