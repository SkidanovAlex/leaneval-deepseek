import Submission.NBody.MarchalBumpKinetic
import Submission.NBody.MarchalBumpRest

/-!
# The assembly of the symmetric-bump argument on one window

Combining the transfer identity `bump_real_action_eq`, the integrability
`bump_pieces_intervalIntegrable`, the kinetic cost `bump_kinetic_cost` and the potential gain
(hypothesis `hpot`), this module bounds the real action difference of the symmetric bump on the
window `[t₀, t₀ + λT]` by

  `λ^{1/3} (K + P) + λ·T·(∑_{cross} mᵢmⱼ)·2λ^{2/3}‖δ‖/ν²`,

where `K = Cd‖u₀‖(T/2)^{-1/3} + ‖u₀‖²/(2‖δ‖)` is the kinetic cost, `P` the potential gain and the
last term the (positive, higher-order) change of the interaction potential.

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

/-- `bumpRescaled` with vanishing collision time is `rescaledCentered`. -/
lemma bumpRescaled_zero (m : Fin N → ℝ) (k : Finset (Fin N)) (x : ℝ → EN E N) (lam : ℝ) :
    bumpRescaled m k x 0 lam = rescaledCentered m k x lam := by
  funext t
  simp [bumpRescaled, rescaledCentered, shiftCurve]

/-- **The window bound of the symmetric-bump action difference.** -/
theorem bump_window_action_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ h : ℝ} (hlam : 0 < lam)
    (hT : 0 < T) (hδT : ‖δ‖ ≤ T / 2) {x : ℝ → EN E N}
    (hac : AbsolutelyContinuousOnInterval x t₀ (t₀ + lam * T))
    (hncI : ∀ u ∈ Ioo t₀ (t₀ + lam * T), WithoutCollisions (x u))
    {Cd Cp ν Pb : ℝ} (hCd : 0 ≤ Cd) (hCp : 0 ≤ Cp) (hν : 0 < ν)
    (hvel : ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (bumpRescaled m k x t₀ lam) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3))
    (hUpot : ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (bumpRescaled m k x t₀ lam t) ≤ Cp * t ^ (-(2:ℝ)/3))
    (hsgn : ∀ t ∈ Ioc (0:ℝ) T, ∀ j ∈ k.erase i₀,
      0 ≤ inner ℝ (bumpRescaled m k x t₀ lam t i₀ - bumpRescaled m k x t₀ lam t j) δ)
    (hsep : ∀ t ∈ Ioc (0:ℝ) T, ClusterSeparated k (x (t₀ + lam * t)) ν)
    (hsmall : 4 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν)
    (hpot : ∫ t in (0:ℝ)..T, (clusterPotential m k
          (bumpRescaled m k x t₀ lam t + stdVarVec m k i₀ δ T t)
        - clusterPotential m k (bumpRescaled m k x t₀ lam t)) ≤ Pb) :
    ∫ u in t₀..(t₀ + lam * T),
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ x u) (deriv (bumpCurve m k i₀ δ T lam t₀ x) u)
          - lagR m h (x u) (deriv x u))
      ≤ lam ^ ((1:ℝ)/3) * ((Cd * ‖stdPertVec m k i₀ δ‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
            + ‖stdPertVec m k i₀ δ‖_[m] ^ 2 / (2 * ‖δ‖)) + Pb)
        + lam * (T * ((∑ p ∈ (pairFinset N).filter
              (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2)
            * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2))) := by
  classical
  have hd : (0:ℝ) < ‖δ‖ := norm_pos_iff.mpr hδ
  obtain ⟨hint1, hint2, hint3, hint4, hint5, hint6⟩ :=
    bump_pieces_intervalIntegrable (m := m) (k := k) (i₀ := i₀) hm hi₀ hδ hlam hT hac hncI
      (Cd := Cd) (Cp := Cp) (ν := ν) hCd hCp hν
      hvel hUpot hsgn hsep hsmall
  have hact := bump_real_action_eq (m := m) (k := k) (i₀ := i₀) (h := h) hm hi₀ hδ hlam hT hac
    hint1 hint2 hint3 hint4 hint5 hint6
  rw [hact]
  set Kb : ℝ := Cd * ‖stdPertVec m k i₀ δ‖_[m] * (T / 2) ^ (-(1:ℝ)/3)
    + ‖stdPertVec m k i₀ δ‖_[m] ^ 2 / (2 * ‖δ‖) with hKb
  -- kinetic part
  have hkin : (∫ s in (0:ℝ)..T, massInner m (deriv (bumpRescaled m k x t₀ lam) s)
        (deriv (stdVarVec m k i₀ δ T) s))
      + (1 / 2) * (∫ s in (0:ℝ)..T, ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2) ≤ Kb := by
    have h1 : (∫ s in (0:ℝ)..T, massInner m (deriv (bumpRescaled m k x t₀ lam) s)
          (deriv (stdVarVec m k i₀ δ T) s))
        + (1 / 2) * (∫ s in (0:ℝ)..T, ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
        = ∫ s in (0:ℝ)..T, (massInner m (deriv (bumpRescaled m k x t₀ lam) s)
            (deriv (stdVarVec m k i₀ δ T) s)
          + (1 / 2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2) := by
      rw [intervalIntegral.integral_add hint1 (hint2.const_mul (1 / 2)),
        intervalIntegral.integral_const_mul]
    rw [h1, hKb]
    exact bump_kinetic_cost (m := m) hm (k := k) (i₀ := i₀) δ hδ hT hδT hCd hvel
  -- potential part
  have hpot2 : (∫ s in (0:ℝ)..T, clusterPotential m k
        (bumpRescaled m k x t₀ lam s + stdVarVec m k i₀ δ T s))
      - (∫ s in (0:ℝ)..T, clusterPotential m k (bumpRescaled m k x t₀ lam s)) ≤ Pb := by
    rw [← intervalIntegral.integral_sub hint3 hint4]
    exact hpot
  -- interaction part
  set Cu : ℝ := ∑ p ∈ (pairFinset N).filter
      (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2 with hCu
  have hrest : (∫ s in (0:ℝ)..T, clusterPotentialRest m k
        (bumpCurve m k i₀ δ T lam t₀ x (t₀ + lam * s)))
      - (∫ s in (0:ℝ)..T, clusterPotentialRest m k (x (t₀ + lam * s)))
      ≤ Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2) * T := by
    have hpt : ∀ s ∈ Set.Ioc (0:ℝ) T,
        clusterPotentialRest m k (bumpCurve m k i₀ δ T lam t₀ x (t₀ + lam * s))
          - clusterPotentialRest m k (x (t₀ + lam * s))
        ≤ Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2) := by
      intro s hs
      have h := clusterPotentialRest_bump_le (m := m) (k := k) (i₀ := i₀) hm hi₀ (δ := δ)
        (lam := lam) (T := T) (t₀ := t₀) (ν := ν) (γ := x) hν hlam hT
        (fun s hs => (hsep s hs).weak)
        (by linarith : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν) hs
      rw [hCu]
      exact h
    rw [← intervalIntegral.integral_sub hint5 hint6]
    have h2 : (∫ s in (0:ℝ)..T, (clusterPotentialRest m k
          (bumpCurve m k i₀ δ T lam t₀ x (t₀ + lam * s))
        - clusterPotentialRest m k (x (t₀ + lam * s))))
        ≤ ∫ _s in (0:ℝ)..T, Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hT.le
        (hint5.sub hint6) intervalIntegrable_const
        (fun s hs => hpt s ⟨hs.1, hs.2.le⟩)
    rw [intervalIntegral.integral_const] at h2
    simpa only [smul_eq_mul, sub_zero, mul_comm] using h2
  -- combine
  have hP : (∫ s in (0:ℝ)..T, massInner m (deriv (bumpRescaled m k x t₀ lam) s)
        (deriv (stdVarVec m k i₀ δ T) s))
      + (1 / 2) * (∫ s in (0:ℝ)..T, ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
      + ((∫ s in (0:ℝ)..T, clusterPotential m k
            (bumpRescaled m k x t₀ lam s + stdVarVec m k i₀ δ T s))
          - (∫ s in (0:ℝ)..T, clusterPotential m k (bumpRescaled m k x t₀ lam s)))
      ≤ Kb + Pb := add_le_add hkin hpot2
  have hR : (∫ s in (0:ℝ)..T, clusterPotentialRest m k
        (bumpCurve m k i₀ δ T lam t₀ x (t₀ + lam * s)))
      - (∫ s in (0:ℝ)..T, clusterPotentialRest m k (x (t₀ + lam * s)))
      ≤ T * (Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2)) := by
    rw [mul_comm] at hrest
    exact hrest
  have h13 : (0:ℝ) < lam ^ ((1:ℝ)/3) := Real.rpow_pos_of_pos hlam _
  calc lam ^ ((1:ℝ)/3) * ((∫ s in (0:ℝ)..T, massInner m
          (deriv (bumpRescaled m k x t₀ lam) s) (deriv (stdVarVec m k i₀ δ T) s))
        + (1 / 2) * (∫ s in (0:ℝ)..T, ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
        + ((∫ s in (0:ℝ)..T, clusterPotential m k
              (bumpRescaled m k x t₀ lam s + stdVarVec m k i₀ δ T s))
            - (∫ s in (0:ℝ)..T, clusterPotential m k (bumpRescaled m k x t₀ lam s))))
      + lam * ((∫ s in (0:ℝ)..T, clusterPotentialRest m k
              (bumpCurve m k i₀ δ T lam t₀ x (t₀ + lam * s)))
          - (∫ s in (0:ℝ)..T, clusterPotentialRest m k (x (t₀ + lam * s))))
      ≤ lam ^ ((1:ℝ)/3) * (Kb + Pb) + lam * (T * (Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2))) :=
        add_le_add (mul_le_mul_of_nonneg_left hP h13.le) (mul_le_mul_of_nonneg_left hR hlam.le)
    _ = lam ^ ((1:ℝ)/3) * (Kb + Pb)
        + lam * (T * ((∑ p ∈ (pairFinset N).filter
              (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2)
            * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2))) := by rw [hCu]

end Submission.NBody
