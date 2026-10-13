/-
# `Work.FTS.EllSol.K5cAux.thWeightCmp`

The angular weight `σ θ = sin(2θ)^{-η}` (`η = Work.Spaces.eta = 99/100`) is comparable with
itself mollified at scale `ε ≤ 1/2` with the (doubly odd) kernel `sKer ε`:

  `∫_{Iθ} σ θ · (ρ_ε(θ-u) + ρ_ε(θ+u) + ρ_ε(θ+u-π)) ≤ K · σ u`  for `u ∈ (0, π/2)`.

The three kernels are the three "images" of `u` under the reflections generating the doubly odd
extension, so the statement is the standard power-weight comparison for a mollifier.

The proof is elementary.  Write `m x = min x (π/2 - x)` for the distance of `x` to the nearest
endpoint of `Iθ = [0, π/2]`.  Then

* `sin(2x) ≤ 2 m x` and `(4/π) m x ≤ sin(2x)` on `Iθ` (Jordan's inequality, reflected);
* consequently `σ x ≤ (π/2)^η m x^{-η}` and `σ x ≥ 2^{-η} m x^{-η}`;
* if the window `[u-ε, u+ε]` stays at distance `≥ 2ε` from both endpoints (`2ε ≤ m u`) then `m`
  is `1`-Lipschitz and `m θ ≥ m u / 2` on the window, so `σ θ ≤ π^η σ u` there, and the kernel
  has total mass `≤ 1`;
* otherwise the window is contained in a layer of width `3ε` at an endpoint, whose `σ`-mass is
  `≤ (π/4)^η (3ε)^{1-η}/(1-η)`, while `σ u ≥ (4ε)^{-η}` because `m u < 2ε`.

Everything is quantified over an existential constant, so any finite bookkeeping constant works.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllSol.WCLayer

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.K5cAux

open Work.FTS.EllSol.PkgK5.K5c

local notation "σ" => Work.FTS.EllipticEst.thEta
local notation "η" => Work.Spaces.eta
local notation "Iθ" => Work.Spaces.Iθ

/-! ## The kernel `sKer` -/

lemma sKer_le_inv {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    sKer ε t ≤ (ε * sMass)⁻¹ := by
  rw [sKer]
  have h1 : (0 : ℝ) ≤ (ε * sMass)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le)
  calc (ε * sMass)⁻¹ * sBump (t / ε) ≤ (ε * sMass)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (sBump_le_one _) h1
    _ = (ε * sMass)⁻¹ := by ring

lemma continuous_sKer (ε : ℝ) : Continuous (sKer ε) := by
  have h : sKer ε = fun t : ℝ => (ε * sMass)⁻¹ * sBump (t / ε) := by
    funext t; rw [sKer]
  rw [h]
  exact continuous_const.mul (sBump_continuous.comp (continuous_id.div_const ε))

lemma hasCompactSupport_sKer {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (sKer ε) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-ε) ε) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  have hlt : |t| < ε := by
    by_contra h
    exact ht (sKer_eq_zero_of_le_abs hε (not_lt.mp h))
  rw [abs_lt] at hlt
  rw [Set.mem_Icc]
  exact ⟨le_of_lt hlt.1, le_of_lt hlt.2⟩

lemma integrable_sKer {ε : ℝ} (hε : 0 < ε) : Integrable (sKer ε) volume :=
  (continuous_sKer ε).integrable_of_hasCompactSupport (hasCompactSupport_sKer hε)

/-- The kernel has total mass at most `1` over the angle interval. -/
lemma integral_Iθ_sKer_sub_le_one {ε u : ℝ} (hε : 0 < ε) :
    ∫ θ in Iθ, sKer ε (θ - u) ≤ 1 := by
  have hint : Integrable (fun θ : ℝ => sKer ε (θ - u)) volume :=
    (integrable_sKer hε).comp_sub_right u
  have h1 : ∫ θ in Iθ, sKer ε (θ - u) ≤ ∫ θ : ℝ, sKer ε (θ - u) :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun t => sKer_nonneg hε _)
  rw [integral_sub_right_eq_self (μ := volume) (sKer ε) u, sKer_integral_eq_one hε] at h1
  exact h1

/-! ## The distance-to-the-endpoint function `m x = min x (π/2 - x)` -/

lemma sin_two_le_two_min {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    Real.sin (2 * θ) ≤ 2 * min θ (Real.pi / 2 - θ) := by
  have h2θ0 : 0 ≤ 2 * θ := by linarith
  have hle1 : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le h2θ0
  have hle2 : Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
    have h : Real.sin (Real.pi - 2 * θ) ≤ Real.pi - 2 * θ :=
      Real.sin_le (by linarith [Real.pi_pos])
    rw [Real.sin_pi_sub, show Real.pi - 2 * θ = 2 * (Real.pi / 2 - θ) by ring] at h
    exact h
  have hmin := le_min hle1 hle2
  rw [← mul_min_of_nonneg θ (Real.pi / 2 - θ) (by norm_num : (0 : ℝ) ≤ 2)] at hmin
  exact hmin

lemma four_div_pi_min_le_sin_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    (4 / Real.pi) * min θ (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  have h2θ0 : 0 ≤ 2 * θ := by linarith
  have h2θπ : 2 * θ ≤ Real.pi := by linarith [Real.pi_pos]
  have key : (2 / Real.pi) * min (2 * θ) (Real.pi - 2 * θ) ≤ Real.sin (2 * θ) := by
    rcases le_total (2 * θ) (Real.pi / 2) with h | h
    · rw [min_eq_left (by linarith)]
      exact Real.mul_le_sin h2θ0 h
    · rw [min_eq_right (by linarith)]
      have h0' : 0 ≤ Real.pi - 2 * θ := by linarith
      have h1' : Real.pi - 2 * θ ≤ Real.pi / 2 := by linarith
      have hh := Real.mul_le_sin h0' h1'
      rwa [Real.sin_pi_sub] at hh
  have hmin : min (2 * θ) (Real.pi - 2 * θ) = 2 * min θ (Real.pi / 2 - θ) := by
    have h := mul_min_of_nonneg θ (Real.pi / 2 - θ) (by norm_num : (0 : ℝ) ≤ 2)
    rw [show (2 : ℝ) * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring] at h
    exact h.symm
  rw [hmin] at key
  calc (4 / Real.pi) * min θ (Real.pi / 2 - θ)
      = (2 / Real.pi) * (2 * min θ (Real.pi / 2 - θ)) := by ring
    _ ≤ Real.sin (2 * θ) := key

lemma min_theta_sub_le (θ u : ℝ) :
    |min θ (Real.pi / 2 - θ) - min u (Real.pi / 2 - u)| ≤ |θ - u| := by
  have h := abs_min_sub_min_le_max θ (Real.pi / 2 - θ) u (Real.pi / 2 - u)
  have h2 : (Real.pi / 2 - θ) - (Real.pi / 2 - u) = -(θ - u) := by ring
  rw [h2, abs_neg] at h
  exact le_trans h (max_le le_rfl le_rfl)

/-! ## Pointwise comparisons of `σ` -/

/-- Away from the endpoints by at least `ε`, `σ` is comparable with `σ u`. -/
lemma sigma_le_of_far {θ u ε : ℝ} (hu0 : 0 < u) (hu2 : u < Real.pi / 2)
    (hε0 : 0 < ε) (hfar : 2 * ε ≤ min u (Real.pi / 2 - u)) (hθu : |θ - u| < ε) :
    σ θ ≤ Real.pi ^ η * σ u := by
  set m := min u (Real.pi / 2 - u) with hm
  have hm_pos : 0 < m := lt_min hu0 (by linarith [Real.pi_pos, hu2])
  have hm_u : m ≤ u := min_le_left _ _
  have hm_pu : m ≤ Real.pi / 2 - u := min_le_right _ _
  have hεhalf : ε ≤ m / 2 := by linarith
  have hθu' := abs_lt.mp hθu
  have hθ_pos : 0 < θ := by linarith [hθu'.1, hm_u, hεhalf]
  have hθ_pi : θ ≤ Real.pi / 2 := by linarith [hθu'.2, hm_pu, hεhalf]
  have hminθ : m / 2 ≤ min θ (Real.pi / 2 - θ) := by
    have h1 : |min θ (Real.pi / 2 - θ) - m| ≤ |θ - u| := by
      rw [hm]; exact min_theta_sub_le θ u
    have h2 : |min θ (Real.pi / 2 - θ) - m| < ε := lt_of_le_of_lt h1 hθu
    have h3 := (abs_lt.mp h2).1
    linarith
  have hsin_lb : (2 / Real.pi) * m ≤ Real.sin (2 * θ) := by
    have h4 := four_div_pi_min_le_sin_two hθ_pos.le hθ_pi
    have hmle : m ≤ 2 * min θ (Real.pi / 2 - θ) := by linarith
    calc (2 / Real.pi) * m ≤ (2 / Real.pi) * (2 * min θ (Real.pi / 2 - θ)) :=
          mul_le_mul_of_nonneg_left hmle (by positivity)
      _ = (4 / Real.pi) * min θ (Real.pi / 2 - θ) := by ring
      _ ≤ Real.sin (2 * θ) := h4
  have hsin_ub : Real.sin (2 * u) ≤ 2 * m := by
    have h := sin_two_le_two_min hu0.le hu2.le
    rwa [← hm] at h
  have hsinu_pos : 0 < Real.sin (2 * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hσu_lb : (2 * m) ^ (-η) ≤ σ u := by
    have h := Real.rpow_le_rpow_of_nonpos hsinu_pos hsin_ub
      (by linarith [Work.Spaces.eta_nonneg] : -η ≤ 0)
    simpa only [Work.FTS.EllipticEst.thEta] using h
  have hm_lb : m ^ (-η) ≤ 2 ^ η * σ u := by
    have h1 : (2 : ℝ) ^ (-η) * m ^ (-η) ≤ σ u := by
      calc (2 : ℝ) ^ (-η) * m ^ (-η) = (2 * m) ^ (-η) :=
            (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hm_pos.le).symm
        _ ≤ σ u := hσu_lb
    have h2 : (2 : ℝ) ^ η * ((2 : ℝ) ^ (-η) * m ^ (-η)) ≤ (2 : ℝ) ^ η * σ u :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)
    have h3 : (2 : ℝ) ^ η * ((2 : ℝ) ^ (-η) * m ^ (-η)) = m ^ (-η) := by
      rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        show η + -η = (0 : ℝ) by ring, Real.rpow_zero, one_mul]
    rwa [h3] at h2
  have hσθ_ub : σ θ ≤ (Real.pi / 2) ^ η * m ^ (-η) := by
    have hbase : 0 < (2 / Real.pi) * m := by positivity
    have h := Real.rpow_le_rpow_of_nonpos hbase hsin_lb
      (by linarith [Work.Spaces.eta_nonneg] : -η ≤ 0)
    have hkey : ((2 : ℝ) / Real.pi * m) ^ (-η) = (Real.pi / 2) ^ η * m ^ (-η) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / Real.pi) hm_pos.le]
      congr 1
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 / Real.pi),
        ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ 2 / Real.pi) η, inv_div]
    rw [hkey] at h
    simpa only [Work.FTS.EllipticEst.thEta] using h
  have hpi : (Real.pi / 2) * 2 = Real.pi := by ring
  calc σ θ ≤ (Real.pi / 2) ^ η * m ^ (-η) := hσθ_ub
    _ ≤ (Real.pi / 2) ^ η * (2 ^ η * σ u) := mul_le_mul_of_nonneg_left hm_lb (by positivity)
    _ = Real.pi ^ η * σ u := by
        rw [← mul_assoc, ← Real.mul_rpow (by positivity : (0 : ℝ) ≤ Real.pi / 2)
          (by norm_num : (0 : ℝ) ≤ 2), hpi]

lemma sigma_ge_two_eps {u ε : ℝ} (hu0 : 0 < u) (hu2 : u < Real.pi / 2) (hε0 : 0 < ε)
    (h : u < ε ∨ Real.pi / 2 - u < ε) : (2 * ε) ^ (-η) ≤ σ u := by
  have hsinu_pos : 0 < Real.sin (2 * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hub := sin_two_le_two_min hu0.le hu2.le
  have hm : min u (Real.pi / 2 - u) < ε := by
    rcases h with h | h
    · exact lt_of_le_of_lt (min_le_left _ _) h
    · exact lt_of_le_of_lt (min_le_right _ _) h
  have hlt : Real.sin (2 * u) ≤ 2 * ε := by linarith
  have h2 := Real.rpow_le_rpow_of_nonpos hsinu_pos hlt
    (by linarith [Work.Spaces.eta_nonneg] : -η ≤ 0)
  simpa only [Work.FTS.EllipticEst.thEta] using h2

lemma sigma_ge_four_eps {u ε : ℝ} (hu0 : 0 < u) (hu2 : u < Real.pi / 2) (hε0 : 0 < ε)
    (hnear : min u (Real.pi / 2 - u) < 2 * ε) : (4 * ε) ^ (-η) ≤ σ u := by
  have hsinu_pos : 0 < Real.sin (2 * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hub := sin_two_le_two_min hu0.le hu2.le
  have hlt : Real.sin (2 * u) ≤ 4 * ε := by linarith
  have h2 := Real.rpow_le_rpow_of_nonpos hsinu_pos hlt
    (by linarith [Work.Spaces.eta_nonneg] : -η ≤ 0)
  simpa only [Work.FTS.EllipticEst.thEta] using h2

/-- `1 ≤ σ u` on the open interval. -/
lemma one_le_sigma {u : ℝ} (hu0 : 0 < u) (hu2 : u < Real.pi / 2) : 1 ≤ σ u := by
  have hsinu_pos : 0 < Real.sin (2 * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have h := Real.rpow_le_rpow_of_nonpos hsinu_pos (Real.sin_le_one _)
    (by linarith [Work.Spaces.eta_nonneg] : -η ≤ 0)
  simpa only [Work.FTS.EllipticEst.thEta, Real.one_rpow] using h

lemma sigma_pos {u : ℝ} (hu0 : 0 < u) (hu2 : u < Real.pi / 2) : 0 < σ u :=
  lt_of_lt_of_le one_pos (one_le_sigma hu0 hu2)

/-- `ε ^ (-η) ≤ 2 ^ η σ u` from `(2ε)^{-η} ≤ σ u`. -/
lemma inv_rpow_le_two_of_le {u ε : ℝ} (hε : 0 < ε) (h2 : (2 * ε) ^ (-η) ≤ σ u) :
    ε ^ (-η) ≤ 2 ^ η * σ u := by
  have h3 : (2 : ℝ) ^ (-η) * ε ^ (-η) = (2 * ε) ^ (-η) :=
    (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le).symm
  have h4 : (2 : ℝ) ^ (-η) * ε ^ (-η) ≤ σ u := by rw [h3]; exact h2
  have h5 : (2 : ℝ) ^ η * ((2 : ℝ) ^ (-η) * ε ^ (-η)) ≤ (2 : ℝ) ^ η * σ u :=
    mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (by norm_num) _)
  have h6 : (2 : ℝ) ^ η * ((2 : ℝ) ^ (-η) * ε ^ (-η)) = ε ^ (-η) := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show η + -η = (0 : ℝ) by ring, Real.rpow_zero, one_mul]
  rwa [h6] at h5

/-- `ε ^ (-η) ≤ 4 ^ η σ u` from `(4ε)^{-η} ≤ σ u`. -/
lemma inv_rpow_le_four_of_le {u ε : ℝ} (hε : 0 < ε) (h2 : (4 * ε) ^ (-η) ≤ σ u) :
    ε ^ (-η) ≤ 4 ^ η * σ u := by
  have h3 : (4 : ℝ) ^ (-η) * ε ^ (-η) = (4 * ε) ^ (-η) :=
    (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hε.le).symm
  have h4 : (4 : ℝ) ^ (-η) * ε ^ (-η) ≤ σ u := by rw [h3]; exact h2
  have h5 : (4 : ℝ) ^ η * ((4 : ℝ) ^ (-η) * ε ^ (-η)) ≤ (4 : ℝ) ^ η * σ u :=
    mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (by norm_num) _)
  have h6 : (4 : ℝ) ^ η * ((4 : ℝ) ^ (-η) * ε ^ (-η)) = ε ^ (-η) := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 4),
      show η + -η = (0 : ℝ) by ring, Real.rpow_zero, one_mul]
  rwa [h6] at h5

lemma div_rpow_one_sub_le_inv_rpow {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 ≤ δ) (hδε : δ ≤ ε) :
    δ ^ (1 - η) / ε ≤ ε ^ (-η) := by
  have h1 : δ ^ (1 - η) ≤ ε ^ (1 - η) :=
    Real.rpow_le_rpow hδ0 hδε (by linarith [eta_lt_one])
  have h2 : δ ^ (1 - η) / ε ≤ ε ^ (1 - η) / ε := div_le_div_of_nonneg_right h1 hε.le
  have h3 : ε ^ (1 - η) / ε = ε ^ (-η) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one ε, ← Real.rpow_add hε,
      show (1 : ℝ) - η + (-1) = -η by ring]
  rwa [h3] at h2

/-- The basic window estimate: `(ε sMass)^{-1} δ^{1-η} ≤ ε^{-η} sMass^{-1}` for `δ ≤ ε`. -/
lemma window_inv_le {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 ≤ δ) (hδε : δ ≤ ε) :
    (ε * sMass)⁻¹ * δ ^ (1 - η) ≤ ε ^ (-η) * sMass⁻¹ := by
  have h := div_rpow_one_sub_le_inv_rpow hε hδ0 hδε
  have e : (ε * sMass)⁻¹ * δ ^ (1 - η) = (δ ^ (1 - η) / ε) * sMass⁻¹ := by
    rw [mul_inv_rev]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr sMass_pos.le)

/-- The `2 ^ η` window bound used for the two reflected kernels. -/
lemma window_le_two {u ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 ≤ δ) (hδε : δ ≤ ε)
    (h2η : ε ^ (-η) ≤ 2 ^ η * σ u) :
    (ε * sMass)⁻¹ * ((Real.pi / 4) ^ η / (1 - η) * δ ^ (1 - η))
      ≤ (Real.pi / 4) ^ η / (1 - η) * 2 ^ η * sMass⁻¹ * σ u := by
  have hA0 : (0 : ℝ) ≤ (Real.pi / 4) ^ η / (1 - η) :=
    div_nonneg (Real.rpow_nonneg (by positivity) _) one_sub_eta_pos.le
  calc (ε * sMass)⁻¹ * ((Real.pi / 4) ^ η / (1 - η) * δ ^ (1 - η))
      = (Real.pi / 4) ^ η / (1 - η) * ((ε * sMass)⁻¹ * δ ^ (1 - η)) := by ring
    _ ≤ (Real.pi / 4) ^ η / (1 - η) * (ε ^ (-η) * sMass⁻¹) :=
          mul_le_mul_of_nonneg_left (window_inv_le hε hδ0 hδε) hA0
    _ ≤ (Real.pi / 4) ^ η / (1 - η) * ((2 ^ η * σ u) * sMass⁻¹) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2η (inv_nonneg.mpr sMass_pos.le)) hA0
    _ = (Real.pi / 4) ^ η / (1 - η) * 2 ^ η * sMass⁻¹ * σ u := by ring

/-- The `4 ^ η`, width `3ε` window bound used for the middle kernel in the near regime. -/
lemma window_le_three {u ε : ℝ} (hε : 0 < ε) (h4η : ε ^ (-η) ≤ 4 ^ η * σ u) :
    (ε * sMass)⁻¹ * ((Real.pi / 4) ^ η / (1 - η) * (3 * ε) ^ (1 - η))
      ≤ (Real.pi / 4) ^ η / (1 - η) * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ * σ u := by
  have hA0 : (0 : ℝ) ≤ (Real.pi / 4) ^ η / (1 - η) :=
    div_nonneg (Real.rpow_nonneg (by positivity) _) one_sub_eta_pos.le
  have h30 : (0 : ℝ) ≤ 3 ^ (1 - η) := Real.rpow_nonneg (by norm_num) _
  calc (ε * sMass)⁻¹ * ((Real.pi / 4) ^ η / (1 - η) * (3 * ε) ^ (1 - η))
      = ((Real.pi / 4) ^ η / (1 - η) * 3 ^ (1 - η)) * ((ε * sMass)⁻¹ * ε ^ (1 - η)) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hε.le]; ring
    _ ≤ ((Real.pi / 4) ^ η / (1 - η) * 3 ^ (1 - η)) * (ε ^ (-η) * sMass⁻¹) :=
          mul_le_mul_of_nonneg_left (window_inv_le hε hε.le le_rfl) (mul_nonneg hA0 h30)
    _ ≤ ((Real.pi / 4) ^ η / (1 - η) * 3 ^ (1 - η)) * ((4 ^ η * σ u) * sMass⁻¹) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h4η (inv_nonneg.mpr sMass_pos.le)) (mul_nonneg hA0 h30)
    _ = (Real.pi / 4) ^ η / (1 - η) * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ * σ u := by ring

/-! ## Window integrals against `σ` -/

lemma integrableOn_sigma_sKer_shift {ε v : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun θ : ℝ => σ θ * sKer ε (θ + v)) Iθ := by
  have hcs : Continuous (fun θ : ℝ => sKer ε (θ + v)) :=
    (continuous_sKer ε).comp (continuous_id.add continuous_const)
  refine Integrable.mono' ((Work.FTS.EllipticEst.integrableOn_thEta.1).const_mul ((ε * sMass)⁻¹))
    ?_ ?_
  · exact (measurable_thEta.mul hcs.measurable).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have hρ : 0 ≤ sKer ε (θ + v) := sKer_nonneg hε _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hσ hρ)]
    calc σ θ * sKer ε (θ + v) ≤ σ θ * (ε * sMass)⁻¹ :=
          mul_le_mul_of_nonneg_left (sKer_le_inv hε _) hσ
      _ = (ε * sMass)⁻¹ * σ θ := by ring

lemma integrableOn_sigma_indicator_mul {c : ℝ} (hc : 0 ≤ c) {s : Set ℝ}
    (hs : MeasurableSet s) :
    IntegrableOn (fun θ : ℝ => c * (σ θ * Set.indicator s (fun _ => (1 : ℝ)) θ)) Iθ := by
  refine Integrable.mono' ((Work.FTS.EllipticEst.integrableOn_thEta.1).const_mul c) ?_ ?_
  · exact (measurable_const.mul (measurable_thEta.mul
      (measurable_const.indicator hs))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have hind : 0 ≤ Set.indicator s (fun _ => (1 : ℝ)) θ :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) θ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (mul_nonneg hσ hind))]
    have hind1 : Set.indicator s (fun _ => (1 : ℝ)) θ ≤ 1 := by
      by_cases h : θ ∈ s
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]; norm_num
    have hle : σ θ * Set.indicator s (fun _ => (1 : ℝ)) θ ≤ σ θ := by
      simpa using mul_le_mul_of_nonneg_left hind1 hσ
    exact mul_le_mul_of_nonneg_left hle hc

/-- The left layer of `σ`: `∫_{Iθ} σ · 1_{[0,b]} = ∫_0^b σ`. -/
lemma indicator_left_setIntegral {b : ℝ} (h0 : 0 ≤ b) (hb : b ≤ Real.pi / 2) :
    ∫ θ in Iθ, σ θ * Set.indicator (Set.Icc (0 : ℝ) b) (fun _ => (1 : ℝ)) θ
      = ∫ θ in (0 : ℝ)..b, σ θ := by
  have hsub : Set.Icc (0 : ℝ) b ⊆ Iθ := by
    intro x hx
    show x ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
    rw [Set.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 hb⟩
  have h1 : ∫ θ in Iθ, σ θ * Set.indicator (Set.Icc (0 : ℝ) b) (fun _ => (1 : ℝ)) θ
      = ∫ θ in Iθ, Set.indicator (Set.Icc (0 : ℝ) b) σ θ := by
    refine integral_congr_ae ?_
    filter_upwards with θ
    by_cases h : θ ∈ Set.Icc (0 : ℝ) b
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [h1, MeasureTheory.integral_indicator (μ := volume.restrict Iθ) measurableSet_Icc,
    Measure.restrict_restrict (μ := volume) (s := Set.Icc (0 : ℝ) b) (t := Iθ)
      measurableSet_Icc,
    Set.inter_eq_left.mpr hsub, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le h0]

/-- The right layer of `σ`: `∫_{Iθ} σ · 1_{[π/2-a, π/2]} = ∫_{π/2-a}^{π/2} σ`. -/
lemma indicator_right_setIntegral {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ Real.pi / 2) :
    ∫ θ in Iθ, σ θ * Set.indicator (Set.Icc (Real.pi / 2 - a) (Real.pi / 2))
        (fun _ => (1 : ℝ)) θ
      = ∫ θ in (Real.pi / 2 - a)..(Real.pi / 2), σ θ := by
  have hsub : Set.Icc (Real.pi / 2 - a) (Real.pi / 2) ⊆ Iθ := by
    intro x hx
    show x ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
    rw [Set.mem_Icc] at hx ⊢
    exact ⟨by linarith [hx.1], hx.2⟩
  have h1 : ∫ θ in Iθ, σ θ * Set.indicator (Set.Icc (Real.pi / 2 - a) (Real.pi / 2))
        (fun _ => (1 : ℝ)) θ
      = ∫ θ in Iθ, Set.indicator (Set.Icc (Real.pi / 2 - a) (Real.pi / 2)) σ θ := by
    refine integral_congr_ae ?_
    filter_upwards with θ
    by_cases h : θ ∈ Set.Icc (Real.pi / 2 - a) (Real.pi / 2)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [h1, MeasureTheory.integral_indicator (μ := volume.restrict Iθ) measurableSet_Icc,
    Measure.restrict_restrict (μ := volume) (s := Set.Icc (Real.pi / 2 - a) (Real.pi / 2))
      (t := Iθ) measurableSet_Icc,
    Set.inter_eq_left.mpr hsub, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : Real.pi / 2 - a ≤ Real.pi / 2)]

end Work.FTS.EllSol.K5cAux
