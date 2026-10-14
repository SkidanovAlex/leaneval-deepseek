import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllSol.WCLayer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

local notation "σ" => Work.FTS.EllipticEst.thEta
local notation "η" => Work.Spaces.eta

set_option autoImplicit false

lemma eta_lt_one : η < 1 := by norm_num [Work.Spaces.eta]

lemma eta_nonneg : 0 ≤ η := Work.Spaces.eta_nonneg

lemma one_sub_eta_pos : 0 < 1 - η := by norm_num [Work.Spaces.eta]

lemma one_sub_eta_ne : (1 : ℝ) - η ≠ 0 := ne_of_gt one_sub_eta_pos

lemma measurable_thEta : Measurable σ := by
  show Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  exact Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id)) _

/-- Jordan's inequality in the form needed here: on `(0, π/4]`,
`sin(2θ)^{-η} ≤ (π/4)^η θ^{-η}`. -/
lemma thEta_le_rpow {θ : ℝ} (h0 : 0 < θ) (h4 : θ ≤ Real.pi / 4) :
    σ θ ≤ (Real.pi / 4) ^ η * θ ^ (-η) := by
  have h2θ0 : 0 ≤ 2 * θ := by linarith
  have h2θ1 : 2 * θ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hj := Real.mul_le_sin h2θ0 h2θ1
  have hle : 4 * θ / Real.pi ≤ Real.sin (2 * θ) := by
    have e : (2 : ℝ) / Real.pi * (2 * θ) = 4 * θ / Real.pi := by ring
    rwa [e] at hj
  have hpos : 0 < 4 * θ / Real.pi := by positivity
  have h1 := Real.rpow_le_rpow_of_nonpos hpos hle (neg_nonpos.mpr eta_nonneg)
  have h2 : 4 * θ / Real.pi = (Real.pi / 4)⁻¹ * θ := by rw [inv_div]; ring
  rw [h2, Real.mul_rpow (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ Real.pi / 4)) h0.le,
    Real.inv_rpow (by positivity : (0 : ℝ) ≤ Real.pi / 4),
    ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ Real.pi / 4), neg_neg] at h1
  exact h1

lemma integral_thEta_zero_a {a : ℝ} (ha : 0 < a) (ha4 : a ≤ Real.pi / 4) :
    (∫ θ in (0 : ℝ)..a, σ θ) ≤ (Real.pi / 4) ^ η * a ^ (1 - η) / (1 - η) := by
  have h0a : (0 : ℝ) ≤ a := ha.le
  have hint1 : IntervalIntegrable σ volume 0 a := by
    rw [intervalIntegrable_iff]
    refine (Work.FTS.EllipticEst.integrableOn_thEta.1).mono_set ?_
    intro θ hθ
    rw [Set.uIoc_of_le ha.le] at hθ
    exact ⟨le_of_lt hθ.1, by linarith [hθ.2, ha4, Real.pi_pos]⟩
  have hint2 : IntervalIntegrable (fun θ : ℝ => (Real.pi / 4) ^ η * θ ^ (-η)) volume 0 a :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith [eta_lt_one] : -1 < -η)).const_mul _
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) a, σ θ ≤ (Real.pi / 4) ^ η * θ ^ (-η) :=
    fun θ hθ => thEta_le_rpow hθ.1 (by linarith [hθ.2, ha4])
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo h0a hint1 hint2 hpt
  have hval : (∫ θ in (0 : ℝ)..a, (Real.pi / 4) ^ η * θ ^ (-η))
      = (Real.pi / 4) ^ η * (a ^ (1 - η) / (1 - η)) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith [eta_lt_one] : -1 < -η))]
    rw [show -η + 1 = 1 - η by ring, Real.zero_rpow (x := 1 - η) one_sub_eta_ne]
    ring
  calc (∫ θ in (0 : ℝ)..a, σ θ)
      ≤ ∫ θ in (0 : ℝ)..a, (Real.pi / 4) ^ η * θ ^ (-η) := hmono
    _ = (Real.pi / 4) ^ η * (a ^ (1 - η) / (1 - η)) := hval
    _ = (Real.pi / 4) ^ η * a ^ (1 - η) / (1 - η) := by ring


/-- `σ` is invariant under the reflection `θ ↦ π/2 - θ`. -/
lemma integrand_sub_pi_div_two (x : ℝ) : σ (Real.pi / 2 - x) = σ x := by
  simp only [Work.FTS.EllipticEst.thEta]
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

lemma integral_thEta_right_layer {a : ℝ} (ha : 0 < a) (ha4 : a ≤ Real.pi / 4) :
    (∫ θ in (Real.pi / 2 - a)..(Real.pi / 2), σ θ)
      ≤ (Real.pi / 4) ^ η * a ^ (1 - η) / (1 - η) := by
  have h := intervalIntegral.integral_comp_sub_left (a := Real.pi / 2 - a) (b := Real.pi / 2)
    (fun θ : ℝ => σ θ) (Real.pi / 2)
  rw [show Real.pi / 2 - (Real.pi / 2 - a) = a by ring,
    show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) by ring] at h
  rw [show (fun x : ℝ => σ (Real.pi / 2 - x)) = σ from funext integrand_sub_pi_div_two] at h
  rw [h]
  exact integral_thEta_zero_a ha ha4


/-! ## The generic two-layer bound -/



/-! ## Integrability of `σ F²` -/


end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LopIterSinDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- The coefficient recursion attached to `L = sin(2θ) ∂_θ` and the special function
`sin(2θ)`:  `hfun 0 = 1` and
`hfun (i+1) θ = 2 cos(2θ) hfun i θ + sin(2θ) · deriv (hfun i) θ`, so that (see
`LopIter_sin_factor`) one has `L^i (sin(2θ)) = fun θ => sin(2θ) · hfun i θ`. -/
noncomputable def hfun : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | (n + 1) => fun θ => 2 * Real.cos (2 * θ) * hfun n θ
      + Real.sin (2 * θ) * deriv (hfun n) θ

@[simp] theorem hfun_zero : hfun 0 = fun _ : ℝ => 1 := rfl

@[simp] theorem hfun_succ (n : ℕ) :
    hfun (n + 1) = fun θ => 2 * Real.cos (2 * θ) * hfun n θ
      + Real.sin (2 * θ) * deriv (hfun n) θ := rfl

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.sin2_parseval_aesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory



/-- **Completeness of the Dirichlet sine system on `Iθ = [0, π/2]`**: a square integrable
function of which every even sine coefficient vanishes is zero a.e. -/
theorem sin_system_complete {f : ℝ → ℝ}
    (hmem : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (h : ∀ n : ℕ, ∫ θ in Work.Spaces.Iθ, f θ * Real.sin (2 * (n + 1) * θ) = 0) :
    f =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] 0 := by
  have hL : (0:ℝ) < Real.pi/2 := by positivity
  have hmeas : (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi/2)))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) from rfl]
    exact MeasureTheory.restrict_Ioc_eq_restrict_Icc
  have hmem' : MeasureTheory.MemLp f 2
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi/2))) := hmeas.symm ▸ hmem
  have h' : ∀ n : ℕ, 0 < n →
      ∫ θ in (0:ℝ)..(Real.pi/2), f θ * Real.sin (n * Real.pi * θ / (Real.pi/2)) = 0 := by
    intro n hn
    have h2 := h (n - 1)
    rw [show Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)] at h2
    rw [show (∫ θ in (0:ℝ)..(Real.pi/2), f θ * Real.sin (n * Real.pi * θ / (Real.pi/2)))
        = ∫ θ in (0:ℝ)..(Real.pi/2), f θ * Real.sin (2 * (((n - 1 : ℕ) : ℝ) + 1) * θ) from by
      apply intervalIntegral.integral_congr
      intro θ _
      show f θ * Real.sin ((n:ℝ) * Real.pi * θ / (Real.pi/2))
        = f θ * Real.sin (2 * (((n - 1 : ℕ) : ℝ) + 1) * θ)
      have hsub : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        rw [Nat.cast_sub hn, Nat.cast_one]; ring
      have key : (n : ℝ) * Real.pi * θ / (Real.pi/2) = 2 * (n:ℝ) * θ := by
        field_simp
      have key2 : 2 * (((n - 1 : ℕ) : ℝ) + 1) * θ = 2 * (n:ℝ) * θ := by rw [hsub]
      rw [key, key2], h2]
  have hfin := sin_complete_Ioc hL hmem' h'
  rwa [hmeas] at hfin


end Work.FTS.EllipticEst
end
