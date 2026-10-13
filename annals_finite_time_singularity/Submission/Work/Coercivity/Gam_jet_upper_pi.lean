import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.E2Slice.E2SliceDefs
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Coercivity.DthU_iter_Gam_all

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular jet of `Γ` is `O((π/2 - θ)^{2α/3})` near `θ = π/2`

`Γ(θ) = (sin θ · cos²θ)^{α/3}` vanishes at `θ = π/2` like `(π/2 - θ)^{2α/3}`, and so do all
its `D_θ`-iterates, because on `(0, π/2)`

`D_θ^{j+1} Γ = α · Tfun j α · Γ`   (`Work.Coercivity.DthU_iter_Gam_all`)

and `sin θ cos²θ` is comparable with `(π/2 - θ)²` on `(π/2 - 1, π/2)`.  The factor
`Tfun j α` is smooth (hence bounded on the closed interval), which gives the claim for
arbitrary real `α` and every `j`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The comparison of `sin θ · cos²θ` with `(π/2 - θ)²` near `π/2` -/

/-- On `(π/2 - 1, π/2)` the base `u(θ) = sin θ · cos²θ` of `Γ(θ) = u(θ)^{α/3}` is comparable
with `(π/2 - θ)²`: with `t = π/2 - θ ∈ (0,1)` one has `cos θ = sin t` and
`2/π · x ≤ sin x ≤ x` on `[0, π/2]`, so `(2/π)² t² ≤ cos²θ ≤ t²`, while
`cos 1 = sin(π/2 - 1) ≤ sin θ ≤ 1`. -/
theorem gam_pi_ratio_bounds :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ Set.Ioo (π / 2 - 1) (π / 2),
      c * (π / 2 - θ) ^ 2 ≤ Real.sin θ * Real.cos θ ^ 2
        ∧ Real.sin θ * Real.cos θ ^ 2 ≤ (π / 2 - θ) ^ 2 := by
  have hcos1 : 0 < Real.cos 1 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  refine ⟨Real.cos 1 * (2 / π) ^ 2, by positivity, ?_⟩
  intro θ hθ
  have hθ0 : 0 < θ := by linarith [hθ.1, Real.pi_gt_three]
  have hθ2 : θ < π / 2 := hθ.2
  have ht0 : 0 < π / 2 - θ := by linarith
  have htpi : π / 2 - θ ≤ π / 2 := by linarith
  have hcos : Real.cos θ = Real.sin (π / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
  -- `sin θ ≥ cos 1`
  have hsinθ : Real.cos 1 ≤ Real.sin θ := by
    have h := Real.monotoneOn_sin
      (show (π / 2 - 1) ∈ Set.Icc (-(π / 2)) (π / 2) from
        ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_pos]⟩)
      (show θ ∈ Set.Icc (-(π / 2)) (π / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [hθ2, Real.pi_pos]⟩)
      (le_of_lt hθ.1)
    rwa [Real.sin_pi_div_two_sub] at h
  -- `sin t ≥ 2/π · t` and `sin t ≤ t` for `t = π/2 - θ`
  have hsin_t_lb : (2 / π) * (π / 2 - θ) ≤ Real.sin (π / 2 - θ) :=
    Real.mul_le_sin (le_of_lt ht0) htpi
  have hsin_t_ub : Real.sin (π / 2 - θ) ≤ π / 2 - θ := le_of_lt (Real.sin_lt ht0)
  have hsin_t_nn : 0 ≤ Real.sin (π / 2 - θ) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_gt_three]))
  have hcos2_ub : Real.cos θ ^ 2 ≤ (π / 2 - θ) ^ 2 := by
    rw [hcos]
    exact pow_le_pow_left₀ hsin_t_nn hsin_t_ub 2
  have hcos2_lb : ((2 / π) * (π / 2 - θ)) ^ 2 ≤ Real.cos θ ^ 2 := by
    rw [hcos]
    exact pow_le_pow_left₀ (by positivity) hsin_t_lb 2
  constructor
  · have h1 : Real.cos 1 * ((2 / π) * (π / 2 - θ)) ^ 2
        ≤ Real.sin θ * Real.cos θ ^ 2 :=
      mul_le_mul hsinθ hcos2_lb (by positivity)
        (le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_gt_three])))
    have he : Real.cos 1 * ((2 / π) * (π / 2 - θ)) ^ 2
        = (Real.cos 1 * (2 / π) ^ 2) * (π / 2 - θ) ^ 2 := by ring
    rwa [he] at h1
  · have h1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 * (π / 2 - θ) ^ 2 :=
      mul_le_mul (Real.sin_le_one θ) hcos2_ub (by positivity) (by norm_num)
    simpa using h1

/-! ## The `i = 0` case: `Γ` itself is `O((π/2 - θ)^{2α/3})` -/

/-- `|Γ(θ)| ≤ C (π/2 - θ)^{2α/3}` on `(π/2 - 1, π/2)`, for every real `α`. -/
theorem Gam_le_pi (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (π / 2 - 1) (π / 2),
      |Spaces.Gam α θ| ≤ C * (π / 2 - θ) ^ (2 * α / 3) := by
  obtain ⟨c, hc0, hc⟩ := gam_pi_ratio_bounds
  refine ⟨max 1 (c ^ (α / 3)), lt_max_iff.2 (Or.inl one_pos), ?_⟩
  intro θ hθ
  have ht0 : 0 < π / 2 - θ := by linarith [hθ.2]
  obtain ⟨hlb, hub⟩ := hc θ hθ
  have hpos : 0 < Real.sin θ * Real.cos θ ^ 2 := by
    have : 0 < c * (π / 2 - θ) ^ 2 := by positivity
    linarith
  have hGam : |Spaces.Gam α θ| = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := by
    rw [show Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl]
    exact abs_of_pos (Real.rpow_pos_of_pos hpos _)
  rw [hGam]
  have hpow : (π / 2 - θ) ^ (2 * α / 3) = ((π / 2 - θ) ^ 2) ^ (α / 3) := by
    rw [show 2 * α / 3 = ((2 : ℕ) : ℝ) * (α / 3) from by push_cast; ring,
      Real.rpow_natCast_mul (le_of_lt ht0)]
  rw [hpow]
  have ht2nn : (0 : ℝ) ≤ (π / 2 - θ) ^ 2 := by positivity
  by_cases hα : 0 ≤ α
  · have hz : 0 ≤ α / 3 := by linarith
    refine (Real.rpow_le_rpow (le_of_lt hpos) hub hz).trans ?_
    have hC : (1 : ℝ) ≤ max 1 (c ^ (α / 3)) := le_max_left _ _
    have hX : 0 ≤ ((π / 2 - θ) ^ 2) ^ (α / 3) := Real.rpow_nonneg ht2nn _
    simpa using mul_le_mul_of_nonneg_right hC hX
  · have hα' : α < 0 := not_le.mp hα
    have hz : α / 3 ≤ 0 := by linarith
    have hct : 0 < c * (π / 2 - θ) ^ 2 := by positivity
    have hle := Real.rpow_le_rpow_of_nonpos hct hlb hz
    rw [Real.mul_rpow (le_of_lt hc0) ht2nn] at hle
    refine hle.trans ?_
    have hC : c ^ (α / 3) ≤ max 1 (c ^ (α / 3)) := le_max_right _ _
    have hX : 0 ≤ ((π / 2 - θ) ^ 2) ^ (α / 3) := Real.rpow_nonneg ht2nn _
    exact mul_le_mul_of_nonneg_right hC hX

/-! ## Assembly -/

/-- `D_θ`-iterates of a function of `θ` alone, viewed as a function of `(z,θ)`, agree with
the univariate iterates `dthU^[i]`. -/
lemma DthIter_rad_eq' (i : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Spaces.DthIter i (fun _ θ => g θ) z θ = Spaces.dthU^[i] g θ := by
  have h : (fun (_ : ℝ) (θ : ℝ) => g θ) = (fun (z : ℝ) (θ : ℝ) => g θ * (1 : ℝ)) := by
    funext z θ; ring
  rw [h, Spaces.DthIter_decomp]
  ring

/-- `Tfun j α` is bounded on the closed angular interval `[π/2 - 1, π/2]`. -/
lemma Tfun_bdd_Icc (j : ℕ) (α : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Icc (π / 2 - 1) (π / 2), |Spaces.Tfun j α θ| ≤ M := by
  have hcont : ContinuousOn (Spaces.Tfun j α) (Set.Icc (π / 2 - 1) (π / 2)) :=
    (Spaces.Tfun_smooth j α).continuous.continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun θ hθ => ?_⟩
  have h := hM θ hθ
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

theorem Gam_jet_upper_pi (α : ℝ) (i : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (π / 2 - 1) (π / 2),
      |Spaces.DthIter i (fun _ θ => Spaces.Gam α θ) 0 θ| ≤ C * (π / 2 - θ) ^ (2 * α / 3) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Gam_le_pi α
  rcases i with _ | i
  · refine ⟨C₀, hC₀pos, fun θ hθ => ?_⟩
    simpa using hC₀ θ hθ
  · obtain ⟨M, hM0, hM⟩ := Tfun_bdd_Icc i α
    refine ⟨max 1 (|α| * M * C₀), lt_max_iff.2 (Or.inl one_pos), fun θ hθ => ?_⟩
    have hθ' : θ ∈ Set.Ioo 0 (π / 2) := ⟨by linarith [hθ.1, Real.pi_gt_three], hθ.2⟩
    have hid : Spaces.dthU^[i + 1] (fun t => Spaces.Gam α t) θ
        = α * Spaces.Tfun i α θ * Spaces.Gam α θ := DthU_iter_Gam_all i α hθ'
    have hval : Spaces.DthIter (i + 1) (fun _ θ => Spaces.Gam α θ) 0 θ
        = α * Spaces.Tfun i α θ * Spaces.Gam α θ := by
      rw [show Spaces.DthIter (i + 1) (fun _ θ => Spaces.Gam α θ) 0 θ
            = Spaces.dthU^[i + 1] (fun t => Spaces.Gam α t) θ from
          DthIter_rad_eq' (i + 1) (fun t => Spaces.Gam α t) 0 θ]
      exact hid
    rw [hval, abs_mul, abs_mul]
    have hb := hC₀ θ hθ
    have hMθ : |Spaces.Tfun i α θ| ≤ M := hM θ (Set.Ioo_subset_Icc_self hθ)
    have h1 : |α| * |Spaces.Tfun i α θ| * |Spaces.Gam α θ|
        ≤ |α| * M * (C₀ * (π / 2 - θ) ^ (2 * α / 3)) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hMθ (abs_nonneg α)) hb (abs_nonneg _) ?_
      exact mul_nonneg (abs_nonneg α) hM0
    refine h1.trans ?_
    have hX : 0 ≤ (π / 2 - θ) ^ (2 * α / 3) := Real.rpow_nonneg (by linarith [hθ.2]) _
    have hfin : |α| * M * (C₀ * (π / 2 - θ) ^ (2 * α / 3))
        ≤ max 1 (|α| * M * C₀) * (π / 2 - θ) ^ (2 * α / 3) := by
      have h := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (|α| * M * C₀)) hX
      have e : |α| * M * (C₀ * (π / 2 - θ) ^ (2 * α / 3))
          = (|α| * M * C₀) * (π / 2 - θ) ^ (2 * α / 3) := by ring
      rwa [e]
    exact hfin

end Work.Coercivity
