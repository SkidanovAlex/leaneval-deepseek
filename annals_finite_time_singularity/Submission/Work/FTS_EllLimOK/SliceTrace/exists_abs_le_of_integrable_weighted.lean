import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology

namespace Work.FTS_EllLimOK.SliceTrace

/-- `sin (2 x) ≥ 0` for `x` in `(t, π/2)` with `t > 0`. -/
private lemma sin_two_nonneg_of_mem {t x : ℝ} (ht : 0 < t) (hx : x ∈ Set.Ioo t (Real.pi / 2)) :
    0 ≤ Real.sin (2 * x) := by
  apply Real.sin_nonneg_of_mem_Icc
  constructor <;> linarith [ht, hx.1, hx.2, Real.pi_pos]

/-- On `(π/2 - θ, π/2)` with `0 < θ < π/2`, the weight `sin (2x) ^ (-γ)` dominates the
constant `(2θ) ^ (-γ)` (for `γ > 0`). -/
private lemma rpow_sin_two_ge {γ θ x : ℝ} (hγ : 0 < γ) (hθπ : θ < Real.pi / 2)
    (hx1 : Real.pi / 2 - θ < x) (hx2 : x < Real.pi / 2) :
    (2 * θ) ^ (-γ) ≤ (Real.sin (2 * x)) ^ (-γ) := by
  have hsx_pos : 0 < Real.sin (2 * x) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have hs2 : Real.sin (2 * x) ≤ 2 * θ := by
    have he : Real.sin (2 * x) = Real.sin (Real.pi - 2 * x) :=
      (Real.sin_pi_sub (2 * x)).symm
    rw [he]
    calc Real.sin (Real.pi - 2 * x) ≤ Real.pi - 2 * x := Real.sin_le (by linarith)
      _ ≤ 2 * θ := by linarith
  exact Real.rpow_le_rpow_of_nonpos hsx_pos hs2 (by linarith)

/-- Near the endpoint `π / 2`, integrability of `f ^ 2 * sin (2θ) ^ (-γ)` with `γ > 1` forces
`|f| ≤ d` at some point. -/
theorem exists_abs_le_of_integrable_weighted {γ : ℝ} (hγ : 1 < γ) {f : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
      (Set.Ioo t (Real.pi / 2))) {d : ℝ} (hd : 0 < d) :
    ∃ τ ∈ Set.Ioo t (Real.pi / 2), |f τ| ≤ d := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hγpos : 0 < γ := by linarith
  set S : Set ℝ := Set.Ioo t (Real.pi / 2) with hS
  set h : ℝ → ℝ := fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) with hh
  have hint' : IntegrableOn h S := hint
  set D : ℝ := ∫ x in S, h x with hD
  have hsnonneg : 0 ≤ᵐ[volume.restrict S] h := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := S) measurableSet_Ioo] with x hx
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (sin_two_nonneg_of_mem ht.1 hx) _)
  -- The key lower bound: the integral over any interval `(π/2 - θ, π/2)` dominates
  -- `d ^ 2 * (2 * θ) ^ (-γ) * θ`.
  have hmain : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2 - t),
      d ^ 2 * (2 * θ) ^ (-γ) * θ ≤ D := by
    intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθu : θ < Real.pi / 2 - t := hθ.2
    have ht1 : 0 < t := ht.1
    have hθπ : θ < Real.pi / 2 := by linarith
    have ha : t < Real.pi / 2 - θ := by linarith
    have hsub : Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2) ⊆ S := by
      rintro x ⟨hx1, hx2⟩
      exact ⟨lt_trans ha hx1, hx2⟩
    have hintf : IntegrableOn h (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2)) :=
      hint'.mono_set hsub
    have hconst : IntegrableOn (fun _ : ℝ => d ^ 2 * (2 * θ) ^ (-γ))
        (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2)) := by
      apply integrableOn_const
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
      · finiteness
    have hmono : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), (d ^ 2 * (2 * θ) ^ (-γ) : ℝ)
        ≤ ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), h x := by
      refine setIntegral_mono_on hconst hintf measurableSet_Ioo ?_
      intro x hx
      have hx1 : Real.pi / 2 - θ < x := hx.1
      have hx2 : x < Real.pi / 2 := hx.2
      have hcx : d < |f x| := hcon x ⟨lt_trans ha hx1, hx2⟩
      have hcsq : d ^ 2 ≤ (f x) ^ 2 := by
        have h := pow_le_pow_left₀ hd.le hcx.le 2
        rwa [sq_abs] at h
      have hw := rpow_sin_two_ge hγpos hθπ hx1 hx2
      have h2θ0 : 0 ≤ (2 * θ) ^ (-γ) := Real.rpow_nonneg (by linarith) _
      calc d ^ 2 * (2 * θ) ^ (-γ) ≤ (f x) ^ 2 * (2 * θ) ^ (-γ) :=
            mul_le_mul_of_nonneg_right hcsq h2θ0
        _ ≤ (f x) ^ 2 * (Real.sin (2 * x)) ^ (-γ) :=
            mul_le_mul_of_nonneg_left hw (sq_nonneg _)
        _ = h x := by rw [hh]
    have hval : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), (d ^ 2 * (2 * θ) ^ (-γ) : ℝ)
        = d ^ 2 * (2 * θ) ^ (-γ) * θ := by
      rw [setIntegral_const, Real.volume_real_Ioo,
        max_eq_left (show (0 : ℝ) ≤ Real.pi / 2 - (Real.pi / 2 - θ) by linarith),
        smul_eq_mul]
      ring
    have hb : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), h x ≤ D := by
      rw [hD]
      refine setIntegral_mono_set hint' ?_ ?_
      · exact hsnonneg
      · exact ae_of_all _ fun x hx => hsub hx
    linarith [hval ▸ hmono]
  -- The lower bound diverges as `θ → 0⁺`.
  have hgtop : Tendsto (fun θ : ℝ => d ^ 2 * (2 * θ) ^ (-γ) * θ) (𝓝[>] (0 : ℝ)) atTop := by
    have hr : Tendsto (fun θ : ℝ => θ ^ (1 - γ)) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_rpow_neg_nhdsGT_zero (by linarith : (1 : ℝ) - γ < 0)
    have hpos : 0 < d ^ 2 * (2 : ℝ) ^ (-γ) := by
      have h2 : 0 < (2 : ℝ) ^ (-γ) := Real.rpow_pos_of_pos (by norm_num) _
      positivity
    refine (hr.const_mul_atTop hpos).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hθ0 : 0 < θ := hθ
    have h1 : θ ^ (-γ) * θ = θ ^ (1 - γ) := by
      have key : θ ^ (-γ) * θ ^ (1 : ℝ) = θ ^ (-γ + 1) := (Real.rpow_add hθ0 (-γ) 1).symm
      rw [Real.rpow_one θ] at key
      rw [key, show -γ + 1 = 1 - γ from by ring]
    have hgoal : d ^ 2 * (2 * θ) ^ (-γ) * θ = d ^ 2 * 2 ^ (-γ) * θ ^ (1 - γ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hθ0.le]
      calc d ^ 2 * (2 ^ (-γ) * θ ^ (-γ)) * θ
          = d ^ 2 * (2 ^ (-γ) * (θ ^ (-γ) * θ)) := by ring
        _ = d ^ 2 * (2 ^ (-γ) * θ ^ (1 - γ)) := by rw [h1]
        _ = d ^ 2 * 2 ^ (-γ) * θ ^ (1 - γ) := by ring
    exact hgoal.symm
  have hevA : ∀ᶠ θ in 𝓝[>] (0 : ℝ), D + 1 < d ^ 2 * (2 * θ) ^ (-γ) * θ :=
    hgtop.eventually_gt_atTop (D + 1)
  have hevB : ∀ᶠ θ in 𝓝[>] (0 : ℝ), d ^ 2 * (2 * θ) ^ (-γ) * θ ≤ D :=
    Filter.mem_of_superset
      (Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 2 - t by linarith [ht.2]))
      fun θ hθ => hmain θ hθ
  obtain ⟨θ, h1, h2⟩ := (hevA.and hevB).exists
  linarith

end Work.FTS_EllLimOK.SliceTrace
