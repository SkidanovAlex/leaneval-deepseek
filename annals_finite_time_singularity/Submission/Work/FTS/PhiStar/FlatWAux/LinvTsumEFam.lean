/-
# `Work.FTS.PhiStar.FlatWAux.LinvTsumEFam` — `Linv` commutes with the `eFam`-series

`Work.FTS.PhiStar.Linv h θ` is the `σ`-normalised zero-moment Dirichlet inverse of `L₀`
(`StarDefs.lean`).  Its *regularised* shape (`Linv23Aux.Defs`) is

`Linv h θ = -(sin²θ cos³θ)⁻¹ · ∫_0^θ (sin t · cos²t / 2) · h t dt`   (`Linv_eq_phi`),

so it is linear in `h` as soon as the integral may be interchanged with the (infinite) series
`Σ_m c_m · eFam m`.  The growth hypotheses `|c_m| ≤ Cd (m+1)^{-5/2}` and
`|eFam m θ| ≤ Ce (2m+1)` make the majorant `Σ_m (2m+1)(m+1)^{-5/2} ≍ Σ_m m^{-3/2}` summable,
which is exactly what the dominated-convergence interchange needs.

The proof is therefore: (i) the regularised integrand of the series is the series of the
regularised integrands (`tsum` manipulation), (ii) the integral/`tsum` interchange
(`MeasureTheory.integral_tsum_of_summable_integral_norm`, with the summable majorant),
(iii) reassembly with `Linv_eq_phi` and `tsum_mul_left`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Linv23Aux.Defs
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-- The summability majorant of the `m`-th summand of the `Linv`-series: `(2m+1)·(m+1)^{-5/2}`,
which is of order `m^{-3/2}` and hence summable. -/
def linvMaj (m : ℕ) : ℝ := (2 * (m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))

theorem linvMaj_def (m : ℕ) :
    linvMaj m = (2 * (m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := rfl

theorem linvMaj_nonneg (m : ℕ) : 0 ≤ linvMaj m := by
  rw [linvMaj_def]
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)

/-- The majorant `Σ_m (2m+1)(m+1)^{-5/2}` is summable (comparison with `Σ_m (m+1)^{-3/2}`). -/
theorem linvMaj_summable : Summable linvMaj := by
  have h3 : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
    have h : Summable (fun m : ℕ => ((m : ℝ)) ^ (-(3 / 2 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(3 / 2 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun m : ℕ => ((m : ℝ)) ^ (-(3 / 2 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  have hmaj : Summable (fun m : ℕ => 2 * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := h3.mul_left 2
  refine Summable.of_nonneg_of_le (fun m => linvMaj_nonneg m) (fun m => ?_) hmaj
  rw [linvMaj_def]
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hpow : ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))
      = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    calc ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))
        = ((m : ℝ) + 1) ^ (1 : ℝ) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
          rw [Real.rpow_one]
      _ = ((m : ℝ) + 1) ^ ((1 : ℝ) + (-(5 / 2 : ℝ))) := by rw [Real.rpow_add hm1]
      _ = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
          rw [show (1 : ℝ) + (-(5 / 2 : ℝ)) = -(3 / 2 : ℝ) by norm_num]
  calc (2 * (m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))
      ≤ (2 * ((m : ℝ) + 1)) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt hm1) _)
        linarith
    _ = 2 * (((m : ℝ) + 1) * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) := by ring
    _ = 2 * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by rw [hpow]

theorem LinvTsumEFam (c : ℕ → ℝ) (Cd Ce : ℝ) (hCd : 0 ≤ Cd) (hCe : 0 ≤ Ce)
    (hsup : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Ce * (2 * (m : ℝ) + 1))
    (hc : ∀ m : ℕ, |c m| ≤ Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.FTS.PhiStar.Linv
          (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
        = ∑' m : ℕ, c m * Work.FTS.PhiStar.Linv
            (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ := by
  intro θ hθ
  obtain ⟨hθ0, hθπ⟩ := hθ
  have hθle : (0 : ℝ) ≤ θ := le_of_lt hθ0
  -- every point of `[0, θ]` lies in `Iθ = [0, π/2]`
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) θ, t ∈ Work.Spaces.Iθ := by
    intro t ht
    have h2 : t ≤ Real.pi / 2 := le_of_lt (lt_of_le_of_lt ht.2 hθπ)
    change t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
    exact Set.mem_Icc.mpr ⟨ht.1, h2⟩
  -- the pointwise bound on the regularised integrand of a single mode
  have hLip : ∀ m t, t ∈ Set.Icc (0 : ℝ) θ →
      |Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t|
        ≤ Ce * (2 * (m : ℝ) + 1) / 2 := by
    intro m t ht
    have hfac : |Real.sin t * Real.cos t ^ 2 / 2| ≤ 1 / 2 := by
      rw [abs_div, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h2 : |Real.sin t| * |Real.cos t| ^ 2 ≤ 1 :=
        calc |Real.sin t| * |Real.cos t| ^ 2 ≤ 1 * 1 :=
              mul_le_mul (Real.abs_sin_le_one t)
                (by nlinarith [Real.abs_cos_le_one t, abs_nonneg (Real.cos t)])
                (by positivity) zero_le_one
          _ = 1 := by norm_num
      linarith
    calc |Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t|
        = |Real.sin t * Real.cos t ^ 2 / 2|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m t| := by
          simp only [Work.FTS.PhiStar.LinvPhiInt, abs_mul]
      _ ≤ (1 / 2) * (Ce * (2 * (m : ℝ) + 1)) :=
          mul_le_mul hfac (hsup m t (hmem t ht)) (abs_nonneg _) (by norm_num)
      _ = Ce * (2 * (m : ℝ) + 1) / 2 := by ring
  -- the same bound against the summable majorant
  have hGb : ∀ m t, t ∈ Set.Icc (0 : ℝ) θ →
      ‖c m * Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖
        ≤ Cd * Ce / 2 * linvMaj m := by
    intro m t ht
    rw [Real.norm_eq_abs, abs_mul]
    calc |c m| * |Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t|
        ≤ (Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) * (Ce * (2 * (m : ℝ) + 1) / 2) :=
          mul_le_mul (hc m) (hLip m t ht) (abs_nonneg _)
            (mul_nonneg hCd (Real.rpow_nonneg (by positivity) _))
      _ = Cd * Ce / 2 * linvMaj m := by
          rw [linvMaj_def]; ring
  -- continuity, hence integrability of every summand on `(0, θ]`
  have hcontG : ∀ m : ℕ, Continuous (fun t : ℝ =>
      c m * Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t) := by
    intro m
    have hli : Continuous (fun t : ℝ =>
        Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t) := by
      change Continuous (fun t : ℝ => Real.sin t * Real.cos t ^ 2 / 2
        * Work.FTS.PhiStar.Gegenbauer.eFam m t)
      exact ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).div_const 2).mul
        (Work.FTS.PhiStar.Series.continuous_eFam m)
    exact continuous_const.mul hli
  have hGint : ∀ m : ℕ, Integrable
      (fun t : ℝ => c m * Work.FTS.PhiStar.LinvPhiInt (Work.FTS.PhiStar.Gegenbauer.eFam m) t)
      (volume.restrict (Set.Ioc (0 : ℝ) θ)) := by
    intro m
    exact ((hcontG m).intervalIntegrable (0 : ℝ) θ).1
  -- the integral of the norm of a summand is bounded by the summable majorant
  have hle : ∀ m : ℕ, ∫ t, ‖c m * Work.FTS.PhiStar.LinvPhiInt
        (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) θ))
      ≤ θ * (Cd * Ce / 2 * linvMaj m) := by
    intro m
    have h1 : IntervalIntegrable (fun t : ℝ => ‖c m * Work.FTS.PhiStar.LinvPhiInt
        (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖) volume (0 : ℝ) θ :=
      (hcontG m).norm.intervalIntegrable 0 θ
    have h2 : IntervalIntegrable (fun _ : ℝ => Cd * Ce / 2 * linvMaj m) volume (0 : ℝ) θ :=
      continuous_const.intervalIntegrable 0 θ
    rw [← intervalIntegral.integral_of_le hθle]
    have hmono := intervalIntegral.integral_mono_on hθle h1 h2 (fun x hx => hGb m x hx)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
    exact hmono
  have hGsum : Summable (fun m : ℕ => ∫ t, ‖c m * Work.FTS.PhiStar.LinvPhiInt
      (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) θ))) := by
    refine Summable.of_norm_bounded (g := fun m : ℕ => θ * (Cd * Ce / 2 * linvMaj m))
      ((linvMaj_summable.mul_left (Cd * Ce / 2)).mul_left θ) (fun m => ?_)
    calc ‖∫ t, ‖c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖
            ∂(volume.restrict (Set.Ioc (0 : ℝ) θ))‖
        ≤ ∫ t, ‖‖c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖‖
            ∂(volume.restrict (Set.Ioc (0 : ℝ) θ)) :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ t, ‖c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t‖
            ∂(volume.restrict (Set.Ioc (0 : ℝ) θ)) := by simp
      _ ≤ θ * (Cd * Ce / 2 * linvMaj m) := hle m
  -- the interchange of the integral with the series
  have hkey : (∑' m : ℕ, ∫ t, c m * Work.FTS.PhiStar.LinvPhiInt
        (Work.FTS.PhiStar.Gegenbauer.eFam m) t ∂(volume.restrict (Set.Ioc (0 : ℝ) θ)))
      = ∫ t in Set.Ioc (0 : ℝ) θ, ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhiInt
          (Work.FTS.PhiStar.Gegenbauer.eFam m) t :=
    MeasureTheory.integral_tsum_of_summable_integral_norm
      (μ := volume.restrict (Set.Ioc (0 : ℝ) θ))
      (F := fun m t => c m * Work.FTS.PhiStar.LinvPhiInt
        (Work.FTS.PhiStar.Gegenbauer.eFam m) t) hGint hGsum
  -- the pointwise identity for the regularised integrand of the series
  have hpt : ∀ t : ℝ, Work.FTS.PhiStar.LinvPhiInt
      (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) t
      = ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhiInt
          (Work.FTS.PhiStar.Gegenbauer.eFam m) t := by
    intro t
    simp only [Work.FTS.PhiStar.LinvPhiInt]
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    rw [← mul_assoc, mul_comm (Real.sin t * Real.cos t ^ 2 / 2) (c m), mul_assoc]
  -- hence `LinvPhi` of the series is the series of the `LinvPhi`
  have hPhi : Work.FTS.PhiStar.LinvPhi
      (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
      = ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhi
          (Work.FTS.PhiStar.Gegenbauer.eFam m) θ := by
    calc Work.FTS.PhiStar.LinvPhi
          (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
        = ∫ t in (0 : ℝ)..θ, Work.FTS.PhiStar.LinvPhiInt
            (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) t := rfl
      _ = ∫ t in (0 : ℝ)..θ, ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t :=
          intervalIntegral.integral_congr (fun t _ => hpt t)
      _ = ∫ t in Set.Ioc (0 : ℝ) θ, ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t := intervalIntegral.integral_of_le hθle
      _ = ∑' m : ℕ, ∫ t in Set.Ioc (0 : ℝ) θ, c m * Work.FTS.PhiStar.LinvPhiInt
            (Work.FTS.PhiStar.Gegenbauer.eFam m) t := hkey.symm
      _ = ∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhi
            (Work.FTS.PhiStar.Gegenbauer.eFam m) θ := by
          refine tsum_congr (fun m => ?_)
          rw [← intervalIntegral.integral_of_le hθle, intervalIntegral.integral_const_mul]
          rfl
  -- the pulled-out form of `Linv`
  have hLinv_eq : ∀ h : ℝ → ℝ, Work.FTS.PhiStar.Linv h θ
      = (-(Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹) * Work.FTS.PhiStar.LinvPhi h θ := by
    intro h
    rw [Work.FTS.PhiStar.Linv_eq_phi]
    rw [neg_mul]
  have hstep : ∀ m : ℕ, c m * Work.FTS.PhiStar.Linv
      (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
      = (-(Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹) * (c m * Work.FTS.PhiStar.LinvPhi
          (Work.FTS.PhiStar.Gegenbauer.eFam m) θ) := by
    intro m
    rw [hLinv_eq]
    rw [← mul_assoc, mul_comm (c m) (-(Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹), mul_assoc]
  -- the final assembly
  calc Work.FTS.PhiStar.Linv
        (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
      = -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * Work.FTS.PhiStar.LinvPhi
          (fun t : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ) :=
        Work.FTS.PhiStar.Linv_eq_phi _ _
    _ = -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ * (∑' m : ℕ, c m * Work.FTS.PhiStar.LinvPhi
          (Work.FTS.PhiStar.Gegenbauer.eFam m) θ)) := by rw [hPhi]
    _ = ∑' m : ℕ, c m * Work.FTS.PhiStar.Linv
          (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ := by
        rw [tsum_congr hstep, tsum_mul_left, neg_mul]

end Work.FTS.PhiStar.FlatWAux
