import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Series.BmodeBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

local notation "Iθ" => Work.Spaces.Iθ
local notation "Idm" => Work.FTS.EllipticEst.Lzero1
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "GB" => Work.FTS.VocabO.GamBar
local notation "λm" => Work.FTS.PhiStar.Gegenbauer.lam

theorem integrableOn_Iθ_of_continuous {f : ℝ → ℝ} (hf : ContinuousOn f Iθ) : IntegrableOn f Iθ := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (show IsCompact Iθ from isCompact_Icc) hf
  exact integrableOn_Iθ_of_bound (hf.aestronglyMeasurable measurableSet_Iθ) (C := C) (fun θ hθ => by
    have h := hC θ hθ
    rwa [Real.norm_eq_abs] at h)

/-- The main coefficient identity: `λ_m · (ψ, e_m) = (Γ̄, e_m)` on `Iθ`. -/
theorem coeff_eq (χ : ℝ → ℝ → ℝ)
    (hχc : ∀ δ : ℝ, 0 < δ → ContDiff ℝ 2 (χ δ))
    (hχ1 : ∀ δ : ℝ, 0 < δ → ∀ θ ∈ Set.Icc δ (Real.pi / 2 - δ), χ δ θ = 1)
    (hχ0 : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, θ ∉ Set.Ioo (δ / 2) (Real.pi / 2 - δ / 2) → χ δ θ = 0)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {ψ : ℝ → ℝ} (hang : AngModel α ψ) (m : ℕ)
    (hlimA : Tendsto (fun n : ℕ => ∫ θ in Iθ, ψ θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
      atTop (nhds (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ)))
    (hlimC : Tendsto (fun n : ℕ => ∫ θ in Iθ, GB α θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
      atTop (nhds (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ)))
    (hlimB : Tendsto (fun n : ℕ => ∫ θ in Iθ, ψ θ *
        (-(deriv (deriv (χ (1 / ((n : ℝ) + 1)))) θ * eF m θ)
          - 2 * (deriv (χ (1 / ((n : ℝ) + 1))) θ * deriv (eF m) θ)
          + Real.tan θ * deriv (χ (1 / ((n : ℝ) + 1))) θ * eF m θ) * Real.cos θ)
      atTop (nhds 0)) :
    λm m * (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ)
      = ∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ := by
  have hmain : ∀ n : ℕ,
      λm m * (∫ θ in Iθ, ψ θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
        + (∫ θ in Iθ, ψ θ * (-(deriv (deriv (χ (1 / ((n : ℝ) + 1)))) θ * eF m θ)
            - 2 * (deriv (χ (1 / ((n : ℝ) + 1))) θ * deriv (eF m) θ)
            + Real.tan θ * deriv (χ (1 / ((n : ℝ) + 1))) θ * eF m θ) * Real.cos θ) = 0 := by
    intro n
    let δ : ℝ := 1 / ((n : ℝ) + 1)
    let e : ℝ → ℝ := fun θ => eF m θ
    let G : ℝ → ℝ := fun θ => GB α θ
    let V : ℝ → ℝ := fun θ => χ δ θ * e θ
    let CD : ℝ → ℝ := fun θ => -(deriv (deriv (χ δ)) θ * e θ)
      - 2 * (deriv (χ δ) θ * deriv e θ) + Real.tan θ * deriv (χ δ) θ * e θ
    change λm m * (∫ θ in Iθ, ψ θ * χ δ θ * e θ * Real.cos θ)
        - (∫ θ in Iθ, G θ * χ δ θ * e θ * Real.cos θ)
        + (∫ θ in Iθ, ψ θ * CD θ * Real.cos θ) = 0
    have hδpos : 0 < δ := by dsimp only [δ]; positivity
    have hδle : δ ≤ 1 := by
      dsimp only [δ]
      rw [div_le_one (by positivity : (0:ℝ) < (n:ℝ) + 1)]
      have h1 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hcpos : 0 < δ / 2 := by linarith
    have hcd : δ / 2 < Real.pi / 2 - δ / 2 := by
      linarith [Real.pi_gt_three, hδle]
    have hdlt : Real.pi / 2 - δ / 2 < Real.pi / 2 := by linarith
    have hf : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (Real.pi / 2)) :=
      hang.smooth.of_le (by simp [Work.Stability.smoothOrder])
    have hVc : ContDiffOn ℝ 2 V (Set.Ioo 0 (Real.pi / 2)) := by
      dsimp only [V]
      exact (hχc δ hδpos).contDiffOn.mul (contDiff_eF m).contDiffOn
    have hV0 : ∀ θ, θ ∉ Set.Icc (δ / 2) (Real.pi / 2 - δ / 2) → V θ = 0 := by
      intro θ hθ
      dsimp only [V]
      rw [hχ0 δ hδpos θ (fun hm => hθ (Set.Ioo_subset_Icc_self hm)), zero_mul]
    have hibp := ibp_Iθ (u := ψ) (v := V) hcpos hcd hdlt hf hVc hV0
    have hpt : ∀ θ ∈ Iθ,
        (ψ θ * Idm V θ - Idm ψ θ * V θ) * Real.cos θ
          = (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ + ψ θ * CD θ) * Real.cos θ := by
      intro θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · rw [← h0]
        have hψ0 : ψ 0 = 0 := hang.bdry0
        have he0 : e 0 = 0 := by dsimp only [e]; exact eF_zero m
        have hG0 : G 0 = 0 := by dsimp only [G]; exact GamBar_zero hα
        have hVz : V 0 = 0 := by dsimp only [V]; rw [he0, mul_zero]
        rw [hψ0, hVz, he0, hG0]
        dsimp only [CD]
        ring
      · rcases eq_or_lt_of_le hθ.2 with h2 | h2
        · rw [h2]
          simp [Real.cos_pi_div_two]
        · have hcos : Real.cos θ ≠ 0 :=
            ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [h0, Real.pi_pos], h2⟩)
          have hVeq : V θ = χ δ θ * e θ := rfl
          have hχe : Idm (fun t => χ δ t * e t) θ
              = χ δ θ * Idm e θ + (-(deriv (deriv (χ δ)) θ * e θ)
                  - 2 * (deriv (χ δ) θ * deriv e θ) + Real.tan θ * deriv (χ δ) θ * e θ) :=
            lzero1_mul_eq (hχc δ hδpos) (contDiff_eF m) hcos
          have hee : Idm e θ = λm m * e θ := by
            have h2' : Idm e θ = Work.Elliptic.Lzero (fun _ θ' => eF m θ') 0 θ :=
              (congrFun (Work.FTS.EllipticEst.Lzero1_eq_Lzero (eF m) 0)) θ
            rw [h2']
            exact Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hcos 0
          have hψψ : Idm ψ θ = G θ := by
            dsimp only [G]; exact hang.eq θ ⟨h0, h2⟩
          have hVe : V θ = χ δ θ * e θ := rfl
          rw [hVe, hχe, hee, hψψ]
          dsimp only [CD]
          ring
    have hkey : (∫ θ in Iθ, (ψ θ * Idm V θ - Idm ψ θ * V θ) * Real.cos θ)
        = ∫ θ in Iθ, (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ
            + ψ θ * CD θ) * Real.cos θ :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Iθ hpt
    have hcontψ : ContinuousOn ψ Iθ := hang.cont
    have hcontχ : ContinuousOn (χ δ) Iθ := (hχc δ hδpos).continuous.continuousOn
    have hconte : ContinuousOn e Iθ := by
      dsimp only [e]; exact (contDiff_eF m).continuous.continuousOn
    have hcontG : ContinuousOn G Iθ := by
      dsimp only [G]; exact continuousOn_GamBar α hα hα1
    have hcontDχ : ContinuousOn (deriv (χ δ)) Iθ :=
      ((hχc δ hδpos).continuous_deriv (by norm_num)).continuousOn
    have hcontD2χ : ContinuousOn (deriv (deriv (χ δ))) Iθ := by
      have h1 : ContDiff ℝ 1 (deriv (χ δ)) := (hχc δ hδpos).deriv'
      exact (h1.continuous_deriv (by norm_num)).continuousOn
    have hcontDe : ContinuousOn (deriv e) Iθ := by
      dsimp only [e]
      exact ((contDiff_eF m).continuous_deriv (by norm_num)).continuousOn
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin θ) Iθ := Real.continuous_sin.continuousOn
    have hcosc : ContinuousOn (fun θ : ℝ => Real.cos θ) Iθ := Real.continuous_cos.continuousOn
    -- integrability of the two pieces
    have hint1 : IntegrableOn (fun θ => (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ)
        * Real.cos θ) Iθ :=
      integrableOn_Iθ_of_continuous
        (((continuousOn_const.mul (hcontψ.mul hcontχ |>.mul hconte))).sub
          (hcontG.mul hcontχ |>.mul hconte) |>.mul hcosc)
    have hCDeq : ∀ θ ∈ Iθ, ψ θ * CD θ * Real.cos θ
        = ψ θ * (-(deriv (deriv (χ δ)) θ * e θ) - 2 * (deriv (χ δ) θ * deriv e θ))
            * Real.cos θ + ψ θ * (Real.sin θ * deriv (χ δ) θ * e θ) := by
      intro θ hθ
      rcases eq_or_ne (Real.cos θ) 0 with hc | hc
      · have heθ : e θ = 0 := by
          dsimp only [e]
          rcases eq_or_lt_of_le hθ.1 with h0 | h0
          · rw [← h0]; exact eF_zero m
          · rcases eq_or_lt_of_le hθ.2 with h2 | h2
            · rw [h2]; exact eF_pi m
            · exact absurd hc (ne_of_gt (Real.cos_pos_of_mem_Ioo
                ⟨by linarith [h0, Real.pi_pos], h2⟩))
        dsimp only [CD]
        rw [hc, heθ]
        ring
      · have htan : Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ
            = Real.sin θ * deriv (χ δ) θ * e θ := by
          rw [Real.tan_eq_sin_div_cos]
          field_simp
        dsimp only [CD]
        rw [show ψ θ * (-(deriv (deriv (χ δ)) θ * e θ) - 2 * (deriv (χ δ) θ * deriv e θ)
              + Real.tan θ * deriv (χ δ) θ * e θ) * Real.cos θ
            = ψ θ * (-(deriv (deriv (χ δ)) θ * e θ) - 2 * (deriv (χ δ) θ * deriv e θ)) * Real.cos θ
              + ψ θ * (Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ) from by ring,
          htan]
    have hint2' : IntegrableOn (fun θ => ψ θ * (-(deriv (deriv (χ δ)) θ * e θ)
        - 2 * (deriv (χ δ) θ * deriv e θ)) * Real.cos θ
        + ψ θ * (Real.sin θ * deriv (χ δ) θ * e θ)) Iθ :=
      integrableOn_Iθ_of_continuous
        ((hcontψ.mul (((hcontD2χ.mul hconte).neg).sub (hcontDχ.mul hcontDe |>.const_mul 2))).mul
            hcosc |>.add (hcontψ.mul (hsin.mul hcontDχ |>.mul hconte)))
    have hint2 : IntegrableOn (fun θ => ψ θ * CD θ * Real.cos θ) Iθ := by
      refine hint2'.congr_fun (fun θ hθ => ?_) measurableSet_Iθ
      exact (hCDeq θ hθ).symm
    -- splitting
    have hsplit1 : (∫ θ in Iθ, (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ
          + ψ θ * CD θ) * Real.cos θ)
        = (∫ θ in Iθ, (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ) * Real.cos θ)
          + (∫ θ in Iθ, ψ θ * CD θ * Real.cos θ) := by
      rw [show (fun θ => (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ + ψ θ * CD θ)
            * Real.cos θ)
          = fun θ => ((λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ) * Real.cos θ)
            + (ψ θ * CD θ * Real.cos θ) from by funext θ; ring]
      rw [integral_add hint1 hint2]
    have hsplit2 : (∫ θ in Iθ, (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ) * Real.cos θ)
        = λm m * (∫ θ in Iθ, ψ θ * χ δ θ * e θ * Real.cos θ)
          - (∫ θ in Iθ, G θ * χ δ θ * e θ * Real.cos θ) := by
      have hP : IntegrableOn (fun θ => λm m * (ψ θ * χ δ θ * e θ * Real.cos θ)) Iθ :=
        integrableOn_Iθ_of_continuous
          (continuousOn_const.mul ((hcontψ.mul hcontχ |>.mul hconte) |>.mul hcosc))
      have hQ : IntegrableOn (fun θ => G θ * χ δ θ * e θ * Real.cos θ) Iθ :=
        integrableOn_Iθ_of_continuous ((hcontG.mul hcontχ |>.mul hconte) |>.mul hcosc)
      have hcongr : (∫ θ in Iθ, (λm m * (ψ θ * χ δ θ * e θ) - G θ * χ δ θ * e θ) * Real.cos θ)
          = ∫ θ in Iθ, ((λm m * (ψ θ * χ δ θ * e θ * Real.cos θ))
              - (G θ * χ δ θ * e θ * Real.cos θ)) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ _ => by ring)
      rw [hcongr, integral_sub hP hQ, integral_const_mul]
    rw [hkey] at hibp
    rw [hsplit1] at hibp
    rw [hsplit2] at hibp
    exact hibp
  have hL1 : Tendsto (fun n : ℕ =>
      λm m * (∫ θ in Iθ, ψ θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)) atTop
      (nhds (λm m * (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ))) :=
    (hlimA.const_mul (λm m)).sub hlimC
  have hL2 : Tendsto (fun n : ℕ =>
      λm m * (∫ θ in Iθ, ψ θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * χ (1 / ((n : ℝ) + 1)) θ * eF m θ * Real.cos θ)
        + (∫ θ in Iθ, ψ θ * (-(deriv (deriv (χ (1 / ((n : ℝ) + 1)))) θ * eF m θ)
            - 2 * (deriv (χ (1 / ((n : ℝ) + 1))) θ * deriv (eF m) θ)
            + Real.tan θ * deriv (χ (1 / ((n : ℝ) + 1))) θ * eF m θ) * Real.cos θ)) atTop
      (nhds (λm m * (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ) + 0)) :=
    hL1.add hlimB
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (nhds (λm m * (∫ θ in Iθ, ψ θ * eF m θ * Real.cos θ)
        - (∫ θ in Iθ, GB α θ * eF m θ * Real.cos θ) + 0)) := by
    refine hL2.congr' ?_
    filter_upwards with n
    exact hmain n
  have hfin := tendsto_nhds_unique hzero tendsto_const_nhds
  linarith [hfin]

/-- The `L²(cos θ dθ)` norm of `e_m` is at least `(2m+1)/2`. -/
theorem eFam_norm_ge (m : ℕ) (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 1) / 2 ≤ ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by
  rw [Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m]
  have h2 : (0:ℝ) < 2 := by norm_num
  have h3 : (0:ℝ) < 4 * (m:ℝ) + 5 := by positivity
  rw [div_le_iff₀ h2]
  rw [show ((2 * (m:ℝ) + 2) * (2 * (m:ℝ) + 3)) / (4 * (m:ℝ) + 5) * 2
      = (2 * ((2 * (m:ℝ) + 2) * (2 * (m:ℝ) + 3))) / (4 * (m:ℝ) + 5) from by ring]
  rw [le_div_iff₀ h3]
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  nlinarith [hm0]

theorem int_cos_Iθ : (∫ θ in Iθ, Real.cos θ) = 1 := by
  rw [← iota_eq]
  rw [integral_cos]
  norm_num


end Work.FTS.PhiStar.Series
