import Mathlib
import Submission.Work.FlowerGlue2.exists_rep_inverse_sector_fatou2
import Submission.Work.FlowerGlue2.fine_Z_decay_fatou
import Submission.Work.FlowerGlue2.exists_preimage_of_lipschitz
import Submission.Work.FlowerGlue2.exists_conjugacy_Z_fine
import Submission.Work.FlowerGlue2.log_ratio_antitone
import Submission.Work.FatouCoord.Repelling.norm_Lambda_sub_le
import Submission.Work.FatouCoordFix.Repelling.ZCorrection
import Submission.Work.FatouCoord.Flower.exists_threshold_log_div
import Submission.Work.FatouCoord.Exist.exists_threshold_log_linear
import Submission.Work.FlowerGlue2.norm_Lambda_shift_no_ha

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The inverse of the repelling coordinate on a Stolz sector, with no hypothesis on `a`

`Work.FlowerGlue2.exists_rep_inverse_stolz` is the *sign-free* Stolz-sector version of
`Work.FlowerGlue2.exists_rep_inverse_sector_fatou2`: same conclusion, but

* the hypothesis `ha : a.re < 1` is dropped (only `ParabolicBounds f h a r A A'` is assumed), and
* the inverse is only asked for on a Stolz sector: for every `R₁ ≥ R` there is a deeper
  `R' ≥ R₁` such that every `w` with `Re w < -R'` and `|Im w| < -Re w + 1` has a preimage
  `v` under the repelling coordinate `V` with `Re v < -R₁ - 2`, and `v` is within
  `K (1 + log ‖w‖)/‖w‖` of the formal inverse `w - (1 - a) Λ w`.

## Why the sign of `Re (1 - a)` is not needed

The construction (`exists_conjugacy_Z_fine`) produces the repelling coordinate
`V w = w + (1 - a) Λ w + Z w` with `Z` of size `O((1 + log ‖w‖)/‖w‖)` on a far left half-plane,
and `V` is a bijection onto it.  The preimage of `w` is obtained by the contraction
`u ↦ u - (V (v₀ + u) - w)` on the ball of radius `ρ ≍ (1 + log ‖w‖)/‖w‖` around the formal
inverse `v₀ = w - (1 - a) Λ w` (`exists_preimage_of_lipschitz`).

The only place where `a.re < 1` entered `exists_rep_inverse_sector_fatou2` was to guarantee that
`v₀` (and hence the ball around it) stays on the far left half-plane, see the note
`NOTES_LEAD_mandelbar_gaps3.md` §1.3: `Re v₀ = Re w - Re(1 - a) log ‖w‖ + O(1)`, and if
`Re (1 - a) < 0` the logarithmic term pushes `v₀` to the *right*.  On the Stolz sector
`|Im w| < -Re w + 1` we have `‖w‖ ≤ 2 (-Re w) + 1`, so

  `Re v₀ ≤ Re w + max 0 (-Re (1-a)) · log (2 (-Re w) + 1) + 2π |Im (1-a)|`,

and `S - α log (2S+1) → ∞` as `S = -Re w → ∞`; choosing `R'` large enough therefore keeps `v₀`
(and the ball of radius `ρ ≤ 1/2` around it) strictly to the left of `-R₁ - 3`, as required.
The estimate `Λ (w - (1-a) Λ w) - Λ w = O((1 + log ‖w‖)/‖w‖)` used for the defect of `v₀` is
also sign-free, `Work.FlowerGlue2.norm_Lambda_shift_no_ha`.

Everything else is copied from the Fatou2 argument: `‖Z‖` is Lipschitz with constant
`1/(R - R_f)` and `Λ` with constant `1/R` on the half-plane `{Re < -R}`, so the map above is a
contraction with ratio `κ = ‖1 - a‖/R + 1/(R - R_f) ≤ 1/2`.
-/

namespace Work.FlowerGlue2

open Filter Set Metric
open scoped Topology
open Work.FatouCoord.Petal

set_option maxHeartbeats 1600000

theorem exists_rep_inverse_stolz {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ R : ℝ, 0 < R ∧ ∃ Z V : ℂ → ℂ,
      DifferentiableOn ℂ V {w : ℂ | w.re < -R} ∧
      (∀ w : ℂ, w.re < -R → V w = w + (1 - a) * Work.FatouCoord.Petal.Lambda w + Z w) ∧
      (∀ w : ℂ, w.re < -R → V (w + 1) = Work.FatouCoord.wMap f (V w)) ∧
      Set.InjOn V {w : ℂ | w.re < -R} ∧ (∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ ‖w‖ / 2) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ R₁ ≥ R, ∃ R' : ℝ, R₁ ≤ R' ∧ ∀ w : ℂ, w.re < -R' → |w.im| < -w.re + 1 →
        ∃ v : ℂ, v.re < -R₁ - 2 ∧ V v = w ∧
          ‖v - (w - (1 - a) * Work.FatouCoord.Petal.Lambda w)‖
            ≤ K * (1 + Real.log ‖w‖) / ‖w‖ := by
  -- #### the fine repelling package
  obtain ⟨Rf, hRfpos, _, Z, V, hZdiff, hZbd, _, hVdiff, hVdef, hVconj, hVnorm, _, hVinj,
    hZdec⟩ := exists_conjugacy_Z_fine hb
  obtain ⟨K_Z, hK_Zpos, hK_Z⟩ := hZdec
  -- #### constants
  set c : ℝ := ‖(1 : ℂ) - a‖ with hcdef
  have hcnn : 0 ≤ c := by rw [hcdef]; exact norm_nonneg _
  set d : ℝ := (1 - a).re with hddef
  set E : ℝ := |(1 - a).im| with hEdef
  have hEnn : 0 ≤ E := by rw [hEdef]; exact abs_nonneg _
  set α : ℝ := max 0 (-d) with hαdef
  have hαnn : 0 ≤ α := by rw [hαdef]; exact le_max_left _ _
  have hlog2pos : 0 < 1 + Real.log 2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith
  set Kb : ℝ := 16 * c ^ 2 + 4 * K_Z * (1 + Real.log 2) + 1 with hKbdef
  have hKbpos : 0 < Kb := by
    rw [hKbdef]
    have h1 : 0 ≤ 16 * c ^ 2 := by positivity
    have h2 : 0 ≤ 4 * K_Z * (1 + Real.log 2) := by nlinarith [hK_Zpos.le, hlog2pos]
    linarith
  -- #### thresholds
  obtain ⟨T₁, hT₁pos, hT₁⟩ := Work.FatouCoord.Flower.exists_threshold_log_div c
  obtain ⟨T₂, hT₂pos, hT₂⟩ := Work.FatouCoord.Flower.exists_threshold_log_div (2 * Kb)
  obtain ⟨T₄, hT₄pos, hT₄⟩ := norm_Lambda_shift_no_ha (a := a)
  let s : Finset ℝ := {Rf + 4, T₁, T₂, T₄, 4 * c + 4, 4}
  have hsne : s.Nonempty := ⟨4, by simp [s]⟩
  set R : ℝ := s.max' hsne with hRdef
  have hle : ∀ x ∈ s, x ≤ R := fun x hx => by rw [hRdef]; exact Finset.le_max' s x hx
  have hRf4 : Rf + 4 ≤ R := hle (Rf + 4) (by simp [s])
  have hT₁R : T₁ ≤ R := hle T₁ (by simp [s])
  have hT₂R : T₂ ≤ R := hle T₂ (by simp [s])
  have hT₄R : T₄ ≤ R := hle T₄ (by simp [s])
  have h4cR : 4 * c + 4 ≤ R := hle (4 * c + 4) (by simp [s])
  have h4R : (4 : ℝ) ≤ R := hle 4 (by simp [s])
  have hRpos : 0 < R := by linarith
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hRfR : Rf < R := by linarith
  -- #### the contraction ratio
  set κ : ℝ := c / R + 1 / (R - Rf) with hκdef
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    have h1 : 0 ≤ c / R := div_nonneg hcnn hRpos.le
    have h2 : 0 ≤ 1 / (R - Rf) := div_nonneg (by norm_num) (by linarith)
    linarith
  have hκ1 : κ ≤ 1 / 2 := by
    rw [hκdef]
    have h1 : c / R ≤ 1 / 4 := by rw [div_le_iff₀ hRpos]; linarith
    have h2 : 1 / (R - Rf) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < R - Rf)]; linarith
    linarith
  have hκlt : κ < 1 := by linarith
  -- #### the half-plane inclusion
  have hsub : {w : ℂ | w.re < -R} ⊆ LeftHalfPlane Rf := fun w hw => by
    have hw' : w.re < -R := hw
    show w.re < -Rf
    linarith
  refine ⟨R, hRpos, Z, V, hVdiff.mono hsub, ?_, ?_, hVinj.mono hsub, ?_,
    ⟨Kb, hKbpos, ?_⟩⟩
  · intro w hw; exact hVdef w (hsub hw)
  · intro w hw; exact hVconj w (hsub hw)
  · intro w hw
    calc ‖V w - w‖ ≤ (1 / 2) * ‖w‖ := hVnorm w (hsub hw)
      _ = ‖w‖ / 2 := by ring
  · -- #### the inverse on the Stolz sector
    intro R₁ hR₁R
    obtain ⟨C, hC⟩ := Work.FatouCoord.Exist.exists_threshold_log_linear_aux (a := 2 * α)
      (d := 2 * R₁ + 2 * (2 * Real.pi * E + 3) + 1) (B := 0) (by linarith)
    simp only [add_zero] at hC
    set R' : ℝ := max R₁ (max (C / 2 + 1) R) with hR'def
    have hR₁R' : R₁ ≤ R' := by rw [hR'def]; exact le_max_left _ _
    have hRmR' : R ≤ R' := by
      rw [hR'def]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hC2R' : C / 2 + 1 ≤ R' := by
      rw [hR'def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hCR' : C < 2 * R' + 1 := by linarith
    refine ⟨R', hR₁R', ?_⟩
    intro w hw hwim
    have hwneg : w.re < 0 := by
      have : 0 < R' := lt_of_lt_of_le hRpos hRmR'
      linarith
    have hSgt : R' < -w.re := by linarith
    have hwabs : -w.re ≤ ‖w‖ := by
      have h := Complex.abs_re_le_norm w
      rwa [abs_of_neg hwneg] at h
    have hwnorm_gt : R' < ‖w‖ := lt_of_lt_of_le hSgt hwabs
    have hwnorm_ge : R ≤ ‖w‖ := le_trans hRmR' hwnorm_gt.le
    have hwnorm1 : 1 ≤ ‖w‖ := by linarith
    have hwnormpos : 0 < ‖w‖ := by linarith
    have hslognn : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hwnorm1
    have hSnorm : ‖w‖ ≤ 2 * (-w.re) + 1 := by
      have h1 : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      rw [abs_of_neg hwneg] at h1
      linarith
    have hlogle : Real.log ‖w‖ ≤ Real.log (2 * (-w.re) + 1) :=
      Real.log_le_log hwnormpos hSnorm
    have hdepth := hC (2 * (-w.re) + 1) (by linarith : C < 2 * (-w.re) + 1)
    have hdepth' : α * Real.log (2 * (-w.re) + 1) + R₁ + (2 * Real.pi * E + 3) < -w.re := by
      linarith
    -- #### the formal inverse
    set v₀ : ℂ := w - (1 - a) * Lambda w with hv₀def
    have hv₀sub : v₀ - w = -((1 - a) * Lambda w) := by rw [hv₀def]; ring
    have hLim0 : 0 ≤ (Lambda w).im := (Lambda_re_im w).2.1
    have hLim2 : (Lambda w).im ≤ 2 * Real.pi := (Lambda_re_im w).2.2
    have himbound : (1 - a).im * (Lambda w).im ≤ E * (2 * Real.pi) := by
      by_cases hcase : 0 ≤ (1 - a).im
      · have hE : (1 - a).im ≤ E := by rw [hEdef]; exact le_abs_self _
        nlinarith [hLim0, hLim2, hEnn, hE, Real.pi_pos.le]
      · have h' : (1 - a).im < 0 := not_le.mp hcase
        have h5 : (1 - a).im * (Lambda w).im ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h'.le hLim0
        nlinarith [hEnn, Real.pi_pos.le]
    have hv₀re : v₀.re = w.re - d * Real.log ‖w‖ + (1 - a).im * (Lambda w).im := by
      have h1 : v₀.re = w.re - ((1 - a) * Lambda w).re := by rw [hv₀def, Complex.sub_re]
      have h2 : ((1 - a) * Lambda w).re =
          d * Real.log ‖w‖ - (1 - a).im * (Lambda w).im := by
        rw [Complex.mul_re, (Lambda_re_im w).1, ← hddef]
      rw [h1, h2]; ring
    have hαlog : -d * Real.log ‖w‖ ≤ α * Real.log (2 * (-w.re) + 1) := by
      have h1 : -d ≤ α := by rw [hαdef]; exact le_max_right _ _
      exact le_trans (mul_le_mul_of_nonneg_right h1 hslognn)
        (mul_le_mul_of_nonneg_left hlogle hαnn)
    have hv₀deep : v₀.re < -R₁ - 3 := by
      rw [hv₀re]
      linarith
    have hv₀memRf : v₀ ∈ LeftHalfPlane Rf := by
      rw [mem_LeftHalfPlane]; linarith
    -- #### `v₀` is comparable to `w`
    have hLnorm : ‖Lambda w‖ ≤ Real.log ‖w‖ + 2 * Real.pi := norm_Lambda_le' hwnorm1
    have hnorm_sub : ‖v₀ - w‖ ≤ c * (Real.log ‖w‖ + 2 * Real.pi) := by
      rw [hv₀sub, norm_neg, norm_mul, ← hcdef]
      exact mul_le_mul_of_nonneg_left hLnorm (norm_nonneg _)
    have hsmall : c * (Real.log ‖w‖ + 2 * Real.pi) ≤ ‖w‖ / 2 := by
      have h := hT₁ ‖w‖ (by linarith : T₁ ≤ ‖w‖)
      linarith
    have habs := abs_norm_sub_norm_le v₀ w
    rw [abs_le] at habs
    have hv₀ge : ‖w‖ / 2 ≤ ‖v₀‖ := by linarith [habs.1, hnorm_sub, hsmall]
    have hv₀le : ‖v₀‖ ≤ 2 * ‖w‖ := by linarith [habs.2, hnorm_sub, hsmall]
    -- #### the defect of the formal inverse
    have hVv₀ : V v₀ = v₀ + (1 - a) * Lambda v₀ + Z v₀ := hVdef v₀ hv₀memRf
    have hdiff : V v₀ - w = (1 - a) * (Lambda v₀ - Lambda w) + Z v₀ := by
      rw [hVv₀, hv₀def]; ring
    have hterm1 : ‖(1 - a) * (Lambda v₀ - Lambda w)‖ ≤
        8 * c ^ 2 * (1 + Real.log ‖w‖) / ‖w‖ := by
      have h := hT₄ w (by linarith : w.re < -T₄)
      have h2 : c * (8 * c * (1 + Real.log ‖w‖) / ‖w‖) =
          8 * c ^ 2 * (1 + Real.log ‖w‖) / ‖w‖ := by ring
      calc ‖(1 - a) * (Lambda v₀ - Lambda w)‖
          = c * ‖Lambda v₀ - Lambda w‖ := by rw [norm_mul, ← hcdef]
        _ = c * ‖Lambda (w - (1 - a) * Lambda w) - Lambda w‖ := by rw [hv₀def]
        _ ≤ c * (8 * c * (1 + Real.log ‖w‖) / ‖w‖) := mul_le_mul_of_nonneg_left h hcnn
        _ = 8 * c ^ 2 * (1 + Real.log ‖w‖) / ‖w‖ := h2
    have hterm2 : ‖Z v₀‖ ≤ 2 * K_Z * (1 + Real.log 2) * (1 + Real.log ‖w‖) / ‖w‖ := by
      have hZ := hK_Z v₀ hv₀memRf
      have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hv₀pos : 0 < ‖v₀‖ := by linarith
      have h1 : 1 + Real.log ‖v₀‖ ≤ (1 + Real.log 2) * (1 + Real.log ‖w‖) := by
        have h2 : Real.log ‖v₀‖ ≤ Real.log 2 + Real.log ‖w‖ := by
          have h3 := Real.log_le_log hv₀pos hv₀le
          rw [Real.log_mul (by norm_num) (ne_of_gt hwnormpos)] at h3
          linarith
        have h4 : 0 ≤ Real.log 2 * Real.log ‖w‖ := mul_nonneg hlog2nn hslognn
        nlinarith
      have h4 : 1 / ‖v₀‖ ≤ 2 / ‖w‖ := by
        have h5 := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < ‖w‖ / 2) hv₀ge
        have h6 : 1 / (‖w‖ / 2) = 2 / ‖w‖ := by rw [one_div, inv_div]
        linarith [h5, h6]
      have h5 : (1 + Real.log ‖v₀‖) / ‖v₀‖ ≤
          (1 + Real.log 2) * (1 + Real.log ‖w‖) * (2 / ‖w‖) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul h1 h4 (by positivity) (by positivity)
      calc ‖Z v₀‖ ≤ K_Z * (1 + Real.log ‖v₀‖) / ‖v₀‖ := hZ
        _ = K_Z * ((1 + Real.log ‖v₀‖) / ‖v₀‖) := by ring
        _ ≤ K_Z * ((1 + Real.log 2) * (1 + Real.log ‖w‖) * (2 / ‖w‖)) :=
            mul_le_mul_of_nonneg_left h5 hK_Zpos.le
        _ = 2 * K_Z * (1 + Real.log 2) * (1 + Real.log ‖w‖) / ‖w‖ := by ring
    have hclose : ‖V v₀ - w‖ ≤ Kb * (1 + Real.log ‖w‖) / (2 * ‖w‖) := by
      have hsum : ‖(1 - a) * (Lambda v₀ - Lambda w) + Z v₀‖ ≤
          8 * c ^ 2 * (1 + Real.log ‖w‖) / ‖w‖ +
            2 * K_Z * (1 + Real.log 2) * (1 + Real.log ‖w‖) / ‖w‖ :=
        le_trans (norm_add_le _ _) (add_le_add hterm1 hterm2)
      have hfac : 8 * c ^ 2 * (1 + Real.log ‖w‖) / ‖w‖ +
            2 * K_Z * (1 + Real.log 2) * (1 + Real.log ‖w‖) / ‖w‖
          = (8 * c ^ 2 + 2 * K_Z * (1 + Real.log 2)) * ((1 + Real.log ‖w‖) / ‖w‖) := by
        ring
      have hKb2 : (8 * c ^ 2 + 2 * K_Z * (1 + Real.log 2)) * ((1 + Real.log ‖w‖) / ‖w‖)
          ≤ (Kb / 2) * ((1 + Real.log ‖w‖) / ‖w‖) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hKbdef]; linarith
      have hfin : (Kb / 2) * ((1 + Real.log ‖w‖) / ‖w‖) =
          Kb * (1 + Real.log ‖w‖) / (2 * ‖w‖) := by ring
      rw [hdiff]
      linarith [hsum, hfac, hKb2, hfin]
    -- #### the radius `ρ` and the contraction
    set ρ : ℝ := Kb * (1 + Real.log ‖w‖) / ‖w‖ with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact div_pos (mul_pos hKbpos (by linarith)) hwnormpos
    have hKbR : Kb * (1 + Real.log R) ≤ R / 2 := by
      have h2 := hT₂ R hT₂R
      have h3 : Kb * (1 + Real.log R) ≤ Kb * (Real.log R + 2 * Real.pi) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.pi_gt_three]) hKbpos.le
      have h4 : Kb * (Real.log R + 2 * Real.pi) ≤ R / 4 := by linarith
      linarith
    have hρhalf : ρ ≤ 1 / 2 := by
      rw [hρdef]
      have h1 : (1 + Real.log ‖w‖) / ‖w‖ ≤ (1 + Real.log R) / R :=
        log_ratio_antitone hR1 hwnorm_ge
      have h2 : Kb * ((1 + Real.log ‖w‖) / ‖w‖) ≤ Kb * ((1 + Real.log R) / R) :=
        mul_le_mul_of_nonneg_left h1 hKbpos.le
      have h3 : Kb * ((1 + Real.log R) / R) = Kb * (1 + Real.log R) / R := by ring
      have h4 : Kb * (1 + Real.log ‖w‖) / ‖w‖ = Kb * ((1 + Real.log ‖w‖) / ‖w‖) := by ring
      have h5 : Kb * ((1 + Real.log R) / R) ≤ 1 / 2 := by
        rw [h3, div_le_iff₀ hRpos]
        linarith [hKbR]
      rw [h4]
      linarith [h2, h5]
    have hlip : ∀ x y : ℂ, dist x v₀ ≤ ρ → dist y v₀ ≤ ρ →
        ‖(V x - x) - (V y - y)‖ ≤ κ * ‖x - y‖ := by
      intro x y hx hy
      have hxle : x.re ≤ v₀.re + ρ := by
        have h1 : x.re - v₀.re ≤ ‖x - v₀‖ := by
          have := Complex.re_le_norm (x - v₀); simpa [Complex.sub_re] using this
        have h2 : ‖x - v₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact hx
        linarith
      have hyle : y.re ≤ v₀.re + ρ := by
        have h1 : y.re - v₀.re ≤ ‖y - v₀‖ := by
          have := Complex.re_le_norm (y - v₀); simpa [Complex.sub_re] using this
        have h2 : ‖y - v₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact hy
        linarith
      have hxR : x ∈ LeftHalfPlane R := by rw [mem_LeftHalfPlane]; linarith
      have hyR : y ∈ LeftHalfPlane R := by rw [mem_LeftHalfPlane]; linarith
      have hxRf : x ∈ LeftHalfPlane Rf := by rw [mem_LeftHalfPlane] at hxR ⊢; linarith
      have hyRf : y ∈ LeftHalfPlane Rf := by rw [mem_LeftHalfPlane] at hyR ⊢; linarith
      have hΛ := Work.FatouCoord.Repelling.norm_Lambda_sub_le hRpos hxR hyR
      have hZ := Work.FatouCoordFix.Repelling.norm_Z_sub_le hRfpos hZdiff hZbd hRfR hxR hyR
      rw [hVdef x hxRf, hVdef y hyRf]
      have h1 : ‖(1 - a) * (Lambda x - Lambda y)‖ ≤ c * (‖x - y‖ / R) := by
        rw [norm_mul, ← hcdef]
        exact mul_le_mul_of_nonneg_left hΛ (norm_nonneg _)
      have heq : (x + (1 - a) * Lambda x + Z x - x) -
            (y + (1 - a) * Lambda y + Z y - y)
          = (1 - a) * (Lambda x - Lambda y) + (Z x - Z y) := by ring
      calc ‖(x + (1 - a) * Lambda x + Z x - x) -
              (y + (1 - a) * Lambda y + Z y - y)‖
          = ‖(1 - a) * (Lambda x - Lambda y) + (Z x - Z y)‖ := by rw [heq]
        _ ≤ ‖(1 - a) * (Lambda x - Lambda y)‖ + ‖Z x - Z y‖ := norm_add_le _ _
        _ ≤ c * (‖x - y‖ / R) + (1 / (R - Rf)) * ‖x - y‖ := add_le_add h1 hZ
        _ = κ * ‖x - y‖ := by rw [hκdef]; ring
    have hclose' : ‖V v₀ - w‖ ≤ (1 - κ) * ρ := by
      have h1 : (1 / 2) * ρ ≤ (1 - κ) * ρ :=
        mul_le_mul_of_nonneg_right (by linarith) hρpos.le
      have h2 : ρ / 2 = Kb * (1 + Real.log ‖w‖) / (2 * ‖w‖) := by rw [hρdef]; ring
      have h3 : ‖V v₀ - w‖ ≤ ρ / 2 := by rw [h2]; exact hclose
      linarith
    obtain ⟨v, hvρ, hvV⟩ := exists_preimage_of_lipschitz hρpos hκ0 hκlt hlip hclose'
    refine ⟨v, ?_, hvV, ?_⟩
    · have h1 : v.re - v₀.re ≤ ‖v - v₀‖ := by
        have := Complex.re_le_norm (v - v₀); simpa [Complex.sub_re] using this
      have h2 : ‖v - v₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact hvρ
      linarith
    · calc ‖v - (w - (1 - a) * Lambda w)‖ = ‖v - v₀‖ := by rw [hv₀def]
        _ = dist v v₀ := by rw [dist_eq_norm]
        _ ≤ ρ := hvρ
        _ = Kb * (1 + Real.log ‖w‖) / ‖w‖ := hρdef

end Work.FlowerGlue2
