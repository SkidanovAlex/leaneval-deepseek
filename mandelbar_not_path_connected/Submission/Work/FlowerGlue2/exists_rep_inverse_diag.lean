import Mathlib
import Submission.Work.FlowerGlue2.exists_rep_inverse_stolz
import Submission.Work.FlowerGlue2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

open Filter Set Metric
open scoped Topology
open Work.FatouCoord.Petal

set_option maxHeartbeats 1600000

/-
## The inversion of the repelling conjugacy `V`, in **diagonal** form

`Work.FlowerGlue2.exists_rep_inverse_stolz` (workspace file
`Submission/Work/FlowerGlue2/exists_rep_inverse_stolz.lean`) states the inversion of `V` with a
*separate* threshold: for every `R₁ ≥ R` there is `R' ≥ R₁` such that every `w` with
`Re w < -R'` and `|Im w| < -Re w + 1` has a preimage `v` with `Re v < -R₁ - 2` and
`‖v - (w - (1-a) Λ w)‖ ≤ K (1 + log ‖w‖)/‖w‖`.  In that form the *usable* relation between the
depth `-Re w` of the point and the depth `-R₁ - 2` of its preimage is only
`-Re w ≥ R' ≥ C (R₁)²` (the proof's `R' = max R₁ (max (C/2+1) R)` with `C ≍ (2R₁)²`), which is
far too lossy: the invertibility is genuinely diagonal, the preimage of a deep point sitting at
depth `≈ -Re w`.

This statement exposes that diagonal content: there is a single absolute threshold `R₀` (and the
same `V`, `Z` as in `Work.FlowerGlue2.exists_conjugacy_Z_fine`) such that the inverse of `V` at
`w` exists whenever `-Re w ≥ R₀`, `-Re w ≥ 2 R₁` (the preimage is at least half as deep as the
point) and `R₀ - 3 ≤ R₁`.

Concretely the proof is the final section of `exists_rep_inverse_stolz` with the choice
`R' := max R₁ (max (C/2+1) R)` replaced by the two diagonal hypotheses `2R₁ ≤ -Re w` and
`R₀ ≤ -Re w`: with `S := -Re w`, the requirement `α log (2S+1) + R₁ + (2πE+3) < S` (where
`α = max 0 (-(1-a).re)`, `E = |(1-a).im|`) follows from `R₁ ≤ S/2` together with
`α log (2S+1) + 2πE + 4 ≤ S/2`, the latter holding for `S ≥ S_d` a threshold depending only on
`a` (obtainable from `Work.FatouCoord.Exist.exists_threshold_log_linear_aux` with
`a := 4α`, `d := 2*(2πE+4)`, `B := 1`, using `log (2S+1) ≤ 2 log (S+1)`).  Everything else (the
formal inverse `v₀ = w - (1-a)Λw`, the Lipschitz constants `κ = ‖1-a‖/R + 1/(R-Rf) ≤ 1/2`, the
defect bounds `norm_Lambda_shift_no_ha` and the `Z`-decay `hZdec`, and
`exists_preimage_of_lipschitz`) is cited verbatim from the existing proof.

One care point: take the Lipschitz threshold `R_lip := max (max (Rf+4) T₁) (max (max T₂ T₄)
(max (4c+4) 4))` of the existing proof and *define* `R₀ := max (R_lip + 3) (S_d + 3)`, rather
than reusing `R₀` itself as the Lipschitz threshold: `v₀.re < -R₁ - 3` and `ρ ≤ 1/2` give the
contraction ball `x.re < -R₁ - 5/2 ≤ -R_lip` only because `R_lip ≤ R₀ - 3 ≤ R₁`.
-/
theorem exists_rep_inverse_diag {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∃ Z V : ℂ → ℂ,
      DifferentiableOn ℂ V {w : ℂ | w.re < -R₀} ∧
      (∀ w : ℂ, w.re < -R₀ → V w = w + (1 - a) * Work.FatouCoord.Petal.Lambda w + Z w) ∧
      (∀ w : ℂ, w.re < -R₀ → V (w + 1) = Work.FatouCoord.wMap f (V w)) ∧
      Set.InjOn V {w : ℂ | w.re < -R₀} ∧
      (∀ w : ℂ, w.re < -R₀ → ‖V w - w‖ ≤ ‖w‖ / 2) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ R₁ : ℝ, ∀ w : ℂ,
        R₀ - 3 ≤ R₁ → 2 * R₁ ≤ -w.re → R₀ ≤ -w.re → |w.im| < -w.re + 1 →
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
  -- #### the diagonal logarithm threshold `S_d`
  obtain ⟨C, hC⟩ := Work.FatouCoord.Exist.exists_threshold_log_linear_aux (a := 4 * α)
    (d := 2 * (2 * Real.pi * E + 4)) (B := 1) (by positivity)
  set S_d : ℝ := max (C + 1) 1 with hSddef
  have hSd : ∀ S : ℝ, S_d ≤ S →
      α * Real.log (2 * S + 1) + 2 * Real.pi * E + 4 ≤ S / 2 := by
    intro S hS
    have hCS : C < S := by
      have : C + 1 ≤ S := le_trans (le_max_left _ _) hS
      linarith
    have h1 : 4 * α * Real.log (S + 1) + 2 * (2 * Real.pi * E + 4) < S := hC S hCS
    have hS1 : (1 : ℝ) ≤ S := le_trans (le_max_right _ _) hS
    have hlog : Real.log (2 * S + 1) ≤ 2 * Real.log (S + 1) := by
      have h2S1 : 0 < 2 * S + 1 := by linarith
      have hle : 2 * S + 1 ≤ (S + 1) ^ 2 := by nlinarith
      calc Real.log (2 * S + 1) ≤ Real.log ((S + 1) ^ 2) := Real.log_le_log h2S1 hle
        _ = 2 * Real.log (S + 1) := by rw [Real.log_pow]; norm_num
    have h2 : 2 * α * Real.log (2 * S + 1) ≤ 4 * α * Real.log (S + 1) := by
      have hm := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ 2 * α)
      linarith
    linarith
  -- #### the single diagonal threshold `R₀`
  set R₀ : ℝ := max (R + 3) (S_d + 3) with hR₀def
  have hR₀pos : 0 < R₀ := by
    rw [hR₀def]
    exact lt_max_iff.mpr (Or.inl (by linarith))
  have hRR₀ : R ≤ R₀ - 3 := by
    rw [hR₀def]
    have := le_max_left (R + 3) (S_d + 3)
    linarith
  have hSdR₀ : S_d ≤ R₀ - 3 := by
    rw [hR₀def]
    have := le_max_right (R + 3) (S_d + 3)
    linarith
  -- #### the half-plane inclusion
  have hsub : {w : ℂ | w.re < -R₀} ⊆ LeftHalfPlane Rf := fun w hw => by
    have hw' : w.re < -R₀ := hw
    show w.re < -Rf
    linarith
  refine ⟨R₀, hR₀pos, Z, V, hVdiff.mono hsub, ?_, ?_, hVinj.mono hsub, ?_,
    ⟨Kb, hKbpos, ?_⟩⟩
  · intro w hw; exact hVdef w (hsub hw)
  · intro w hw; exact hVconj w (hsub hw)
  · intro w hw
    calc ‖V w - w‖ ≤ (1 / 2) * ‖w‖ := hVnorm w (hsub hw)
      _ = ‖w‖ / 2 := by ring
  · -- #### the inverse, diagonal in the depth
    intro R₁ w hR₁ h2R₁ hR₀ hwim
    have hwneg : w.re < 0 := by linarith
    have hwabs : -w.re ≤ ‖w‖ := by
      have h := Complex.abs_re_le_norm w
      rwa [abs_of_neg hwneg] at h
    have hwnorm_ge : R ≤ ‖w‖ := by linarith
    have hwnorm1 : 1 ≤ ‖w‖ := by linarith
    have hwnormpos : 0 < ‖w‖ := by linarith
    have hslognn : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hwnorm1
    have hSnorm : ‖w‖ ≤ 2 * (-w.re) + 1 := by
      have h1 : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      rw [abs_of_neg hwneg] at h1
      linarith
    have hlogle : Real.log ‖w‖ ≤ Real.log (2 * (-w.re) + 1) :=
      Real.log_le_log hwnormpos hSnorm
    have hdepth' : α * Real.log (2 * (-w.re) + 1) + R₁ + (2 * Real.pi * E + 3) < -w.re := by
      have hsd := hSd (-w.re) (by linarith)
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
