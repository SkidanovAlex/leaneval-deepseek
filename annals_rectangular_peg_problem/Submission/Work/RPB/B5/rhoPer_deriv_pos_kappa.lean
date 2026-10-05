import Mathlib
import Submission.Work.RPB.B5.RhoPerDefs
import Submission.Work.RPB.B5.rhoQuad_sub_rhoMid_nonneg
import Submission.Work.RPB.B5.deriv_rhoMid_rhoQuad
import Submission.Work.RPB.B5.deriv_wM
import Submission.Work.RPB.B5.rhoPer_deriv_pos
import Submission.Work.RPB.B5.sig_abs_le_kappa
import Submission.Work.RPB.B5.hasDerivAt_rhoe_comp_sig_kappa
import Submission.Work.RPB.B5.exists_rho_per

open Set

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- Positivity of the `x`-derivative of the blended radius function `rhoPer` with the cutoff
width `κ/4` in place of `1/4`.  This is the `κ`-generalisation of `rhoPer_deriv_pos`; the only
changes are that `sig_abs_le` is replaced by `sig_abs_le_kappa` and
`hasDerivAt_rhoe_comp_sig` by `hasDerivAt_rhoe_comp_sig_kappa`. -/
theorem rhoPer_deriv_pos_kappa (ρe : ℝ → ℝ → ℝ → ℝ) (δ δA u₂ κ : ℝ)
    (hκ : 0 < κ)
    (hδ : 0 < δ) (hδδA : δ < δA) (hδAu : δA < u₂) (hu₂ : u₂ < Real.sqrt 2 - δ)
    (hδA4 : Real.sqrt 2 * δA ≤ κ / 4)
    (hder : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t σ : ℝ, |σ| ≤ κ / 4 →
      deriv (fun s : ℝ => ρe τ t s) σ < 0)
    (hA : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t x : ℝ, δ < x + Real.sqrt 2 →
      x + Real.sqrt 2 < δA → ρe τ t (sig x) ≤ Real.pi ^ 2 / 32)
    (hu₂ge : 4 * u₂ ^ 2 ≥ 1 + u₂) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
      0 < deriv (fun y => rhoPer ρe δ δA u₂ τ y t) x := by
  intro τ hτ x hx t
  have hδAlt : δA < Real.sqrt 2 := by linarith
  have hδApos : 0 < δA := lt_trans hδ hδδA
  have hxlo : -Real.sqrt 2 < x := hx.1
  by_cases hcase : x + Real.sqrt 2 < δA
  · -- ### Case I: the `ρh`-branch is active, `x + √2 < δA`
    have hxu : x + Real.sqrt 2 < u₂ := lt_trans hcase hδAu
    have hxneg : x < 0 := by linarith
    have hsig : |sig x| ≤ κ / 4 := sig_abs_le_kappa hκ hδA4 hx (le_of_lt hcase)
    have hAbase : HasDerivAt (fun y : ℝ => ρe τ t (sig y))
        (deriv (fun s : ℝ => ρe τ t s) (sig x) * x) x :=
      hasDerivAt_rhoe_comp_sig_kappa ρe τ t κ (fun σ hσ => hder τ hτ t σ hσ) hsig
    have hApos : 0 < deriv (fun s : ℝ => ρe τ t s) (sig x) * x :=
      mul_pos_of_neg_of_neg (hder τ hτ t (sig x) hsig) hxneg
    have hRzero : ∀ᶠ y in nhds x, wR δ u₂ y = 0 := by
      have hcont : Continuous (fun y : ℝ => y + Real.sqrt 2) := by continuity
      have hlt : ∀ᶠ y : ℝ in nhds x, y + Real.sqrt 2 < u₂ :=
        hcont.continuousAt.eventually (Iio_mem_nhds hxu)
      filter_upwards [hlt] with y hy
      exact wR_eq_zero hu₂ (le_of_lt hy)
    have hflocal : (fun y => rhoPer ρe δ δA u₂ τ y t)
        =ᶠ[nhds x] (fun y => wL δ δA y * ρe τ t (sig y) + wM δ δA u₂ y * rhoMid y) := by
      filter_upwards [hRzero] with y hy
      simp only [rhoPer, hy, zero_mul, add_zero]
    have hLdiff : DifferentiableAt ℝ (wL δ δA) x :=
      ((wL_contDiff δ δA).differentiable (by norm_num)).differentiableAt
    have hMdiff : DifferentiableAt ℝ (wM δ δA u₂) x :=
      ((wM_contDiff δ δA u₂).differentiable (by norm_num)).differentiableAt
    have hm : HasDerivAt rhoMid (Real.pi ^ 2 / 32) x := by
      have h := (hasDerivAt_deriv_iff (f := rhoMid) (x := x)).mpr
        (by unfold rhoMid; fun_prop : DifferentiableAt ℝ rhoMid x)
      rwa [(deriv_rhoMid_rhoQuad x hxlo).1] at h
    have hsum := (hLdiff.hasDerivAt.mul hAbase).add (hMdiff.hasDerivAt.mul hm)
    set D : ℝ := (deriv (wL δ δA) x * (ρe τ t (sig x))
        + wL δ δA x * (deriv (fun s : ℝ => ρe τ t s) (sig x) * x))
        + (deriv (wM δ δA u₂) x * rhoMid x + wM δ δA u₂ x * (Real.pi ^ 2 / 32)) with hDdef
    have hHasD : HasDerivAt (fun y => rhoPer ρe δ δA u₂ τ y t) D x := by
      have hh : HasDerivAt (fun y => rhoPer ρe δ δA u₂ τ y t) _ x :=
        hsum.congr_of_eventuallyEq hflocal
      simpa only [hDdef] using hh
    rw [hHasD.deriv, hDdef]
    have hwMeq : deriv (wM δ δA u₂) x = - deriv (wL δ δA) x := by
      rw [deriv_wM, wR_deriv_eq_zero_of_le hu₂ (le_of_lt hxu)]
      ring
    rw [hwMeq]
    have h1 : 0 < wL δ δA x * (deriv (fun s : ℝ => ρe τ t s) (sig x) * x) :=
      mul_pos (wL_pos_of hδδA hcase) hApos
    have h3 : 0 ≤ deriv (wL δ δA) x * (ρe τ t (sig x) - rhoMid x) := by
      rcases lt_or_ge δ (x + Real.sqrt 2) with hlt | hle
      · -- inside the transition region: `ρe τ t (sig x) ≤ π²/32 < rhoMid x`
        have hAub : ρe τ t (sig x) ≤ Real.pi ^ 2 / 32 := hA τ hτ t x hlt hcase
        have hMlb : Real.pi ^ 2 / 32 < rhoMid x := by
          unfold rhoMid
          have hxp : 0 < x + Real.sqrt 2 := by linarith
          have hp2 : (0 : ℝ) < Real.pi ^ 2 / 32 := by positivity
          have := mul_pos hp2 hxp
          nlinarith [this]
        have hneg : ρe τ t (sig x) - rhoMid x < 0 := by linarith
        exact mul_nonneg_of_nonpos_of_nonpos (wL_deriv_nonpos hδδA x) (le_of_lt hneg)
      · -- left plateau: the cutoff derivative vanishes
        rw [wL_deriv_eq_zero_of_le hδδA hle]; ring_nf; positivity
    have h2 : 0 ≤ wM δ δA u₂ x * (Real.pi ^ 2 / 32) :=
      mul_nonneg (wM_nonneg hδδA hδAu hu₂ x) (by positivity)
    nlinarith [h1, h2, h3]
  · -- ### Case II: `δA ≤ x + √2`
    have hδA_le : δA ≤ x + Real.sqrt 2 := not_lt.mp hcase
    by_cases hcase2 : x + Real.sqrt 2 = δA
    · -- ### Case IIb: the degenerate point `x + √2 = δA`
      have hxu : x + Real.sqrt 2 < u₂ := by rw [hcase2]; exact hδAu
      have hsig : |sig x| ≤ κ / 4 := sig_abs_le_kappa hκ hδA4 hx (le_of_eq hcase2)
      have hAbase : HasDerivAt (fun y : ℝ => ρe τ t (sig y))
          (deriv (fun s : ℝ => ρe τ t s) (sig x) * x) x :=
        hasDerivAt_rhoe_comp_sig_kappa ρe τ t κ (fun σ hσ => hder τ hτ t σ hσ) hsig
      have hRzero : ∀ᶠ y in nhds x, wR δ u₂ y = 0 := by
        have hcont : Continuous (fun y : ℝ => y + Real.sqrt 2) := by continuity
        have hlt : ∀ᶠ y : ℝ in nhds x, y + Real.sqrt 2 < u₂ :=
          hcont.continuousAt.eventually (Iio_mem_nhds hxu)
        filter_upwards [hlt] with y hy
        exact wR_eq_zero hu₂ (le_of_lt hy)
      have hflocal : (fun y => rhoPer ρe δ δA u₂ τ y t)
          =ᶠ[nhds x] (fun y => wL δ δA y * ρe τ t (sig y) + wM δ δA u₂ y * rhoMid y) := by
        filter_upwards [hRzero] with y hy
        simp only [rhoPer, hy, zero_mul, add_zero]
      have hLdiff : DifferentiableAt ℝ (wL δ δA) x :=
        ((wL_contDiff δ δA).differentiable (by norm_num)).differentiableAt
      have hMdiff : DifferentiableAt ℝ (wM δ δA u₂) x :=
        ((wM_contDiff δ δA u₂).differentiable (by norm_num)).differentiableAt
      have hm : HasDerivAt rhoMid (Real.pi ^ 2 / 32) x := by
        have h := (hasDerivAt_deriv_iff (f := rhoMid) (x := x)).mpr
          (by unfold rhoMid; fun_prop : DifferentiableAt ℝ rhoMid x)
        rwa [(deriv_rhoMid_rhoQuad x hxlo).1] at h
      have hsum := (hLdiff.hasDerivAt.mul hAbase).add (hMdiff.hasDerivAt.mul hm)
      set D : ℝ := (deriv (wL δ δA) x * (ρe τ t (sig x))
          + wL δ δA x * (deriv (fun s : ℝ => ρe τ t s) (sig x) * x))
          + (deriv (wM δ δA u₂) x * rhoMid x + wM δ δA u₂ x * (Real.pi ^ 2 / 32)) with hDdef
      have hHasD : HasDerivAt (fun y => rhoPer ρe δ δA u₂ τ y t) D x := by
        have hh : HasDerivAt (fun y => rhoPer ρe δ δA u₂ τ y t) _ x :=
          hsum.congr_of_eventuallyEq hflocal
        simpa only [hDdef] using hh
      rw [hHasD.deriv, hDdef]
      have hwLx : wL δ δA x = 0 := wL_eq_zero hδδA hδA_le
      have hwLder : deriv (wL δ δA) x = 0 := wL_deriv_eq_zero_of_ge hδδA hδA_le
      have hwRx : wR δ u₂ x = 0 := wR_eq_zero hu₂ (le_of_lt hxu)
      have hwMx : wM δ δA u₂ x = 1 := wM_eq_one hδδA hu₂ hδA_le (le_of_lt hxu)
      have hwMder : deriv (wM δ δA u₂) x = 0 := by
        rw [deriv_wM, hwLder, wR_deriv_eq_zero_of_le hu₂ (le_of_lt hxu)]
        ring
      rw [hwLder, hwMder, hwLx, hwMx]
      simp only [zero_mul, one_mul, zero_add, add_zero]
      positivity
    · -- ### Case IIa: `δA < x + √2`, the `ρh`-branch is switched off
      have hgt : δA < x + Real.sqrt 2 := lt_of_le_of_ne hδA_le (Ne.symm hcase2)
      have hu₂pos : 0 < u₂ := lt_trans hδApos hδAu
      have hwLzero : ∀ᶠ y in nhds x, wL δ δA y = 0 := by
        have hcont : Continuous (fun y : ℝ => y + Real.sqrt 2) := by continuity
        have hlt : ∀ᶠ y : ℝ in nhds x, δA < y + Real.sqrt 2 :=
          hcont.continuousAt.eventually (Ioi_mem_nhds hgt)
        filter_upwards [hlt] with y hy
        exact wL_eq_zero hδδA (le_of_lt hy)
      have hflocal : (fun y => rhoPer ρe δ δA u₂ τ y t)
          =ᶠ[nhds x] (fun y => wM δ δA u₂ y * rhoMid y + wR δ u₂ y * rhoQuad y) := by
        filter_upwards [hwLzero] with y hy
        simp only [rhoPer, hy, zero_mul, zero_add]
      have hMdiff : DifferentiableAt ℝ (wM δ δA u₂) x :=
        ((wM_contDiff δ δA u₂).differentiable (by norm_num)).differentiableAt
      have hRdiff : DifferentiableAt ℝ (wR δ u₂) x :=
        ((wR_contDiff δ u₂).differentiable (by norm_num)).differentiableAt
      have hm : HasDerivAt rhoMid (Real.pi ^ 2 / 32) x := by
        have h := (hasDerivAt_deriv_iff (f := rhoMid) (x := x)).mpr
          (by unfold rhoMid; fun_prop : DifferentiableAt ℝ rhoMid x)
        rwa [(deriv_rhoMid_rhoQuad x hxlo).1] at h
      have hq : HasDerivAt rhoQuad (deriv rhoQuad x) x :=
        (hasDerivAt_deriv_iff (f := rhoQuad) (x := x)).mpr
          (by unfold rhoQuad; fun_prop : DifferentiableAt ℝ rhoQuad x)
      have hsum := (hMdiff.hasDerivAt.mul hm).add (hRdiff.hasDerivAt.mul hq)
      set D : ℝ := (deriv (wM δ δA u₂) x * rhoMid x + wM δ δA u₂ x * (Real.pi ^ 2 / 32))
          + (deriv (wR δ u₂) x * rhoQuad x + wR δ u₂ x * deriv rhoQuad x) with hDdef
      have hHasD : HasDerivAt (fun y => rhoPer ρe δ δA u₂ τ y t) D x := by
        have hh : HasDerivAt (fun y => rhoPer ρe δ δA u₂ τ y t) _ x :=
          hsum.congr_of_eventuallyEq hflocal
        simpa only [hDdef] using hh
      rw [hHasD.deriv, hDdef]
      have hwLder : deriv (wL δ δA) x = 0 := wL_deriv_eq_zero_of_ge hδδA hδA_le
      have hwMder : deriv (wM δ δA u₂) x = - deriv (wR δ u₂) x := by
        rw [deriv_wM, hwLder]; ring
      rw [hwMder]
      have h3 : 0 ≤ deriv (wR δ u₂) x * (rhoQuad x - rhoMid x) := by
        rcases lt_or_ge u₂ (x + Real.sqrt 2) with hlt | hle
        · exact mul_nonneg (wR_deriv_nonneg hu₂ x)
            (rhoQuad_sub_rhoMid_nonneg hu₂ge hu₂pos hlt)
        · rw [wR_deriv_eq_zero_of_le hu₂ hle]; ring_nf; positivity
      have hpos : 0 < wM δ δA u₂ x * (Real.pi ^ 2 / 32) + wR δ u₂ x * deriv rhoQuad x := by
        by_cases hwm : wM δ δA u₂ x = 0
        · -- then `wR x = 1`, so the second term is `(rhoQuad)' x > 0`
          have hwLx : wL δ δA x = 0 := wL_eq_zero hδδA hδA_le
          have hwRx : wR δ u₂ x = 1 := by
            have h1 : 1 - wL δ δA x - wR δ u₂ x = 0 := hwm
            rw [hwLx] at h1; linarith
          have hqpos : 0 < deriv rhoQuad x := (deriv_rhoMid_rhoQuad x hxlo).2
          nlinarith [hwRx, hqpos]
        · -- otherwise the first term is strictly positive
          have hwmpos : 0 < wM δ δA u₂ x :=
            lt_of_le_of_ne (wM_nonneg hδδA hδAu hu₂ x) (Ne.symm hwm)
          have h1 : 0 < wM δ δA u₂ x * (Real.pi ^ 2 / 32) := mul_pos hwmpos (by positivity)
          have h2 : 0 ≤ wR δ u₂ x * deriv rhoQuad x :=
            mul_nonneg (wR_nonneg δ u₂ x) (le_of_lt (deriv_rhoMid_rhoQuad x hxlo).2)
          linarith
      have e : (-deriv (wR δ u₂) x * rhoMid x + wM δ δA u₂ x * (Real.pi ^ 2 / 32))
          + (deriv (wR δ u₂) x * rhoQuad x + wR δ u₂ x * deriv rhoQuad x)
          = deriv (wR δ u₂) x * (rhoQuad x - rhoMid x)
            + (wM δ δA u₂ x * (Real.pi ^ 2 / 32) + wR δ u₂ x * deriv rhoQuad x) := by ring
      nlinarith [h3, hpos, e]

end Work.RPB.B5
