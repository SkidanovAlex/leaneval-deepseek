import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.APsi.slit_facts
import Submission.Work.APsi.lune_facts
import Submission.Work.APsi.psiA_facts

/-! # The lower bound `‖ψ_A z‖ ≥ 1/2500` on the annulus `1/1000 ≤ ‖z‖ ≤ 1`

The analytic core of the third conjunct of `Submission.CDTPlan.ANumerics`.

* **slit stage.**  If `u = slit r w`, the Joukowski relation `u + u⁻¹ = α (w + w⁻¹) - β`
  (`α = (1+r)²/(4r)`, `β = (r-1)²/(2r)`) gives `1/‖u‖ ≤ ‖u + u⁻¹‖ + ‖u‖ ≤ α(ρ + 1/ρ) + β + 1`
  for `ρ ≤ ‖w‖ ≤ 1`, hence `‖u‖ ≥ 1/(α(ρ + 1/ρ) + β + 1)`.
* **lune stage.**  With `u = lune c ζ`, the inverse rational identity `ζ = u(B + Cu)/(C + Bu)`
  (`B = 1 + c²`, `C = c² - 1`) gives `‖ζ‖ ≤ f(‖u‖)` for the increasing `f(u) = u(B+Cu)/(C-Bu)`;
  hence `‖lune c ζ‖ ≥ u₀` whenever `f(u₀) ≤ ‖ζ‖`.
-/

namespace Work.ANum

open Submission.CDTPlan Work.APsi Complex

noncomputable section

/-- If `u ≠ 0`, `‖u‖ ≤ 1` and `‖u + u⁻¹‖ ≤ M`, then `‖u‖ ≥ 1/(M+1)`. -/
theorem inv_add_inv_lower {u : ℂ} (hu : u ≠ 0) (h1 : ‖u‖ ≤ 1) {M : ℝ}
    (hM : ‖u + u⁻¹‖ ≤ M) : 1 / (M + 1) ≤ ‖u‖ := by
  have hnorm : ‖u⁻¹‖ = 1 / ‖u‖ := by rw [norm_inv, one_div]
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have htri : ‖u⁻¹‖ ≤ ‖u + u⁻¹‖ + ‖u‖ := by
    have h := norm_sub_le (u + u⁻¹) u
    have h2 : (u + u⁻¹) - u = u⁻¹ := by ring
    rwa [h2] at h
  have h2 : 1 / ‖u‖ ≤ M + 1 := by rw [← hnorm]; linarith
  have hMp : 0 < M + 1 := lt_of_lt_of_le (by positivity) h2
  have h2' : 1 ≤ (M + 1) * ‖u‖ := by
    rw [div_le_iff₀ hpos] at h2; linarith
  rw [div_le_iff₀ hMp]
  linarith

/-- `x + 1/x` is decreasing on `(0,1]`. -/
theorem add_inv_anti {ρ x : ℝ} (hρ : 0 < ρ) (hx : ρ ≤ x) (h1 : x ≤ 1) :
    x + 1 / x ≤ ρ + 1 / ρ := by
  have hx0 : 0 < x := lt_of_lt_of_le hρ hx
  have hkey : ρ + 1 / ρ - (x + 1 / x) = (ρ - x) * (ρ * x - 1) / (ρ * x) := by
    field_simp
    ring
  have h1' : ρ - x ≤ 0 := by linarith
  have h2' : ρ * x - 1 ≤ 0 := by nlinarith
  have h3' : 0 < ρ * x := mul_pos hρ hx0
  have h4 : 0 ≤ (ρ - x) * (ρ * x - 1) := mul_nonneg_of_nonpos_of_nonpos h1' h2'
  have h5 : 0 ≤ (ρ - x) * (ρ * x - 1) / (ρ * x) := div_nonneg h4 h3'.le
  linarith

/-- **Slit lower bound.**  For `w ≠ 0` with `ρ ≤ ‖w‖ ≤ 1` and `u = slit r w`,
`‖u‖ ≥ 1/(α(ρ + 1/ρ) + β + 1)` with `α = (1+r)²/(4r)`, `β = (r-1)²/(2r)`. -/
theorem slit_lower {r ρ : ℝ} (hr : 0 < r) (hr1 : r < 1) {w : ℂ} (hw : w ≠ 0)
    (hρ : 0 < ρ) (hρw : ρ ≤ ‖w‖) (h1 : ‖w‖ ≤ 1) :
    1 / (((1 + r) ^ 2 / (4 * r)) * (ρ + 1 / ρ) + ((r - 1) ^ 2 / (2 * r)) + 1) ≤ ‖slit r w‖ := by
  refine inv_add_inv_lower (slit_ne_zero r hr w hw) (slit_norm_le_one r hr hr1 w h1) ?_
  rw [slit_joukowski_ab r hr w hw]
  have htri : ‖w + w⁻¹‖ ≤ ρ + 1 / ρ := by
    have h2 : ‖w + w⁻¹‖ ≤ ‖w‖ + 1 / ‖w‖ := by
      have h := norm_add_le w w⁻¹
      have h3 : ‖w‖ + ‖w⁻¹‖ = ‖w‖ + 1 / ‖w‖ := by rw [norm_inv, inv_eq_one_div]
      linarith
    exact le_trans h2 (add_inv_anti hρ hρw h1)
  have hab : ‖(1 + (r:ℂ))^2 / (4 * (r:ℂ))‖ = (1 + r)^2 / (4 * r) := by
    rw [show ((1 + (r:ℂ))^2 / (4 * (r:ℂ))) = (((1+r)^2/(4*r) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hcd : ‖((r:ℂ) - 1)^2 / (2 * (r:ℂ))‖ = (r - 1)^2 / (2 * r) := by
    rw [show (((r:ℂ) - 1)^2 / (2 * (r:ℂ))) = (((r-1)^2/(2*r) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hstep : ‖(1 + (r:ℂ))^2 / (4 * (r:ℂ)) * (w + w⁻¹) - ((r:ℂ) - 1)^2 / (2 * (r:ℂ))‖
      ≤ (1 + r)^2 / (4 * r) * (ρ + 1 / ρ) + (r - 1)^2 / (2 * r) := by
    calc ‖(1 + (r:ℂ))^2 / (4 * (r:ℂ)) * (w + w⁻¹) - ((r:ℂ) - 1)^2 / (2 * (r:ℂ))‖
        ≤ ‖(1 + (r:ℂ))^2 / (4 * (r:ℂ)) * (w + w⁻¹)‖ + ‖((r:ℂ) - 1)^2 / (2 * (r:ℂ))‖ :=
          norm_sub_le _ _
      _ = (1 + r)^2 / (4 * r) * ‖w + w⁻¹‖ + (r - 1)^2 / (2 * r) := by
          rw [norm_mul, hab, hcd]
      _ ≤ (1 + r)^2 / (4 * r) * (ρ + 1 / ρ) + (r - 1)^2 / (2 * r) := by
          have : (0:ℝ) ≤ (1 + r)^2 / (4 * r) := by positivity
          nlinarith [htri]
  linarith

/-- `u ↦ u(B + Cu)/(C - Bu)` is strictly increasing on `[0, C/B)`. -/
theorem lune_f_lt {c a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b * (1 + c ^ 2) < c ^ 2 - 1) :
    a * (1 + c ^ 2 + (c ^ 2 - 1) * a) / (c ^ 2 - 1 - (1 + c ^ 2) * a)
      < b * (1 + c ^ 2 + (c ^ 2 - 1) * b) / (c ^ 2 - 1 - (1 + c ^ 2) * b) := by
  have hB : 0 < 1 + c ^ 2 := by positivity
  have hb0 : 0 < b := lt_of_le_of_lt ha hab
  have hC : 0 < c ^ 2 - 1 := by nlinarith [hb, hB]
  have hda : 0 < c ^ 2 - 1 - (1 + c ^ 2) * a := by nlinarith [ha, hb, hB]
  have hdb : 0 < c ^ 2 - 1 - (1 + c ^ 2) * b := by linarith
  have hab1 : a * b < 1 := by
    have h : b < (c ^ 2 - 1) / (1 + c ^ 2) := by rw [lt_div_iff₀ hB]; linarith
    have h2 : (c ^ 2 - 1) / (1 + c ^ 2) ≤ 1 := by rw [div_le_one hB]; linarith
    have h3 : a * b ≤ b * b := mul_le_mul_of_nonneg_right hab.le hb0.le
    have h4 : b * b < 1 := by
      have h5 : b < 1 := lt_of_lt_of_le h h2
      nlinarith
    linarith
  have hbr : 0 < (1 + c ^ 2) * (c ^ 2 - 1) + (c ^ 2 - 1) ^ 2 * (a + b)
      - (1 + c ^ 2) * (c ^ 2 - 1) * a * b := by
    have hsplit : (1 + c ^ 2) * (c ^ 2 - 1) + (c ^ 2 - 1) ^ 2 * (a + b)
        - (1 + c ^ 2) * (c ^ 2 - 1) * a * b
        = (1 + c ^ 2) * (c ^ 2 - 1) * (1 - a * b) + (c ^ 2 - 1) ^ 2 * (a + b) := by ring
    rw [hsplit]
    have h1 : 0 < (1 + c ^ 2) * (c ^ 2 - 1) * (1 - a * b) :=
      mul_pos (mul_pos hB hC) (by linarith)
    have h2 : 0 ≤ (c ^ 2 - 1) ^ 2 * (a + b) := mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  have hfac : b * (1 + c ^ 2 + (c ^ 2 - 1) * b) * (c ^ 2 - 1 - (1 + c ^ 2) * a)
      - (c ^ 2 - 1 - (1 + c ^ 2) * b) * (a * (1 + c ^ 2 + (c ^ 2 - 1) * a))
      = (b - a) * ((1 + c ^ 2) * (c ^ 2 - 1) + (c ^ 2 - 1) ^ 2 * (a + b)
          - (1 + c ^ 2) * (c ^ 2 - 1) * a * b) := by ring
  rw [← sub_pos, div_sub_div _ _ (ne_of_gt hdb) (ne_of_gt hda)]
  refine div_pos ?_ (by positivity)
  rw [hfac]
  exact mul_pos (by linarith) hbr

/-- **Lune lower bound.**  If `‖ζ‖ ≥ ρ₀` and `f(u₀) ≤ ρ₀`, then `‖lune c ζ‖ ≥ u₀`. -/
theorem lune_lower {c ρ0 u0 : ℝ} (hc : 1 < c) (hu0 : 0 ≤ u0)
    (hu0B : u0 * (1 + c ^ 2) < c ^ 2 - 1)
    (hf : u0 * (1 + c ^ 2 + (c ^ 2 - 1) * u0) / (c ^ 2 - 1 - (1 + c ^ 2) * u0) ≤ ρ0)
    {ζ : ℂ} (hζ : ρ0 ≤ ‖ζ‖) : u0 ≤ ‖lune c ζ‖ := by
  set u := lune c ζ with hu
  have hB : 0 < 1 + c ^ 2 := by positivity
  have hC : 0 < c ^ 2 - 1 := by nlinarith
  have hle : u0 ≤ (c ^ 2 - 1) / (1 + c ^ 2) := by
    rw [le_div_iff₀ hB]; linarith
  rcases lt_or_ge ‖u‖ ((c ^ 2 - 1) / (1 + c ^ 2)) with hcase | hcase
  · have hCmu : 0 < c ^ 2 - 1 - (1 + c ^ 2) * ‖u‖ := by
      have h := mul_lt_mul_of_pos_left hcase hB
      have h2 : (1 + c ^ 2) * ((c ^ 2 - 1) / (1 + c ^ 2)) = c ^ 2 - 1 := by
        field_simp
      rw [h2] at h
      linarith
    have hnorm : ‖ζ‖
        ≤ ‖u‖ * (1 + c ^ 2 + (c ^ 2 - 1) * ‖u‖) / (c ^ 2 - 1 - (1 + c ^ 2) * ‖u‖) := by
      have hζeq : ζ = luneF c u := by
        rw [hu]; exact (luneF_lune c hc ζ).symm
      rw [hζeq, luneF, luneB, luneC, luneBr, luneCr, norm_div, norm_mul]
      have h1 : ‖((1 + c ^ 2 : ℝ) : ℂ) + ((c ^ 2 - 1 : ℝ) : ℂ) * u‖
          ≤ 1 + c ^ 2 + (c ^ 2 - 1) * ‖u‖ := by
        calc ‖((1 + c ^ 2 : ℝ) : ℂ) + ((c ^ 2 - 1 : ℝ) : ℂ) * u‖
            ≤ ‖((1 + c ^ 2 : ℝ) : ℂ)‖ + ‖((c ^ 2 - 1 : ℝ) : ℂ) * u‖ := norm_add_le _ _
          _ = 1 + c ^ 2 + (c ^ 2 - 1) * ‖u‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
                Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have h2 : c ^ 2 - 1 - (1 + c ^ 2) * ‖u‖
          ≤ ‖((c ^ 2 - 1 : ℝ) : ℂ) + ((1 + c ^ 2 : ℝ) : ℂ) * u‖ := by
        have h := norm_sub_le (((c ^ 2 - 1 : ℝ) : ℂ) + ((1 + c ^ 2 : ℝ) : ℂ) * u)
          (((1 + c ^ 2 : ℝ) : ℂ) * u)
        rw [add_sub_cancel_right] at h
        have hA : ‖((c ^ 2 - 1 : ℝ) : ℂ)‖ = c ^ 2 - 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        have hB2 : ‖((1 + c ^ 2 : ℝ) : ℂ)‖ = 1 + c ^ 2 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [hA, norm_mul, hB2] at h
        linarith
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left h1 (norm_nonneg u))
        hCmu h2
    rcases lt_or_ge ‖u‖ u0 with hlt | hge
    · exfalso
      have hstrict : ‖u‖ * (1 + c ^ 2 + (c ^ 2 - 1) * ‖u‖) / (c ^ 2 - 1 - (1 + c ^ 2) * ‖u‖)
          < u0 * (1 + c ^ 2 + (c ^ 2 - 1) * u0) / (c ^ 2 - 1 - (1 + c ^ 2) * u0) :=
        lune_f_lt (c := c) (norm_nonneg u) hlt hu0B
      linarith
    · exact hge
  · exact le_trans hle hcase


/-- **Upper bound.**  `‖ψ_A z‖ ≤ 4/5` on the closed unit disc. -/
theorem psiA_norm_upper {z : ℂ} (h2 : ‖z‖ ≤ 1) : ‖psiA z‖ ≤ 4 / 5 := by
  have hsl : ‖slitsA z‖ ≤ 1 := by
    have hmem : Work.APsi.psiA_st5 z ∈ Metric.closedBall (0 : ℂ) 1 :=
      Work.APsi.psiA_st5_maps (Work.APsi.psiA_mem_closedBall_one.mpr h2)
    have hle : ‖Work.APsi.psiA_st5 z‖ ≤ 1 := Work.APsi.psiA_mem_closedBall_one.mp hmem
    rwa [Work.APsi.psiA_slitsA_eq]
  have hl : ‖lune (36 / 5) (-slitsA z)‖ ≤ 1 :=
    lune_norm_le_one (36 / 5) (by norm_num) _ (by rw [norm_neg]; exact hsl)
  rw [psiA, norm_mul]
  have hc : ‖(-(4 / 5) : ℂ)‖ = 4 / 5 := by norm_num
  rw [hc]
  linarith

/-- **The five-stage chain.**  `‖ψ_A z‖ ≥ 1/2500` for `1/1000 ≤ ‖z‖ ≤ 1`. -/
theorem psiA_norm_lower {z : ℂ} (h1 : (1:ℝ)/1000 ≤ ‖z‖) (h2 : ‖z‖ ≤ 1) :
    (1:ℝ)/2500 ≤ ‖psiA z‖ := by
  have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at h1; norm_num at h1
  -- input of the first slit
  have hw1 : ‖(491/500 : ℂ) * z‖ = (491/500) * ‖z‖ := by rw [norm_mul]; norm_num
  -- stage 1
  have hρ1 : (491:ℝ)/500000 ≤ ‖(491/500 : ℂ) * z‖ := by rw [hw1]; linarith
  have hup1 : ‖(491/500 : ℂ) * z‖ ≤ 1 := by rw [hw1]; nlinarith
  have hzero1 : (491/500 : ℂ) * z ≠ 0 := by
    have hc : ((491:ℂ)/500) ≠ 0 := by norm_num
    exact mul_ne_zero hc hz
  have hout1 : (97:ℝ)/100000 ≤ ‖slit (9/10) ((491/500 : ℂ) * z)‖ := by
    refine le_trans ?_ (slit_lower (r := 9/10) (ρ := 491/500000) (by norm_num) (by norm_num)
      hzero1 (by norm_num) hρ1 hup1)
    norm_num
  -- stage 2
  have hv1 : (97:ℝ)/100000
      ≤ ‖rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z)‖ := by
    rw [norm_mul, norm_rot, one_mul]; exact hout1
  have hupv1 : ‖rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z)‖ ≤ 1 := by
    rw [norm_mul, norm_rot, one_mul]
    exact slit_norm_le_one (9/10) (by norm_num) (by norm_num) _ hup1
  have hzv1 : rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z) ≠ 0 :=
    mul_ne_zero (rot_ne_zero _) (slit_ne_zero (9/10) (by norm_num) _ hzero1)
  have hout2 : (91:ℝ)/100000
      ≤ ‖slit (379/625) (rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z))‖ := by
    refine le_trans ?_ (slit_lower (r := 379/625) (ρ := 97/100000) (by norm_num) (by norm_num)
      hzv1 (by norm_num) hv1 hupv1)
    norm_num
  -- stage 3
  have hv2 : (91:ℝ)/100000 ≤ ‖rot (2927/25000) * slit (379/625)
      (rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z))‖ := by
    rw [norm_mul, norm_rot, one_mul]; exact hout2
  have hupv2 : ‖rot (2927/25000) * slit (379/625)
      (rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z))‖ ≤ 1 := by
    rw [norm_mul, norm_rot, one_mul]
    exact slit_norm_le_one (379/625) (by norm_num) (by norm_num) _ hupv1
  have hzv2 : rot (2927/25000) * slit (379/625)
      (rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z)) ≠ 0 :=
    mul_ne_zero (rot_ne_zero _) (slit_ne_zero (379/625) (by norm_num) _ hzv1)
  have hout3 : (82:ℝ)/100000 ≤ ‖slit (673/1250) (rot (2927/25000) * slit (379/625)
      (rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z)))‖ := by
    refine le_trans ?_ (slit_lower (r := 673/1250) (ρ := 91/100000) (by norm_num) (by norm_num)
      hzv2 (by norm_num) hv2 hupv2)
    norm_num
  -- stage 4
  have hv3 : (82:ℝ)/100000 ≤ ‖rot (453/12500) * slit (673/1250)
      (rot (2927/25000) * slit (379/625)
        (rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z)))‖ := by
    rw [norm_mul, norm_rot, one_mul]; exact hout3
  have hupv3 : ‖rot (453/12500) * slit (673/1250)
      (rot (2927/25000) * slit (379/625)
        (rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z)))‖ ≤ 1 := by
    rw [norm_mul, norm_rot, one_mul]
    exact slit_norm_le_one (673/1250) (by norm_num) (by norm_num) _ hupv2
  have hzv3 : rot (453/12500) * slit (673/1250)
      (rot (2927/25000) * slit (379/625)
        (rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z))) ≠ 0 :=
    mul_ne_zero (rot_ne_zero _) (slit_ne_zero (673/1250) (by norm_num) _ hzv2)
  have hout4 : (79:ℝ)/100000 ≤ ‖slit (7487/10000) (rot (453/12500) * slit (673/1250)
      (rot (2927/25000) * slit (379/625)
        (rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z))))‖ := by
    refine le_trans ?_ (slit_lower (r := 7487/10000) (ρ := 82/100000) (by norm_num) (by norm_num)
      hzv3 (by norm_num) hv3 hupv3)
    norm_num
  -- the lune stage
  have hzeta : (79:ℝ)/100000 ≤ ‖-slitsA z‖ := by
    rw [norm_neg]
    show (79:ℝ)/100000 ≤ ‖rot (-1971/25000) * slit (7487/10000)
      (rot (453/12500) * slit (673/1250)
        (rot (2927/25000) * slit (379/625)
          (rot (2033/25000) * slit (9/10) ((491/500 : ℂ) * z))))‖
    rw [norm_mul, norm_rot, one_mul]
    exact hout4
  have hlune : (1:ℝ)/2000 ≤ ‖lune (36/5) (-slitsA z)‖ :=
    lune_lower (c := 36/5) (ρ0 := 79/100000) (u0 := 1/2000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hzeta
  have hfinal : ‖psiA z‖ = (4/5) * ‖lune (36/5) (-slitsA z)‖ := by
    rw [psiA, norm_mul]
    norm_num
  rw [hfinal]
  linarith


end

end Work.ANum
