import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.ACTrig.sin_pi_round
import Submission.Work.Cert.ACTrig.thales_arc
import Submission.Work.Cert.ACTrig.rot_dist_le
import Submission.Work.Cert.ACTrig.rot_chord
import Submission.Work.Cert.ACGeom.geomOK_facts
import Submission.Work.Cert.ACGeom.leafC_close
import Submission.Work.Cert.ACGeom.leafR_ge

/-! # Arc cover (soundness of the Theorem-A arc certificate)

The certificate (`Defs.lean`) presents the circle `|z| = Rk k / S` as a chain of short CCW leaves
`A → B` (`geomOK`), the first starting at `E`, consecutive leaves sharing endpoints, the last ending
at `n`, with `E` and `n` within `65536` ulps of the grid points `Rk k/S · rot(j/4096)` and
`Rk k/S · rot((j+1)/4096)`.  This module proves that the union of the leaf discs
`disc (leafC l) (leafR l)` covers the whole parameter interval `[j/4096, (j+1)/4096]`.

Geometry: a leaf's disc is the disc on the diameter between its two endpoints inflated by `ETOL`
ulps; by Thales the diameter disc contains the (minor) arc between the endpoint directions, and the
`ETOL` slack absorbs the endpoint errors (`65536` ulps) and the projection/rounding errors
(`CTOL` ulps, `1` ulp).  The lifted angle along the chain increases, so the leaf intervals tile. -/

namespace Work.Cert

open Complex Submission.CDTPlan
open scoped ComplexConjugate

/-! ## Basic facts about `rot` -/

theorem ac_rot_add (a b : ℝ) : rot (a + b) = rot a * rot b := by
  simp only [rot, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ac_norm_rot (t : ℝ) : ‖rot t‖ = 1 := by
  rw [rot, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

theorem ac_rot_ne_zero (t : ℝ) : rot t ≠ 0 := by
  intro h
  have := ac_norm_rot t
  rw [h] at this
  simp at this

theorem ac_S_pos : (0 : ℝ) < (S : ℝ) := by norm_num [S]

/-- the tolerance `CTOL` in absolute units (an opaque atom for `linarith`). -/
noncomputable def acCTOL : ℝ := (CTOL : ℝ) / (S : ℝ)

/-- one ulp in absolute units. -/
noncomputable def acE1 : ℝ := 1 / (S : ℝ)

theorem ac_norm_sub_le (x y z : ℂ) : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  have h := norm_add_le (x - y) (y - z)
  rwa [show x - y + (y - z) = x - z by ring] at h

theorem ac_norm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    ring
  calc ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h]
    _ = |r| := Real.sqrt_sq_eq_abs r

/-- `acAng z` is the argument of `z` in *turns*; `rot (acAng z) = z / ‖z‖`. -/
noncomputable def acAng (z : ℂ) : ℝ := Complex.arg z / (2 * Real.pi)

theorem ac_rot_acAng {z : ℂ} (hz : z ≠ 0) : rot (acAng z) = z / ‖z‖ := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  have hone : Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I) = z / ‖z‖ := by
    rw [eq_div_iff (by exact_mod_cast norm_ne_zero_iff.mpr hz)]
    rw [mul_comm]
    exact h
  rw [acAng, rot]
  convert hone using 1
  push_cast
  field_simp

theorem ac_unit_norm (z : ℂ) (hz : z ≠ 0) : ‖z / ‖z‖‖ = 1 := by
  rw [norm_div, ac_norm_ofReal, abs_of_nonneg (norm_nonneg z),
    div_self (ne_of_gt (norm_pos_iff.mpr hz))]

theorem ac_unit_mul_star (z : ℂ) (hz : z ≠ 0) : (z / ‖z‖) * star (z / ‖z‖) = 1 := by
  calc (z / ‖z‖) * star (z / ‖z‖) = ((Complex.normSq (z / ‖z‖) : ℝ) : ℂ) :=
        Complex.mul_conj (z / ‖z‖)
    _ = 1 := by rw [Complex.normSq_eq_norm_sq, ac_unit_norm z hz]; norm_num

theorem ac_normSq_cast (z : ℂ) :
    (((Complex.normSq z : ℝ)) : ℂ) = (((‖z‖ : ℝ) : ℂ)) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem ac_unit_star_mul (z : ℂ) (hz : z ≠ 0) : star (z / ‖z‖) * (z / ‖z‖) = 1 := by
  calc star (z / ‖z‖) * (z / ‖z‖) = (((Complex.normSq (z / ‖z‖) : ℝ)) : ℂ) := by
        rw [ac_normSq_cast]
        exact Complex.conj_mul' (z / ‖z‖)
    _ = 1 := by rw [Complex.normSq_eq_norm_sq, ac_unit_norm z hz]; norm_num

theorem ac_mul_ne_zero (p q : ℂ) (hp : p ≠ 0) (hq : q ≠ 0) : star p * q ≠ 0 := by
  intro h
  rcases mul_eq_zero.mp h with h1 | h2
  · exact hp (by simpa using congrArg star h1)
  · exact hq h2

/-- rotating `p` to `q` in the CCW direction: `rot τ · (p/‖p‖) = q/‖q‖`. -/
theorem ac_rot_turn (p q : ℂ) (hp : p ≠ 0) (hq : q ≠ 0) :
    rot (acAng (star p * q)) * (p / ‖p‖) = q / ‖q‖ := by
  have hpne : (((‖p‖ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hp)
  have hqne : (((‖q‖ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hq)
  have hw : star p * q ≠ 0 := ac_mul_ne_zero p q hp hq
  rw [ac_rot_acAng hw, Complex.norm_mul, norm_star]
  have hkey : star p * q / ((↑(‖p‖ * ‖q‖) : ℂ)) * (p / ((‖p‖ : ℝ) : ℂ))
      = (star p * p) * q / ((((‖p‖ : ℝ) : ℂ)) ^ 2 * (((‖q‖ : ℝ) : ℂ))) := by
    field_simp <;> push_cast <;> ring
  have hpp : star p * p = (((‖p‖ : ℝ) : ℂ)) ^ 2 := Complex.conj_mul' p
  rw [hkey, hpp]
  field_simp <;> ring

/-- rotating a product by a unit complex number does not change `star p * q`. -/
theorem ac_star_mul_unit (u p q : ℂ) (hu : ‖u‖ = 1) : star (u * p) * (u * q) = star p * q := by
  have huu : star u * u = 1 := by
    calc star u * u = (((Complex.normSq u : ℝ)) : ℂ) := by
          rw [ac_normSq_cast]
          exact Complex.conj_mul' u
      _ = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  have hsp : star (u * p) = star p * star u := by
    calc star (u * p) = star u * star p := star_mul' u p
      _ = star p * star u := by ring
  rw [hsp]
  calc star p * star u * (u * q) = star p * (star u * u) * q := by ring
    _ = star p * q := by rw [huu]; ring

/-! ## The scaled Thales lemma in rotated form -/

theorem ac_thales_gen (Rr : ℝ) (hR : 0 ≤ Rr) (a : ℂ) (ha : ‖a‖ = 1) (τ u : ℝ)
    (hτ0 : 0 ≤ τ) (hτ4 : τ ≤ 1 / 4) (hu0 : 0 ≤ u) (hu : u ≤ τ) :
    ‖Rr * (a * rot u) - Rr * (a + a * rot τ) / 2‖ ≤ Rr * ‖a - a * rot τ‖ / 2 := by
  have h := ACTrig.thales_arc Rr τ u hR hτ0 hτ4 hu0 hu
  have e1 : Rr * (a * rot u) - Rr * (a + a * rot τ) / 2
      = a * (Rr * rot u - Rr * (1 + rot τ) / 2) := by ring
  have e2 : a - a * rot τ = a * (1 - rot τ) := by ring
  rw [e1, e2, norm_mul, norm_mul, ha, one_mul, one_mul]
  exact h

/-- the final arithmetic of one leaf step: discard-free combination of the triangle
inequality, the Thales bound, the Lipschitz bound and the disc-radius budget. -/
theorem ac_final {nrm X Y W Q D r c2 e1 Rr : ℝ}
    (h4 : nrm ≤ X + Y) (hX : X ≤ D + Rr * W / 2) (hY : Y ≤ 2 * c2 + e1)
    (hW : Rr * W ≤ 4 * c2 + Q) (hr : Q / 2 + 4 * c2 + e1 + D ≤ r) : nrm ≤ r := by
  linarith

/-! ## The per-leaf geometric step

If `p`, `q` are the (rotated) endpoints of a short CCW leaf, `c` its (rotated) disc centre and `θ`
the lifted turn angle of `p`, then the disc of radius `r` covers the lifted interval
`[θ-δ, θ+τ+δ]` as soon as `r` exceeds the explicit threshold. -/

theorem acLeafStep {Rr δ : ℝ} {p q c : ℂ} {r : ℝ}
    (hRr : 0 ≤ Rr) (hδ : 0 ≤ δ)
    (him : 0 < (star p * q).im) (hre : 0 < (star p * q).re)
    (hnp : |‖p‖ - Rr| ≤ 2 * acCTOL)
    (hnq : |‖q‖ - Rr| ≤ 2 * acCTOL)
    (hc : ‖c - (p + q) / 2‖ ≤ acE1)
    (hr : ‖p - q‖ / 2 + 4 * acCTOL + acE1 + 2 * Real.pi * Rr * δ ≤ r)
    {θ : ℝ} (hθ : rot θ = p / ‖p‖) :
    ∀ s ∈ Set.Icc (θ - δ) (θ + acAng (star p * q) + δ), ‖Rr * rot s - c‖ ≤ r := by
  set w : ℂ := star p * q with hw
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at him
    simp at him
  have himw : 0 < w.im := by simpa [hw] using him
  have hrew : 0 < w.re := by simpa [hw] using hre
  have harg0 : 0 < w.arg := by
    have h1 : ¬ w.arg < 0 := by
      rw [Complex.arg_neg_iff]
      exact not_lt.mpr (le_of_lt himw)
    have h2 : w.arg ≠ 0 := by
      intro h
      have hz := (Complex.arg_eq_zero_iff.mp h).2
      linarith
    exact lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm h2)
  have harg2 : w.arg < Real.pi / 2 := by
    have hcos : Real.cos w.arg = w.re / ‖w‖ := Complex.cos_arg hwne
    have hpos : 0 < Real.cos w.arg := by rw [hcos]; positivity
    by_contra hcon
    have hcon' : Real.pi / 2 ≤ w.arg := le_of_not_gt hcon
    have h3 := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : (0 : ℝ) ≤ Real.pi / 2)
      (Complex.arg_le_pi w) hcon'
    rw [Real.cos_pi_div_two] at h3
    linarith
  have hτnn : 0 ≤ acAng w := by rw [acAng]; positivity
  have hτ4 : acAng w ≤ 1 / 4 := by
    rw [acAng, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [harg2]
  have hp0 : p ≠ 0 := fun h => hwne (by simp [hw, h])
  have hq0 : q ≠ 0 := fun h => hwne (by simp [hw, h])
  set a : ℂ := p / ‖p‖ with ha
  set b : ℂ := q / ‖q‖ with hb
  have ha1 : ‖a‖ = 1 := by rw [ha]; exact ac_unit_norm p hp0
  have hτmul : rot (acAng w) * a = b := by
    rw [ha, hb]
    exact ac_rot_turn p q hp0 hq0
  have haτb : a * rot (acAng w) = b := by rw [mul_comm]; exact hτmul
  have hθa : rot θ = a := by rw [ha]; exact hθ
  have hrotb : rot (θ + acAng w) = b := by
    rw [ac_rot_add, hθa, mul_comm]
    exact hτmul
  have hpne : (((‖p‖ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hp0)
  have hqne : (((‖q‖ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hq0)
  have hab_pair : Rr * a - p = (((Rr - ‖p‖ : ℝ)) : ℂ) * a := by
    simp only [ha]
    push_cast
    field_simp <;> ring
  have hda : ‖Rr * a - p‖ ≤ 2 * acCTOL := by
    rw [hab_pair, norm_mul, ac_norm_ofReal, abs_sub_comm]
    rw [ha1, mul_one]
    exact hnp
  have hdb' : Rr * b - q = (((Rr - ‖q‖ : ℝ)) : ℂ) * b := by
    simp only [hb]
    push_cast
    field_simp <;> ring
  have hb1 : ‖b‖ = 1 := by rw [hb]; exact ac_unit_norm q hq0
  have hdb : ‖Rr * b - q‖ ≤ 2 * acCTOL := by
    rw [hdb', norm_mul, ac_norm_ofReal, abs_sub_comm]
    rw [hb1, mul_one]
    exact hnq
  have h2c : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = (((2 : ℝ)) : ℂ) by norm_num, ac_norm_ofReal]
    norm_num
  have hcenter : ‖Rr * (a + b) / 2 - c‖ ≤ 2 * acCTOL + acE1 := by
    have h2 : ‖Rr * (a + b) / 2 - (p + q) / 2‖ ≤ 2 * acCTOL := by
      have heq : Rr * (a + b) / 2 - (p + q) / 2 = ((Rr * a - p) + (Rr * b - q)) / 2 := by ring
      rw [heq, norm_div, h2c, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith [hda, hdb, norm_add_le (Rr * a - p) (Rr * b - q)]
    calc ‖Rr * (a + b) / 2 - c‖
        ≤ ‖Rr * (a + b) / 2 - (p + q) / 2‖ + ‖(p + q) / 2 - c‖ :=
          ac_norm_sub_le _ _ _
      _ ≤ 2 * acCTOL + acE1 := by
          have h4 : ‖(p + q) / 2 - c‖ = ‖c - (p + q) / 2‖ := norm_sub_rev _ _
          linarith [h4, hc]
  have hab_pair2 : Rr * ‖a - b‖ ≤ 4 * acCTOL + ‖p - q‖ := by
    have heq : ‖Rr * a - Rr * b‖ = Rr * ‖a - b‖ := by
      rw [← mul_sub, norm_mul, ac_norm_ofReal, abs_of_nonneg hRr]
    rw [← heq]
    have h3 : ‖q - Rr * b‖ = ‖Rr * b - q‖ := norm_sub_rev q (Rr * b)
    calc ‖Rr * a - Rr * b‖ = ‖(Rr * a - p) + (p - q) + (q - Rr * b)‖ := by
          congr 1; ring
      _ ≤ ‖Rr * a - p‖ + ‖p - q‖ + ‖q - Rr * b‖ := by
          have h1 := norm_add_le ((Rr * a - p) + (p - q)) (q - Rr * b)
          have h2 := norm_add_le (Rr * a - p) (p - q)
          linarith
      _ ≤ 4 * acCTOL + ‖p - q‖ := by
          rw [h3]; linarith [hda, hdb]
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  by_cases hle : s ≤ θ
  · have hlip : ‖Rr * rot s - Rr * a‖ ≤ 2 * Real.pi * Rr * δ := by
      have h := ACTrig.rot_dist_le Rr s θ hRr
      rw [abs_of_nonpos (by linarith : s - θ ≤ 0), neg_sub] at h
      rw [hθa] at h
      have h1 : θ - s ≤ δ := by linarith
      have h2 : 2 * Real.pi * Rr * (θ - s) ≤ 2 * Real.pi * Rr * δ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    have htri : ‖Rr * rot s - Rr * (a + b) / 2‖ ≤ 2 * Real.pi * Rr * δ + Rr * ‖a - b‖ / 2 := by
      have heq : Rr * (a + b) / 2 = Rr * a + (Rr * b - Rr * a) / 2 := by ring
      rw [heq]
      have h2 : ‖Rr * rot s - (Rr * a + (Rr * b - Rr * a) / 2)‖
          ≤ ‖Rr * rot s - Rr * a‖ + ‖(Rr * b - Rr * a) / 2‖ := by
        have h := ac_norm_sub_le (Rr * rot s) (Rr * a)
          (Rr * a + (Rr * b - Rr * a) / 2)
        rw [show Rr * a - (Rr * a + (Rr * b - Rr * a) / 2) = -((Rr * b - Rr * a) / 2) by ring,
          norm_neg] at h
        exact h
      have h3 : ‖(Rr * b - Rr * a) / 2‖ = Rr * ‖a - b‖ / 2 := by
        rw [show Rr * b - Rr * a = Rr * (b - a) by ring, norm_div, norm_mul, h2c,
          ac_norm_ofReal, abs_of_nonneg hRr]
        rw [norm_sub_rev b a]
      linarith [h2, h3, hlip]
    have hfin : ‖Rr * rot s - c‖ ≤ r := by
      have h4 := ac_norm_sub_le (Rr * rot s) (Rr * (a + b) / 2) c
      exact ac_final (c2 := acCTOL) (e1 := acE1) (Q := ‖p - q‖)
        (W := ‖a - b‖) (D := 2 * Real.pi * Rr * δ) h4 htri hcenter hab_pair2 hr
    exact hfin
  · have hgt : θ < s := not_le.mp hle
    by_cases hle2 : s ≤ θ + acAng w
    · have hu0 : 0 ≤ s - θ := by linarith
      have hu1 : s - θ ≤ acAng w := by linarith
      have hkey := ac_thales_gen Rr hRr a ha1 (acAng w) (s - θ) hτnn hτ4 hu0 hu1
      have hcs : a * rot (s - θ) = rot s := by
        rw [← hθa, ← ac_rot_add]
        congr 1
        ring
      have he1 : a + a * rot (acAng w) = a + b := by rw [haτb]
      have he2 : a - a * rot (acAng w) = a - b := by rw [haτb]
      rw [hcs, he1, he2] at hkey
      have hfin : ‖Rr * rot s - c‖ ≤ r := by
        have h4 := ac_norm_sub_le (Rr * rot s) (Rr * (a + b) / 2) c
        have hk' : ‖Rr * rot s - Rr * (a + b) / 2‖
            ≤ 2 * Real.pi * Rr * δ + Rr * ‖a - b‖ / 2 := by
          have h0 : 0 ≤ 2 * Real.pi * Rr * δ := by positivity
          linarith [hkey, h0]
        exact ac_final (c2 := acCTOL) (e1 := acE1) (Q := ‖p - q‖)
          (W := ‖a - b‖) (D := 2 * Real.pi * Rr * δ) h4 hk' hcenter hab_pair2 hr
      exact hfin
    · have hgt2 : θ + acAng w < s := not_le.mp hle2
      have hlip : ‖Rr * rot s - Rr * b‖ ≤ 2 * Real.pi * Rr * δ := by
        have h := ACTrig.rot_dist_le Rr s (θ + acAng w) hRr
        rw [abs_of_nonneg (by linarith : 0 ≤ s - (θ + acAng w))] at h
        rw [hrotb] at h
        have h1 : s - (θ + acAng w) ≤ δ := by linarith
        have h2 : 2 * Real.pi * Rr * (s - (θ + acAng w)) ≤ 2 * Real.pi * Rr * δ :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        linarith
      have htri : ‖Rr * rot s - Rr * (a + b) / 2‖ ≤ 2 * Real.pi * Rr * δ + Rr * ‖a - b‖ / 2 := by
        have heq : Rr * (a + b) / 2 = Rr * b + (Rr * a - Rr * b) / 2 := by ring
        rw [heq]
        have h2 : ‖Rr * rot s - (Rr * b + (Rr * a - Rr * b) / 2)‖
            ≤ ‖Rr * rot s - Rr * b‖ + ‖(Rr * a - Rr * b) / 2‖ := by
          have h := ac_norm_sub_le (Rr * rot s) (Rr * b)
            (Rr * b + (Rr * a - Rr * b) / 2)
          rw [show Rr * b - (Rr * b + (Rr * a - Rr * b) / 2) = -((Rr * a - Rr * b) / 2) by ring,
            norm_neg] at h
          exact h
        have h3 : ‖(Rr * a - Rr * b) / 2‖ = Rr * ‖a - b‖ / 2 := by
          rw [show Rr * a - Rr * b = Rr * (a - b) by ring, norm_div, norm_mul, h2c,
            ac_norm_ofReal, abs_of_nonneg hRr]
        linarith [h2, h3, hlip]
      have hfin : ‖Rr * rot s - c‖ ≤ r := by
        have h4 := ac_norm_sub_le (Rr * rot s) (Rr * (a + b) / 2) c
        exact ac_final (c2 := acCTOL) (e1 := acE1) (Q := ‖p - q‖)
          (W := ‖a - b‖) (D := 2 * Real.pi * Rr * δ) h4 htri hcenter hab_pair2 hr
      exact hfin

/-- `ETOL` in absolute units (an opaque atom for `linarith`). -/
noncomputable def acET : ℝ := (ETOL : ℝ) / (S : ℝ)

theorem ac_twoCTOL : 2 * (CTOL : ℝ) / (S : ℝ) = 2 * acCTOL := by
  rw [acCTOL]
  ring

/-! ## Helpers for the endpoint analysis -/

theorem ac_unit_self_mul_star {z : ℂ} (hz : ‖z‖ = 1) : z * star z = 1 := by
  calc z * star z = (((Complex.normSq z : ℝ)) : ℂ) := Complex.mul_conj z
    _ = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num

theorem ac_unit_self_star_mul {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  calc star z * z = (((Complex.normSq z : ℝ)) : ℂ) := by
        rw [ac_normSq_cast]; exact Complex.conj_mul' z
    _ = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num

theorem ac_rot_neg (t : ℝ) : rot (-t) = star (rot t) := by
  have h1 : rot (-t) * rot t = 1 := by
    rw [← ac_rot_add, neg_add_cancel]
    simp [rot]
  exact mul_right_cancel₀ (ac_rot_ne_zero t) (by rw [h1, ac_unit_self_star_mul (ac_norm_rot t)])

theorem ac_rot_sub (θ t : ℝ) : rot (θ - t) = rot θ * star (rot t) := by
  rw [show θ - t = θ + (-t) by ring, ac_rot_add, ac_rot_neg]

/-- if `z` is within `B` of the circle of radius `Rr` and `rot θ = z/‖z‖`, then
`rot θ` is within `4B/Rr` of `1`. -/
theorem ac_rot_sub_one_le {Rr B θ : ℝ} {z : ℂ} (hRr : 0 < Rr) (hB : 0 ≤ B)
    (hz : ‖z - (((Rr : ℝ)) : ℂ)‖ ≤ B) (hbig : B ≤ Rr / 2) (hθ : rot θ = z / ‖z‖) :
    ‖rot θ - 1‖ ≤ 4 * B / Rr := by
  have h1 : |Rr - ‖z‖| ≤ B := by
    have h2 : |‖(((Rr : ℝ)) : ℂ)‖ - ‖z‖| ≤ ‖(((Rr : ℝ)) : ℂ) - z‖ :=
      abs_norm_sub_norm_le _ _
    rw [ac_norm_ofReal] at h2
    have h3 : ‖(((Rr : ℝ)) : ℂ) - z‖ = ‖z - (((Rr : ℝ)) : ℂ)‖ := norm_sub_rev _ _
    rw [h3, abs_of_nonneg (le_of_lt hRr)] at h2
    linarith
  have hzn : Rr / 2 ≤ ‖z‖ := by linarith [(abs_le.mp h1).2]
  have hzn0 : ‖z‖ ≠ 0 := by linarith
  have hzc : (((‖z‖ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hzn0
  have hz2 : ‖z - (((‖z‖ : ℝ)) : ℂ)‖ ≤ 2 * B := by
    have h4 : ‖z - (((‖z‖ : ℝ)) : ℂ)‖ ≤ ‖z - (((Rr : ℝ)) : ℂ)‖
        + ‖(((Rr : ℝ)) : ℂ) - (((‖z‖ : ℝ)) : ℂ)‖ := ac_norm_sub_le _ _ _
    have h5 : ‖(((Rr : ℝ)) : ℂ) - (((‖z‖ : ℝ)) : ℂ)‖ = |Rr - ‖z‖| := by
      rw [← Complex.ofReal_sub, ac_norm_ofReal]
    linarith [h4, h5, hz, h1]
  rw [hθ]
  have h6 : z / ‖z‖ - 1 = (z - (((‖z‖ : ℝ)) : ℂ)) / ‖z‖ := by
    field_simp <;> ring
  rw [h6, norm_div, ac_norm_ofReal, abs_of_nonneg (norm_nonneg z)]
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖z‖)]
  have h7 : 4 * B / Rr * (Rr / 2) = 2 * B := by
    field_simp <;> ring
  have h8 : 4 * B / Rr * (Rr / 2) ≤ 4 * B / Rr * ‖z‖ :=
    mul_le_mul_of_nonneg_left hzn (by positivity)
  linarith

/-- the sine bound at the endpoints: `2|sin (πx)| ≤ C` and `|x| ≤ 1/2` give `|x| ≤ C/4`. -/
theorem ac_abs_le_of_sin {x C : ℝ} (hx : |x| ≤ 1 / 2) (hC1 : C ≤ 1)
    (h : 2 * |Real.sin (Real.pi * x)| ≤ C) : |x| ≤ C / 4 := by
  obtain ⟨m, hm⟩ := ACTrig.sin_pi_round x
  have hm2 : |x - (m : ℝ)| ≤ C / 4 := by
    have h2 : |Real.sin (Real.pi * x)| ≤ C / 2 := by linarith
    linarith
  have hm0 : m = 0 := by
    have h2 : |(m : ℝ)| ≤ |x| + |x - (m : ℝ)| := by
      have hm : (m : ℝ) = x - (x - (m : ℝ)) := by ring
      calc |(m : ℝ)| = |x - (x - (m : ℝ))| := congrArg abs hm
        _ ≤ |x| + |x - (m : ℝ)| := by
              rw [abs_le]
              constructor <;>
                nlinarith [le_abs_self x, le_abs_self (x - (m : ℝ)), neg_le_abs x,
                  neg_le_abs (x - (m : ℝ))]
    have h3 : |(m : ℝ)| < 1 := by linarith
    have h4 : (-1 : ℝ) < (m : ℝ) ∧ (m : ℝ) < 1 := abs_lt.mp h3
    have h5 : (-1 : ℤ) < m := by exact_mod_cast h4.1
    have h6 : m < (1 : ℤ) := by exact_mod_cast h4.2
    omega
  rw [hm0] at hm2
  simpa using hm2

/-! ## The chain of leaves -/

noncomputable def acA (L : Leaf) : ℂ := cx L.Ax L.Ay

noncomputable def acB (L : Leaf) : ℂ := cx L.Bx L.By

/-- the chain predicate: `ls` is a nonempty chain of leaves starting at `p` and ending at `N`. -/
def acChainP (p N : ℂ) : List Leaf → Prop
  | [] => False
  | l :: rest => acA l = p ∧ (rest.map acA) ++ [N] = (l :: rest).map acB

/-- total turned angle (in turns) along the chain starting at `p`. -/
noncomputable def acTot (p : ℂ) : List Leaf → ℝ
  | [] => 0
  | l :: rest => acAng (star p * acB l) + acTot (acB l) rest

theorem acAng_pos_of {w : ℂ} (him : 0 < w.im) (hre : 0 < w.re) : 0 < acAng w := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at him
    simp at him
  rw [acAng]
  apply div_pos _ (by positivity : (0 : ℝ) < 2 * Real.pi)
  have h1 : ¬ w.arg < 0 := by
    rw [Complex.arg_neg_iff]
    exact not_lt.mpr (le_of_lt him)
  have h2 : w.arg ≠ 0 := by
    intro h
    have hz := (Complex.arg_eq_zero_iff.mp h).2
    linarith
  exact lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm h2)

/-- the tail of a chain of at least two leaves is again a chain. -/
theorem acChainP_tail {p N : ℂ} {l m : Leaf} {rest : List Leaf}
    (h : acChainP p N (l :: m :: rest)) : acChainP (acB l) N (m :: rest) := by
  obtain ⟨hAl, hrest⟩ := h
  refine ⟨?_, ?_⟩
  · have h' := hrest
    rw [List.map_cons, List.cons_append, List.map_cons] at h'
    exact (List.cons.inj h').1
  · have h' := hrest
    rw [List.map_cons, List.cons_append, List.map_cons] at h'
    exact (List.cons.inj h').2

/-- the chain predicate of the certificate. -/
theorem ac_chain_of : ∀ (ls : List Leaf) (Ex Ey nx ny : ℤ),
    (match ls with | [] => false | l :: _ => decide (l.Ax = Ex) && decide (l.Ay = Ey)) = true →
    chainOK nx ny ls = true → acChainP (cx Ex Ey) (cx nx ny) ls
  | [], Ex, Ey, nx, ny, h1, _ => by simp at h1
  | [l], Ex, Ey, nx, ny, h1, h2 => by
      have hAx : l.Ax = Ex ∧ l.Ay = Ey := by
        simpa [Bool.and_eq_true, decide_eq_true_eq] using h1
      have hBx : l.Bx = nx ∧ l.By = ny := by
        have h := h2
        simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h
      refine ⟨?_, ?_⟩
      · rw [acA, hAx.1, hAx.2]
      · simp only [List.map_nil, List.nil_append, List.map_cons]
        rw [acB, hBx.1, hBx.2]
  | l :: m :: rest, Ex, Ey, nx, ny, h1, h2 => by
      have hAx : l.Ax = Ex ∧ l.Ay = Ey := by
        simpa [Bool.and_eq_true, decide_eq_true_eq] using h1
      have h2' : l.Bx = m.Ax ∧ l.By = m.Ay ∧ chainOK nx ny (m :: rest) = true := by
        have h := h2
        simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨h.1.1, h.1.2, h.2⟩
      obtain ⟨hAm, hmap⟩ :=
        ac_chain_of (m :: rest) m.Ax m.Ay nx ny (by simp) h2'.2.2
      refine ⟨?_, ?_⟩
      · rw [acA, hAx.1, hAx.2]
      · have heq : acA m = acB l := by rw [hAm, acB, h2'.1, h2'.2.1]
        simp only [List.map_cons, List.cons_append, hmap, heq]

/-- the last endpoint of a chain is nonzero. -/
theorem acChainP_end_ne : ∀ (ls : List Leaf) (p N : ℂ), acChainP p N ls →
    (∀ l ∈ ls, acB l ≠ 0) → N ≠ 0
  | [], p, N, h, _ => by simp [acChainP] at h
  | [l], p, N, h, hne => by
      have hqN : acB l = N := by
        have hh := h.2
        simp only [List.map_nil, List.nil_append, List.map_cons] at hh
        simpa using hh.symm
      rw [← hqN]
      exact hne l (by simp)
  | l :: m :: rest, p, N, h, hne =>
      acChainP_end_ne (m :: rest) (acB l) N (acChainP_tail h)
        (fun x hx => hne x (by simp [hx]))

/-- the total turn of a CCW chain is nonnegative. -/
theorem ac_acTot_nonneg : ∀ (ls : List Leaf) (p N : ℂ), acChainP p N ls →
    (∀ l ∈ ls, 0 < acAng (star (acA l) * acB l)) → 0 ≤ acTot p ls
  | [], p, N, h, _ => by simp [acTot]
  | [l], p, N, h, hpos => by
      have hAl : acA l = p := h.1
      have h1 : 0 < acAng (star p * acB l) := by rw [← hAl]; exact hpos l (by simp)
      rw [show acTot p (l :: []) = acAng (star p * acB l) + acTot (acB l) [] from rfl,
        show acTot (acB l) [] = 0 from rfl, add_zero]
      linarith
  | l :: m :: rest, p, N, h, hpos => by
      have hAl : acA l = p := h.1
      have h1 : 0 < acAng (star p * acB l) := by rw [← hAl]; exact hpos l (by simp)
      have h2 : 0 ≤ acTot (acB l) (m :: rest) :=
        ac_acTot_nonneg (m :: rest) (acB l) N (acChainP_tail h)
          (fun x hx => hpos x (by simp [hx]))
      rw [show acTot p (l :: m :: rest)
          = acAng (star p * acB l) + acTot (acB l) (m :: rest) from rfl]
      linarith

/-- the total turn rotates `p/‖p‖` to `N/‖N‖`. -/
theorem ac_rot_acTot : ∀ (ls : List Leaf) (p N : ℂ), p ≠ 0 → N ≠ 0 →
    (∀ l ∈ ls, acB l ≠ 0) → acChainP p N ls → rot (acTot p ls) * (p / ‖p‖) = N / ‖N‖
  | [], p, N, _, _, _, h => by simp [acChainP] at h
  | [l], p, N, hp, hN, hne, h => by
      have hql : acB l ≠ 0 := hne l (by simp)
      have hqN : acB l = N := by
        have hh := h.2
        simp only [List.map_nil, List.nil_append, List.map_cons] at hh
        simpa using hh.symm
      have hrot := ac_rot_turn p (acB l) hp hql
      rw [show acTot p (l :: []) = acAng (star p * acB l) + acTot (acB l) [] from rfl,
        show acTot (acB l) [] = 0 from rfl, add_zero]
      rw [hrot, hqN]
  | l :: m :: rest, p, N, hp, hN, hne, h => by
      have hql : acB l ≠ 0 := hne l (by simp)
      have hch' : acChainP (acB l) N (m :: rest) := acChainP_tail h
      have ih' := ac_rot_acTot (m :: rest) (acB l) N hql hN
          (fun x hx => hne x (by simp [hx])) hch'
      have hrot := ac_rot_turn p (acB l) hp hql
      rw [show acTot p (l :: m :: rest)
          = acAng (star p * acB l) + acTot (acB l) (m :: rest) from rfl]
      rw [ac_rot_add]
      calc rot (acAng (star p * acB l)) * rot (acTot (acB l) (m :: rest)) * (p / ‖p‖)
          = (rot (acAng (star p * acB l)) * (p / ‖p‖)) * rot (acTot (acB l) (m :: rest)) := by
            ring
        _ = (acB l / ‖acB l‖) * rot (acTot (acB l) (m :: rest)) := by rw [hrot]
        _ = rot (acTot (acB l) (m :: rest)) * (acB l / ‖acB l‖) := by ring
        _ = N / ‖N‖ := ih'

/-! ## The chain covers the arc -/

theorem acCov (k : ℕ) (Rr δ : ℝ) (hRr : Rr = (Rk k : ℝ) / (S : ℝ)) (hδ : 0 ≤ δ)
    (hRrpos : 0 < Rr) (hgap : 2 * acCTOL < Rr)
    (hbud : 4 * acCTOL + 2 * acE1 + 2 * Real.pi * Rr * δ ≤ acET)
    (u : ℂ) (hu : ‖u‖ = 1) (N : ℂ) :
    ∀ (ls : List Leaf) (p : ℂ) (θ : ℝ), p ≠ 0 → rot θ = u * (p / ‖p‖) → acChainP p N ls →
      (∀ l ∈ ls, geomOK l = true) → (∀ l ∈ ls, l.k = k) →
      ∀ s ∈ Set.Icc (θ - δ) (θ + acTot p ls + δ),
        ∃ l ∈ ls, ‖Rr * rot s - u * leafC l‖ ≤ leafR l
  | [], p, θ, hp, hθ, hch, hg, hk, s, hs => by simp [acChainP] at hch
  | [l], p, θ, hp, hθ, hch, hg, hk, s, hs => by
      have hch0 := hch
      have hAl : acA l = p := hch.1
      have hgl : geomOK l = true := hg l (by simp)
      have hkl : l.k = k := hk l (by simp)
      obtain ⟨hchU, hdist, him0, hre0, hna, hnb⟩ := ACGeom.geomOK_facts l hgl
      have hstar : star (u * p) * (u * acB l) = star p * acB l := ac_star_mul_unit u p (acB l) hu
      have him : 0 < (star (u * p) * (u * acB l)).im := by rw [hstar, ← hAl]; exact him0
      have hre : 0 < (star (u * p) * (u * acB l)).re := by rw [hstar, ← hAl]; exact hre0
      have hna' : |‖acA l‖ - Rr| ≤ 2 * acCTOL := by
        have h := hna
        rw [hkl, ac_twoCTOL] at h
        rw [hRr]
        exact h
      have hnb' : |‖acB l‖ - Rr| ≤ 2 * acCTOL := by
        have h := hnb
        rw [hkl, ac_twoCTOL] at h
        rw [hRr]
        exact h
      have hnp : |‖u * p‖ - Rr| ≤ 2 * acCTOL := by
        rw [norm_mul, hu, one_mul, ← hAl]
        exact hna'
      have hnq : |‖u * acB l‖ - Rr| ≤ 2 * acCTOL := by
        rw [norm_mul, hu, one_mul]
        exact hnb'
      have hc : ‖u * leafC l - (u * p + u * acB l) / 2‖ ≤ acE1 := by
        have he : u * leafC l - (u * p + u * acB l) / 2
            = u * (leafC l - (p + acB l) / 2) := by ring
        rw [he, norm_mul, hu, one_mul, ← hAl]
        exact ACGeom.leafC_close l
      have hr : ‖u * p - u * acB l‖ / 2 + 4 * acCTOL + acE1 + 2 * Real.pi * Rr * δ ≤ leafR l := by
        have hpq : ‖u * p - u * acB l‖ ≤ (l.chU : ℝ) / (S : ℝ) := by
          rw [← mul_sub, norm_mul, hu, one_mul, ← hAl]
          exact hdist
        have hRg := ACGeom.leafR_ge l hchU
        have hRg' : (l.chU : ℝ) / (2 * (S : ℝ)) + acET - acE1 ≤ leafR l := by
          have he : (l.chU : ℝ) / (2 * (S : ℝ)) + acET - acE1
              = ((l.chU : ℝ) / 2 + (ETOL : ℝ) - 1) / (S : ℝ) := by
            rw [acET, acE1]; field_simp <;> ring
          rw [he]; exact hRg
        have hrel : ((l.chU : ℝ) / (S : ℝ)) / 2 = (l.chU : ℝ) / (2 * (S : ℝ)) := by ring
        linarith [hpq, hRg', hbud, hrel]
      have hθ' : rot θ = (u * p) / ‖u * p‖ := by
        rw [hθ, norm_mul, hu, one_mul]
        ring
      have hq_ne : acB l ≠ 0 := by
        intro h0
        have h1 : ‖acB l‖ = 0 := by rw [h0]; simp
        linarith [(abs_le.mp hnb').1, h1, hgap]
      have hleaf := acLeafStep (Rr := Rr) (δ := δ) (p := u * p) (q := u * acB l)
        (c := u * leafC l) (r := leafR l) (le_of_lt hRrpos) hδ him hre hnp hnq hc hr hθ'
      rw [hstar] at hleaf
      have hτ : acTot p (l :: []) = acAng (star p * acB l) := by simp [acTot]
      rw [hτ] at hs
      exact ⟨l, by simp, hleaf s hs⟩
  | l :: m :: rest, p, θ, hp, hθ, hch, hg, hk, s, hs => by
      have hch0 := hch
      have hAl : acA l = p := hch.1
      have hgl : geomOK l = true := hg l (by simp)
      have hkl : l.k = k := hk l (by simp)
      obtain ⟨hchU, hdist, him0, hre0, hna, hnb⟩ := ACGeom.geomOK_facts l hgl
      have hstar : star (u * p) * (u * acB l) = star p * acB l := ac_star_mul_unit u p (acB l) hu
      have him : 0 < (star (u * p) * (u * acB l)).im := by rw [hstar, ← hAl]; exact him0
      have hre : 0 < (star (u * p) * (u * acB l)).re := by rw [hstar, ← hAl]; exact hre0
      have hna' : |‖acA l‖ - Rr| ≤ 2 * acCTOL := by
        have h := hna
        rw [hkl, ac_twoCTOL] at h
        rw [hRr]
        exact h
      have hnb' : |‖acB l‖ - Rr| ≤ 2 * acCTOL := by
        have h := hnb
        rw [hkl, ac_twoCTOL] at h
        rw [hRr]
        exact h
      have hnp : |‖u * p‖ - Rr| ≤ 2 * acCTOL := by
        rw [norm_mul, hu, one_mul, ← hAl]
        exact hna'
      have hnq : |‖u * acB l‖ - Rr| ≤ 2 * acCTOL := by
        rw [norm_mul, hu, one_mul]
        exact hnb'
      have hc : ‖u * leafC l - (u * p + u * acB l) / 2‖ ≤ acE1 := by
        have he : u * leafC l - (u * p + u * acB l) / 2
            = u * (leafC l - (p + acB l) / 2) := by ring
        rw [he, norm_mul, hu, one_mul, ← hAl]
        exact ACGeom.leafC_close l
      have hr : ‖u * p - u * acB l‖ / 2 + 4 * acCTOL + acE1 + 2 * Real.pi * Rr * δ ≤ leafR l := by
        have hpq : ‖u * p - u * acB l‖ ≤ (l.chU : ℝ) / (S : ℝ) := by
          rw [← mul_sub, norm_mul, hu, one_mul, ← hAl]
          exact hdist
        have hRg := ACGeom.leafR_ge l hchU
        have hRg' : (l.chU : ℝ) / (2 * (S : ℝ)) + acET - acE1 ≤ leafR l := by
          have he : (l.chU : ℝ) / (2 * (S : ℝ)) + acET - acE1
              = ((l.chU : ℝ) / 2 + (ETOL : ℝ) - 1) / (S : ℝ) := by
            rw [acET, acE1]; field_simp <;> ring
          rw [he]; exact hRg
        have hrel : ((l.chU : ℝ) / (S : ℝ)) / 2 = (l.chU : ℝ) / (2 * (S : ℝ)) := by ring
        linarith [hpq, hRg', hbud, hrel]
      have hθ' : rot θ = (u * p) / ‖u * p‖ := by
        rw [hθ, norm_mul, hu, one_mul]
        ring
      have hq_ne : acB l ≠ 0 := by
        intro h0
        have h1 : ‖acB l‖ = 0 := by rw [h0]; simp
        linarith [(abs_le.mp hnb').1, h1, hgap]
      have hleaf := acLeafStep (Rr := Rr) (δ := δ) (p := u * p) (q := u * acB l)
        (c := u * leafC l) (r := leafR l) (le_of_lt hRrpos) hδ him hre hnp hnq hc hr hθ'
      rw [hstar] at hleaf
      have hch' : acChainP (acB l) N (m :: rest) := acChainP_tail hch
      have hg' : ∀ x ∈ m :: rest, geomOK x = true := fun x hx => hg x (by simp [hx])
      have hk' : ∀ x ∈ m :: rest, x.k = k := fun x hx => hk x (by simp [hx])
      have hτmul : rot (acAng (star p * acB l)) * (p / ‖p‖) = acB l / ‖acB l‖ :=
        ac_rot_turn p (acB l) hp hq_ne
      have hθ'' : rot (θ + acAng (star p * acB l)) = u * (acB l / ‖acB l‖) := by
        rw [ac_rot_add, hθ]
        calc u * (p / ‖p‖) * rot (acAng (star p * acB l))
            = u * (rot (acAng (star p * acB l)) * (p / ‖p‖)) := by ring
          _ = u * (acB l / ‖acB l‖) := by rw [hτmul]
      by_cases hsle : s ≤ θ + acAng (star p * acB l) + δ
      · refine ⟨l, by simp, ?_⟩
        exact hleaf s ⟨hs.1, hsle⟩
      · have hs2' : s ∈ Set.Icc ((θ + acAng (star p * acB l)) - δ)
            ((θ + acAng (star p * acB l)) + acTot (acB l) (m :: rest) + δ) := by
          refine ⟨by linarith [hs.1], ?_⟩
          have hτ : acTot p (l :: m :: rest)
              = acAng (star p * acB l) + acTot (acB l) (m :: rest) := rfl
          rw [hτ] at hs
          linarith [hs.2]
        obtain ⟨x, hx, hxc⟩ := acCov k Rr δ hRr hδ hRrpos hgap hbud u hu N
          (m :: rest) (acB l) (θ + acAng (star p * acB l)) hq_ne hθ'' hch' hg' hk' s hs2'
        exact ⟨x, by simp [hx], hxc⟩

/-! ## The numeric side conditions for `Rk` -/

theorem ac_Rk_ge (k : ℕ) (hk : k ≤ 2) : (10995116277760000 : ℤ) ≤ Rk k := by
  interval_cases k
  · rw [show Rk 0 = fdiv S 10000 from rfl]; decide
  · rw [show Rk 1 = fdiv (283 * S) 500 from rfl]; decide
  · rw [show Rk 2 = S from rfl]; decide

/-! ## Assembly -/

theorem arc_cover : ArcCover := by
  intro k j Ex Ey nx ny ls hk hj hE hn hfirst hchain hall
  set Rr : ℝ := (Rk k : ℝ) / (S : ℝ) with hRr
  set δ : ℝ := 100000 / ((S : ℝ) * Rr) with hδdef
  have hSp : (0 : ℝ) < (S : ℝ) := ac_S_pos
  have hRkge : (10995116277760000 : ℝ) ≤ (Rk k : ℝ) := by
    exact_mod_cast ac_Rk_ge k hk
  have hRrpos : 0 < Rr := by rw [hRr]; positivity
  have hSR : (S : ℝ) * Rr = (Rk k : ℝ) := by rw [hRr]; field_simp
  have hSRpos : 0 < (S : ℝ) * Rr := by rw [hSR]; linarith
  have hRrge : (10995116277760000 : ℝ) / (S : ℝ) ≤ Rr := by
    rw [hRr]; exact div_le_div_of_nonneg_right hRkge (le_of_lt hSp)
  have hgap : 2 * acCTOL < Rr := by
    rw [acCTOL, hRr]
    rw [show 2 * ((CTOL : ℝ) / (S : ℝ)) = (2 * (CTOL : ℝ)) / (S : ℝ) by ring]
    rw [div_lt_div_iff_of_pos_right hSp]
    rw [show (CTOL : ℝ) = 1024 by norm_num [CTOL]]
    linarith
  have hδnn : 0 ≤ δ := by rw [hδdef]; positivity
  have hδ18 : δ ≤ 1 / 8 := by
    rw [hδdef, div_le_iff₀ hSRpos]
    rw [show (1 / 8 : ℝ) * ((S : ℝ) * Rr) = (Rk k : ℝ) / 8 by rw [hSR]; ring]
    linarith
  have hbud : 4 * acCTOL + 2 * acE1 + 2 * Real.pi * Rr * δ ≤ acET := by
    have hkey : 2 * Real.pi * Rr * δ = 2 * Real.pi * 100000 / (S : ℝ) := by
      rw [hδdef]; field_simp <;> ring
    rw [hkey, acCTOL, acE1, acET]
    rw [show 4 * ((CTOL : ℝ) / (S : ℝ)) + 2 * (1 / (S : ℝ)) + 2 * Real.pi * 100000 / (S : ℝ)
        = (4 * (CTOL : ℝ) + 2 * 1 + 2 * Real.pi * 100000) / (S : ℝ) by ring]
    rw [div_le_div_iff_of_pos_right hSp]
    have hpi : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
    rw [show (CTOL : ℝ) = 1024 by norm_num [CTOL],
      show (ETOL : ℝ) = 1048576 by norm_num [ETOL]]
    nlinarith [hpi]
  -- the rotated frame
  set u : ℂ := star (rot ((j : ℝ) / 4096)) with hudef
  have hu : ‖u‖ = 1 := by rw [hudef, norm_star, ac_norm_rot]
  have hu_ne : u ≠ 0 := by
    rw [hudef]; exact star_ne_zero.mpr (ac_rot_ne_zero _)
  have hall' : ∀ l ∈ ls, l.k = k ∧ geomOK l = true := by
    intro l hl
    have h := (List.all_eq_true.mp hall) l hl
    simpa [Bool.and_eq_true, decide_eq_true_eq] using h
  have hgeom : ∀ l ∈ ls, geomOK l = true := fun l hl => (hall' l hl).2
  have hkk : ∀ l ∈ ls, l.k = k := fun l hl => (hall' l hl).1
  have hchP : acChainP (cx Ex Ey) (cx nx ny) ls := ac_chain_of ls Ex Ey nx ny hfirst hchain
  have hne : ∀ l ∈ ls, acB l ≠ 0 := by
    intro l hl
    obtain ⟨_, _, _, _, _, hnb⟩ := ACGeom.geomOK_facts l (hgeom l hl)
    have h : |‖acB l‖ - Rr| ≤ 2 * acCTOL := by
      have hh := hnb
      rw [hkk l hl, ac_twoCTOL] at hh
      rw [hRr]
      exact hh
    intro h0
    have h1 : ‖acB l‖ = 0 := by rw [h0]; simp
    linarith [(abs_le.mp h).1, h1, hgap]
  have hN_ne : cx nx ny ≠ 0 := acChainP_end_ne ls (cx Ex Ey) (cx nx ny) hchP hne
  -- nonemptiness and the first leaf
  cases hls : ls with
  | nil =>
    rw [hls] at hfirst
    simp at hfirst
  | cons l0 rest0 =>
    have hm_l0 : l0 ∈ ls := by rw [hls]; simp
    have hgl0 : geomOK l0 = true := hgeom l0 hm_l0
    obtain ⟨hchU0, hdist0, him00, hre00, hna0, hnb0⟩ := ACGeom.geomOK_facts l0 hgl0
    have hA0 : acA l0 = cx Ex Ey := by
      have h := hchP
      rw [hls] at h
      exact h.1
    have hna0' : |‖cx Ex Ey‖ - Rr| ≤ 2 * acCTOL := by
      have h := hna0
      rw [hkk l0 hm_l0, ac_twoCTOL] at h
      rw [hRr, ← hA0]
      exact h
    have hpne : cx Ex Ey ≠ 0 := by
      intro h0
      have h1 : ‖cx Ex Ey‖ = 0 := by rw [h0]; simp
      linarith [(abs_le.mp hna0').1, h1, hgap]
    -- the endpoint deviations
    have huE : ‖u * cx Ex Ey - Rr‖ ≤ 65536 / (S : ℝ) := by
      have h1 : u * (Rr * rot ((j : ℝ) / 4096)) = Rr := by
        rw [hudef]
        calc star (rot ((j : ℝ) / 4096)) * (Rr * rot ((j : ℝ) / 4096))
            = Rr * (star (rot ((j : ℝ) / 4096)) * rot ((j : ℝ) / 4096)) := by ring
          _ = Rr := by rw [ac_unit_self_star_mul (ac_norm_rot _), mul_one]
      have he : u * cx Ex Ey - Rr = u * (cx Ex Ey - Rr * rot ((j : ℝ) / 4096)) := by
        rw [mul_sub, h1]
      rw [he, norm_mul, hu, one_mul]
      exact hE
    have huN : ‖u * cx nx ny - Rr * rot (1 / 4096)‖ ≤ 65536 / (S : ℝ) := by
      have h1 : u * (Rr * rot (((j : ℝ) + 1) / 4096)) = Rr * rot (1 / 4096) := by
        rw [hudef]
        rw [show ((j : ℝ) + 1) / 4096 = (j : ℝ) / 4096 + 1 / 4096 by ring, ac_rot_add]
        calc star (rot ((j : ℝ) / 4096)) * (Rr * (rot ((j : ℝ) / 4096) * rot (1 / 4096)))
            = Rr * ((star (rot ((j : ℝ) / 4096)) * rot ((j : ℝ) / 4096)) * rot (1 / 4096)) := by
              ring
          _ = Rr * rot (1 / 4096) := by
              rw [ac_unit_self_star_mul (ac_norm_rot _), one_mul]
      have he : u * cx nx ny - Rr * rot (1 / 4096)
          = u * (cx nx ny - Rr * rot (((j : ℝ) + 1) / 4096)) := by
        rw [mul_sub, h1]
      rw [he, norm_mul, hu, one_mul]
      exact hn
    -- the bounds on the start angle
    have hB : 65536 / (S : ℝ) ≤ Rr / 2 := by
      rw [div_le_div_iff₀ hSp (by norm_num : (0 : ℝ) < 2), mul_comm Rr (S : ℝ), hSR]
      linarith [hRkge]
    have hnf : Rr / 2 ≤ ‖u * cx Ex Ey‖ := by
      have h2 : Rr ≤ ‖u * cx Ex Ey‖ + ‖u * cx Ex Ey - (((Rr : ℝ)) : ℂ)‖ := by
        have h3 : ‖u * cx Ex Ey - (u * cx Ex Ey - (((Rr : ℝ)) : ℂ))‖
            ≤ ‖u * cx Ex Ey‖ + ‖u * cx Ex Ey - (((Rr : ℝ)) : ℂ)‖ := by
          have hh := ac_norm_sub_le (u * cx Ex Ey) 0 (u * cx Ex Ey - (((Rr : ℝ)) : ℂ))
          rw [sub_zero, zero_sub, norm_neg] at hh
          exact hh
        rwa [show u * cx Ex Ey - (u * cx Ex Ey - (((Rr : ℝ)) : ℂ)) = (((Rr : ℝ)) : ℂ) by ring,
          ac_norm_ofReal, abs_of_nonneg (le_of_lt hRrpos)] at h3
      linarith [huE, h2, hB]
    have hEne : u * cx Ex Ey ≠ 0 := mul_ne_zero hu_ne hpne
    have hθle : ‖rot (acAng (u * cx Ex Ey)) - 1‖ ≤ 4 * (65536 / (S : ℝ)) / Rr :=
      ac_rot_sub_one_le hRrpos (by positivity) huE hB (ac_rot_acAng hEne)
    have hθabs : |acAng (u * cx Ex Ey)| ≤ 1 / 2 := by
      rw [acAng, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
        div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have h1 := Complex.neg_pi_lt_arg (u * cx Ex Ey)
      have h2 := Complex.arg_le_pi (u * cx Ex Ey)
      have h3 : |Complex.arg (u * cx Ex Ey)| ≤ Real.pi := abs_le.mpr ⟨le_of_lt h1, h2⟩
      linarith
    have hC1 : 4 * (65536 / (S : ℝ)) / Rr ≤ 1 := by
      have hrel : 4 * (65536 / (S : ℝ)) / Rr = 262144 / ((S : ℝ) * Rr) := by
        field_simp <;> ring
      rw [hrel, div_le_one hSRpos, hSR]
      linarith [hRkge]
    have hsin1 : 2 * |Real.sin (Real.pi * acAng (u * cx Ex Ey))| ≤ 4 * (65536 / (S : ℝ)) / Rr := by
      have h2 := ACTrig.rot_chord (acAng (u * cx Ex Ey)) 0
      rw [sub_zero, show rot (0 : ℝ) = 1 from by simp [rot]] at h2
      rw [← h2]
      exact hθle
    have hε : 65536 / ((S : ℝ) * Rr) ≤ δ := by
      rw [hδdef, div_le_div_iff₀ hSRpos hSRpos]
      exact mul_le_mul_of_nonneg_right (by norm_num : (65536 : ℝ) ≤ 100000) (le_of_lt hSRpos)
    have hθ_le : acAng (u * cx Ex Ey) ≤ δ := by
      have h4 := ac_abs_le_of_sin hθabs hC1 hsin1
      have h5 : (4 * (65536 / (S : ℝ)) / Rr) / 4 ≤ δ := by
        rw [show (4 * (65536 / (S : ℝ)) / Rr) / 4 = 65536 / ((S : ℝ) * Rr) by
          field_simp <;> ring]
        exact hε
      have h6 : |acAng (u * cx Ex Ey)| ≤ δ := by linarith
      linarith [abs_le.mp h6]
    -- the end angle
    set θE : ℝ := acAng (u * cx Ex Ey) with hθEdef
    have hθ : rot θE = u * (cx Ex Ey / ‖cx Ex Ey‖) := by
      rw [hθEdef, ac_rot_acAng hEne, norm_mul, hu, one_mul]
      ring
    have htend_nn : 0 ≤ acTot (cx Ex Ey) ls :=
      ac_acTot_nonneg ls (cx Ex Ey) (cx nx ny) hchP (fun l hl => by
        obtain ⟨_, _, him, hre, _, _⟩ := ACGeom.geomOK_facts l (hgeom l hl)
        exact acAng_pos_of him hre)
    have hrot_end : rot (θE + acTot (cx Ex Ey) ls) = u * (cx nx ny / ‖cx nx ny‖) := by
      have h1 := ac_rot_acTot ls (cx Ex Ey) (cx nx ny) hpne hN_ne hne hchP
      rw [ac_rot_add]
      calc rot θE * rot (acTot (cx Ex Ey) ls)
          = u * (rot (acTot (cx Ex Ey) ls) * (cx Ex Ey / ‖cx Ex Ey‖)) := by rw [hθ]; ring
        _ = u * (cx nx ny / ‖cx nx ny‖) := by rw [h1]
    -- end deviation, in the frame rotated to the end point
    set w : ℂ := cx nx ny * star (rot (1 / 4096)) with hwdef
    have hw2 : ‖u * w - Rr‖ ≤ 65536 / (S : ℝ) := by
      have h1 : star (rot (1 / 4096)) * (Rr * rot (1 / 4096)) = Rr := by
        calc star (rot (1 / 4096)) * (Rr * rot (1 / 4096))
            = Rr * (star (rot (1 / 4096)) * rot (1 / 4096)) := by ring
          _ = Rr := by rw [ac_unit_self_star_mul (ac_norm_rot _), mul_one]
      have he : u * w - Rr = star (rot (1 / 4096)) * (u * cx nx ny - Rr * rot (1 / 4096)) := by
        rw [hwdef]
        rw [show star (rot (1 / 4096)) * (u * cx nx ny - Rr * rot (1 / 4096))
            = star (rot (1 / 4096)) * u * cx nx ny
              - star (rot (1 / 4096)) * (Rr * rot (1 / 4096)) by ring]
        rw [h1]
        ring
      rw [he, norm_mul, norm_star, ac_norm_rot, one_mul]
      exact huN
    have hNnorm : (((‖cx nx ny‖ : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hN_ne)
    have hrot_w : rot (θE + acTot (cx Ex Ey) ls - 1 / 4096) = (u * w) / ‖u * w‖ := by
      have hnorm : ‖u * w‖ = ‖cx nx ny‖ := by
        rw [hwdef]
        simp only [norm_mul, norm_star, ac_norm_rot, hu, one_mul, mul_one]
      calc rot (θE + acTot (cx Ex Ey) ls - 1 / 4096)
          = rot (θE + acTot (cx Ex Ey) ls) * star (rot (1 / 4096)) := by rw [ac_rot_sub]
        _ = u * (cx nx ny / ‖cx nx ny‖) * star (rot (1 / 4096)) := by rw [hrot_end]
        _ = (u * w) / ‖u * w‖ := by
            rw [hnorm, hwdef]
            field_simp <;> ring
    have hwle : ‖rot (θE + acTot (cx Ex Ey) ls - 1 / 4096) - 1‖ ≤ 4 * (65536 / (S : ℝ)) / Rr :=
      ac_rot_sub_one_le hRrpos (by positivity) hw2 hB hrot_w
    -- the end angle bound
    set θend : ℝ := θE + acTot (cx Ex Ey) ls with hθenddef
    have hsin_end : 2 * |Real.sin (Real.pi * (θend - 1 / 4096))| ≤ 4 * (65536 / (S : ℝ)) / Rr := by
      have h2 := ACTrig.rot_chord (θend - 1 / 4096) 0
      rw [sub_zero, show rot (0 : ℝ) = 1 from by simp [rot]] at h2
      rw [← h2]
      rw [hθenddef]
      exact hwle
    have hxt : -(1 : ℝ) / 2 ≤ θend := by
      rw [hθenddef, hθEdef]
      have h2 : |acAng (u * cx Ex Ey)| ≤ 1 / 2 := hθabs
      linarith [abs_le.mp h2, htend_nn]
    obtain ⟨m, hm⟩ := ACTrig.sin_pi_round (θend - 1 / 4096)
    have hm2 : |θend - 1 / 4096 - (m : ℝ)| ≤ δ := by
      have h2 : |Real.sin (Real.pi * (θend - 1 / 4096))| ≤ 2 * (65536 / (S : ℝ)) / Rr := by
        have hrel : 4 * (65536 / (S : ℝ)) / Rr = 2 * (2 * (65536 / (S : ℝ)) / Rr) := by ring
        linarith [hsin_end, hrel]
      have h3 : (2 * (65536 / (S : ℝ)) / Rr) / 2 = 65536 / ((S : ℝ) * Rr) := by
        field_simp <;> ring
      linarith [hm, h3, hε]
    have hθend_ge : 1 / 4096 - δ ≤ θend := by
      have h1 : θend - 1 / 4096 - (m : ℝ) ≤ δ := (abs_le.mp hm2).2
      have h3 : -(1 : ℝ) / 2 - 1 / 4096 - δ > -1 := by linarith [hδ18]
      have hlow : -(1 : ℝ) / 2 - 1 / 4096 - δ ≤ θend - 1 / 4096 - δ := by linarith [hxt]
      have h4 : (-1 : ℝ) < (m : ℝ) := by linarith [h1, h3, hlow]
      have h5 : (-1 : ℤ) < m := by exact_mod_cast h4
      have h6 : (0 : ℤ) ≤ m := by omega
      have h7 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h6
      have h8 : -(δ) ≤ θend - 1 / 4096 - (m : ℝ) := (abs_le.mp hm2).1
      linarith
    -- apply the chain cover
    have hcov := acCov k Rr δ hRr hδnn hRrpos hgap hbud u hu (cx nx ny) ls (cx Ex Ey) θE
      hpne hθ hchP hgeom hkk
    intro t ht
    have hs1 : (0 : ℝ) ≤ t - (j : ℝ) / 4096 := by linarith [ht.1]
    have hs2 : t - (j : ℝ) / 4096 ≤ 1 / 4096 := by
      have h2 := ht.2
      rw [show (((j : ℝ) + 1) / 4096) = (j : ℝ) / 4096 + 1 / 4096 by ring] at h2
      linarith
    have hsU : θE - δ ≤ t - (j : ℝ) / 4096 := by
      have h1 : θE ≤ δ := by rw [hθEdef]; exact hθ_le
      linarith
    have hsO : t - (j : ℝ) / 4096 ≤ θE + acTot (cx Ex Ey) ls + δ := by linarith
    obtain ⟨l, hl, hlc⟩ := hcov (t - (j : ℝ) / 4096) ⟨hsU, hsO⟩
    rw [hls] at hl
    refine ⟨l, hl, ?_⟩
    have heq : Rr * rot t - leafC l
        = rot ((j : ℝ) / 4096) * (Rr * rot (t - (j : ℝ) / 4096) - u * leafC l) := by
      have hrt : rot t = rot ((j : ℝ) / 4096) * rot (t - (j : ℝ) / 4096) := by
        conv_lhs => rw [show t = (j : ℝ) / 4096 + (t - (j : ℝ) / 4096) by ring]
        rw [ac_rot_add]
      have h1 : rot ((j : ℝ) / 4096) * star (rot ((j : ℝ) / 4096)) = 1 :=
        ac_unit_self_mul_star (ac_norm_rot _)
      have h2 : Rr * rot t = rot ((j : ℝ) / 4096) * (Rr * rot (t - (j : ℝ) / 4096)) := by
        rw [hrt]; ring
      have h3 : leafC l = rot ((j : ℝ) / 4096) * (star (rot ((j : ℝ) / 4096)) * leafC l) := by
        rw [← mul_assoc, h1, one_mul]
      calc Rr * rot t - leafC l
          = rot ((j : ℝ) / 4096) * (Rr * rot (t - (j : ℝ) / 4096)) - leafC l := by rw [h2]
        _ = rot ((j : ℝ) / 4096) * (Rr * rot (t - (j : ℝ) / 4096))
              - rot ((j : ℝ) / 4096) * (star (rot ((j : ℝ) / 4096)) * leafC l) := by
              nth_rewrite 1 [h3]
              rfl
        _ = rot ((j : ℝ) / 4096) * (Rr * rot (t - (j : ℝ) / 4096) - u * leafC l) := by
              rw [hudef]; ring
    rw [heq, norm_mul, ac_norm_rot, one_mul]
    exact hlc

end Work.Cert
