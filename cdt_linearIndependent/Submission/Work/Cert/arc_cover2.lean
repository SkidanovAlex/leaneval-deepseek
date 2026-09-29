import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.arc_cover

/-! # Arc cover on the 1024-grid (soundness of the v4 conjunct-2 arc certificate)

Copy-edit of `Submission/Work/Cert/arc_cover.lean` (`ArcCover`, 4096-grid).  Every geometric helper
there (`acLeafStep`, `acCov`, `ac_rot_acTot`, the absolute-unit budgets, ...) is grid-independent and
is reused by import; only the endpoint parametrisation `j/4096 -> j/NARC2` changes.  The one
genuinely new numeric input is `1/NARC2 <= 1/8` (`NARC2 = 1024`), which lets the end-angle rounding
argument go through with the four-times-longer arc. -/

namespace Work.Cert

open Complex Submission.CDTPlan
open scoped ComplexConjugate

theorem ac_NARC2_cast : ((NARC2 : ℝ)) = 1024 := by norm_num [NARC2]

theorem ac_NARC2_inv_le : (1 : ℝ) / (NARC2 : ℝ) ≤ 1 / 8 := by
  rw [ac_NARC2_cast]; norm_num

theorem arc_cover2 : ArcCover2 := by
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
  set u : ℂ := star (rot ((j : ℝ) / (NARC2 : ℝ))) with hudef
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
      have h1 : u * (Rr * rot ((j : ℝ) / (NARC2 : ℝ))) = Rr := by
        rw [hudef]
        calc star (rot ((j : ℝ) / (NARC2 : ℝ))) * (Rr * rot ((j : ℝ) / (NARC2 : ℝ)))
            = Rr * (star (rot ((j : ℝ) / (NARC2 : ℝ))) * rot ((j : ℝ) / (NARC2 : ℝ))) := by ring
          _ = Rr := by rw [ac_unit_self_star_mul (ac_norm_rot _), mul_one]
      have he : u * cx Ex Ey - Rr = u * (cx Ex Ey - Rr * rot ((j : ℝ) / (NARC2 : ℝ))) := by
        rw [mul_sub, h1]
      rw [he, norm_mul, hu, one_mul]
      exact hE
    have huN : ‖u * cx nx ny - Rr * rot (1 / (NARC2 : ℝ))‖ ≤ 65536 / (S : ℝ) := by
      have h1 : u * (Rr * rot (((j : ℝ) + 1) / (NARC2 : ℝ))) = Rr * rot (1 / (NARC2 : ℝ)) := by
        rw [hudef]
        rw [show ((j : ℝ) + 1) / (NARC2 : ℝ) = (j : ℝ) / (NARC2 : ℝ) + 1 / (NARC2 : ℝ) by ring, ac_rot_add]
        calc star (rot ((j : ℝ) / (NARC2 : ℝ))) * (Rr * (rot ((j : ℝ) / (NARC2 : ℝ)) * rot (1 / (NARC2 : ℝ))))
            = Rr * ((star (rot ((j : ℝ) / (NARC2 : ℝ))) * rot ((j : ℝ) / (NARC2 : ℝ))) * rot (1 / (NARC2 : ℝ))) := by
              ring
          _ = Rr * rot (1 / (NARC2 : ℝ)) := by
              rw [ac_unit_self_star_mul (ac_norm_rot _), one_mul]
      have he : u * cx nx ny - Rr * rot (1 / (NARC2 : ℝ))
          = u * (cx nx ny - Rr * rot (((j : ℝ) + 1) / (NARC2 : ℝ))) := by
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
    set w : ℂ := cx nx ny * star (rot (1 / (NARC2 : ℝ))) with hwdef
    have hw2 : ‖u * w - Rr‖ ≤ 65536 / (S : ℝ) := by
      have h1 : star (rot (1 / (NARC2 : ℝ))) * (Rr * rot (1 / (NARC2 : ℝ))) = Rr := by
        calc star (rot (1 / (NARC2 : ℝ))) * (Rr * rot (1 / (NARC2 : ℝ)))
            = Rr * (star (rot (1 / (NARC2 : ℝ))) * rot (1 / (NARC2 : ℝ))) := by ring
          _ = Rr := by rw [ac_unit_self_star_mul (ac_norm_rot _), mul_one]
      have he : u * w - Rr = star (rot (1 / (NARC2 : ℝ))) * (u * cx nx ny - Rr * rot (1 / (NARC2 : ℝ))) := by
        rw [hwdef]
        rw [show star (rot (1 / (NARC2 : ℝ))) * (u * cx nx ny - Rr * rot (1 / (NARC2 : ℝ)))
            = star (rot (1 / (NARC2 : ℝ))) * u * cx nx ny
              - star (rot (1 / (NARC2 : ℝ))) * (Rr * rot (1 / (NARC2 : ℝ))) by ring]
        rw [h1]
        ring
      rw [he, norm_mul, norm_star, ac_norm_rot, one_mul]
      exact huN
    have hNnorm : (((‖cx nx ny‖ : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hN_ne)
    have hrot_w : rot (θE + acTot (cx Ex Ey) ls - 1 / (NARC2 : ℝ)) = (u * w) / ‖u * w‖ := by
      have hnorm : ‖u * w‖ = ‖cx nx ny‖ := by
        rw [hwdef]
        simp only [norm_mul, norm_star, ac_norm_rot, hu, one_mul, mul_one]
      calc rot (θE + acTot (cx Ex Ey) ls - 1 / (NARC2 : ℝ))
          = rot (θE + acTot (cx Ex Ey) ls) * star (rot (1 / (NARC2 : ℝ))) := by rw [ac_rot_sub]
        _ = u * (cx nx ny / ‖cx nx ny‖) * star (rot (1 / (NARC2 : ℝ))) := by rw [hrot_end]
        _ = (u * w) / ‖u * w‖ := by
            rw [hnorm, hwdef]
            field_simp <;> ring
    have hwle : ‖rot (θE + acTot (cx Ex Ey) ls - 1 / (NARC2 : ℝ)) - 1‖ ≤ 4 * (65536 / (S : ℝ)) / Rr :=
      ac_rot_sub_one_le hRrpos (by positivity) hw2 hB hrot_w
    -- the end angle bound
    set θend : ℝ := θE + acTot (cx Ex Ey) ls with hθenddef
    have hsin_end : 2 * |Real.sin (Real.pi * (θend - 1 / (NARC2 : ℝ)))| ≤ 4 * (65536 / (S : ℝ)) / Rr := by
      have h2 := ACTrig.rot_chord (θend - 1 / (NARC2 : ℝ)) 0
      rw [sub_zero, show rot (0 : ℝ) = 1 from by simp [rot]] at h2
      rw [← h2]
      rw [hθenddef]
      exact hwle
    have hxt : -(1 : ℝ) / 2 ≤ θend := by
      rw [hθenddef, hθEdef]
      have h2 : |acAng (u * cx Ex Ey)| ≤ 1 / 2 := hθabs
      linarith [abs_le.mp h2, htend_nn]
    obtain ⟨m, hm⟩ := ACTrig.sin_pi_round (θend - 1 / (NARC2 : ℝ))
    have hm2 : |θend - 1 / (NARC2 : ℝ) - (m : ℝ)| ≤ δ := by
      have h2 : |Real.sin (Real.pi * (θend - 1 / (NARC2 : ℝ)))| ≤ 2 * (65536 / (S : ℝ)) / Rr := by
        have hrel : 4 * (65536 / (S : ℝ)) / Rr = 2 * (2 * (65536 / (S : ℝ)) / Rr) := by ring
        linarith [hsin_end, hrel]
      have h3 : (2 * (65536 / (S : ℝ)) / Rr) / 2 = 65536 / ((S : ℝ) * Rr) := by
        field_simp <;> ring
      linarith [hm, h3, hε]
    have hθend_ge : 1 / (NARC2 : ℝ) - δ ≤ θend := by
      have h1 : θend - 1 / (NARC2 : ℝ) - (m : ℝ) ≤ δ := (abs_le.mp hm2).2
      have h3 : -(1 : ℝ) / 2 - 1 / (NARC2 : ℝ) - δ > -1 := by
        linarith [hδ18, ac_NARC2_inv_le]
      have hlow : -(1 : ℝ) / 2 - 1 / (NARC2 : ℝ) - δ ≤ θend - 1 / (NARC2 : ℝ) - δ := by linarith [hxt]
      have h4 : (-1 : ℝ) < (m : ℝ) := by linarith [h1, h3, hlow]
      have h5 : (-1 : ℤ) < m := by exact_mod_cast h4
      have h6 : (0 : ℤ) ≤ m := by omega
      have h7 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h6
      have h8 : -(δ) ≤ θend - 1 / (NARC2 : ℝ) - (m : ℝ) := (abs_le.mp hm2).1
      linarith
    -- apply the chain cover
    have hcov := acCov k Rr δ hRr hδnn hRrpos hgap hbud u hu (cx nx ny) ls (cx Ex Ey) θE
      hpne hθ hchP hgeom hkk
    intro t ht
    have hs1 : (0 : ℝ) ≤ t - (j : ℝ) / (NARC2 : ℝ) := by linarith [ht.1]
    have hs2 : t - (j : ℝ) / (NARC2 : ℝ) ≤ 1 / (NARC2 : ℝ) := by
      have h2 := ht.2
      rw [show (((j : ℝ) + 1) / (NARC2 : ℝ)) = (j : ℝ) / (NARC2 : ℝ) + 1 / (NARC2 : ℝ) by ring] at h2
      linarith
    have hsU : θE - δ ≤ t - (j : ℝ) / (NARC2 : ℝ) := by
      have h1 : θE ≤ δ := by rw [hθEdef]; exact hθ_le
      linarith
    have hsO : t - (j : ℝ) / (NARC2 : ℝ) ≤ θE + acTot (cx Ex Ey) ls + δ := by linarith
    obtain ⟨l, hl, hlc⟩ := hcov (t - (j : ℝ) / (NARC2 : ℝ)) ⟨hsU, hsO⟩
    rw [hls] at hl
    refine ⟨l, hl, ?_⟩
    have heq : Rr * rot t - leafC l
        = rot ((j : ℝ) / (NARC2 : ℝ)) * (Rr * rot (t - (j : ℝ) / (NARC2 : ℝ)) - u * leafC l) := by
      have hrt : rot t = rot ((j : ℝ) / (NARC2 : ℝ)) * rot (t - (j : ℝ) / (NARC2 : ℝ)) := by
        conv_lhs => rw [show t = (j : ℝ) / (NARC2 : ℝ) + (t - (j : ℝ) / (NARC2 : ℝ)) by ring]
        rw [ac_rot_add]
      have h1 : rot ((j : ℝ) / (NARC2 : ℝ)) * star (rot ((j : ℝ) / (NARC2 : ℝ))) = 1 :=
        ac_unit_self_mul_star (ac_norm_rot _)
      have h2 : Rr * rot t = rot ((j : ℝ) / (NARC2 : ℝ)) * (Rr * rot (t - (j : ℝ) / (NARC2 : ℝ))) := by
        rw [hrt]; ring
      have h3 : leafC l = rot ((j : ℝ) / (NARC2 : ℝ)) * (star (rot ((j : ℝ) / (NARC2 : ℝ))) * leafC l) := by
        rw [← mul_assoc, h1, one_mul]
      calc Rr * rot t - leafC l
          = rot ((j : ℝ) / (NARC2 : ℝ)) * (Rr * rot (t - (j : ℝ) / (NARC2 : ℝ))) - leafC l := by rw [h2]
        _ = rot ((j : ℝ) / (NARC2 : ℝ)) * (Rr * rot (t - (j : ℝ) / (NARC2 : ℝ)))
              - rot ((j : ℝ) / (NARC2 : ℝ)) * (star (rot ((j : ℝ) / (NARC2 : ℝ))) * leafC l) := by
              nth_rewrite 1 [h3]
              rfl
        _ = rot ((j : ℝ) / (NARC2 : ℝ)) * (Rr * rot (t - (j : ℝ) / (NARC2 : ℝ)) - u * leafC l) := by
              rw [hudef]; ring
    rw [heq, norm_mul, ac_norm_rot, one_mul]
    exact hlc

end Work.Cert
