import Mathlib
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.germC_apply_ne
import Submission.Work.EQ.germPt_of_real

/-! ## The real/complex bridge for the germ

This file connects the complexified algebra of `HeteroAlgebra` with the real half map `eqU` and
the real germ `germPt` of `Defs.lean`, determines which backward branch stays in the upper half
plane, and records the explicit formulas for the two backward branches. -/

namespace Work.EQ
open Complex Filter _root_.Topology
noncomputable section

theorem bsq_ofReal (x y : ℝ) : bsq (((x : ℂ)), ((y : ℂ))) = ((x ^ 2 + y ^ 2 : ℝ) : ℂ) := by
  simp only [bsq]; push_cast; ring

theorem brho_ofReal (x y : ℝ) :
    brho (((x : ℂ)), ((y : ℂ))) = ((Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) := by
  rw [brho, bsq_ofReal, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ x ^ 2 + y ^ 2)]
  congr 1
  exact (Real.sqrt_eq_rpow _).symm

theorem subO1_Rpt (a : ℝ) (z : ℂ) :
    subO1 a (Rpt z) = (((z.re + a / 2 : ℝ) : ℂ), ((z.im : ℝ) : ℂ)) := by
  simp only [subO1, Rpt]
  rw [show ((z.re : ℂ) + (((a / 2 : ℝ)) : ℂ)) = (((z.re + a / 2 : ℝ)) : ℂ) from by push_cast; ring]

theorem subO2_Rpt (a : ℝ) (z : ℂ) :
    subO2 a (Rpt z) = (((z.re - a / 2 : ℝ) : ℂ), ((z.im : ℝ) : ℂ)) := by
  simp only [subO2, Rpt]
  rw [show ((z.re : ℂ) - (((a / 2 : ℝ)) : ℂ)) = (((z.re - a / 2 : ℝ)) : ℂ) from by push_cast; ring]

theorem brho_subO1_Rpt (a : ℝ) (z : ℂ) :
    brho (subO1 a (Rpt z)) = ((Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) : ℝ) : ℂ) := by
  rw [subO1_Rpt, brho_ofReal]

theorem brho_subO2_Rpt (a : ℝ) (z : ℂ) :
    brho (subO2 a (Rpt z)) = ((‖z - (((a / 2 : ℝ)) : ℂ)‖ : ℝ) : ℂ) := by
  rw [subO2_Rpt, brho_ofReal]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  congr 1
  ring

theorem Rpt_eqU (a : ℝ) (z : ℂ) : Rpt (eqU a z) = fwdC a (Rpt z) := by
  have hρ := brho_subO2_Rpt a z
  ext
  · rw [Rpt_fst, fwdC, hρ, eqU]
    simp only [Prod.fst, Rpt, Complex.add_re, Complex.neg_re, Complex.div_ofReal_re,
      Complex.sub_re, Complex.ofReal_re]
    push_cast
    ring
  · rw [Rpt_snd, fwdC, hρ, eqU]
    simp only [Prod.snd, Rpt, Complex.add_im, Complex.neg_im, Complex.div_ofReal_im,
      Complex.sub_im, Complex.ofReal_im]
    push_cast
    ring

theorem invBranch_snd (a : ℝ) (s : Bool) (Q : ℂ × ℂ) :
    (invBranch a s Q).2
      = -Q.2 + (if s then (1 : ℂ) else -1) * Q.2 / brho (subO1 a Q) := by
  rw [invBranch]
  simp only [subO1, brho, bsq, Prod.snd]

theorem invBranch_true_snd (a : ℝ) (Q : ℂ × ℂ) :
    (invBranch a true Q).2 = -Q.2 + Q.2 / brho (subO1 a Q) := by
  rw [invBranch_snd a true Q]
  simp

theorem invBranch_false_snd (a : ℝ) (Q : ℂ × ℂ) :
    (invBranch a false Q).2 = -Q.2 - Q.2 / brho (subO1 a Q) := by
  rw [invBranch_snd a false Q]
  simp [sub_eq_add_neg, neg_div]

theorem eqRelC_preimage_upper {a : ℝ} {P : ℂ × ℂ} {z : ℂ} (hz : 0 < z.im)
    (h1 : P.1.im = 0) (h2 : P.2.im = 0) (hP : 0 < P.2.re) (h : EqRelC a P (Rpt z)) :
    P = invBranch a true (Rpt z) ∧ ‖z + (((a / 2 : ℝ)) : ℂ)‖ < 1 := by
  have hzre : (0 : ℝ) < (z.re + a / 2) ^ 2 + z.im ^ 2 := by positivity
  have hb : bsq (subO1 a (Rpt z)) ≠ 0 := by
    rw [subO1_Rpt, bsq_ofReal]
    exact_mod_cast (ne_of_gt hzre)
  have hρ := brho_subO1_Rpt a z
  have hρpos : (0 : ℝ) < Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) := Real.sqrt_pos.mpr hzre
  have hPn : P.2 = ((P.2.re : ℝ) : ℂ) := Complex.ext rfl (by simpa using h2)
  have hnorm : ‖z + (((a / 2 : ℝ)) : ℂ)‖ = Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    congr 1
    ring
  rcases eqRelC_solutions h hb with hP' | hP'
  · refine ⟨hP', ?_⟩
    have hval : ((-z.im + z.im / Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) : ℝ) : ℂ)
        = ((P.2.re : ℝ) : ℂ) := by
      have h2' : (invBranch a true (Rpt z)).2 = P.2 := by rw [hP']
      rw [← hPn, ← h2', invBranch_true_snd, hρ, Rpt_snd]
      push_cast
      ring
    have hlt : z.im < z.im / Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) := by
      have := Complex.ofReal_inj.mp hval
      linarith [hP]
    have h5 : Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) < 1 := by
      have h4 : z.im * Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) < z.im * 1 := by
        rw [lt_div_iff₀ hρpos] at hlt
        rw [mul_one]
        exact hlt
      have h6 : z.im * Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) / z.im < z.im * 1 / z.im :=
        div_lt_div_of_pos_right h4 hz
      rw [mul_div_cancel_left₀ _ hz.ne', mul_one, div_self hz.ne'] at h6
      exact h6
    rw [hnorm]; exact h5
  · exfalso
    have hval : ((-z.im - z.im / Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) : ℝ) : ℂ)
        = ((P.2.re : ℝ) : ℂ) := by
      have h2' : (invBranch a false (Rpt z)).2 = P.2 := by rw [hP']
      rw [← hPn, ← h2', invBranch_false_snd, hρ, Rpt_snd]
      push_cast
      ring
    have hz2 : (-z.im - z.im / Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) : ℝ) = P.2.re :=
      Complex.ofReal_inj.mp hval
    have : -z.im - z.im / Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) < 0 := by
      have : 0 < z.im / Real.sqrt ((z.re + a / 2) ^ 2 + z.im ^ 2) := div_pos hz hρpos
      linarith
    linarith

theorem fwdC_mirror (a : ℝ) (Q : ℂ × ℂ) :
    fwdC a (eqMirror Q) = eqMirror (invBranch a true Q) := by
  have hρ : brho (subO2 a (eqMirror Q)) = brho (subO1 a Q) := by
    rw [brho, brho]
    congr 1
    simp only [bsq, subO2, subO1, eqMirror, Prod.fst, Prod.snd]
    ring
  ext
  · rw [fwdC, hρ, invBranch]
    simp only [eqMirror, subO1, brho, bsq, Prod.fst, Prod.snd]
    norm_num <;> ring
  · rw [fwdC, hρ, invBranch]
    simp only [eqMirror, subO1, brho, bsq, Prod.fst, Prod.snd]
    norm_num <;> ring

theorem Rpt_neg_conj (z : ℂ) : Rpt (-(starRingEnd ℂ z)) = eqMirror (Rpt z) := by
  ext <;> simp [Rpt, eqMirror]

theorem germC_real {a : ℝ} {h : ℂ → ℂ} (h0 : h 0 = 0) {t : ℝ} (ht : t ≠ 0)
    (h1 : (h (t : ℂ)).im = 0) (h2 : (h ((eqLam a : ℂ) * (t : ℂ))).im = 0)
    (hden : h ((eqLam a : ℂ) * (t : ℂ)) ≠ h (t : ℂ)) :
    germC a h (t : ℂ) = Rpt (germPt a h t) := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  set β : ℝ := (h (t : ℂ)).re
  set γ : ℝ := (h ((eqLam a : ℂ) * (t : ℂ))).re
  have hβ : h (t : ℂ) = (β : ℂ) := Complex.ext rfl (by simpa [β] using h1)
  have hγ : h ((eqLam a : ℂ) * (t : ℂ)) = (γ : ℂ) := Complex.ext rfl (by simpa [γ] using h2)
  have hden' : γ - β ≠ 0 := by
    intro hc
    exact hden (by rw [hβ, hγ, sub_eq_zero.mp hc])
  rw [germC_apply_ne h0 htC, hβ, hγ,
    germPt_of_real (β := β) (γ := γ) (t := t) hβ hγ hden']
  refine Prod.ext ?_ ?_
  · simp only [Rpt, Prod.fst, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_I_re, neg_zero, add_zero]
    exact (show (a * (γ : ℂ) / ((γ : ℂ) - (β : ℂ)) - (((a / 2 : ℝ)) : ℂ))
        = (((a * γ / (γ - β) - a / 2 : ℝ)) : ℂ) from by push_cast; ring)
  · simp only [Rpt, Prod.snd, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, zero_add]
    exact (show (a * (β : ℂ) * (γ : ℂ) / ((γ : ℂ) - (β : ℂ)))
        = (((a * β * γ / (γ - β) : ℝ)) : ℂ) from by push_cast; ring)

end
end Work.EQ
