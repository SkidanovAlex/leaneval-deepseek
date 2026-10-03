/-
# `Submission.Work.FIArea6T.Support` — the elementary pair facts behind the Schur bound (T2)

The L² Schur bound `Work.FIArea6T.TcutBil_le_polar` for the (10.13) form rests on four elementary
facts about a pair `(z₁,z₂)` of the polar box (5.14):

* `polar_absDelta_le`: `|Δ(z₁,z₂)| ≤ 4πθN` (the sector form of (6.2));
* `polar_fibre_card`: the fibre `{z₂ ∈ boxN : Δ(z₁,z₂) = m}` of a squarefree-norm polar point has
  at most three elements (the fibre bound of `fibre_bound`);
* `logFac6_abs_le`: `|log(8|z₁z₂|/|Δ|)| ≤ 4 log(2+N)` for `|z₁|², |z₂|² ≤ 2N`;
* `ratioSym_abs_le_one`: `|(z₂/z₁|d)| ≤ 1`.

These are copies of the corresponding results of `Submission/Work/FIArea6/` (which live in modules
of the round-6 route that are *not* in the τ-removal's import closure), restated here so that the
τ-removal lane depends only on built modules.  The proofs are the same.
-/
import Mathlib
import Submission.Work.FIArea6.fiber_card_le
import Submission.Work.FIArea6.UcutMod_pair_bound
import Submission.Work.FIArea4.absDelta_le_sector
import Submission.Work.FIArea6T.Defs

set_option autoImplicit false

namespace Work.FIArea6T

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The ratio symbol `(z₂/z₁|d)` is a Jacobi symbol, hence `≤ 1` in absolute value. -/
lemma ratioSym_abs_le_one (z1 z2 : GaussianInt) (d : ℕ) :
    |(Work.FIArea7.ratioSym z1 z2 d : ℝ)| ≤ 1 := by
  rw [Work.FIArea7.ratioSym, ← Int.cast_abs]
  exact_mod_cast (Work.FIArea6.abs_jacobiSym_le_one _ d)

/-- **The sector bound**: two points of the polar box (5.14) have `|Δ(z₁,z₂)| ≤ 4πθN`. -/
theorem polar_absDelta_le (Pa : Work.FITop.Params) (φ : ℝ) {z1 z2 : GaussianInt}
    (h1 : Work.FITop4.InPolarBox Pa φ z1) (h2 : Work.FITop4.InPolarBox Pa φ z2) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := by
  have hsec := Work.FIArea4.absDelta_le_sector Pa φ h1 h2
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := le_trans zero_le_one hN1
  have hθn : (0 : ℝ) ≤ Pa.θ := Pa.hθ0.le
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea6.theta_le_one Pa
  have hg1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h1.2.2.1
  have hg2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h2.2.2.1
  have hgn2 : (0 : ℝ) ≤ ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ (1 + Pa.θ) * Pa.N := mul_nonneg (by linarith) hN0
  have hsq : Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)
      * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul, ← Work.FIArea6.gnorm_mulU]
    have hle : ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ≤ ((1 + Pa.θ) * Pa.N) ^ 2 := by
      rw [Work.FIArea6.gnorm_mulU, Nat.cast_mul, pow_two]
      exact mul_le_mul hg1 hg2 hgn2 hM0
    calc Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        ≤ Real.sqrt (((1 + Pa.θ) * Pa.N) ^ 2) := Real.sqrt_le_sqrt hle
      _ = (1 + Pa.θ) * Pa.N := Real.sqrt_sq hM0
  have h2π : 0 ≤ 2 * Real.pi * Pa.θ :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hθn
  have h2πN : 0 ≤ 2 * Real.pi * Pa.θ * Pa.N := mul_nonneg h2π hN0
  calc ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ 2 * Real.pi * Pa.θ * Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)
          * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := hsec
    _ = 2 * Real.pi * Pa.θ * (Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)
          * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by ring
    _ ≤ 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) := mul_le_mul_of_nonneg_left hsq h2π
    _ ≤ 4 * Real.pi * Pa.θ * Pa.N := by
        have h1θ : (1 + Pa.θ) ≤ 2 := by linarith
        calc 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N)
            = (2 * Real.pi * Pa.θ * Pa.N) * (1 + Pa.θ) := by ring
          _ ≤ (2 * Real.pi * Pa.θ * Pa.N) * 2 := mul_le_mul_of_nonneg_left h1θ h2πN
          _ = 4 * Real.pi * Pa.θ * Pa.N := by ring

/-- **The fibre bound of the polar box**: for a polar `z₁` with squarefree norm, each value of
`Δ(z₁,·)` is taken at most three times on the box `boxN Pa`. -/
theorem polar_fibre_card (Pa : Work.FITop.Params) (φ : ℝ) {z1 : GaussianInt}
    (h1 : Work.FITop4.InPolarBox Pa φ z1) (hsf : Squarefree (Work.FIPlan.gnorm z1)) (m : ℤ) :
    (((Work.FITop.boxN Pa).filter (fun z2 => Work.FITop4.InPolarBox Pa φ z2 ∧
        Work.FIPlan.Delta z1 z2 = m)).card : ℝ) ≤ 3 := by
  set S := (Work.FITop.boxN Pa).filter (fun z2 => Work.FITop4.InPolarBox Pa φ z2 ∧
      Work.FIPlan.Delta z1 z2 = m) with hSdef
  rcases S.eq_empty_or_nonempty with hS | hSne
  · rw [hS]; simp
  · obtain ⟨z0, hz0S⟩ := hSne
    have hz0delta : Work.FIPlan.Delta z1 z0 = m := (Finset.mem_filter.mp hz0S).2.2
    have hcop : IsCoprime z1.re z1.im := Work.FIArea6.isCoprime_re_im_of_squarefree hsf
    have hre1 : z1.re ≠ 0 := by
      have hodd : Odd z1.re := h1.1.1
      intro h0
      obtain ⟨k, hk⟩ := hodd
      omega
    let P : GaussianInt → Prop := fun z2 => ∃ t : ℤ, z2 = z0 + (t : GaussianInt) * z1
    let tfun : GaussianInt → ℤ := fun z2 => if h : P z2 then h.choose else 0
    have hP : ∀ z2 ∈ S, z2 = z0 + (tfun z2 : GaussianInt) * z1 := by
      intro z2 hz2
      have hz2d : Work.FIPlan.Delta z1 z2 = m := (Finset.mem_filter.mp hz2).2.2
      have hd : Work.FIPlan.Delta z1 (z2 - z0) = 0 := by
        rw [Work.FIArea6.delta_eq] at hz2d hz0delta ⊢
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
        linarith
      have hPz : P z2 := by
        obtain ⟨t, ht⟩ := Work.FIArea6.eq_mul_of_delta_eq_zero hre1 hcop hd
        exact ⟨t, by rw [← ht]; abel⟩
      have htfun : tfun z2 = hPz.choose := by
        simp only [tfun]
        rw [dif_pos hPz]
      rw [htfun]
      exact hPz.choose_spec
    have hinj : Set.InjOn tfun ↑S := by
      intro z2 hz2 z2' hz2' heq
      rw [Finset.mem_coe] at hz2 hz2'
      rw [hP z2 hz2, hP z2' hz2', heq]
    have hmap : Set.MapsTo tfun ↑S ↑(S.image tfun) := by
      intro z2 hz2
      rw [Finset.mem_coe] at hz2
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨z2, hz2, rfl⟩)
    have hcard_le : S.card ≤ (S.image tfun).card :=
      Finset.card_le_card_of_injOn tfun hmap hinj
    have hn1 : Pa.N < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := h1.2.1
    have hT : (S.image tfun).card ≤ 3 := by
      refine Work.FIArea6.card_le_three_of_pairwise ?_
      intro a ha b hb
      rw [Finset.mem_image] at ha hb
      obtain ⟨z2, hz2S, rfl⟩ := ha
      obtain ⟨z2', hz2'S, rfl⟩ := hb
      have hbox2 : Work.FITop4.InPolarBox Pa φ z2 := (Finset.mem_filter.mp hz2S).2.1
      have hbox2' : Work.FITop4.InPolarBox Pa φ z2' := (Finset.mem_filter.mp hz2'S).2.1
      have hn2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := hbox2.2.2.1
      have hn2' : ((Work.FIPlan.gnorm z2' : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := hbox2'.2.2.1
      refine Work.FIArea6.sq_sub_le_seven_of_quad (c := (Work.FIPlan.gnorm z1 : ℝ))
        (e := ((z1.re * z0.re + z1.im * z0.im : ℤ) : ℝ))
        (f := (Work.FIPlan.gnorm z0 : ℝ)) (B := (1 + Pa.θ) * Pa.N) ?_ ?_ ?_ ?_ ?_
      · have hNpos : (0 : ℝ) < Pa.N := by
          have : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
          linarith
        linarith
      · rw [Work.FIArea6.cf_sub_e_sq z1 z0]; positivity
      · have hθ := Work.FIArea6.theta_le_one Pa
        have hNnn : (0 : ℝ) ≤ Pa.N := by
          have : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
          linarith
        have h2N : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by nlinarith [hθ, hNnn]
        have hgt : 2 * Pa.N < 2 * (Work.FIPlan.gnorm z1 : ℝ) := by linarith
        linarith
      · have hgn : (Work.FIPlan.gnorm z2 : ℝ)
            = (Work.FIPlan.gnorm (z0 + (tfun z2 : GaussianInt) * z1) : ℝ) :=
          congrArg (fun w => (Work.FIPlan.gnorm w : ℝ)) (hP z2 hz2S)
        have hq : (Work.FIPlan.gnorm z2 : ℝ)
            = (Work.FIPlan.gnorm z1 : ℝ) * (tfun z2 : ℝ) ^ 2
              + 2 * ((z1.re * z0.re + z1.im * z0.im : ℤ) : ℝ) * (tfun z2 : ℝ)
              + (Work.FIPlan.gnorm z0 : ℝ) := hgn.trans (Work.FIArea6.quad_norm z1 z0 (tfun z2))
        rw [← hq]
        exact hn2
      · have hgn : (Work.FIPlan.gnorm z2' : ℝ)
            = (Work.FIPlan.gnorm (z0 + (tfun z2' : GaussianInt) * z1) : ℝ) :=
          congrArg (fun w => (Work.FIPlan.gnorm w : ℝ)) (hP z2' hz2'S)
        have hq : (Work.FIPlan.gnorm z2' : ℝ)
            = (Work.FIPlan.gnorm z1 : ℝ) * (tfun z2' : ℝ) ^ 2
              + 2 * ((z1.re * z0.re + z1.im * z0.im : ℤ) : ℝ) * (tfun z2' : ℝ)
              + (Work.FIPlan.gnorm z0 : ℝ) := hgn.trans (Work.FIArea6.quad_norm z1 z0 (tfun z2'))
        rw [← hq]
        exact hn2'
    exact_mod_cast le_trans hcard_le hT

/-- **(7.10) on the support of a round-6 coefficient**: `|logFac6 z₁ z₂| ≤ 4 log(2+N)` whenever
`|z₁|², |z₂|² ≤ 2N`. -/
lemma logFac6_abs_le (Pa : Work.FITop.Params) {z1 z2 : GaussianInt} (hN : 1 ≤ Pa.N)
    (hn1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ 2 * Pa.N)
    (hn2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ 2 * Pa.N) :
    |Work.FITop4.logFac6 z1 z2| ≤ 4 * Real.log (2 + Pa.N) := by
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast hN
  rcases Nat.eq_zero_or_pos (Work.FIPlan.absDelta z1 z2) with h0 | hpos
  · have hz : Work.FITop4.logFac6 z1 z2 = 0 := by
      unfold Work.FITop4.logFac6
      rw [h0]; simp
    rw [hz, abs_zero]
    have : 0 ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith)
    linarith
  · have hΔ1 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hΔpos : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by linarith
    have hsqrt : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
        ≤ Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) :=
      Work.FIArea6.absDelta_le_sqrt_gnormU z1 z2
    have hgn2 : Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ≤ 2 * Pa.N :=
      Work.FIArea6.sqrt_gnorm_mul_leU Pa.N hN1 z1 z2 hn1 hn2
    have harg_ge : 8 ≤ 8 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hΔpos]
      nlinarith [hsqrt]
    have harg_le : 8 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 16 * Pa.N := by
      rw [div_le_iff₀ hΔpos]
      nlinarith [hsqrt, hgn2, hΔ1]
    have hargpos : 0 < 8 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
        / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by linarith
    rw [show Work.FITop4.logFac6 z1 z2
        = Real.log (8 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
            / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) from rfl,
      abs_of_nonneg (Real.log_nonneg (by linarith))]
    calc Real.log (8 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
          / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ≤ Real.log (16 * Pa.N) :=
          Real.log_le_log hargpos harg_le
      _ ≤ 4 * Real.log (2 + Pa.N) := by
          have h16 : (16 : ℝ) * Pa.N ≤ (2 + Pa.N) ^ 4 := by
            have h3 : (3 : ℝ) ≤ 2 + Pa.N := by linarith
            have h27 : (27 : ℝ) ≤ (2 + Pa.N) ^ 3 := by
              have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3 3
              norm_num at this ⊢
              exact this
            calc (16 : ℝ) * Pa.N ≤ 16 * (2 + Pa.N) := by linarith
              _ ≤ (2 + Pa.N) ^ 3 * (2 + Pa.N) := by
                  exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
              _ = (2 + Pa.N) ^ 4 := by ring
          calc Real.log (16 * Pa.N) ≤ Real.log ((2 + Pa.N) ^ 4) :=
                Real.log_le_log (by linarith) h16
            _ = 4 * Real.log (2 + Pa.N) := by rw [Real.log_pow]; norm_num

end

end Work.FIArea6T
