import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auTailDefs
import Submission.Work.Resample.auTailWin
import Submission.Work.Resample.tsum_int_block
import Submission.Work.Resample.auK_close
import Submission.Work.Resample.auM_ge
import Submission.Work.ResMath.summable_exp_neg_affine_sq

/-!
# The truncation error of the ideal resampling weights (paper Lemma 4.9, tail part)

`Work.Resample.auTail` bounds the difference between the finite windowed sum
`Σ_{i<L} auWi p α s t k i · u(auJ k i)` and the exact resampling entry
`(resA s t α).mulVec u k` by `2^{-p}`.

Both sides are `(2α)^{-1}` times a sum of the Gaussian summand
`auHf s α ζ u n = exp(−π(n−ζ)²/α²)·u(n mod s)` (`ζ = s·k/t`): the finite window
`{K−m, …, K+m}` on the left (`auTailWin`) and *all* of `ℤ` on the right
(`auTail_resA_tsum`).  The difference is therefore the two Gaussian tails of the window,
each bounded by `2·e^{−πp}` (`auTail_upper_tail`, `auTail_lower_tail`), which is
comfortably below `α·2^{-p}`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## Elementary estimates -/

/-- `e^{−πp} ≤ 2^{−p}`. -/
theorem auTail_exp_bound (p : ℕ) :
    Real.exp (-(Real.pi * (p : ℝ))) ≤ (2 : ℝ) ^ (-(p : ℤ)) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hlog2 : Real.log 2 ≤ Real.pi := by
    have h1 : Real.log 2 ≤ 1 :=
      (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith [Real.exp_one_gt_d9])
    linarith [Real.pi_gt_three]
  rw [zpow_neg, zpow_natCast, ← Real.exp_log (by norm_num : (0 : ℝ) < 2),
    ← Real.exp_nat_mul, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Summability of the Gaussian weight over `ℤ`. -/
theorem auTail_gauss_summable (α ζ : ℝ) (hα : 0 < α) : Summable (auGauss α ζ) := by
  have ha : 0 < Real.pi / α ^ 2 := by positivity
  have h := Work.ResMath.summable_exp_neg_affine_sq (Real.pi / α ^ 2) (-ζ) ha (t := 1)
    (by norm_num)
  refine h.congr fun n => ?_
  simp only [auGauss]
  congr 1
  push_cast
  ring

/-- Summability of the resampling summand `auHf` over `ℤ`. -/
theorem auTail_auHf_summable (s : ℕ) (hs : 0 < s) (α ζ : ℝ) (hα : 0 < α)
    (u : Fin s → ℂ) : Summable (auHf s hs α ζ u) := by
  refine Summable.of_norm_bounded (g := fun n : ℤ => ‖u‖ * auGauss α ζ n)
    ((auTail_gauss_summable α ζ hα).mul_left ‖u‖) fun n => ?_
  rw [auHf, norm_mul]
  have h1 : ‖((auGauss α ζ n : ℝ) : ℂ)‖ = auGauss α ζ n :=
    RCLike.norm_of_nonneg (auGauss_nonneg α ζ n)
  rw [h1, mul_comm ‖u‖]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u _) (auGauss_nonneg α ζ n)

/-- A constant identity: `(1/2)·(1/n) = 1/(2n)` for complex numbers. -/
theorem auTail_const_mul (n : ℕ) (hn : n ≠ 0) :
    (1 / 2 : ℂ) * (1 / (n : ℂ)) = (1 / (2 * (n : ℝ)) : ℂ) := by
  have h3 : (1 / (2 * (n : ℝ)) : ℂ) = ((1 / (2 * (n : ℝ)) : ℝ) : ℂ) := by
    first | simp | norm_cast | (push_cast; ring)
  have h1 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    first | simp | norm_cast | (push_cast; ring)
  have h2 : (1 / (n : ℂ)) = ((1 / (n : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n]
    first | simp | norm_cast | (push_cast; ring)
  rw [h1, h2, h3, ← Complex.ofReal_mul]
  congr 1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  first
  | (field_simp; ring)
  | field_simp
  | ring

/-- **The Gaussian tail over `ℕ`.**  If `c ≥ α√p` and `α² < p` then the Gaussian tail
`Σ_{j≥0} e^{−π(c+j)²/α²}` is at most `2 e^{−πp}` (comfortably below `α·2^{−p}`). -/
theorem auTail_gauss_nat_le (α : ℝ) (p : ℕ) (hα : 0 < α) (hp : 1 ≤ p) (hαp : α ^ 2 < p)
    (c : ℝ) (hc : α * Real.sqrt p ≤ c) :
    (∑' j : ℕ, Real.exp (-(Real.pi * (c + (j : ℝ)) ^ 2 / α ^ 2)))
      ≤ 2 * Real.exp (-(Real.pi * (p : ℝ))) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hα2 : (0 : ℝ) < α ^ 2 := pow_pos hα 2
  have hsp1 : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]; exact_mod_cast hp
  have hc0 : 0 < c := by
    have h1 : 0 < α * Real.sqrt p := mul_pos hα (lt_of_lt_of_le one_pos hsp1)
    linarith
  -- `p α² ≤ c²`
  have hc2 : (p : ℝ) * α ^ 2 ≤ c ^ 2 := by
    have h1 : (α * Real.sqrt p) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by positivity) hc 2
    have h2 : (α * Real.sqrt p) ^ 2 = (p : ℝ) * α ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hp0)]; ring
    linarith
  have hαlt : α < Real.sqrt p := by
    rw [Real.lt_sqrt hα.le]; exact hαp
  have hratio : (1 : ℝ) ≤ Real.sqrt p / α := by
    rw [le_div_iff₀ hα]; linarith
  have hlog2 : Real.log 2 ≤ 2 * Real.pi := by
    have h1 : Real.log 2 ≤ 1 :=
      (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith [Real.exp_one_gt_d9])
    linarith [Real.pi_gt_three]
  set ρ : ℝ := Real.exp (-(2 * Real.pi * c / α ^ 2)) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρhalf : ρ ≤ 1 / 2 := by
    have hstep1 : -(2 * Real.pi * c / α ^ 2) ≤ -(2 * Real.pi * Real.sqrt p / α) := by
      have h : 2 * Real.pi * Real.sqrt p / α ≤ 2 * Real.pi * c / α ^ 2 := by
        rw [div_le_div_iff₀ hα hα2]
        have h' : Real.sqrt p * α ^ 2 ≤ c * α := by nlinarith [hc, hα, Real.sqrt_nonneg p]
        have h'' : 2 * Real.pi * (Real.sqrt p * α ^ 2) ≤ 2 * Real.pi * (c * α) :=
          mul_le_mul_of_nonneg_left h' (by positivity)
        linarith
      linarith
    have hstep2 : Real.exp (-(2 * Real.pi * Real.sqrt p / α)) ≤ Real.exp (-(2 * Real.pi)) := by
      apply Real.exp_le_exp.mpr
      have h : (2 * Real.pi) * 1 ≤ (2 * Real.pi) * (Real.sqrt p / α) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      have h' : (2 * Real.pi) * (Real.sqrt p / α) = 2 * Real.pi * Real.sqrt p / α := by ring
      simp only [mul_one] at h
      linarith [h, h']
    have hstep3 : Real.exp (-(2 * Real.pi)) ≤ 1 / 2 := by
      have h2 : (2 : ℝ) ≤ Real.exp (2 * Real.pi) := by
        have hle : Real.exp 1 ≤ Real.exp (2 * Real.pi) :=
          Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
        linarith [Real.exp_one_gt_d9]
      rw [Real.exp_neg]
      have h := (inv_le_inv₀ (Real.exp_pos (2 * Real.pi)) (by norm_num : (0 : ℝ) < 2)).mpr h2
      simpa using h
    calc ρ = Real.exp (-(2 * Real.pi * c / α ^ 2)) := hρdef
      _ ≤ Real.exp (-(2 * Real.pi * Real.sqrt p / α)) := Real.exp_le_exp.mpr hstep1
      _ ≤ Real.exp (-(2 * Real.pi)) := hstep2
      _ ≤ 1 / 2 := hstep3
  have hρlt : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hρ0]
    linarith
  have hgeom0 : Summable (fun j : ℕ => ρ ^ j) :=
    (summable_geometric_iff_norm_lt_one (ξ := ρ)).mpr hρlt
  have hgeom : Summable (fun j : ℕ => Real.exp (-(Real.pi * c ^ 2 / α ^ 2)) * ρ ^ j) :=
    hgeom0.mul_left _
  have hterm : ∀ j : ℕ, Real.exp (-(Real.pi * (c + (j : ℝ)) ^ 2 / α ^ 2))
      ≤ Real.exp (-(Real.pi * c ^ 2 / α ^ 2)) * ρ ^ j := by
    intro j
    have hkey : -(Real.pi * (c + (j : ℝ)) ^ 2 / α ^ 2)
        = -(Real.pi * c ^ 2 / α ^ 2)
          + (-(Real.pi * ((j : ℝ) ^ 2 + 2 * c * (j : ℝ)) / α ^ 2)) := by ring
    rw [hkey, Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    rw [hρdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 : (j : ℝ) * -(2 * Real.pi * c / α ^ 2) = -(2 * Real.pi * c * (j : ℝ) / α ^ 2) := by
      ring
    have h2 : -(Real.pi * ((j : ℝ) ^ 2 + 2 * c * (j : ℝ)) / α ^ 2)
        = -(Real.pi * (j : ℝ) ^ 2 / α ^ 2) + -(2 * Real.pi * c * (j : ℝ) / α ^ 2) := by
      ring
    rw [h1, h2]
    have h3 : 0 ≤ Real.pi * (j : ℝ) ^ 2 / α ^ 2 := by positivity
    linarith
  have hsum : Summable (fun j : ℕ => Real.exp (-(Real.pi * (c + (j : ℝ)) ^ 2 / α ^ 2))) :=
    Summable.of_nonneg_of_le (fun j => Real.exp_nonneg _) hterm hgeom
  have hinv : (1 - ρ)⁻¹ ≤ 2 := by
    have h1 : (0 : ℝ) < 1 - ρ := by linarith
    rw [inv_le_iff_one_le_mul₀ h1]
    linarith
  have hexp : Real.exp (-(Real.pi * c ^ 2 / α ^ 2)) ≤ Real.exp (-(Real.pi * (p : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have h1 : Real.pi * (p : ℝ) ≤ Real.pi * c ^ 2 / α ^ 2 := by
      rw [le_div_iff₀ hα2]
      nlinarith [hc2, Real.pi_pos]
    linarith
  calc (∑' j : ℕ, Real.exp (-(Real.pi * (c + (j : ℝ)) ^ 2 / α ^ 2)))
      ≤ ∑' j : ℕ, Real.exp (-(Real.pi * c ^ 2 / α ^ 2)) * ρ ^ j :=
        Summable.tsum_le_tsum hterm hsum hgeom
    _ = Real.exp (-(Real.pi * c ^ 2 / α ^ 2)) * (1 - ρ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hρlt]
    _ ≤ Real.exp (-(Real.pi * (p : ℝ))) * 2 :=
        mul_le_mul hexp hinv
          (le_of_lt (inv_pos.mpr (by linarith [hρhalf] : (0 : ℝ) < 1 - ρ)))
          (Real.exp_nonneg _)
    _ = 2 * Real.exp (-(Real.pi * (p : ℝ))) := by ring

/-! ## The exact row of `resA` as a single `ℤ`-sum -/

/-- **Reindexing.**  The `k`-th entry of `(resA s t α).mulVec u` is `(2α)^{-1}` times the
single Gaussian sum `Σ_{n:ℤ} exp(−π(n−ζ)²/α²)·u(n mod s)`, `ζ = sk/t`. -/
theorem auTail_resA_tsum (s t α : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 0 < α)
    (u : Fin s → ℂ) (k : Fin t) :
    (HvdH.resA s t α).mulVec u k
      = (1 / (2 * (α : ℝ)) : ℂ) *
        ∑' n : ℤ, auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u n := by
  have hs0 : 0 < s := by omega
  have ht0 : 0 < t := by omega
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  have hαR : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  haveI : NeZero s := ⟨hs0.ne'⟩
  set e : Fin s × ℤ ≃ ℤ := (Equiv.prodComm (Fin s) ℤ).trans (Int.divModEquiv s).symm with he
  -- summability of the theta fibres
  have hfiber : ∀ j : Fin s,
      Summable (fun q : ℤ => ((auTailE s t α (k : ℕ) (j : ℕ) q : ℝ) : ℂ) * u j) := by
    intro j
    have ha : 0 < Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2 :=
      div_pos (mul_pos Real.pi_pos (pow_pos hsR 2)) (pow_pos hαR 2)
    have hreal : Summable (fun q : ℤ => auTailE s t α (k : ℕ) (j : ℕ) q) := by
      refine (Work.ResMath.summable_exp_neg_affine_sq (Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2)
        (-((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ))) ha (t := 1) (by norm_num)).congr
        (fun q => ?_)
      simp only [auTailE]
      congr 1
      ring
    exact ((Complex.summable_ofReal).mpr hreal).mul_right (u j)
  have hprod : Summable (fun p : Fin s × ℤ =>
      ‖((auTailE s t α (k : ℕ) (p.1 : ℕ) p.2 : ℝ) : ℂ) * u p.1‖) :=
    (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
      ⟨fun j => (hfiber j).norm, Summable.of_finite⟩
  have hsumm : Summable (fun p : Fin s × ℤ =>
      ((auTailE s t α (k : ℕ) (p.1 : ℕ) p.2 : ℝ) : ℂ) * u p.1) := hprod.of_norm
  -- the pointwise identification with `auHf`
  have heval : ∀ (j : Fin s) (q : ℤ), e (j, q) = (j : ℤ) + (s : ℤ) * q := by
    intro j q
    rw [he]
    simp only [Equiv.trans_apply, Equiv.prodComm_apply, Int.divModEquiv_symm_apply,
      Prod.fst_swap, Prod.snd_swap]
    ring
  have hkey : ∀ p : Fin s × ℤ, ((auTailE s t α (k : ℕ) (p.1 : ℕ) p.2 : ℝ) : ℂ) * u p.1
      = auHf s hs0 (α : ℝ) (auZeta s t (k : ℕ)) u (e p) := by
    rintro ⟨j, q⟩
    rw [heval j q, auHf, finMod_eq_of s hs0 j q]
    congr 1
    rw [auGauss, auTailE, auZeta, Complex.ofReal_inj]
    congr 1
    have hsne : (s : ℝ) ≠ 0 := ne_of_gt hsR
    have htne : (t : ℝ) ≠ 0 := ne_of_gt htR
    push_cast
    have hXY : (s : ℝ) ^ 2 * ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2
        = ((j : ℝ) + (s : ℝ) * (q : ℝ) - (s : ℝ) * (k : ℝ) / (t : ℝ)) ^ 2 := by
      have h1 : (s : ℝ) * ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ))
          = -((j : ℝ) + (s : ℝ) * (q : ℝ) - (s : ℝ) * (k : ℝ) / (t : ℝ)) := by
        field_simp
        ring
      have h2 : ((j : ℝ) + (s : ℝ) * (q : ℝ) - (s : ℝ) * (k : ℝ) / (t : ℝ))
          = -((s : ℝ) * ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ))) := by
        rw [h1]; ring
      rw [h2]
      ring
    rw [show -Real.pi * (s : ℝ) ^ 2 / (α : ℝ) ^ 2
          * ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2
        = -(Real.pi * ((s : ℝ) ^ 2
          * ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2) / (α : ℝ) ^ 2) by ring,
      hXY]
  -- the algebraic unfolding of one entry of `resA`
  have hstep : ∀ j : Fin s, HvdH.resSmat s t α k j =
      (1 / (α : ℂ)) * ∑' q : ℤ, (auTailE s t α (k : ℕ) (j : ℕ) q : ℂ) := by
    intro j
    rw [HvdH.resSmat, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_tsum]
    congr 1
  have hrow : (HvdH.resA s t α).mulVec u k
      = (1 / (2 * (α : ℝ)) : ℂ) * ∑ j : Fin s, ∑' q : ℤ,
          ((auTailE s t α (k : ℕ) (j : ℕ) q : ℝ) : ℂ) * u j := by
    simp only [Matrix.mulVec_apply, dotProduct]
    change (∑ j : Fin s, (HvdH.resA s t α) k j * u j)
      = (1 / (2 * (α : ℝ)) : ℂ) * ∑ j : Fin s, ∑' q : ℤ,
          ((auTailE s t α (k : ℕ) (j : ℕ) q : ℝ) : ℂ) * u j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hconst : (1 / 2 : ℂ) * (1 / (α : ℂ)) = (1 / (2 * (α : ℝ)) : ℂ) :=
      auTail_const_mul α hα.ne'
    rw [HvdH.resA, Matrix.smul_apply, smul_eq_mul, hstep j]
    rw [tsum_mul_right, ← mul_assoc, hconst, mul_assoc]
  calc (HvdH.resA s t α).mulVec u k
      = (1 / (2 * (α : ℝ)) : ℂ) * ∑ j : Fin s, ∑' q : ℤ,
          ((auTailE s t α (k : ℕ) (j : ℕ) q : ℝ) : ℂ) * u j := hrow
    _ = (1 / (2 * (α : ℝ)) : ℂ) * ∑' p : Fin s × ℤ,
          ((auTailE s t α (k : ℕ) (p.1 : ℕ) p.2 : ℝ) : ℂ) * u p.1 := by
        congr 1
        rw [← tsum_fintype (L := SummationFilter.unconditional (Fin s))
          (f := fun j : Fin s => ∑' q : ℤ,
          ((auTailE s t α (k : ℕ) (j : ℕ) q : ℝ) : ℂ) * u j)]
        exact (Summable.tsum_prod hsumm).symm
    _ = (1 / (2 * (α : ℝ)) : ℂ) * ∑' p : Fin s × ℤ,
          auHf s hs0 (α : ℝ) (auZeta s t (k : ℕ)) u (e p) := by
        congr 1
        exact tsum_congr hkey
    _ = (1 / (2 * (α : ℝ)) : ℂ) *
          ∑' n : ℤ, auHf s hs0 (α : ℝ) (auZeta s t (k : ℕ)) u n := by
        congr 1
        exact Equiv.tsum_eq e _

/-! ## The two Gaussian tails of the retained window -/

/-- Upper Gaussian tail of the retained window: the part of the `ℤ`-sum above the window
`{K−m, …, K+m}` is at most `2 e^{-πp}`. -/
theorem auTail_upper_tail (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
    (hα : 0 < α) (hp : 1 ≤ p) (hαp : α ^ 2 < p) (u : Fin s → ℂ) (hu : ‖u‖ ≤ 1)
    (k : Fin t)
    (hgaussTail : ∀ (c : ℝ), (α : ℝ) * Real.sqrt p ≤ c →
      (∑' j : ℕ, Real.exp (-(Real.pi * (c + (j : ℝ)) ^ 2 / (α : ℝ) ^ 2)))
        ≤ 2 * Real.exp (-(Real.pi * (p : ℝ)))) :
    ‖∑' j : ℕ, auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
        (auW0 p α s t (k : ℕ) + (auL p α : ℤ) + (j : ℤ))‖
      ≤ 2 * Real.exp (-(Real.pi * (p : ℝ))) := by
  have hα0 : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hinj : Function.Injective
      (fun j : ℕ => auW0 p α s t (k : ℕ) + (auL p α : ℤ) + (j : ℤ)) := by
    intro a b hab
    have h1 : ((a : ℤ)) = ((b : ℤ)) := add_left_cancel hab
    exact_mod_cast h1
  have hSummℤ : Summable (fun n : ℤ => auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u n) :=
    auTail_auHf_summable s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) hα0 u
  have hsumU : Summable (fun j : ℕ => auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
      (auW0 p α s t (k : ℕ) + (auL p α : ℤ) + (j : ℤ))) := hSummℤ.comp_injective hinj
  have hgaussℤ : Summable (fun n : ℤ => auGauss (α : ℝ) (auZeta s t (k : ℕ)) n) :=
    auTail_gauss_summable (α : ℝ) (auZeta s t (k : ℕ)) hα0
  have hgaussℕ : Summable (fun j : ℕ => auGauss (α : ℝ) (auZeta s t (k : ℕ))
      (auW0 p α s t (k : ℕ) + (auL p α : ℤ) + (j : ℤ))) := hgaussℤ.comp_injective hinj
  set cU : ℝ := (auL p α : ℝ) - (auZeta s t (k : ℕ) - (auW0 p α s t (k : ℕ) : ℝ)) with hcUdef
  have hcU : (α : ℝ) * Real.sqrt p ≤ cU := by
    rw [hcUdef]
    have h1 : (auL p α : ℝ) = 2 * (auM p α : ℝ) + 1 := by simp only [auL]; push_cast; ring
    have h2 : (auW0 p α s t (k : ℕ) : ℝ) = (auK s t (k : ℕ) : ℝ) - (auM p α : ℝ) := by
      simp only [auW0]; push_cast; ring
    have h3 : auZeta s t (k : ℕ) - (auK s t (k : ℕ) : ℝ) ≤ 1 / 2 := by
      have h := abs_le.mp (auK_close s t (k : ℕ) (by omega))
      linarith [h.2]
    have h4 := auM_ge p α
    linarith
  calc ‖∑' j : ℕ, auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
        (auW0 p α s t (k : ℕ) + (auL p α : ℤ) + (j : ℤ))‖
      ≤ ∑' j : ℕ, ‖auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
          (auW0 p α s t (k : ℕ) + (auL p α : ℤ) + (j : ℤ))‖ :=
        norm_tsum_le_tsum_norm hsumU.norm
    _ ≤ ∑' j : ℕ, auGauss (α : ℝ) (auZeta s t (k : ℕ))
          (auW0 p α s t (k : ℕ) + (auL p α : ℤ) + (j : ℤ)) :=
        Summable.tsum_le_tsum
          (fun j => auHf_norm_le s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u hu _)
          hsumU.norm hgaussℕ
    _ = ∑' j : ℕ, Real.exp (-(Real.pi * ((cU + (j : ℝ)) ^ 2) / (α : ℝ) ^ 2)) := by
        apply tsum_congr; intro j
        simp only [auGauss]
        rw [hcUdef]
        congr 1
        push_cast
        ring
    _ ≤ 2 * Real.exp (-(Real.pi * (p : ℝ))) := hgaussTail cU hcU

/-- Lower Gaussian tail of the retained window: the part of the `ℤ`-sum below the window
`{K−m, …, K+m}` is at most `2 e^{-πp}`. -/
theorem auTail_lower_tail (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
    (hα : 0 < α) (hp : 1 ≤ p) (hαp : α ^ 2 < p) (u : Fin s → ℂ) (hu : ‖u‖ ≤ 1)
    (k : Fin t)
    (hgaussTail : ∀ (c : ℝ), (α : ℝ) * Real.sqrt p ≤ c →
      (∑' j : ℕ, Real.exp (-(Real.pi * (c + (j : ℝ)) ^ 2 / (α : ℝ) ^ 2)))
        ≤ 2 * Real.exp (-(Real.pi * (p : ℝ)))) :
    ‖∑' j : ℕ, auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
        (auW0 p α s t (k : ℕ) - 1 - (j : ℤ))‖
      ≤ 2 * Real.exp (-(Real.pi * (p : ℝ))) := by
  have hα0 : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hinj : Function.Injective
      (fun j : ℕ => (auW0 p α s t (k : ℕ) - 1) + (-(j : ℤ))) := by
    intro a b hab
    have h1 : -((a : ℤ)) = -((b : ℤ)) := add_left_cancel hab
    exact_mod_cast (neg_inj.mp h1)
  have hSummℤ : Summable (fun n : ℤ => auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u n) :=
    auTail_auHf_summable s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) hα0 u
  have hsumU0 : Summable (fun j : ℕ => auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
      ((auW0 p α s t (k : ℕ) - 1) + (-(j : ℤ)))) := hSummℤ.comp_injective hinj
  have hsumU : Summable (fun j : ℕ => auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
      (auW0 p α s t (k : ℕ) - 1 - (j : ℤ))) :=
    hsumU0.congr (fun j => by congr 1)
  have hgaussℤ : Summable (fun n : ℤ => auGauss (α : ℝ) (auZeta s t (k : ℕ)) n) :=
    auTail_gauss_summable (α : ℝ) (auZeta s t (k : ℕ)) hα0
  have hgaussℕ0 : Summable (fun j : ℕ => auGauss (α : ℝ) (auZeta s t (k : ℕ))
      ((auW0 p α s t (k : ℕ) - 1) + (-(j : ℤ)))) := hgaussℤ.comp_injective hinj
  have hgaussℕ : Summable (fun j : ℕ => auGauss (α : ℝ) (auZeta s t (k : ℕ))
      (auW0 p α s t (k : ℕ) - 1 - (j : ℤ))) :=
    hgaussℕ0.congr (fun j => by congr 1)
  set cL : ℝ := 1 + (auZeta s t (k : ℕ) - (auW0 p α s t (k : ℕ) : ℝ)) with hcLdef
  have hcL : (α : ℝ) * Real.sqrt p ≤ cL := by
    rw [hcLdef]
    have h1 : (auL p α : ℝ) = 2 * (auM p α : ℝ) + 1 := by simp only [auL]; push_cast; ring
    have h2 : (auW0 p α s t (k : ℕ) : ℝ) = (auK s t (k : ℕ) : ℝ) - (auM p α : ℝ) := by
      simp only [auW0]; push_cast; ring
    have h3 : (auK s t (k : ℕ) : ℝ) - auZeta s t (k : ℕ) ≤ 1 / 2 := by
      have h := abs_le.mp (auK_close s t (k : ℕ) (by omega))
      linarith [h.1]
    have h4 := auM_ge p α
    linarith
  calc ‖∑' j : ℕ, auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
        (auW0 p α s t (k : ℕ) - 1 - (j : ℤ))‖
      ≤ ∑' j : ℕ, ‖auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
          (auW0 p α s t (k : ℕ) - 1 - (j : ℤ))‖ :=
        norm_tsum_le_tsum_norm hsumU.norm
    _ ≤ ∑' j : ℕ, auGauss (α : ℝ) (auZeta s t (k : ℕ))
          (auW0 p α s t (k : ℕ) - 1 - (j : ℤ)) :=
        Summable.tsum_le_tsum
          (fun j => auHf_norm_le s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u hu _)
          hsumU.norm hgaussℕ
    _ = ∑' j : ℕ, Real.exp (-(Real.pi * ((cL + (j : ℝ)) ^ 2) / (α : ℝ) ^ 2)) := by
        apply tsum_congr; intro j
        simp only [auGauss]
        rw [hcLdef]
        congr 1
        push_cast
        ring
    _ ≤ 2 * Real.exp (-(Real.pi * (p : ℝ))) := hgaussTail cL hcL

/-- The truncation error of the ideal resampling weights (paper Lemma 4.9). -/
theorem auTail (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) : ∀ (u : Fin s → ℂ), ‖u‖ ≤ 1 → ∀ k : Fin t, ‖(∑ i ∈ Finset.range (auL p α), ((auWi p α s t (k : ℕ) i : ℝ) : ℂ) * u ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩) - (HvdH.resA s t α).mulVec u k‖ ≤ (2 : ℝ) ^ (-(p : ℤ)) := by
  intro u hu k
  have hα0 : (0 : ℝ) < (α : ℝ) := by exact_mod_cast (by omega : 0 < α)
  have hαpos : 0 < α := by omega
  have hE : Real.exp (-(Real.pi * (p : ℝ))) ≤ (2 : ℝ) ^ (-(p : ℤ)) := auTail_exp_bound p
  have hα2 : (2 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
  have h2p : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) := zpow_pos (by norm_num) _
  have hgaussTail : ∀ (c : ℝ), (α : ℝ) * Real.sqrt p ≤ c →
      (∑' j : ℕ, Real.exp (-(Real.pi * (c + (j : ℝ)) ^ 2 / (α : ℝ) ^ 2)))
        ≤ 2 * Real.exp (-(Real.pi * (p : ℝ))) :=
    auTail_gauss_nat_le (α : ℝ) p hα0 (by omega) (by exact_mod_cast hαp)
  have hSumm : Summable (fun n : ℤ => auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u n) :=
    auTail_auHf_summable s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) hα0 u
  have hBlock := tsum_int_block (fun n : ℤ => auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u n)
    hSumm (auW0 p α s t (k : ℕ)) (auL p α)
  have hU : ‖∑' j : ℕ, auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
      (auW0 p α s t (k : ℕ) + (auL p α : ℤ) + (j : ℤ))‖
      ≤ 2 * Real.exp (-(Real.pi * (p : ℝ))) :=
    auTail_upper_tail p α s t hs hst (by omega) (by omega) hαp u hu k hgaussTail
  have hV : ‖∑' j : ℕ, auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
      (auW0 p α s t (k : ℕ) - 1 - (j : ℤ))‖
      ≤ 2 * Real.exp (-(Real.pi * (p : ℝ))) :=
    auTail_lower_tail p α s t hs hst (by omega) (by omega) hαp u hu k hgaussTail
  rw [auTailWin p α s t hs hst u k, auTail_resA_tsum s t α hs hst hαpos u k]
  rw [← mul_sub, norm_mul]
  have hnorm : ‖(1 / (2 * (α : ℝ)) : ℂ)‖ = 1 / (2 * (α : ℝ)) := by
    have hcast : (1 / (2 * (α : ℝ)) : ℂ) = ((1 / (2 * (α : ℝ)) : ℝ) : ℂ) := by
      first
      | simp
      | norm_cast
      | (push_cast; ring)
    rw [hcast]
    exact RCLike.norm_of_nonneg
      (le_of_lt (div_pos (by norm_num) (mul_pos (by norm_num) hα0)))
  rw [hnorm, hBlock]
  set U : ℂ := ∑' j : ℕ, auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
      (auW0 p α s t (k : ℕ) + (auL p α : ℤ) + (j : ℤ)) with hUdef
  set V : ℂ := ∑' j : ℕ, auHf s (by omega) (α : ℝ) (auZeta s t (k : ℕ)) u
      (auW0 p α s t (k : ℕ) - 1 - (j : ℤ)) with hVdef
  have hU' : ‖U‖ ≤ 2 * Real.exp (-(Real.pi * (p : ℝ))) := by rw [hUdef]; exact hU
  have hV' : ‖V‖ ≤ 2 * Real.exp (-(Real.pi * (p : ℝ))) := by rw [hVdef]; exact hV
  have hgen : ∀ a b c : ℂ, a - (a + b + c) = -(b + c) := fun a b c => by abel
  rw [hgen, norm_neg]
  calc (1 / (2 * (α : ℝ))) * ‖U + V‖
      ≤ (1 / (2 * (α : ℝ))) * (‖U‖ + ‖V‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le U V)
          (le_of_lt (div_pos (by norm_num) (mul_pos (by norm_num) hα0)))
    _ ≤ (1 / (2 * (α : ℝ))) * (2 * Real.exp (-(Real.pi * (p : ℝ)))
          + 2 * Real.exp (-(Real.pi * (p : ℝ)))) :=
        mul_le_mul_of_nonneg_left (add_le_add hU' hV')
          (le_of_lt (div_pos (by norm_num) (mul_pos (by norm_num) hα0)))
    _ ≤ (2 : ℝ) ^ (-(p : ℤ)) := by
        rw [one_div, inv_mul_le_iff₀ (mul_pos (by norm_num) hα0)]
        nlinarith [hE, h2p, hα2]

end Work.Resample
