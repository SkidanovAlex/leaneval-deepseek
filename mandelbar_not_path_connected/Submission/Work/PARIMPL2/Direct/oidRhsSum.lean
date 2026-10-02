import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Bound on the number of steps of the orbit, from the monotone decrease of the
real parts (`hdec`), the two-sided real-part window `[R/4+2, π/λ-R/4]` (`hx1`,`hx2`).

Since `(u k).re + k/3` is non-increasing, `(u n).re + n/3 ≤ (u 0).re`, and
`R/4+2 ≤ (u n).re`, `(u 0).re ≤ π/λ - R/4` give `(n : ℝ) * lam ≤ 3 * π`. -/
theorem oidRhsSum_step (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (n : ℕ) (u : ℕ → ℂ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re) (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3) :
    (n : ℝ) * lam ≤ 3 * Real.pi := by
  have hRpos : (0:ℝ) < R := by linarith
  have hmono : ∀ k ≤ n, (u k).re + (k : ℝ) * (1 / 3) ≤ (u 0).re := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hkn : k ≤ n := le_trans (Nat.le_succ k) hk
      have ih' := ih hkn
      have hklt : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hd := hdec k hklt
      have h2 : ((k : ℝ) + 1) * (1 / 3) = (k : ℝ) * (1 / 3) + 1 / 3 := by ring
      have : (u (k+1)).re + ((k:ℝ)+1) * (1/3) ≤ (u 0).re := by
        rw [h2]; linarith [ih', hd]
      simpa [Nat.cast_add, Nat.cast_one] using this
  have h1' : (n : ℝ) * (1 / 3) ≤ Real.pi / lam - R / 4 - (R / 4 + 2) := by
    have a := hx2 0 (Nat.zero_le n)
    have b := hx1 n le_rfl
    have c := hmono n le_rfl
    linarith
  have h2' : (n : ℝ) * lam / 3 ≤ Real.pi - lam * (R / 2 + 2) := by
    have h3 := mul_le_mul_of_nonneg_left h1' hlam.le
    have h4 : lam * (Real.pi / lam - R / 4 - (R / 4 + 2)) = Real.pi - lam * (R / 2 + 2) := by
      rw [mul_sub, mul_sub, mul_div_cancel₀ _ (ne_of_gt hlam)]; ring
    have h5 : lam * ((n : ℝ) * (1 / 3)) = (n : ℝ) * lam / 3 := by ring
    linarith [h3, h4.le, h4.ge, h5.le, h5.ge]
  nlinarith [h2', hlam, Real.pi_pos, hRpos]

theorem oidRhsSum (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (h1 : ℂ) (n : ℕ) (u : ℕ → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : B ≤ 3 * R / 32) (hh1 : ‖h1‖ ≤ B)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re) (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3)
    (hS : ∑ j ∈ Finset.range n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2 ≤ 24 / R)
    (hzn : ∀ j ≤ n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ≤ 4 / R) :
    ∑ j ∈ Finset.range n, (100 * lam ^ 2
        + (9 / 4) * A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 3
        + (33 / 10) * ‖h1‖ * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
        + (11 / 5) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
        + (3 / R) * A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2)
      ≤ 288 * A / R ^ 2 + 8 := by
  have hRpos : (0:ℝ) < R := by linarith
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hR2pos : (0:ℝ) < R^2 := by positivity
  have hB0 : 0 ≤ B := le_trans (norm_nonneg h1) hh1
  have hnlam : (n:ℝ) * lam ≤ 3 * Real.pi := oidRhsSum_step lam R hlam hR n u hx1 hx2 hdec
  -- `(n : ℝ) * λ² ≤ 3π/R²`, hence `100 λ² n ≤ 1/8`.
  have hnlam2 : (n:ℝ) * lam^2 ≤ 3 * Real.pi / R^2 := by
    have hs : (n:ℝ) * lam^2 ≤ (3*Real.pi) * lam := by
      have := mul_le_mul_of_nonneg_right hnlam hlam.le
      nlinarith [this]
    have h2 : lam ≤ 1/R^2 := by rw [le_div_iff₀ hR2pos]; linarith [hlamR]
    have h3 : (3*Real.pi)*lam ≤ (3*Real.pi)*(1/R^2) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (3*Real.pi)*(1/R^2) = 3*Real.pi/R^2 := by ring
    linarith [hs, h3, h4.le, h4.ge]
  have hterm0 : 100 * lam^2 * (n:ℝ) ≤ 1/8 := by
    have hs : 100 * ((n:ℝ) * lam^2) ≤ 100 * (3*Real.pi/R^2) :=
      mul_le_mul_of_nonneg_left hnlam2 (by norm_num : (0:ℝ) ≤ 100)
    have hkey : 100 * (3*Real.pi/R^2) ≤ 1/8 := by
      rw [show 100 * (3*Real.pi/R^2) = 300*Real.pi/R^2 by ring]
      rw [div_le_iff₀ hR2pos]
      nlinarith [hR, Real.pi_lt_four]
    have heq : 100 * lam^2 * (n:ℝ) = 100 * ((n:ℝ) * lam^2) := by ring
    linarith [hs, hkey, heq.le, heq.ge]
  let e : ℕ → ℝ := fun j => ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖
  have he_nn : ∀ j, 0 ≤ e j := fun j => norm_nonneg _
  have hS_e : (∑ j ∈ Finset.range n, (e j)^2) ≤ 24/R := hS
  -- Pointwise estimate: use `e j ≤ 4/R` on the cubic and `‖h1‖ ≤ B` on the middle term.
  have hpoint : ∀ j ∈ Finset.range n,
      (100 * lam^2 + (9/4)*A*(e j)^3 + (33/10)*‖h1‖*(e j)^2 + (11/5)*(e j)^2 + (3/R)*A*(e j)^2)
      ≤ 100*lam^2 + (12*A/R + (33/10)*B + 11/5) * (e j)^2 := by
    intro j hj
    have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
    have hej : 0 ≤ e j := he_nn j
    have hzj : e j ≤ 4/R := hzn j hjn
    have hcube : (e j)^3 ≤ (4/R) * (e j)^2 := by
      rw [show (e j)^3 = (e j) * (e j)^2 by ring]
      exact mul_le_mul_of_nonneg_right hzj (by positivity)
    have hA1 : (9/4)*A*(e j)^3 ≤ (9*A/R)*(e j)^2 := by
      have h1' : (9/4)*A*(e j)^3 ≤ (9/4)*A*((4/R)*(e j)^2) :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
      have h2' : (9/4)*A*((4/R)*(e j)^2) = (9*A/R)*(e j)^2 := by ring
      linarith [h1', h2'.le, h2'.ge]
    have hA2 : (3/R)*A*(e j)^2 = (3*A/R)*(e j)^2 := by ring
    have hC : (33/10)*‖h1‖*(e j)^2 ≤ (33/10)*B*(e j)^2 := by
      have h1' : (33/10)*‖h1‖ ≤ (33/10)*B := by
        have h := mul_le_mul_of_nonneg_left hh1 (by norm_num : (0:ℝ) ≤ 33/10)
        linarith
      exact mul_le_mul_of_nonneg_right h1' (by positivity)
    have hcomb : (9*A/R)*(e j)^2 + (3*A/R)*(e j)^2 = (12*A/R)*(e j)^2 := by ring
    have hexp : (12*A/R + (33/10)*B + 11/5) * (e j)^2
        = (12*A/R)*(e j)^2 + (33/10)*B*(e j)^2 + (11/5)*(e j)^2 := by ring
    linarith [hA1, hA2, hC, hcomb, hexp.le, hexp.ge]
  have hsum_le : (∑ j ∈ Finset.range n, (100 * lam^2 + (9/4)*A*(e j)^3 + (33/10)*‖h1‖*(e j)^2 + (11/5)*(e j)^2 + (3/R)*A*(e j)^2))
      ≤ ∑ j ∈ Finset.range n, (100*lam^2 + (12*A/R + (33/10)*B + 11/5) * (e j)^2) :=
    Finset.sum_le_sum hpoint
  have hsum_eq : (∑ j ∈ Finset.range n, (100*lam^2 + (12*A/R + (33/10)*B + 11/5) * (e j)^2))
      = 100*lam^2*(n:ℝ) + (12*A/R + (33/10)*B + 11/5) * (∑ j ∈ Finset.range n, (e j)^2) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hC0 : 0 ≤ 12*A/R + (33/10)*B + 11/5 := by
    have h1' : 0 ≤ 12*A/R := by positivity
    have h2' : 0 ≤ (33/10)*B := by positivity
    linarith
  have hCtor : (12*A/R + (33/10)*B + 11/5) * (∑ j ∈ Finset.range n, (e j)^2)
      ≤ (12*A/R + (33/10)*B + 11/5) * (24/R) :=
    mul_le_mul_of_nonneg_left hS_e hC0
  have hCval : (12*A/R + (33/10)*B + 11/5) * (24/R) ≤ 288*A/R^2 + 297/40 + 33/80 := by
    have hexp : (12*A/R + (33/10)*B + 11/5) * (24/R)
        = (12*A/R)*(24/R) + (33/10)*B*(24/R) + (11/5)*(24/R) := by ring
    have h1v : (12*A/R)*(24/R) = 288*A/R^2 := by field_simp; ring
    have h2v : (33/10)*B*(24/R) ≤ 297/40 := by
      have hcoef : 0 ≤ (33/10)*(24/R) := by positivity
      have hle : B * ((33/10)*(24/R)) ≤ (3*R/32) * ((33/10)*(24/R)) :=
        mul_le_mul_of_nonneg_right hB hcoef
      have he : (3*R/32)*((33/10)*(24/R)) = 297/40 := by field_simp; ring
      nlinarith [hle, he.le, he.ge]
    have h3v : (11/5)*(24/R) ≤ 33/80 := by
      rw [show (11:ℝ)/5*(24/R) = 264/(5*R) by ring, div_le_iff₀ (by positivity : (0:ℝ) < 5*R)]
      nlinarith [hR]
    linarith [hexp.le, hexp.ge, h1v.le, h1v.ge, h2v, h3v]
  calc ∑ j ∈ Finset.range n, (100 * lam^2 + (9/4)*A*(e j)^3 + (33/10)*‖h1‖*(e j)^2 + (11/5)*(e j)^2 + (3/R)*A*(e j)^2)
      ≤ ∑ j ∈ Finset.range n, (100*lam^2 + (12*A/R + (33/10)*B + 11/5) * (e j)^2) := hsum_le
    _ = 100*lam^2*(n:ℝ) + (12*A/R + (33/10)*B + 11/5) * (∑ j ∈ Finset.range n, (e j)^2) := hsum_eq
    _ ≤ 100*lam^2*(n:ℝ) + (12*A/R + (33/10)*B + 11/5) * (24/R) := by linarith [hCtor]
    _ ≤ 1/8 + (288*A/R^2 + 297/40 + 33/80) := by linarith [hterm0, hCval]
    _ ≤ 288*A/R^2 + 8 := by linarith

end Work.PARIMPL2.Direct
