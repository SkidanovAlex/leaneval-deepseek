import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.EllipticEst.not_integrableOn_of_le_const_on_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `phi_eq_zero_of_euler_gap_weighted`

Weighted variant of `EllipticEst.phi_eq_zero_of_euler_gap`: a non-negative `C²` function `Φ` on
`(0,∞)` which

* is integrable on `(0,∞)`;
* satisfies the Euler-gap inequality `α²z²Φ'' + α(5+α)zΦ' ≥ 0`;
* has `Φ z · z^{-4}` integrable on `(0,1)` (instead of the boundedness of `Φ'` near `0`),

vanishes identically.

The proof is the same Euler-ODE argument as in the unweighted case: with `c = (5+α)/α > 1` the
inequality says `(z^c Φ')' ≥ 0`, so `G(z) = z^c Φ'(z)` is non-decreasing.  The two alternatives
`G(z₀) > 0` (then `Φ` is bounded below on a half-line and is not integrable) and `G(z₀) < 0`
(then `Φ` grows like `z^{1-c}` near `0` and `Φ z^{-4}` is not integrable) are both excluded; hence
`G ≡ 0`, `Φ` is constant, and integrability forces the constant to be `0`.
-/

namespace Work.FTS_EllLimOK

open MeasureTheory Filter
open scoped Topology

/-- The key differential computation: with `c = (5+α)/α`, the Euler gap inequality
`α²z²Φ'' + α(5+α)zΦ' ≥ 0` is equivalent, after multiplication by the positive factor
`z^{c-2}/α²`, to the nonnegativity of the derivative of `z ↦ z^c Φ'(z)`. -/
private theorem euler_key (α : ℝ) (hα : 0 < α) (Phi : ℝ → ℝ)
    (hineq : ∀ z ∈ Set.Ioi (0 : ℝ),
      0 ≤ α ^ 2 * z ^ 2 * deriv (deriv Phi) z + α * (5 + α) * z * deriv Phi z)
    {z : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) :
    0 ≤ ((5 + α) / α) * z ^ (((5 + α) / α) - 1) * deriv Phi z
      + z ^ ((5 + α) / α) * deriv (deriv Phi) z := by
  set c : ℝ := (5 + α) / α with hcdef
  have hz0 : 0 < z := hz
  have hzpow : 0 < z ^ (c - 2) := Real.rpow_pos_of_pos hz0 _
  have hα2 : 0 < α ^ 2 := by positivity
  have hineqz : 0 ≤ α ^ 2 * z ^ (2 : ℝ) * deriv (deriv Phi) z + α * (5 + α) * z * deriv Phi z := by
    have h := hineq z hz
    have he : z ^ (2 : ℕ) = z ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    rwa [he] at h
  have h1 : 0 ≤ z ^ (c - 2) *
      (α ^ 2 * z ^ (2 : ℝ) * deriv (deriv Phi) z + α * (5 + α) * z * deriv Phi z) :=
    mul_nonneg hzpow.le hineqz
  have hc2 : z ^ (c - 2) * z ^ (2 : ℝ) = z ^ c := by
    rw [← Real.rpow_add hz0, show c - 2 + 2 = c from by ring]
  have hc1 : z ^ (c - 2) * z = z ^ (c - 1) := by
    calc z ^ (c - 2) * z = z ^ (c - 2) * z ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = z ^ (c - 1) := by rw [← Real.rpow_add hz0, show c - 2 + 1 = c - 1 from by ring]
  have hcα : α ^ 2 * c = α * (5 + α) := by
    rw [hcdef]; field_simp
  have key : z ^ (c - 2) *
        (α ^ 2 * z ^ (2 : ℝ) * deriv (deriv Phi) z + α * (5 + α) * z * deriv Phi z)
      = α ^ 2 * (c * z ^ (c - 1) * deriv Phi z + z ^ c * deriv (deriv Phi) z) := by
    have hA : z ^ (c - 2) * (α ^ 2 * z ^ (2 : ℝ) * deriv (deriv Phi) z)
        = α ^ 2 * (z ^ c * deriv (deriv Phi) z) := by
      calc z ^ (c - 2) * (α ^ 2 * z ^ (2 : ℝ) * deriv (deriv Phi) z)
          = α ^ 2 * ((z ^ (c - 2) * z ^ (2 : ℝ)) * deriv (deriv Phi) z) := by ring
        _ = α ^ 2 * (z ^ c * deriv (deriv Phi) z) := by rw [hc2]
    have hB : z ^ (c - 2) * (α * (5 + α) * z * deriv Phi z)
        = α ^ 2 * (c * z ^ (c - 1) * deriv Phi z) := by
      calc z ^ (c - 2) * (α * (5 + α) * z * deriv Phi z)
          = (α * (5 + α)) * ((z ^ (c - 2) * z) * deriv Phi z) := by ring
        _ = (α * (5 + α)) * (z ^ (c - 1) * deriv Phi z) := by rw [hc1]
        _ = (α ^ 2 * c) * (z ^ (c - 1) * deriv Phi z) := by rw [← hcα]
        _ = α ^ 2 * (c * z ^ (c - 1) * deriv Phi z) := by ring
    rw [mul_add, hA, hB]; ring
  have hfin : 0 ≤ c * z ^ (c - 1) * deriv Phi z + z ^ c * deriv (deriv Phi) z :=
    nonneg_of_mul_nonneg_right (key ▸ h1) hα2
  rwa [hcdef] at hfin

/-- If `f z ≥ m · z^p` for `z ∈ (0,a)` with `m > 0`, `a > 0` and `p ≤ 3`, then
`z ↦ f z · z^{-4}` is not integrable on `(0,1)`: near `0` it dominates the divergent power
`z^{p-4}`. -/
private theorem not_integrableOn_mul_rpow_Ioo {f : ℝ → ℝ} {a m p : ℝ} (ha : 0 < a) (hm : 0 < m)
    (hp : p ≤ 3) (hf : ∀ z ∈ Set.Ioo (0 : ℝ) a, m * z ^ p ≤ f z) :
    ¬ MeasureTheory.IntegrableOn (fun z => f z * z ^ (-4 : ℝ)) (Set.Ioo (0 : ℝ) 1) := by
  intro h
  set b : ℝ := min a 1 with hbdef
  have hbpos : 0 < b := lt_min ha one_pos
  have hb1 : b ≤ 1 := min_le_right _ _
  have hba : b ≤ a := min_le_left _ _
  have h' : MeasureTheory.IntegrableOn (fun z => f z * z ^ (-4 : ℝ)) (Set.Ioo (0 : ℝ) b) :=
    h.mono_set (Set.Ioo_subset_Ioo_right hb1)
  -- the dominating function `z ↦ (1/m) * (f z * z^{-4})`
  have hg : MeasureTheory.IntegrableOn (fun z => (1 / m) * (f z * z ^ (-4 : ℝ)))
      (Set.Ioo (0 : ℝ) b) := by
    change Integrable (fun z => f z * z ^ (-4 : ℝ)) (volume.restrict (Set.Ioo (0 : ℝ) b)) at h'
    change Integrable (fun z => (1 / m) * (f z * z ^ (-4 : ℝ)))
      (volume.restrict (Set.Ioo (0 : ℝ) b))
    exact h'.const_mul (1 / m)
  -- `z ↦ z^{p-4}` is dominated by it on `(0,b)`
  have hzpow : MeasureTheory.IntegrableOn (fun z => z ^ (p - 4)) (Set.Ioo (0 : ℝ) b) := by
    change Integrable (fun z => (1 / m) * (f z * z ^ (-4 : ℝ)))
      (volume.restrict (Set.Ioo (0 : ℝ) b)) at hg
    change Integrable (fun z => z ^ (p - 4)) (volume.restrict (Set.Ioo (0 : ℝ) b))
    refine hg.mono' ?_ ?_
    · exact ((continuous_id.continuousOn).rpow_const
        (fun x hx => Or.inl (ne_of_gt hx.1))).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      have hz0 : 0 < z := hz.1
      have hza : z ∈ Set.Ioo (0 : ℝ) a := ⟨hz0, lt_of_lt_of_le hz.2 hba⟩
      have hmz : m * z ^ p ≤ f z := hf z hza
      have hz4 : (0 : ℝ) < z ^ (-4 : ℝ) := Real.rpow_pos_of_pos hz0 _
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hz0 (p - 4))]
      have hsplit : m * z ^ p * z ^ (-4 : ℝ) = m * z ^ (p - 4) := by
        rw [mul_assoc, ← Real.rpow_add hz0, show p + -4 = p - 4 from by ring]
      calc z ^ (p - 4) = (1 / m) * (m * z ^ (p - 4)) := by
            field_simp
        _ ≤ (1 / m) * (f z * z ^ (-4 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc m * z ^ (p - 4) = m * z ^ p * z ^ (-4 : ℝ) := hsplit.symm
              _ ≤ f z * z ^ (-4 : ℝ) := mul_le_mul_of_nonneg_right hmz hz4.le
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hbpos).mp hzpow
  linarith

/-- Grönwall comparison, "upward" direction: if `Φ' ≥ k·z^{-c}` past `z₀` (with `c > 1`), then
`Φ` is bounded below on `(z₀,∞)` by the integral of `k·z^{-c}`. -/
private theorem le_of_deriv_ge_rpow {Phi : ℝ → ℝ} {z₀ k c : ℝ} (hc : 1 < c) (hz₀ : 0 < z₀)
    (hder : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt Phi (deriv Phi z) z) (hnn : 0 ≤ Phi z₀)
    (hge : ∀ z ∈ Set.Ioi z₀, k * z ^ (-c) ≤ deriv Phi z) :
    ∀ z ∈ Set.Ioi z₀, (k / (c - 1)) * (z₀ ^ (1 - c) - z ^ (1 - c)) ≤ Phi z := by
  have hc1 : c - 1 ≠ 0 := by linarith
  have hpsi : ∀ z ∈ Set.Ioi z₀,
      HasDerivAt (fun s => Phi s + (k / (c - 1)) * s ^ (1 - c)) (deriv Phi z - k * z ^ (-c)) z := by
    intro z hz
    have hz0 : 0 < z := lt_trans hz₀ hz
    have h1 := (hder z hz0).add
      ((Real.hasDerivAt_rpow_const (x := z) (p := 1 - c) (Or.inl (ne_of_gt hz0))).const_mul
        (k / (c - 1)))
    convert h1 using 1
    rw [show (1 - c) - 1 = -c from by ring]
    field_simp
    ring
  have hmono : MonotoneOn (fun s => Phi s + (k / (c - 1)) * s ^ (1 - c)) (Set.Ici z₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici z₀) ?_ ?_ ?_
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hz₀ hx
      exact ((hder x hx0).add
        ((Real.hasDerivAt_rpow_const (x := x) (p := 1 - c)
          (Or.inl (ne_of_gt hx0))).const_mul (k / (c - 1)))).continuousAt.continuousWithinAt
    · rw [interior_Ici]; intro x hx
      exact (hpsi x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]; intro x hx
      rw [(hpsi x hx).deriv]
      linarith [hge x hx]
  intro z hz
  have hzx : z ∈ Set.Ici z₀ := Set.mem_Ici.mpr (le_of_lt hz)
  have h := hmono (Set.mem_Ici.mpr le_rfl) hzx hz.le
  linarith

/-- Grönwall comparison, "downward" direction: if `Φ' ≤ -k·z^{-c}` below `z₀` (with `c > 1`), then
`Φ` is bounded below on `(0,z₀)` by minus the integral of `k·z^{-c}`. -/
private theorem le_of_deriv_le_rpow {Phi : ℝ → ℝ} {z₀ k c : ℝ} (hc : 1 < c) (hz₀ : 0 < z₀)
    (hder : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt Phi (deriv Phi z) z) (hnn : 0 ≤ Phi z₀)
    (hle : ∀ z ∈ Set.Ioo (0 : ℝ) z₀, deriv Phi z ≤ -(k * z ^ (-c))) :
    ∀ z ∈ Set.Ioo (0 : ℝ) z₀, (k / (c - 1)) * (z ^ (1 - c) - z₀ ^ (1 - c)) ≤ Phi z := by
  intro z hz
  have hz0 : 0 < z := hz.1
  have hzz₀ : z ≤ z₀ := le_of_lt hz.2
  have hpsi : ∀ s ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t => Phi t - (k / (c - 1)) * t ^ (1 - c))
        (deriv Phi s + k * s ^ (-c)) s := by
    intro s hs
    have h1 := (hder s hs).sub
      ((Real.hasDerivAt_rpow_const (x := s) (p := 1 - c) (Or.inl (ne_of_gt hs))).const_mul
        (k / (c - 1)))
    convert h1 using 1
    rw [show (1 - c) - 1 = -c from by ring]
    have hc1 : c - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hmono : AntitoneOn (fun t => Phi t - (k / (c - 1)) * t ^ (1 - c)) (Set.Icc z z₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc z z₀) ?_ ?_ ?_
    · intro x hx
      exact (hpsi x (lt_of_lt_of_le hz0 hx.1)).continuousAt.continuousWithinAt
    · rw [interior_Icc]; intro x hx
      exact (hpsi x (lt_of_lt_of_le hz0 (le_of_lt hx.1))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro x hx
      rw [(hpsi x (lt_of_lt_of_le hz0 (le_of_lt hx.1))).deriv]
      linarith [hle x (Set.mem_Ioo.mpr ⟨lt_of_lt_of_le hz0 (le_of_lt hx.1), hx.2⟩)]
  have h := hmono (Set.mem_Icc.mpr ⟨le_rfl, hzz₀⟩) (Set.mem_Icc.mpr ⟨hzz₀, le_rfl⟩) hzz₀
  linarith

theorem phi_eq_zero_of_euler_gap_weighted (α : ℝ) (hα : 0 < α) (Phi : ℝ → ℝ)
    (hder1 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt Phi (deriv Phi z) z)
    (hder2 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (deriv Phi) (deriv (deriv Phi) z) z)
    (hineq : ∀ z ∈ Set.Ioi (0 : ℝ),
      0 ≤ α ^ 2 * z ^ 2 * deriv (deriv Phi) z + α * (5 + α) * z * deriv Phi z)
    (hnonneg : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ Phi z)
    (hint : MeasureTheory.IntegrableOn Phi (Set.Ioi (0 : ℝ)))
    (hweight : MeasureTheory.IntegrableOn (fun z => Phi z * z ^ (-4 : ℝ)) (Set.Ioo (0 : ℝ) 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), Phi z = 0 := by
  set c : ℝ := (5 + α) / α with hcdef
  have hc : 1 < c := by
    rw [hcdef, lt_div_iff₀ hα]
    linarith
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  -- the derivative of `G z = z^c Φ'(z)`
  have hGderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun w : ℝ => w ^ c * deriv Phi w)
      (c * z ^ (c - 1) * deriv Phi z + z ^ c * deriv (deriv Phi) z) z := by
    intro z hz
    exact (Real.hasDerivAt_rpow_const (x := z) (p := c) (Or.inl (ne_of_gt hz))).mul (hder2 z hz)
  have hGkey : ∀ z ∈ Set.Ioi (0 : ℝ),
      0 ≤ c * z ^ (c - 1) * deriv Phi z + z ^ c * deriv (deriv Phi) z := by
    intro z hz
    have h := euler_key α hα Phi hineq hz
    rw [hcdef]
    exact h
  -- `G` is non-decreasing
  have hGmono : MonotoneOn (fun z => z ^ c * deriv Phi z) (Set.Ioi (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · intro z hz; exact (hGderiv z hz).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; intro z hz
      exact (hGderiv z hz).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; intro z hz
      rw [(hGderiv z hz).deriv]
      exact hGkey z hz
  -- `Φ'` in terms of `G`
  have hderivPhi : ∀ z ∈ Set.Ioi (0 : ℝ), deriv Phi z = z ^ (-c) * (z ^ c * deriv Phi z) := by
    intro z hz
    have hzc : z ^ c ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz c)
    rw [Real.rpow_neg hz.le, ← mul_assoc, inv_mul_cancel₀ hzc, one_mul]
  by_cases hcase1 : ∃ z₀ ∈ Set.Ioi (0 : ℝ), 0 < z₀ ^ c * deriv Phi z₀
  · -- `G` positive somewhere: `Φ` is bounded below on a half-line, hence not integrable
    obtain ⟨z₀, hz₀, hgt⟩ := hcase1
    have hz₀pos : (0 : ℝ) < z₀ := Set.mem_Ioi.mp hz₀
    have hge : ∀ z ∈ Set.Ioi z₀, (z₀ ^ c * deriv Phi z₀) * z ^ (-c) ≤ deriv Phi z := by
      intro z hz
      have hzlt : z₀ < z := Set.mem_Ioi.mp hz
      have hz0 : 0 < z := lt_trans hz₀pos hzlt
      have hG := hGmono hz₀ hz0 hzlt.le
      rw [hderivPhi z hz0]
      calc z₀ ^ c * deriv Phi z₀ * z ^ (-c)
          = (z₀ ^ c * deriv Phi z₀) * z ^ (-c) := by ring
        _ ≤ (z ^ c * deriv Phi z) * z ^ (-c) :=
            mul_le_mul_of_nonneg_right hG (Real.rpow_pos_of_pos hz0 (-c)).le
        _ = z ^ (-c) * (z ^ c * deriv Phi z) := by ring
    have hbound := le_of_deriv_ge_rpow hc hz₀pos hder1 (hnonneg z₀ hz₀) hge
    refine absurd hint (_root_.Work.FTS.EllipticEst.not_integrableOn_of_le_const_on_Ioi
      (a := 2 * z₀)
      (m := (z₀ ^ c * deriv Phi z₀) / (c - 1) * (z₀ ^ (1 - c) - (2 * z₀) ^ (1 - c)))
      (by linarith) ?_ ?_)
    · refine mul_pos (div_pos hgt hc1) ?_
      have h2 : (2 * z₀) ^ (1 - c) < z₀ ^ (1 - c) := by
        rw [Real.rpow_lt_rpow_iff_of_neg (by linarith : (0 : ℝ) < 2 * z₀) hz₀pos
          (by linarith : 1 - c < 0)]
        linarith
      linarith
    · intro z hz
      have hzlt : 2 * z₀ < z := Set.mem_Ioi.mp hz
      have hz0 : 0 < z := by linarith
      have hb := hbound z (Set.mem_Ioi.mpr (by linarith : z₀ < z))
      have h2 : z ^ (1 - c) ≤ (2 * z₀) ^ (1 - c) := by
        rw [Real.rpow_le_rpow_iff_of_neg hz0 (by linarith : (0 : ℝ) < 2 * z₀)
          (by linarith : 1 - c < 0)]
        linarith
      have hcoef : 0 ≤ (z₀ ^ c * deriv Phi z₀) / (c - 1) := div_nonneg hgt.le hc1.le
      calc (z₀ ^ c * deriv Phi z₀) / (c - 1) * (z₀ ^ (1 - c) - (2 * z₀) ^ (1 - c))
          ≤ (z₀ ^ c * deriv Phi z₀) / (c - 1) * (z₀ ^ (1 - c) - z ^ (1 - c)) := by
            apply mul_le_mul_of_nonneg_left _ hcoef
            linarith
        _ ≤ Phi z := hb
  · push_neg at hcase1
    by_cases hcase2 : ∃ z₀ ∈ Set.Ioi (0 : ℝ), z₀ ^ c * deriv Phi z₀ < 0
    · -- `G` negative somewhere: `Φ` grows like `z^{1-c}` near `0`
      obtain ⟨z₀, hz₀, hlt⟩ := hcase2
      set k : ℝ := -(z₀ ^ c * deriv Phi z₀) with hkdef
      have hk : 0 < k := by rw [hkdef]; linarith
      have hle : ∀ z ∈ Set.Ioo (0 : ℝ) z₀, deriv Phi z ≤ -(k * z ^ (-c)) := by
        intro z hz
        have hz0 : 0 < z := hz.1
        have hG := hGmono hz0 hz₀ (le_of_lt hz.2)
        have hGz : z ^ c * deriv Phi z ≤ -k := by
          rw [hkdef, neg_neg]
          exact hG
        rw [hderivPhi z hz0]
        calc z ^ (-c) * (z ^ c * deriv Phi z) ≤ z ^ (-c) * (-k) :=
              mul_le_mul_of_nonneg_left hGz (Real.rpow_pos_of_pos hz0 (-c)).le
          _ = -(k * z ^ (-c)) := by ring
      have hbound := le_of_deriv_le_rpow hc hz₀ hder1 (hnonneg z₀ hz₀) hle
      set z₁ : ℝ := z₀ * 2 ^ (-(1 / (c - 1))) with hz₁def
      have hz₁pos : 0 < z₁ := by
        rw [hz₁def]; exact mul_pos hz₀ (Real.rpow_pos_of_pos (by norm_num) _)
      have hz₁le : z₁ ≤ z₀ := by
        rw [hz₁def]
        calc z₀ * 2 ^ (-(1 / (c - 1))) ≤ z₀ * 2 ^ (0 : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ hz₀.le
              apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
              exact neg_nonpos.mpr (div_nonneg (by norm_num) hc1.le)
          _ = z₀ := by rw [Real.rpow_zero, mul_one]
      have hz₁pow : z₁ ^ (1 - c) = 2 * z₀ ^ (1 - c) := by
        rw [hz₁def, Real.mul_rpow hz₀.le (Real.rpow_pos_of_pos (by norm_num) _).le,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hcne : c - 1 ≠ 0 := ne_of_gt hc1
        have he : -(1 / (c - 1)) * (1 - c) = 1 := by
          field_simp
          ring
        rw [he, Real.rpow_one]
        ring
      refine absurd hweight (not_integrableOn_mul_rpow_Ioo (a := z₁) (m := k / (2 * (c - 1)))
        (p := 1 - c) hz₁pos (by positivity) (by linarith) ?_)
      intro z hz
      have hz0 : 0 < z := hz.1
      have hzz₀ : z < z₀ := lt_of_lt_of_le hz.2 hz₁le
      have hb := hbound z (Set.mem_Ioo.mpr ⟨hz0, hzz₀⟩)
      have hzp : (2 : ℝ) * z₀ ^ (1 - c) ≤ z ^ (1 - c) := by
        rw [← hz₁pow]
        rw [Real.rpow_le_rpow_iff_of_neg hz₁pos hz0 (by linarith : 1 - c < 0)]
        exact le_of_lt hz.2
      have hid : k / (2 * (c - 1)) = k / (c - 1) * (1 / 2) := by
        rw [mul_one_div, div_div, show 2 * (c - 1) = (c - 1) * 2 from by ring]
      calc k / (2 * (c - 1)) * z ^ (1 - c)
          = k / (c - 1) * ((1 / 2) * z ^ (1 - c)) := by rw [hid]; ring
        _ ≤ k / (c - 1) * (z ^ (1 - c) - z₀ ^ (1 - c)) := by
            apply mul_le_mul_of_nonneg_left _ (div_nonneg hk.le hc1.le)
            linarith
        _ ≤ Phi z := hb
    · -- `G ≡ 0`
      push_neg at hcase2
      have hGzero : ∀ z ∈ Set.Ioi (0 : ℝ), z ^ c * deriv Phi z = 0 :=
        fun z hz => le_antisymm (hcase1 z hz) (hcase2 z hz)
      have hdz : ∀ z ∈ Set.Ioi (0 : ℝ), deriv Phi z = 0 := by
        intro z hz
        rcases mul_eq_zero.mp (hGzero z hz) with h | h
        · exact absurd h (ne_of_gt (Real.rpow_pos_of_pos hz c))
        · exact h
      have hcont : ContinuousOn Phi (Set.Ioi (0 : ℝ)) :=
        fun z hz => (hder1 z hz).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ Phi (interior (Set.Ioi (0 : ℝ))) := by
        rw [interior_Ioi]; intro z hz
        exact (hder1 z hz).differentiableAt.differentiableWithinAt
      have hmono : MonotoneOn Phi (Set.Ioi (0 : ℝ)) :=
        monotoneOn_of_deriv_nonneg (convex_Ioi 0) hcont hdiff (by
          rw [interior_Ioi]; intro z hz
          rw [hdz z hz])
      have hcont' : ContinuousOn (fun z => -Phi z) (Set.Ioi (0 : ℝ)) := fun z hz =>
        (hder1 z hz).neg.continuousAt.continuousWithinAt
      have hdiff' : DifferentiableOn ℝ (fun z => -Phi z) (interior (Set.Ioi (0 : ℝ))) := by
        rw [interior_Ioi]; intro z hz
        exact (hder1 z hz).neg.differentiableAt.differentiableWithinAt
      have hantimono : MonotoneOn (fun z => -Phi z) (Set.Ioi (0 : ℝ)) :=
        monotoneOn_of_deriv_nonneg (convex_Ioi 0) hcont' hdiff' (by
          rw [interior_Ioi]; intro z hz
          have hneg : deriv (fun z => -Phi z) z = -deriv Phi z := (hder1 z hz).neg.deriv
          rw [hneg, hdz z hz]
          norm_num)
      have h1mem : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr one_pos
      have hconst : ∀ w ∈ Set.Ioi (0 : ℝ), Phi w = Phi 1 := by
        intro w hw
        rcases le_total w 1 with h | h
        · exact le_antisymm (hmono hw h1mem h) (by have := hantimono hw h1mem h; linarith)
        · exact le_antisymm (by have := hantimono h1mem hw h; linarith) (hmono h1mem hw h)
      have hC0 : Phi 1 = 0 := by
        by_contra hne
        have hpos1 : 0 < Phi 1 := lt_of_le_of_ne (hnonneg 1 h1mem) (Ne.symm hne)
        have hint' : MeasureTheory.IntegrableOn (fun _ : ℝ => Phi 1) (Set.Ioi (0 : ℝ)) :=
          hint.congr_fun (fun w hw => hconst w hw) measurableSet_Ioi
        exact _root_.Work.FTS.EllipticEst.not_integrableOn_of_le_const_on_Ioi
          (f := fun _ : ℝ => Phi 1) (a := 1) (m := Phi 1) one_pos hpos1
          (fun z _ => le_refl _) hint'
      intro z hz
      rw [hconst z hz, hC0]

end Work.FTS_EllLimOK
