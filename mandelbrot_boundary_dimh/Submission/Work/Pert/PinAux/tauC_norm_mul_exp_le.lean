import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.iInf_dist_eq_norm_sub_round
import Submission.Work.Pert.norm_sq_one_sub_exp_two_pi_I_mul
import Submission.Work.Pert.sin_sq_pi_ge_of_lattice
import Submission.Work.Pert.tauC_exp_one_of_iInf_eq_zero

/-!
# `Work.Pert.PinAux.tauC_norm_mul_exp_le`

The **sharp (weighted) pointwise bound** for the universal cover
`τ_f w = tauC σ α w = σ / (1 - exp (-2πi α w))`:

  `∀ w, ‖τ_f w‖ · exp (π · (α w).im) ≤ 4π² / dist (w, ℤ/α)`

where `dist (w, ℤ/α) = ⨅ k, dist w (k/α)`.

The weight `exp (π (α w).im)` is exactly what makes the estimate true for all `w` (the unweighted
form fails as `(α w).im → +∞`): the denominator `1 - e^{-2πiζ}` carries `e^{π Im ζ}·2|sin (πζ)|`, so
the weight cancels the exponential factor and leaves the lattice-distance decay `≍ 1/dist`.

The inputs are all in the workspace:

* the exact modulus identity `‖1 - e^{-2πiζ}‖² = 4 e^{2π Im ζ}(sinh²(π Im ζ) + sin²(π Re ζ))`
  (`Work.Pert.norm_sq_one_sub_exp_two_pi_I_mul` + `Real.sinh_eq`);
* the lattice condition `sin²(π P) ≥ 4 δ²` with `δ = dist (P, ℤ)`
  (`Work.Pert.sin_sq_pi_ge_of_lattice`, via the nearest integer `round`);
* `sinh²(π y) ≥ 4 y²`;
* the `ℤ/α`-lattice as the `α`-preimage of `ℤ` (`iInf_dist_div_eq`, using
  `Work.Pert.iInf_dist_eq_norm_sub_round`), and the normalisation `‖σ‖ ≤ 8π‖α‖`, which gives
  `2π/L ≤ 4π²/L`.

The degenerate case `⨅ k, dist w (k/α) = 0` (i.e. `w` a lattice point, where `τ_f` has its poles)
is handled by `Work.Pert.tauC_exp_one_of_iInf_eq_zero`: then `1 - e^{-2πiαw} = 0`, `τ_f w = 0`, and
both sides of the asserted inequality are `0`.
-/

namespace Work.Pert.PinAux

open Complex

noncomputable section

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-- `(1 - e^{2πy})² = 4 e^{2πy} sinh²(πy)`: the `sinh`-form of the reverse-triangle factor. -/
lemma one_sub_exp_two_pi_sq (y : ℝ) :
    (1 - Real.exp (2 * Real.pi * y)) ^ 2
      = 4 * Real.exp (2 * Real.pi * y) * Real.sinh (Real.pi * y) ^ 2 := by
  have hexp : Real.exp (2 * Real.pi * y) = Real.exp (Real.pi * y) * Real.exp (Real.pi * y) := by
    rw [show 2 * Real.pi * y = Real.pi * y + Real.pi * y by ring, Real.exp_add]
  have hneg : Real.exp (-(Real.pi * y)) = (Real.exp (Real.pi * y))⁻¹ := Real.exp_neg _
  have hmain : Real.exp (2 * Real.pi * y) - 1
      = 2 * Real.exp (Real.pi * y) * Real.sinh (Real.pi * y) := by
    rw [Real.sinh_eq, hneg, hexp]
    field_simp [Real.exp_ne_zero]
  have hsquare : (1 - Real.exp (2 * Real.pi * y)) ^ 2
      = (Real.exp (2 * Real.pi * y) - 1) ^ 2 := by ring
  rw [hsquare, hmain, hexp]
  ring

/-- **Exact modulus identity in the sign form used by `tauC`**:
`‖1 - e^{-2πiζ}‖² = 4 e^{2π Im ζ} (sinh²(π Im ζ) + sin²(π Re ζ))`. -/
lemma norm_one_sub_exp_neg_sq (ζ : ℂ) :
    ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * ζ))‖ ^ 2
      = 4 * Real.exp (2 * Real.pi * ζ.im) *
        (Real.sinh (Real.pi * ζ.im) ^ 2 + Real.sin (Real.pi * ζ.re) ^ 2) := by
  have hb := norm_sq_one_sub_exp_two_pi_I_mul (-ζ)
  have harg : 2 * (Real.pi : ℂ) * Complex.I * (-ζ) = -(2 * Real.pi * Complex.I * ζ) := by ring
  rw [harg, Complex.neg_im, Complex.neg_re] at hb
  rw [hb, show -2 * Real.pi * (-ζ.im) = 2 * Real.pi * ζ.im by ring,
    one_sub_exp_two_pi_sq, show Real.pi * (-ζ.re) = -(Real.pi * ζ.re) by ring, Real.sin_neg]
  ring

/-- `4 y² ≤ sinh²(π y)`: `sinh` dominates its argument and `π > 2`. -/
lemma four_mul_sq_le_sinh_pi_sq (y : ℝ) : 4 * y ^ 2 ≤ Real.sinh (Real.pi * y) ^ 2 := by
  have habs : |Real.sinh (Real.pi * y)| = Real.sinh (Real.pi * |y|) := by
    rcases le_or_gt 0 y with hy | hy
    · have hpos : 0 ≤ Real.sinh (Real.pi * y) :=
        le_trans (by positivity) (Real.self_le_sinh_iff.mpr (by positivity))
      rw [abs_of_nonneg hy, abs_of_nonneg hpos]
    · have hneg : Real.sinh (Real.pi * y) < 0 := by
        have h := Real.sinh_lt_sinh.mpr (show Real.pi * y < 0 by nlinarith [Real.pi_pos, hy])
        rwa [Real.sinh_zero] at h
      rw [abs_of_neg hy, abs_of_neg hneg,
        show Real.pi * (-y) = -(Real.pi * y) by ring, Real.sinh_neg]
  have h1 : Real.pi * |y| ≤ Real.sinh (Real.pi * |y|) :=
    Real.self_le_sinh_iff.mpr (by positivity)
  have h2 : (Real.pi * |y|) ^ 2 ≤ Real.sinh (Real.pi * y) ^ 2 := by
    rw [← habs] at h1
    have h3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Real.pi * |y|) h1 2
    rwa [sq_abs] at h3
  have h4 : 4 * y ^ 2 ≤ (Real.pi * |y|) ^ 2 := by
    have hπ : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    rw [mul_pow, sq_abs]
    nlinarith [hπ, sq_nonneg y]
  linarith

/-- The lattice `ℤ/α` is the `α`-preimage of `ℤ`: the distance to it is the distance to `ℤ` in
`α w`-coordinates, divided by `‖α‖`. -/
lemma iInf_dist_div_eq {α w : ℂ} (hα : α ≠ 0) :
    (⨅ k : ℤ, dist w ((k : ℂ) / α))
      = (⨅ k : ℤ, dist (α * w) (k : ℂ)) / ‖α‖ := by
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hterm : ∀ k : ℤ, dist w ((k : ℂ) / α) = dist (α * w) (k : ℂ) / ‖α‖ := by
    intro k
    have hmul : α * (w - (k : ℂ) / α) = α * w - (k : ℂ) := by
      rw [mul_sub, mul_div_assoc', mul_div_cancel_left₀ _ hα]
    rw [dist_eq_norm, dist_eq_norm, ← hmul, norm_mul]
    rw [mul_div_cancel_left₀ _ hαpos.ne']
  obtain ⟨m, _hm1, hm2⟩ := iInf_dist_eq_norm_sub_round (α * w)
  have hbdd : BddBelow (Set.range (fun j : ℤ => dist (α * w) (j : ℂ))) :=
    ⟨0, by rintro _ ⟨j, rfl⟩; exact dist_nonneg⟩
  refine le_antisymm ?_ ?_
  · have h : (⨅ k : ℤ, dist w ((k : ℂ) / α)) ≤ dist w ((m : ℂ) / α) :=
      ciInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact dist_nonneg⟩ m
    rwa [hterm m, dist_eq_norm, ← hm2] at h
  · refine le_ciInf (fun k : ℤ => ?_)
    rw [hterm k]
    exact div_le_div_of_nonneg_right (ciInf_le hbdd k) (norm_nonneg α)

theorem tauC_norm_mul_exp_le {σ α : ℂ} (hα : α ≠ 0)
    (hσs : ‖σ‖ ≤ 8 * Real.pi * ‖α‖) :
    ∀ w : ℂ, ‖Work.Pert.tauC σ α w‖ * Real.exp (Real.pi * (α * w).im) ≤
      4 * Real.pi ^ 2 / (⨅ k : ℤ, dist w ((k : ℂ) / α)) := by
  intro w
  set L : ℝ := ⨅ k : ℤ, dist w ((k : ℂ) / α) with hLdef
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hLnn : 0 ≤ L := by
    rw [hLdef]
    exact le_ciInf (fun k : ℤ => dist_nonneg)
  have hLd : L = (⨅ k : ℤ, dist (α * w) (k : ℂ)) / ‖α‖ := by
    rw [hLdef]
    exact iInf_dist_div_eq hα
  by_cases hL0 : L = 0
  · -- Degenerate case: `w` is a lattice point, `τ_f w = 0` and the right side is `0`.
    have hE : Complex.exp (-(2 * Real.pi * Complex.I * α * w)) = 1 :=
      tauC_exp_one_of_iInf_eq_zero hα (by rw [← hLdef]; exact hL0)
    rw [hL0]
    simp [Work.Pert.tauC, hE]
  · have hLpos : 0 < L := lt_of_le_of_ne hLnn (Ne.symm hL0)
    -- nearest lattice point `m` of `α w`
    obtain ⟨m, _hm1, hm2⟩ := iInf_dist_eq_norm_sub_round (α * w)
    set d : ℝ := ‖α * w - (m : ℂ)‖ with hddef
    have hd_eq : d = ⨅ k : ℤ, dist (α * w) (k : ℂ) := by
      rw [hddef]
      exact hm2.symm
    have hLd' : L = d / ‖α‖ := by
      rw [hLd, ← hd_eq]
    have hdpos : 0 < d := by
      have h1 : 0 < d / ‖α‖ := by rw [← hLd']; exact hLpos
      rcases div_pos_iff.mp h1 with h | h
      · exact h.1
      · exact absurd h.2 (not_lt.mpr (norm_nonneg α))
    have hdL : d = L * ‖α‖ := by
      rw [hLd', div_mul_cancel₀ _ hαpos.ne']
    -- `sin²(π Re ζ) ≥ 4 dist(Re ζ, ℤ)²` with `dist(Re ζ, ℤ) = |Re ζ - m|`
    have hsin : 4 * ((α * w).re - (m : ℝ)) ^ 2 ≤ Real.sin (Real.pi * (α * w).re) ^ 2 := by
      have hlat : ∀ k : ℤ,
          ((α * w).re - (m : ℝ)) ^ 2 ≤ ((α * w).re - (k : ℝ)) ^ 2 + (0 : ℝ) ^ 2 := by
        intro k
        have hbdd : BddBelow (Set.range (fun j : ℤ => dist (α * w) (j : ℂ))) :=
          ⟨0, by rintro _ ⟨j, rfl⟩; exact dist_nonneg⟩
        have hle : ‖α * w - (m : ℂ)‖ ≤ ‖α * w - (k : ℂ)‖ := by
          have h := ciInf_le hbdd k
          rwa [← hd_eq, hddef, dist_eq_norm] at h
        have hsq : ‖α * w - (m : ℂ)‖ ^ 2 ≤ ‖α * w - (k : ℂ)‖ ^ 2 := by
          nlinarith [hle, norm_nonneg (α * w - (m : ℂ)), norm_nonneg (α * w - (k : ℂ))]
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at hsq
        simp only [Complex.sub_re, Complex.sub_im, Complex.intCast_re, Complex.intCast_im,
          sub_zero] at hsq
        linarith [hsq]
      have h3 := sin_sq_pi_ge_of_lattice (P := (α * w).re) (T := 0)
        (δ := (α * w).re - (m : ℝ)) hlat
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, sub_zero, max_eq_right (sq_nonneg _)] at h3
      exact h3
    have hsinh : 4 * (α * w).im ^ 2 ≤ Real.sinh (Real.pi * (α * w).im) ^ 2 :=
      four_mul_sq_le_sinh_pi_sq ((α * w).im)
    -- the exact squared modulus of the denominator
    set D : ℝ := ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w))‖ with hDdef
    have hD2 : D ^ 2 = 4 * Real.exp (2 * Real.pi * (α * w).im) *
        (Real.sinh (Real.pi * (α * w).im) ^ 2 + Real.sin (Real.pi * (α * w).re) ^ 2) := by
      have h := norm_one_sub_exp_neg_sq (α * w)
      rw [show -(2 * Real.pi * Complex.I * (α * w))
          = -(2 * Real.pi * Complex.I * α * w) by ring] at h
      rw [hDdef]
      exact h
    have hdm : d ^ 2 = ((α * w).re - (m : ℝ)) ^ 2 + (α * w).im ^ 2 := by
      rw [hddef, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.intCast_re, Complex.intCast_im, sub_zero]
      ring
    have hexppos : (0 : ℝ) < Real.exp (2 * Real.pi * (α * w).im) := Real.exp_pos _
    have hDbound : 16 * Real.exp (2 * Real.pi * (α * w).im) * d ^ 2 ≤ D ^ 2 := by
      rw [hD2, hdm]
      have hsum : 4 * ((α * w).re - (m : ℝ)) ^ 2 + 4 * (α * w).im ^ 2
          ≤ Real.sinh (Real.pi * (α * w).im) ^ 2 + Real.sin (Real.pi * (α * w).re) ^ 2 := by
        linarith [hsin, hsinh]
      have hsumE := mul_le_mul_of_nonneg_left hsum hexppos.le
      nlinarith [hsumE]
    have hDge : 4 * Real.exp (Real.pi * (α * w).im) * d ≤ D := by
      have hsq : (4 * Real.exp (Real.pi * (α * w).im) * d) ^ 2 ≤ D ^ 2 := by
        have he : (4 * Real.exp (Real.pi * (α * w).im) * d) ^ 2
            = 16 * Real.exp (2 * Real.pi * (α * w).im) * d ^ 2 := by
          rw [show Real.exp (2 * Real.pi * (α * w).im)
              = Real.exp (Real.pi * (α * w).im) * Real.exp (Real.pi * (α * w).im) by
                rw [show 2 * Real.pi * (α * w).im
                    = Real.pi * (α * w).im + Real.pi * (α * w).im by ring, Real.exp_add]]
          ring
        rw [he]
        exact hDbound
      have h := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at h
      exact h
    have hden : 0 < 4 * Real.exp (Real.pi * (α * w).im) * d := by positivity
    calc ‖Work.Pert.tauC σ α w‖ * Real.exp (Real.pi * (α * w).im)
        = ‖σ‖ * Real.exp (Real.pi * (α * w).im) / D := by
          rw [Work.Pert.tauC, norm_div, hDdef]
          ring
      _ ≤ ‖σ‖ * Real.exp (Real.pi * (α * w).im)
            / (4 * Real.exp (Real.pi * (α * w).im) * d) :=
          div_le_div_of_nonneg_left (by positivity) hden hDge
      _ = ‖σ‖ / (4 * d) := by
          rw [mul_comm ‖σ‖ (Real.exp (Real.pi * (α * w).im)),
            show 4 * Real.exp (Real.pi * (α * w).im) * d
              = Real.exp (Real.pi * (α * w).im) * (4 * d) by ring,
            mul_div_mul_left _ _ (Real.exp_ne_zero _)]
      _ ≤ 8 * Real.pi * ‖α‖ / (4 * d) := div_le_div_of_nonneg_right hσs (by positivity)
      _ = 2 * Real.pi * ‖α‖ / d := by ring
      _ = 2 * Real.pi / L := by
          rw [hdL, mul_comm L ‖α‖,
            show 2 * Real.pi * ‖α‖ = ‖α‖ * (2 * Real.pi) by ring,
            mul_div_mul_left _ _ hαpos.ne']
      _ ≤ 4 * Real.pi ^ 2 / L := by
          apply div_le_div_of_nonneg_right _ hLpos.le
          nlinarith [Real.pi_gt_three]

end

end Work.Pert.PinAux
