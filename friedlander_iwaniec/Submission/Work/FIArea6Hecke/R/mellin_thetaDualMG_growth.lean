/-
# `Submission.Work.FIArea6Hecke.R.mellin_thetaDualMG_growth`

Growth of the Mellin transform of the weight-`k` dual theta kernel `thetaDualMG d χ k` on the
vertical strip `k/2 + 1/2 ≤ re t ≤ k/2 + R + 1`:

  `log ‖mellin (thetaDualMG d χ k) t‖ ≤ C · R · (log (R+2) + K)`.

## The argument

Write `f = thetaDualMG d χ k`, `σ = re t` and `Φ x = ‖f x‖ · x^(σ-1)`.  Since Mathlib's Mellin
transform is an integral over `(0,∞)`, the triangle inequality gives

  `‖mellin f t‖ ≤ ∫₀^∞ Φ`.

The integral is then split at `1` and, on the two pieces, the *two* decay properties of `f` are
used (both consequences of the Poisson transformation `thetaHol χ k (1/x) = x^{k+1}·f x`):

* **near `0`** (`Work.FIArea6Hecke.R.MGGrow.thetaDualMG_near_zero_bound`) one has
  `‖f x‖ ≤ C x^{-(k+1)} e^{-π/x}` for `x ≤ 1`; since `σ - 1 ≥ k/2 - 1/2`, the integrand is at most
  `C x^{-k/2-3/2} e^{-π/x} ≤ K x^{k/2-1/2}`, the last inequality being the elementary supremum
  bound `t^a e^{-bt} ≤ (a/(be))^a` (`MGGrow.rpow_mul_exp_neg_le`) applied with `t = π/x`.  The
  resulting integral `∫₀¹ x^{k/2-1/2} = 2/(k+1)` is **independent of `σ` and `R`**.
* **near `∞`** (`Work.FIArea6Hecke.R.MGGrow.thetaDualMG_exp_decay_inf`) one has
  `‖f x‖ ≤ M e^{-cx}` for `x ≥ 1`, `c = π/(16d²)`.  On `[1,16d²]` this is a plain bound, and on
  `[16d²,∞)` the supremum bound turns `e^{-cx}x^{k/2+R}` into `(2(k/2+R)/(ce))^{k/2+R}·e^{-cx/2}`,
  whose integral is again elementary.  This is where the `R`-dependence enters: through the power
  `(k/2+R)^{k/2+R}`, which is why the final estimate has the shape `R·log(R+2)`.

The final numerical bookkeeping — that the logarithm of the resulting three-term sum is at most
`C·R·(log(R+2)+K)` — is the (independent, Mathlib-only) lemma
`Work.FIArea6Hecke.R.MGGrow.log_growth_arith`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaHol_one_div_dual
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaDualM_decay
import Submission.Work.FIArea5.S16Hecke.thetaHol_bound_of_summable
import Submission.Work.FIArea6Hecke.R.LamRightHalf.Defs
import Submission.Work.FIArea6Hecke.R.MGGrow.thetaDualMG_exp_decay_inf
import Submission.Work.FIArea6Hecke.R.MGGrow.thetaDualMG_near_zero_bound
import Submission.Work.FIArea6Hecke.R.MGGrow.log_growth_arith
import Submission.Work.FIArea6Hecke.R.MGGrow.rpow_mul_exp_neg_le

set_option maxHeartbeats 1600000
set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-! ### Elementary estimates -/

/-- The Mellin transform of `f` is dominated by the integral of the modulus of its integrand. -/
private lemma mellin_norm_le_integral (f : ℝ → ℂ) (t : ℂ) :
    ‖mellin f t‖ ≤ ∫ x : ℝ in Set.Ioi 0, ‖f x‖ * x ^ (t.re - 1) := by
  have h1 : ‖mellin f t‖ ≤ ∫ x : ℝ in Set.Ioi 0, ‖(x : ℂ) ^ (t - 1) • f x‖ := by
    rw [mellin]
    exact norm_integral_le_integral_norm _
  refine h1.trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re]
  ring

/-- Near the origin, `e^{-π/x}` is dominated by a polynomial of degree `k+1`. -/
private lemma exp_neg_pi_div_le (k : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.exp (-Real.pi / x) ≤
      ((((k : ℝ) + 1) / Real.exp 1) ^ ((k : ℝ) + 1) * (1 / Real.pi) ^ ((k : ℝ) + 1)) *
        x ^ ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hπx : 0 < Real.pi / x := by positivity
  have h := MGGrow.rpow_mul_exp_neg_le (a := (k : ℝ) + 1) (b := 1) (t := Real.pi / x)
    hk one_pos hπx
  simp only [one_mul] at h
  -- h : (π/x)^(k+1) * exp (-(π/x)) ≤ ((k+1)/exp 1)^(k+1)
  have hone : (Real.pi / x) ^ ((k : ℝ) + 1) * (x / Real.pi) ^ ((k : ℝ) + 1) = 1 := by
    rw [← Real.mul_rpow hπx.le (by positivity)]
    have h2 : Real.pi / x * (x / Real.pi) = 1 := by field_simp
    rw [h2, Real.one_rpow]
  have h3 : Real.exp (-(Real.pi / x)) ≤
      (((k : ℝ) + 1) / Real.exp 1) ^ ((k : ℝ) + 1) * (x / Real.pi) ^ ((k : ℝ) + 1) := by
    calc Real.exp (-(Real.pi / x))
        = Real.exp (-(Real.pi / x)) * ((Real.pi / x) ^ ((k : ℝ) + 1) *
            (x / Real.pi) ^ ((k : ℝ) + 1)) := by rw [hone, mul_one]
      _ = (Real.exp (-(Real.pi / x)) * (Real.pi / x) ^ ((k : ℝ) + 1)) *
            (x / Real.pi) ^ ((k : ℝ) + 1) := by ring
      _ ≤ (((k : ℝ) + 1) / Real.exp 1) ^ ((k : ℝ) + 1) * (x / Real.pi) ^ ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (by rw [mul_comm]; exact h)
            (Real.rpow_nonneg (by positivity) _)
  have hxπ : (x / Real.pi) ^ ((k : ℝ) + 1)
      = (1 / Real.pi) ^ ((k : ℝ) + 1) * x ^ ((k : ℝ) + 1) := by
    rw [div_eq_mul_inv, one_div, Real.mul_rpow hx.le (by positivity),
      Real.inv_rpow Real.pi_pos.le]
    ring
  calc Real.exp (-Real.pi / x) = Real.exp (-(Real.pi / x)) := by
        congr 1
        ring
    _ ≤ (((k : ℝ) + 1) / Real.exp 1) ^ ((k : ℝ) + 1) * (x / Real.pi) ^ ((k : ℝ) + 1) := h3
    _ = (((k : ℝ) + 1) / Real.exp 1) ^ ((k : ℝ) + 1) * (1 / Real.pi) ^ ((k : ℝ) + 1) *
          x ^ ((k : ℝ) + 1) := by rw [hxπ]; ring

/-- Integrability of `x ↦ x^a` on `(0,1]` for `a > -1`. -/
private lemma integrableOn_rpow_Ioc_zero_one {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioc 0 1) := by
  have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) ha
  rwa [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h

/-- Integrability of `x ↦ x^a` on `(1,X]` for `a > -1`. -/
private lemma integrableOn_rpow_Ioc {a X : ℝ} (hX : 1 ≤ X) (ha : -1 < a) :
    IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioc 1 X) := by
  have h := intervalIntegral.intervalIntegrable_rpow' (a := (1 : ℝ)) (b := X) ha
  rwa [intervalIntegrable_iff, Set.uIoc_of_le hX] at h

/-- `∫₀¹ x^a = 1/(a+1)` for `a > -1`. -/
private lemma integral_Ioc_zero_one_rpow {a : ℝ} (ha : -1 < a) :
    ∫ x : ℝ in Set.Ioc 0 1, x ^ a = 1 / (a + 1) := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_rpow (Or.inl ha), Real.one_rpow, Real.zero_rpow (by linarith : a + 1 ≠ 0),
    sub_zero]

/-- `∫₁^X x^a ≤ X^(a+1)` for `a ≥ 0` and `X ≥ 1`. -/
private lemma integral_Ioc_one_le_rpow {a X : ℝ} (ha : 0 ≤ a) (hX : 1 ≤ X) :
    ∫ x : ℝ in Set.Ioc 1 X, x ^ a ≤ X ^ (a + 1) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  rw [← intervalIntegral.integral_of_le hX, integral_rpow (Or.inl (by linarith)),
    Real.one_rpow, div_le_iff₀ (by linarith : (0 : ℝ) < a + 1)]
  nlinarith [Real.rpow_pos_of_pos hX0 (a + 1), mul_nonneg (Real.rpow_pos_of_pos hX0 (a + 1)).le ha]

/-- `∫_T^∞ e^{-bx} dx = e^{-bT}/b` for `b > 0`. -/
private lemma integral_exp_neg_mul_Ioi {b T : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in Set.Ioi T, Real.exp (-b * x) = Real.exp (-b * T) / b := by
  have h := integral_comp_mul_left_Ioi' (fun u : ℝ => Real.exp (-u)) T hb
  rw [integral_exp_neg_Ioi (b * T), smul_eq_mul] at h
  rw [show (fun x : ℝ => Real.exp (-b * x)) = fun x : ℝ => Real.exp (-(b * x)) from by
    funext x
    rw [neg_mul]]
  rw [show Real.exp (-b * T) = Real.exp (-(b * T)) from by rw [neg_mul]]
  rw [eq_div_iff hb.ne', mul_comm]
  exact h

/-! ### The main theorem -/

theorem mellin_thetaDualMG_growth (d : ℕ) (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) (k : ℕ)
    (hU : Work.FIArea5.S16Hecke.unitSum chi k ≠ 0)
    (h0 : k = 0 → Work.FIArea5.S16Hecke.gaussSum d chi 0 = 0) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ t : ℂ,
      (k : ℝ) / 2 + 1 / 2 ≤ t.re → t.re ≤ (k : ℝ) / 2 + R + 1 →
      Real.log ‖mellin (thetaDualMG d chi k) t‖ ≤ C * R * (Real.log (R + 2) + K) := by
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := fun z => hchi.1.2.2.1 z
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  obtain ⟨Cn, hCnpos, hnz⟩ := MGGrow.thetaDualMG_near_zero_bound d hd hchi k hU
  obtain ⟨Md, hMdpos, Mdec⟩ := MGGrow.thetaDualMG_exp_decay_inf d hd hb k h0
  -- decay rate at `∞` and the rescaling constant of the near-zero bound
  set cc : ℝ := Real.pi / (16 * (d : ℝ) ^ 2) with hcc
  have hccpos : 0 < cc := by rw [hcc]; positivity
  set c1 : ℝ := 16 * (d : ℝ) ^ 2 with hc1
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  have hc1ge : 1 ≤ c1 := by
    rw [hc1]
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  -- the constants of the final answer
  set Khead : ℝ := Cn * (((k : ℝ) + 1) / Real.exp 1) ^ ((k : ℝ) + 1) *
    (1 / Real.pi) ^ ((k : ℝ) + 1) with hKhead
  have hKheadpos : 0 < Khead := by rw [hKhead]; positivity
  set A : ℝ := Khead * (1 / ((k : ℝ) / 2 + 1 / 2)) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set Mf : ℝ := Md * c1 ^ ((k : ℝ) / 2 + 1) with hMf
  have hMfpos : 0 < Mf := by rw [hMf]; positivity
  set A0 : ℝ := Md * (2 / cc) * Real.exp (-(Real.pi / 2)) with hA0
  have hA0pos : 0 < A0 := by rw [hA0]; positivity
  set c2 : ℝ := max 1 (2 / (cc * Real.exp 1)) with hc2
  have hc2ge : 1 ≤ c2 := le_max_left _ _
  have hc2pos : 0 < c2 := lt_of_lt_of_le one_pos hc2ge
  obtain ⟨C, K, hCpos, hK0, harith⟩ :=
    MGGrow.log_growth_arith k (A := A) (Mf := Mf) (A₀ := A0) (c₁ := c1) (c₂ := c2)
      hApos hMfpos hA0pos hc1ge hc2ge
  refine ⟨C, K, hCpos, hK0, ?_⟩
  intro R hR t ht1 ht2
  set A2 : ℝ := (k : ℝ) / 2 + R with hA2
  have hA2pos : 0 < A2 := by rw [hA2]; linarith
  set Phi : ℝ → ℝ := fun x => ‖thetaDualMG d chi k x‖ * x ^ (t.re - 1) with hPhi
  have hmain : ‖mellin (thetaDualMG d chi k) t‖ ≤ A + Mf * c1 ^ R + A0 * (A2 ^ A2 * c2 ^ A2) := by
    refine le_trans (mellin_norm_le_integral (thetaDualMG d chi k) t) ?_
    by_cases hint : IntegrableOn Phi (Set.Ioi 0)
    · -- the integrable case: split the integral and bound each piece
      have hsub1 : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi 0 := fun x hx => hx.1
      have hsub2 : Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢; linarith
      have hsub3 : Set.Ioc (1 : ℝ) c1 ⊆ Set.Ioi 0 := fun x hx => by
        simp only [Set.mem_Ioc, Set.mem_Ioi] at hx ⊢; linarith [hx.1]
      have hsub4 : Set.Ioi c1 ⊆ Set.Ioi 0 := fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢; linarith [hc1ge]
      have hsplit : ∫ x : ℝ in Set.Ioi 0, Phi x
          = (∫ x : ℝ in Set.Ioc 0 1, Phi x) + ∫ x : ℝ in Set.Ioi 1, Phi x := by
        rw [show Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 from
          (Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)).symm]
        exact setIntegral_union (disjoint_left.mpr fun x hx1 hx2 =>
            absurd hx2 (not_lt.mpr hx1.2)) measurableSet_Ioi
          (hint.mono_set hsub1) (hint.mono_set hsub2)
      have hhead : ∫ x : ℝ in Set.Ioc 0 1, Phi x ≤ A := by
        have hpoint : ∀ x ∈ Set.Ioc 0 1, Phi x ≤ Khead * x ^ ((k : ℝ) / 2 - 1 / 2) := by
          intro x hx
          obtain ⟨hx0, hx1⟩ := hx
          have hD2 := hnz x hx0 hx1
          have hM := exp_neg_pi_div_le k hx0
          have hxx : x ^ (-((k : ℝ) + 1)) * x ^ ((k : ℝ) + 1) = 1 := by
            rw [← Real.rpow_add hx0]
            simp
          have hf : ‖thetaDualMG d chi k x‖ ≤ Khead := by
            refine le_trans hD2 ?_
            calc Cn * x ^ (-((k : ℝ) + 1)) * Real.exp (-Real.pi / x)
                ≤ Cn * x ^ (-((k : ℝ) + 1)) *
                    ((((k : ℝ) + 1) / Real.exp 1) ^ ((k : ℝ) + 1) *
                      (1 / Real.pi) ^ ((k : ℝ) + 1) * x ^ ((k : ℝ) + 1)) :=
                  mul_le_mul_of_nonneg_left hM (by positivity)
              _ = Khead := by
                  rw [hKhead]
                  calc Cn * x ^ (-((k : ℝ) + 1)) *
                        ((((k : ℝ) + 1) / Real.exp 1) ^ ((k : ℝ) + 1) *
                          (1 / Real.pi) ^ ((k : ℝ) + 1) * x ^ ((k : ℝ) + 1))
                      = Cn * ((((k : ℝ) + 1) / Real.exp 1) ^ ((k : ℝ) + 1) *
                            (1 / Real.pi) ^ ((k : ℝ) + 1)) *
                          (x ^ (-((k : ℝ) + 1)) * x ^ ((k : ℝ) + 1)) := by ring
                    _ = Cn * (((k : ℝ) + 1) / Real.exp 1) ^ ((k : ℝ) + 1) *
                          (1 / Real.pi) ^ ((k : ℝ) + 1) := by
                        rw [hxx, mul_one]
                        ring
          calc Phi x = ‖thetaDualMG d chi k x‖ * x ^ (t.re - 1) := rfl
            _ ≤ Khead * x ^ (t.re - 1) := mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg hx0.le _)
            _ ≤ Khead * x ^ ((k : ℝ) / 2 - 1 / 2) :=
                mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)) hKheadpos.le
        have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 1)] Phi := by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (le_of_lt hx.1) _)
        have hle : Phi ≤ᵐ[volume.restrict (Set.Ioc 0 1)]
            (fun x : ℝ => Khead * x ^ ((k : ℝ) / 2 - 1 / 2)) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact hpoint x hx
        have hintK : IntegrableOn (fun x : ℝ => Khead * x ^ ((k : ℝ) / 2 - 1 / 2))
            (Set.Ioc 0 1) :=
          (integrableOn_rpow_Ioc_zero_one (a := (k : ℝ) / 2 - 1 / 2)
            (by linarith [hk0])).const_mul Khead
        calc ∫ x : ℝ in Set.Ioc 0 1, Phi x
            ≤ ∫ x : ℝ in Set.Ioc 0 1, Khead * x ^ ((k : ℝ) / 2 - 1 / 2) :=
              integral_mono_of_nonneg hnn hintK hle
          _ = Khead * (1 / ((k : ℝ) / 2 - 1 / 2 + 1)) := by
              rw [integral_const_mul,
                integral_Ioc_zero_one_rpow (a := (k : ℝ) / 2 - 1 / 2) (by linarith [hk0])]
          _ = A := by
              rw [show (k : ℝ) / 2 - 1 / 2 + 1 = (k : ℝ) / 2 + 1 / 2 by ring, hA]
      have htail : ∫ x : ℝ in Set.Ioi 1, Phi x ≤ Mf * c1 ^ R + A0 * (A2 ^ A2 * c2 ^ A2) := by
        have hsplit2 : ∫ x : ℝ in Set.Ioi 1, Phi x
            = (∫ x : ℝ in Set.Ioc 1 c1, Phi x) + ∫ x : ℝ in Set.Ioi c1, Phi x := by
          rw [show Set.Ioi (1 : ℝ) = Set.Ioc 1 c1 ∪ Set.Ioi c1 from
            (Ioc_union_Ioi_eq_Ioi hc1ge).symm]
          exact setIntegral_union (disjoint_left.mpr fun x hx1 hx2 =>
              absurd hx2 (not_lt.mpr hx1.2)) measurableSet_Ioi
            (hint.mono_set hsub3) (hint.mono_set hsub4)
        have hpart1 : ∫ x : ℝ in Set.Ioc 1 c1, Phi x ≤ Mf * c1 ^ R := by
          have hpoint1 : ∀ x ∈ Set.Ioc 1 c1, Phi x ≤ Md * x ^ A2 := by
            intro x hx
            obtain ⟨hx1, _⟩ := hx
            have hx0 : (0 : ℝ) < x := by linarith
            have hdec := Mdec x (le_of_lt hx1)
            have hexp : Real.exp (-cc * x) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              nlinarith [hccpos]
            have hrpow : x ^ (t.re - 1) ≤ x ^ A2 :=
              Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) (by rw [hA2]; linarith)
            calc Phi x = ‖thetaDualMG d chi k x‖ * x ^ (t.re - 1) := rfl
              _ ≤ (Md * Real.exp (-cc * x)) * x ^ (t.re - 1) :=
                  mul_le_mul_of_nonneg_right hdec (Real.rpow_nonneg hx0.le _)
              _ = Md * (Real.exp (-cc * x) * x ^ (t.re - 1)) := by ring
              _ ≤ Md * (1 * x ^ A2) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul hexp hrpow (Real.rpow_nonneg hx0.le _) zero_le_one) hMdpos.le
              _ = Md * x ^ A2 := by ring
          have hnn1 : 0 ≤ᵐ[volume.restrict (Set.Ioc 1 c1)] Phi := by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
            exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by linarith [hx.1]) _)
          have hle1 : Phi ≤ᵐ[volume.restrict (Set.Ioc 1 c1)] (fun x : ℝ => Md * x ^ A2) := by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
            exact hpoint1 x hx
          have hintM1 : IntegrableOn (fun x : ℝ => Md * x ^ A2) (Set.Ioc 1 c1) :=
            (integrableOn_rpow_Ioc (X := c1) hc1ge (by rw [hA2]; linarith)).const_mul Md
          calc ∫ x : ℝ in Set.Ioc 1 c1, Phi x ≤ ∫ x : ℝ in Set.Ioc 1 c1, Md * x ^ A2 :=
                integral_mono_of_nonneg hnn1 hintM1 hle1
            _ = Md * ∫ x : ℝ in Set.Ioc 1 c1, x ^ A2 := by rw [integral_const_mul]
            _ ≤ Md * c1 ^ (A2 + 1) :=
                mul_le_mul_of_nonneg_left (integral_Ioc_one_le_rpow hA2pos.le hc1ge) hMdpos.le
            _ = Mf * c1 ^ R := by
                rw [hMf, show A2 + 1 = (k : ℝ) / 2 + 1 + R by rw [hA2]; ring,
                  Real.rpow_add hc1pos]
                ring
        have hpart2 : ∫ x : ℝ in Set.Ioi c1, Phi x ≤ A0 * (A2 ^ A2 * c2 ^ A2) := by
          have hpoint2 : ∀ x ∈ Set.Ioi c1,
              Phi x ≤ Md * (2 * A2 / (cc * Real.exp 1)) ^ A2 * Real.exp (-(cc / 2) * x) := by
            intro x hx
            have hxge1 : (1 : ℝ) ≤ x := le_trans hc1ge (le_of_lt (Set.mem_Ioi.mp hx))
            have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hxge1
            have hdec := Mdec x hxge1
            have hrpow : x ^ (t.re - 1) ≤ x ^ A2 :=
              Real.rpow_le_rpow_of_exponent_le hxge1 (by rw [hA2]; linarith)
            have hsup' : Real.exp (-(cc / 2) * x) * x ^ A2
                ≤ (2 * A2 / (cc * Real.exp 1)) ^ A2 := by
              have h := MGGrow.rpow_mul_exp_neg_le (a := A2) (b := cc / 2) (t := x)
                hA2pos (by positivity) hx0
              have hexp' : Real.exp (-(cc / 2) * x) = Real.exp (-((cc / 2) * x)) := by
                congr 1
                rw [neg_mul]
              calc Real.exp (-(cc / 2) * x) * x ^ A2
                  = x ^ A2 * Real.exp (-((cc / 2) * x)) := by rw [hexp']; ring
                _ ≤ (A2 / ((cc / 2) * Real.exp 1)) ^ A2 := h
                _ = (2 * A2 / (cc * Real.exp 1)) ^ A2 := by
                    congr 1
                    field_simp
            have hexp3 : Real.exp (-cc * x) ≤ Real.exp (-(cc / 2) * x) := by
              rw [Real.exp_le_exp]
              nlinarith [hx0]
            have hsplit_exp : Real.exp (-cc * x)
                = Real.exp (-(cc / 2) * x) * Real.exp (-(cc / 2) * x) := by
              rw [← Real.exp_add]
              congr 1
              ring
            calc Phi x = ‖thetaDualMG d chi k x‖ * x ^ (t.re - 1) := rfl
              _ ≤ (Md * Real.exp (-cc * x)) * x ^ (t.re - 1) :=
                  mul_le_mul_of_nonneg_right hdec (Real.rpow_nonneg hx0.le _)
              _ = Md * (Real.exp (-(cc / 2) * x) *
                    (Real.exp (-(cc / 2) * x) * x ^ (t.re - 1))) := by
                  rw [hsplit_exp]
                  ring
              _ ≤ Md * (Real.exp (-(cc / 2) * x) *
                    (Real.exp (-(cc / 2) * x) * x ^ A2)) := by
                  refine mul_le_mul_of_nonneg_left ?_ hMdpos.le
                  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
                  exact mul_le_mul_of_nonneg_left hrpow (Real.exp_nonneg _)
              _ = Md * ((Real.exp (-(cc / 2) * x) * x ^ A2) * Real.exp (-(cc / 2) * x)) := by
                  ring
              _ ≤ Md * ((2 * A2 / (cc * Real.exp 1)) ^ A2 * Real.exp (-(cc / 2) * x)) := by
                  refine mul_le_mul_of_nonneg_left ?_ hMdpos.le
                  exact mul_le_mul_of_nonneg_right hsup' (Real.exp_nonneg _)
              _ = Md * (2 * A2 / (cc * Real.exp 1)) ^ A2 * Real.exp (-(cc / 2) * x) := by
                  ring
          have hnn2 : 0 ≤ᵐ[volume.restrict (Set.Ioi c1)] Phi := by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            exact mul_nonneg (norm_nonneg _)
              (Real.rpow_nonneg (by linarith [hc1ge, le_of_lt (Set.mem_Ioi.mp hx)]) _)
          have hle2 : Phi ≤ᵐ[volume.restrict (Set.Ioi c1)]
              (fun x : ℝ => Md * (2 * A2 / (cc * Real.exp 1)) ^ A2 * Real.exp (-(cc / 2) * x)) := by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            exact hpoint2 x hx
          have hintM2 : IntegrableOn
              (fun x : ℝ => Md * (2 * A2 / (cc * Real.exp 1)) ^ A2 * Real.exp (-(cc / 2) * x))
              (Set.Ioi c1) :=
            (exp_neg_integrableOn_Ioi c1 (by positivity : (0 : ℝ) < cc / 2)).const_mul _
          calc ∫ x : ℝ in Set.Ioi c1, Phi x
              ≤ ∫ x : ℝ in Set.Ioi c1,
                  Md * (2 * A2 / (cc * Real.exp 1)) ^ A2 * Real.exp (-(cc / 2) * x) :=
                integral_mono_of_nonneg hnn2 hintM2 hle2
            _ = Md * (2 * A2 / (cc * Real.exp 1)) ^ A2 *
                  ∫ x : ℝ in Set.Ioi c1, Real.exp (-(cc / 2) * x) := by
                rw [integral_const_mul]
            _ = Md * (2 * A2 / (cc * Real.exp 1)) ^ A2 *
                  (Real.exp (-(cc / 2) * c1) / (cc / 2)) := by
                rw [integral_exp_neg_mul_Ioi (b := cc / 2) (T := c1) (by positivity)]
            _ = A0 * (2 * A2 / (cc * Real.exp 1)) ^ A2 := by
                have hcT : cc / 2 * c1 = Real.pi / 2 := by
                  rw [hcc, hc1]
                  field_simp
                rw [hA0, neg_mul, hcT]
                field_simp
            _ ≤ A0 * (A2 ^ A2 * c2 ^ A2) := by
                refine mul_le_mul_of_nonneg_left ?_ hA0pos.le
                rw [show 2 * A2 / (cc * Real.exp 1) = (2 / (cc * Real.exp 1)) * A2 by ring,
                  Real.mul_rpow (by positivity) hA2pos.le]
                calc (2 / (cc * Real.exp 1)) ^ A2 * A2 ^ A2
                    ≤ c2 ^ A2 * A2 ^ A2 :=
                      mul_le_mul_of_nonneg_right
                        (Real.rpow_le_rpow (by positivity) (by rw [hc2]; exact le_max_right _ _)
                          hA2pos.le) (Real.rpow_nonneg hA2pos.le _)
                  _ = A2 ^ A2 * c2 ^ A2 := by ring
        rw [hsplit2]
        linarith
      rw [hsplit]
      linarith
    · -- otherwise the Bochner integral vanishes, and the bound is trivial
      rw [MeasureTheory.integral_undef hint]
      have h1 : 0 < Mf * c1 ^ R := mul_pos hMfpos (Real.rpow_pos_of_pos hc1pos R)
      have h2 : 0 < A0 * (A2 ^ A2 * c2 ^ A2) :=
        mul_pos hA0pos (mul_pos (Real.rpow_pos_of_pos hA2pos A2) (Real.rpow_pos_of_pos hc2pos A2))
      linarith
  rcases eq_or_ne ‖mellin (thetaDualMG d chi k) t‖ 0 with hz | hz
  · rw [hz, Real.log_zero]
    have h1 : (0 : ℝ) ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ Real.log (R + 2) + K := by linarith
    exact mul_nonneg (mul_nonneg hCpos.le (le_trans zero_le_one hR)) h2
  · have hpos : 0 < ‖mellin (thetaDualMG d chi k) t‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    refine le_trans (Real.log_le_log hpos hmain) ?_
    have harg : A + Mf * c1 ^ R + A0 * (A2 ^ A2 * c2 ^ A2)
        = A + Mf * c1 ^ R + A0 * A2 ^ A2 * c2 ^ A2 := by ring
    rw [harg, hA2]
    exact harith R hR

end

end Work.FIArea6Hecke.R
