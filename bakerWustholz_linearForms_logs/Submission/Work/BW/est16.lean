import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.split_aux
import Submission.Work.BW.est13p
import Submission.Work.BW.est14
import Submission.Work.BW.est15
import Submission.Work.BW.num_T
import Submission.Work.BW.num_kum
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.est16_half_arith
import Submission.Work.BW.est16_main_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester): BW analytic_core split, node `est16`
(BW (16) at descent level `J`, p. 45 and p. 58). -/

namespace Work.BW

/-! ## `est16`: BW (16) at descent level `J`

BW (16) is assembled here from the three estimates of BW §14–15 at level `J`:
`est13p` (13) bounds `f(z)` from above, `est14` (14) bounds `f(s) − g(s)`, and `est15` (15) bounds
`g(s)` from below (Liouville).  The bridge is the argument of BW p. 44–45:

* `est15` at `s` and `est14` at `s`, together with the arithmetic margin between the two
  (the `−9·2^r SD` of (14) against the `+2·2^r SD` of (15)), give `‖g(s)‖ ≤ 2‖f(s)‖`;
* `est13` at `z` against `est15` at `s` then gives the claim, the `log 2` produced by the
  factor `2` being absorbed by `log 2 ≤ 0·001 SD` (`num_kum`).

The two real-arithmetic bookkeeping lemmas are the sibling modules `est16_half_arith` and
`est16_main_arith`; `est16_glue` below is the analytic `exp`/norm shuffling. -/

/-- Norm-and-`exp` glue: from `‖u‖ ≤ e^{A+C}`, `‖v−w‖ ≤ e^{A+X}`, `e^{A−Z} ≤ ‖w‖` and the two
exponent inequalities `e^{A+X}·2 ≤ e^{A−Z}`, `C+Z+log 2 ≤ G`, deduce `‖u‖ ≤ ‖v‖ e^G`. -/
theorem est16_glue {A X Z C G : ℝ} {u v w : ℂ}
    (h13 : ‖u‖ ≤ Real.exp (A + C)) (h14 : ‖v - w‖ ≤ Real.exp (A + X))
    (h15 : Real.exp (A - Z) ≤ ‖w‖) (hα : Real.exp (A + X) * 2 ≤ Real.exp (A - Z))
    (hβ : C + Z + Real.log 2 ≤ G) :
    ‖u‖ ≤ ‖v‖ * Real.exp G := by
  have h2log : (2:ℝ) = Real.exp (Real.log 2) := by rw [Real.exp_log]; norm_num
  -- (14) at `s` against (15) at `s`: `‖g(s)‖ ≤ 2‖f(s)‖`
  have h2 : Real.exp (A - Z) ≤ ‖v‖ * 2 := by
    have hwv : (w - v) + v = w := by ring
    have hw : ‖w‖ ≤ Real.exp (A + X) + ‖v‖ := by
      calc ‖w‖ = ‖(w - v) + v‖ := by rw [hwv]
        _ ≤ ‖w - v‖ + ‖v‖ := norm_add_le _ _
        _ = ‖v - w‖ + ‖v‖ := by rw [norm_sub_rev]
        _ ≤ Real.exp (A + X) + ‖v‖ := by linarith [h14]
    have hE : Real.exp (A - Z) ≤ Real.exp (A + X) + ‖v‖ := le_trans h15 hw
    have h3 : Real.exp (A + X) ≤ Real.exp (A - Z) / 2 := by linarith [hα]
    linarith
  have h4 : Real.exp (A - Z) / 2 ≤ ‖v‖ := by linarith [h2]
  -- (13) at `z` against (15) at `s`, the `log 2` being absorbed
  have h5 : Real.exp (A + C) * 2 ≤ Real.exp (A - Z) * Real.exp G := by
    have e1 : Real.exp (A + C) * 2 = Real.exp (A + C + Real.log 2) := by
      conv_lhs => rw [h2log]
      rw [← Real.exp_add]
    rw [e1, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  calc ‖u‖ ≤ Real.exp (A + C) := h13
    _ ≤ ‖v‖ * Real.exp G := by nlinarith [h5, h4, Real.exp_pos G]

/-- BW (16) at level `J` (p. 45, p. 58): for integer `s`, `2^{-J}|s| ≤ 2^r S`, `g(s) ≠ 0`: `log|f(z)/f(s)| ≤ dhT* + 1·055SD + 1·008·2^{-J}(|z|+|s|)D + kum_J`. First `|f(s) − g(s)| < ½|g(s)|` ((14) ≤ ln(p) − 7·2^rSD against (15) ≥ −2·2^rSD); then (12), (13), (15). -/
theorem est16 {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) (μ : Fin r → ℕ) (Tst : ℝ) (hTst : Tst ≤ acT K σ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (s : ℤ)
    (hs : ((|s| : ℤ) : ℝ) / 2 ^ J ≤ 2 ^ r * acS K r b v) (hg : acg φ α b k L ι v σ p J μ t0 t (s : ℂ) ≠ 0) (z : ℂ) :
    ‖acf φ α b k L ι v σ p J μ t0 t z‖ ≤ ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ *
      Real.exp ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 1.055 * acS K r b v * acD K σ +
        1.008 * ((‖z‖ + ((|s| : ℤ) : ℝ)) / 2 ^ J) * acD K σ + kumJ K b v σ J) := by
  classical
  -- the parameters are non-degenerate
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := by
    have hpos : 0 < dK K := by
      haveI : Nontrivial K := inferInstance
      exact Module.finrank_pos (R := ℚ) (M := K)
    omega
  have hdR : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd
  have hh : 19 ≤ acH K b v := (acH_lower H).1
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hlog2rd : 0 < Real.log (2 * r * (dK K : ℝ)) := log_2rd_pos hr hd
  have hDpos : 0 < acD K σ := pD_pos hr hd σ hσ
  have hSpos : 0 < acS K r b v := by
    have h1 : 0 < pS r (dK K) (acH K b v) := by
      rw [pS]
      have : 0 < acH K b v := by omega
      positivity
    exact_mod_cast h1
  have hss0 : (0:ℝ) ≤ ((|s| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg s
  -- `Tst ≤ T`, so `dhT* ≤ 0·735 SD` (`num_T`)
  have hTs : (dK K : ℝ) * (acH K b v : ℝ) * Tst ≤ 0.735 * acS K r b v * acD K σ := by
    have h1 := (num_T hr hd hh σ hσ).2.2.1
    have h2 : Tst ≤ (pT r (dK K) σ : ℝ) := hTst
    have h3 : (0:ℝ) ≤ (dK K : ℝ) * (acH K b v : ℝ) := by positivity
    calc (dK K : ℝ) * (acH K b v : ℝ) * Tst
        ≤ (dK K : ℝ) * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ ≤ 0.735 * acS K r b v * acD K σ := h1
  have hHp : Height.logHeight p ≤ 0.85 * acS K r b v * acD K σ := H.hp12
  have hSD : Real.log 2 ≤ 0.001 * acS K r b v * acD K σ := (num_kum hr hd hh σ hσ J).2.2
  -- the Kummer contribution stays below `2·2 SD` (BW p. 58: `0·044 J ≤ 2·2 log(2rd)`)
  have hkum : kumJ K b v σ J ≤ 2.2 * acS K r b v * acD K σ := by
    rw [kumJ]
    have hJle : (J : ℝ) ≤ 50 * Real.log (2 * r * (dK K : ℝ)) := by
      have h1 : (pI r (dK K) : ℝ) ≤ 50 * Real.log (2 * r * (dK K : ℝ)) := by
        simpa only [pI] using
          Nat.floor_le (show (0:ℝ) ≤ 50 * Real.log (2 * r * (dK K : ℝ)) by positivity)
      exact le_trans (by exact_mod_cast hJ) h1
    have hSDnn : 0 ≤ acS K r b v * acD K σ := le_of_lt (mul_pos hSpos hDpos)
    calc 0.044 * (J : ℝ) / Real.log (2 * r * (dK K : ℝ)) * acS K r b v * acD K σ
        = (0.044 * (J : ℝ) / Real.log (2 * r * (dK K : ℝ))) *
            (acS K r b v * acD K σ) := by ring
      _ ≤ 2.2 * (acS K r b v * acD K σ) := by
          apply mul_le_mul_of_nonneg_right _ hSDnn
          rw [div_le_iff₀ hlog2rd]
          nlinarith [hJle]
      _ = 2.2 * acS K r b v * acD K σ := by ring
  -- the three estimates of BW §14–15 at level `J`
  have h13 := est13p H J μ Tst hTst t0 t ht z
  have h14 := est14 H J hJ μ Tst hTst t0 t ht (s : ℂ)
  have h15 := est15 H J μ Tst hTst t0 t ht s hg
  have hnrm : ‖((s : ℤ) : ℂ)‖ = ((|s| : ℤ) : ℝ) := by simp
  rw [hnrm] at h14
  -- abbreviations matching the three exponents and the target exponent
  set A : ℝ := lnp φ p with hA
  set G : ℝ := (dK K : ℝ) * (acH K b v : ℝ) * Tst + 1.055 * acS K r b v * acD K σ +
        1.008 * ((‖z‖ + ((|s| : ℤ) : ℝ)) / 2 ^ J) * acD K σ + kumJ K b v σ J with hG
  set X : ℝ := (acH K b v : ℝ) * Tst +
    (0.205 * (1 / (dK K : ℝ)) + 1.01 * (((|s| : ℤ) : ℝ) / 2 ^ J) / acS K r b v - 9 * 2 ^ r) *
      acS K r b v * acD K σ with hX
  set Z : ℝ := Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
      ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J with hZ
  set C : ℝ := (acH K b v : ℝ) * Tst + 0.204 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ +
    1.008 * (‖z‖ / 2 ^ J) * acD K σ with hC
  have h13' : ‖acf φ α b k L ι v σ p J μ t0 t z‖ ≤ Real.exp (A + C) := by
    convert h13 using 2 <;> ring
  have h14' : ‖acf φ α b k L ι v σ p J μ t0 t (s : ℂ) - acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ ≤
      Real.exp (A + X) := by
    convert h14 using 2 <;> ring
  have h15' : Real.exp (A - Z) ≤ ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by
    convert h15 using 2 <;> ring
  -- the two arithmetic margins
  have hα0 := est16_half_arith (A := A) (h := (acH K b v : ℝ)) (d := (dK K : ℝ))
    (ss := ((|s| : ℤ) : ℝ)) (S := acS K r b v) (D := acD K σ) (Tst := Tst)
    (Hp := Height.logHeight p) (kumJ := kumJ K b v σ J) (J := J) (r := r)
    hr hdR hSpos (le_of_lt hDpos) hss0 hTs hHp hs hkum hSD
  have hα : Real.exp (A + X) * 2 ≤ Real.exp (A - Z) := by
    rw [show A + X = (A + (acH K b v : ℝ) * Tst +
        (0.205 * (1 / (dK K : ℝ)) + 1.01 * (((|s| : ℤ) : ℝ) / 2 ^ J) / acS K r b v - 9 * 2 ^ r) *
          acS K r b v * acD K σ) from by rw [hX]; ring,
      show A - Z = (A - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
        ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J)) from by rw [hZ]]
    exact hα0
  have hβ0 := est16_main_arith (h := (acH K b v : ℝ)) (d := (dK K : ℝ))
    (ss := ((|s| : ℤ) : ℝ)) (S := acS K r b v) (D := acD K σ) (Tst := Tst)
    (Hp := Height.logHeight p) (kumJ := kumJ K b v σ J) (nz := ‖z‖) (J := J)
    hdR hSpos (le_of_lt hDpos) hss0 hHp hSD
  have hβ : C + Z + Real.log 2 ≤ G := by
    rw [show C + Z + Real.log 2 = ((acH K b v : ℝ) * Tst +
        0.204 * (1 / (dK K : ℝ)) * acS K r b v * acD K σ + 1.008 * (‖z‖ / 2 ^ J) * acD K σ +
        (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
          ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
          1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J) +
        Real.log 2) from by rw [hC, hZ],
      show G = ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 1.055 * acS K r b v * acD K σ +
        1.008 * ((‖z‖ + ((|s| : ℤ) : ℝ)) / 2 ^ J) * acD K σ + kumJ K b v σ J) from by rw [hG]]
    exact hβ0
  exact est16_glue h13' h14' h15' hα hβ

end Work.BW
