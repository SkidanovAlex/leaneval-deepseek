import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.Zeta.xi_logDeriv_re_lower

noncomputable section
open Complex Filter
open scoped Real Topology
set_option autoImplicit false

namespace Commons.NumberTheory.Zeta

/-! # `zeta_logDeriv_re_regular_bound` (reduction to the ξ-core)

The target is the "regular" upper bound for the real part of `−ζ′/ζ` on the strip
`1 < σ ≤ 2`, large `|t|`:

    Re(−ζ′/ζ)(σ + i t) ≤ C + (1/2)·Re ψ(1 + (σ + i t)/2).

**Reduction.**  Let `ξ(s) := (1/2)·s·(s−1)·Λ(s)` be the classical completed zeta
(`Λ = completedRiemannZeta`; entire away from the values at `0, 1`, with zeros
exactly at the nontrivial zeros of ζ).  On `Re s > 1` one has the identity
(`logDeriv_riemannZeta_eq` below)

    ζ′/ζ(s) = ξ′/ξ(s) − 1/(s−1) + (log π)/2 − (1/2)·ψ(1 + s/2),

a pure consequence of `ξ(s) = (1/2)·s·(s−1)·Γℝ(s)·ζ(s)` on `Re s > 1` and the
Γℝ log-derivative formula.  Taking real parts gives

    Re(−ζ′/ζ)(s) − (1/2)·Re ψ(1+s/2) = −Re(ξ′/ξ)(s) + Re(1/(s−1)) − (1/2)·log π,

so the whole target is equivalent to the analytic core lemma
`xi_logDeriv_re_lower` below:

    ∃ C0 > 0, ∃ H0 ≥ 2: ∀ |t| ≥ H0, ∀ 1 < σ ≤ 2:  Re(ξ′/ξ)(σ+i t) ≥ −C0.

That core is the classical partial-fraction lower bound for `ξ′/ξ` (its real part is
`Re B + Σ_ρ [(σ−β_ρ)/|s−ρ|² + β_ρ/|ρ|²]` over the nontrivial zeros `ρ = β + iγ`,
every summand nonnegative for `σ ≥ 1`), which is being formalised separately from the
Weierstrass/Hadamard product of `ξ`.  Everything downstream of the core is proved here.

## Content

* `xi` : the completed function `ξ(s) = (1/2)·s·(s−1)·Λ(s)`.
* analyticity/nonvanishing facts for `ξ` on `Re s > 1`;
* `xi_logDeriv_eq`, `logDeriv_riemannZeta_eq` : the two log-derivative identities;
* `logDerivRe_eq` : the real-part identity above;
* a few elementary bounds (`re_inv_sub_one_le`, log π positivity);
* the deep core `xi_logDeriv_re_lower` (single hole, see module docstring);
* `zeta_logDeriv_re_regular_bound` : the target, deduced from the core.
-/

/-- The classical completed (xi) function ξ(s) := (1/2)·s·(s−1)·Λ(s), where Λ =
`completedRiemannZeta`.  Entire away from the (removable) junk values at 0 and 1;
zeros exactly at the nontrivial zeros of ζ. -/
noncomputable def xi (s : ℂ) : ℂ := (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s

/-! ## Basic facts about ξ on the right half-plane `Re s > 1` -/

lemma re_ne_zero_of_one_lt_re {s : ℂ} (hs : (1 : ℝ) < s.re) : s ≠ 0 := by
  intro hz
  have hre : s.re = 0 := by simp [hz]
  linarith

lemma sub_one_ne_zero_of_one_lt_re {s : ℂ} (hs : (1 : ℝ) < s.re) : s - 1 ≠ 0 := by
  intro h1s
  have h1 : s = 1 := sub_eq_zero.mp h1s
  have hsre : s.re = 1 := by
    have h := congrArg Complex.re h1
    simpa using h
  linarith

lemma ne_one_of_one_lt_re {s : ℂ} (hs : (1 : ℝ) < s.re) : s ≠ 1 := by
  exact sub_ne_zero.mp (sub_one_ne_zero_of_one_lt_re hs)

lemma Gammaℝ_ne_zero_of_one_lt_re {s : ℂ} (hs : (1 : ℝ) < s.re) : s.Gammaℝ ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)

lemma xi_ne_zero_of_one_lt_re (s : ℂ) (hs : (1 : ℝ) < s.re) : xi s ≠ 0 := by
  have hs0 : s ≠ 0 := re_ne_zero_of_one_lt_re hs
  have hs1 : s - 1 ≠ 0 := sub_one_ne_zero_of_one_lt_re hs
  have hG : s.Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_one_lt_re hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)
  unfold xi
  rw [show completedRiemannZeta s = riemannZeta s * s.Gammaℝ by
    have hdef := riemannZeta_def_of_ne_zero (s := s) hs0
    have : riemannZeta s * s.Gammaℝ = completedRiemannZeta s := by
      rw [hdef]
      field_simp [hG]
    exact this.symm]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1) (mul_ne_zero hz hG)

lemma differentiableAt_xi (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ xi s := by
  unfold xi
  have hdΛ : DifferentiableAt ℂ completedRiemannZeta s := differentiableAt_completedZeta hs0 hs1
  have hdf : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s := by fun_prop
  exact hdf.mul hdΛ

lemma differentiableAt_xi_of_one_lt_re (s : ℂ) (hs : (1 : ℝ) < s.re) :
    DifferentiableAt ℂ xi s :=
  differentiableAt_xi s (re_ne_zero_of_one_lt_re hs) (ne_one_of_one_lt_re hs)

/-! ## ξ(s) = head(s)·ζ(s)·Γℝ(s) and the log-derivative identities on Re s > 1 -/

/-- logDeriv of the polynomial head (1/2)·s·(s−1): `1/s + 1/(s−1)`. -/
lemma logDeriv_head (s : ℂ) (hs0 : s ≠ 0) (hs1 : s - 1 ≠ 0) :
    logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s = 1 / s + 1 / (s - 1) := by
  have h₂ : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply]
    have hder : deriv (fun z : ℂ => z - 1) s = 1 := by
      have h₁ : (fun z : ℂ => z - 1) = fun z => z + (-1 : ℂ) := by funext z; ring
      rw [h₁]
      simp
    rw [hder]
  have hpar : logDeriv (fun z : ℂ => z * (z - 1)) s = 1 / s + 1 / (s - 1) := by
    have hm := logDeriv_fun_mul (x := s) (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1)
      hs0 hs1 (by fun_prop) (by fun_prop)
    simpa [h₂] using hm
  calc
    logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s
        = logDeriv (fun z : ℂ => (1 / 2 : ℂ) * (z * (z - 1))) s := by
            congr 1
            funext z
            ring
    _ = logDeriv (fun z : ℂ => z * (z - 1)) s := by
            exact logDeriv_const_mul (f := fun z : ℂ => z * (z - 1)) (x := s) ((1 / 2 : ℂ))
              (by norm_num : (1 / 2 : ℂ) ≠ 0)
    _ = 1 / s + 1 / (s - 1) := hpar

/-- Pointwise product identity `ξ = head·ζ·Γℝ` on `Re s > 1`. -/
lemma xi_eq_prod (s : ℂ) (hs : (1 : ℝ) < s.re) :
    xi s = ((1 / 2 : ℂ) * s * (s - 1)) * (riemannZeta s * s.Gammaℝ) := by
  have hs0 : s ≠ 0 := re_ne_zero_of_one_lt_re hs
  have hG : s.Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_one_lt_re hs
  unfold xi
  have hdef := riemannZeta_def_of_ne_zero (s := s) hs0
  have hΛ : completedRiemannZeta s = riemannZeta s * s.Gammaℝ := by
    have : riemannZeta s * s.Gammaℝ = completedRiemannZeta s := by
      rw [hdef]
      field_simp [hG]
    exact this.symm
  rw [hΛ]

/-- Function-level version of `xi_eq_prod` on a neighbourhood of `s` (for logDeriv congruence). -/
lemma xi_eventuallyEq_prod (s : ℂ) (hs : (1 : ℝ) < s.re) :
    (fun z : ℂ => xi z) =ᶠ[𝓝 s] (fun z : ℂ =>
      ((1 / 2 : ℂ) * z * (z - 1)) * (riemannZeta z * z.Gammaℝ)) := by
  have hopen : IsOpen {z : ℂ | (1 : ℝ) < z.re} := by
    simpa [Set.preimage, Set.mem_Ioi] using
      (isOpen_Ioi.preimage Complex.continuous_re)
  exact eventually_of_mem (IsOpen.mem_nhds hopen hs) (by intro z hz; exact xi_eq_prod z hz)

/-- **Main log-derivative identity for ξ on Re s > 1**:
    `ξ′/ξ = 1/s + 1/(s−1) + Γℝ′/Γℝ + ζ′/ζ`. -/
theorem xi_logDeriv_eq (s : ℂ) (hs : (1 : ℝ) < s.re) :
    logDeriv xi s = 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := re_ne_zero_of_one_lt_re hs
  have hs1 : s - 1 ≠ 0 := sub_one_ne_zero_of_one_lt_re hs
  have hsG : 0 < s.re := by linarith
  have hG : s.Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_one_lt_re hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)
  have hdΓ : DifferentiableAt ℂ Complex.Gammaℝ s :=
    Commons.NumberTheory.DirichletCharacter.differentiableAt_Gammaℝ s hsG
  have hdz : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta (ne_one_of_one_lt_re hs)
  have hdhead : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s := by fun_prop
  have hhead0 : ((1 / 2 : ℂ) * s * (s - 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1
  have hcongr : logDeriv xi s =
      logDeriv (fun z : ℂ => ((1 / 2 : ℂ) * z * (z - 1)) * (riemannZeta z * z.Gammaℝ)) s := by
    have hxie : (fun z : ℂ => xi z) =ᶠ[𝓝 s] (fun z : ℂ =>
        ((1 / 2 : ℂ) * z * (z - 1)) * (riemannZeta z * z.Gammaℝ)) := xi_eventuallyEq_prod s hs
    have hlg : logDeriv xi =ᶠ[𝓝 s] logDeriv (fun z : ℂ =>
        ((1 / 2 : ℂ) * z * (z - 1)) * (riemannZeta z * z.Gammaℝ)) := (logDeriv_congr_nhds hxie)
    exact hlg.eq_of_nhds
  have hζΓ := logDeriv_fun_mul (x := s) (f := fun z : ℂ => riemannZeta z) (g := fun z : ℂ => z.Gammaℝ)
    hz hG hdz hdΓ
  have hprod := logDeriv_fun_mul (x := s)
    (f := fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) (g := fun z : ℂ => riemannZeta z * z.Gammaℝ)
    hhead0 (mul_ne_zero hz hG) hdhead (hdz.mul hdΓ)
  have hhead := logDeriv_head s hs0 hs1
  calc
    logDeriv xi s
        = logDeriv (fun z : ℂ => ((1 / 2 : ℂ) * z * (z - 1)) * (riemannZeta z * z.Gammaℝ)) s := hcongr
    _ = logDeriv (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) s +
          logDeriv (fun z : ℂ => riemannZeta z * z.Gammaℝ) s := hprod
    _ = (1 / s + 1 / (s - 1)) + (logDeriv riemannZeta s + logDeriv Complex.Gammaℝ s) := by
          rw [hhead, hζΓ]
    _ = 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
          ring

/-- digamma shift identity at s/2 (Re s > 1 side condition). -/
lemma digamma_add_one_half (s : ℂ) (hs : (1 : ℝ) < s.re) :
    Complex.digamma (1 + s / 2) = Complex.digamma (s / 2) + (s / 2)⁻¹ := by
  have hhyp : ∀ m : ℕ, s / 2 ≠ - (m : ℂ) := by
    intro m hm
    have hre1 : (s / 2).re = s.re / 2 := by simp [div_eq_mul_inv, Complex.mul_re]
    have hre2 : (-(m : ℂ)).re = - (m : ℝ) := by simp
    have : (s / 2).re = (-(m : ℂ)).re := by rw [hm]
    rw [hre1, hre2] at this
    have hm_nonneg : (0 : ℝ) ≤ m := by exact_mod_cast (Nat.zero_le m)
    linarith
  have h := Complex.digamma_apply_add_one (s / 2) hhyp
  simpa [add_comm] using h

/-- **ζ′/ζ in terms of ξ′/ξ, the pole at s=1 and the Γ-factor**: for `Re s > 1`,
    `ζ′/ζ = ξ′/ξ − 1/(s−1) + (log π)/2 − (1/2)·ψ(1 + s/2)`. -/
theorem logDeriv_riemannZeta_eq (s : ℂ) (hs : (1 : ℝ) < s.re) :
    logDeriv riemannZeta s = logDeriv xi s - 1 / (s - 1) + (Complex.log (Real.pi : ℂ)) / 2
      - Complex.digamma (1 + s / 2) / 2 := by
  rw [xi_logDeriv_eq s hs]
  rw [Commons.NumberTheory.DirichletCharacter.logDeriv_Gammaℝ_formula s (by linarith)]
  have hψ : Complex.digamma (s / 2) = Complex.digamma (1 + s / 2) - (s / 2)⁻¹ := by
    have hψ' := digamma_add_one_half s hs
    rw [hψ']
    ring
  rw [hψ]
  ring

/-! ## Real-part identity and elementary bounds -/

lemma re_div_two (a : ℂ) : (a / (2 : ℂ)).re = a.re / 2 := by
  rw [Complex.div_re]
  norm_num [Complex.normSq]
  ring

/-- **Real-part identity**: for `Re s > 1`,
    `Re(−ζ′/ζ)(s) = −Re(ξ′/ξ)(s) + Re(1/(s−1)) − (1/2)log π + (1/2)·Re ψ(1 + s/2)`. -/
theorem logDerivRe_eq (s : ℂ) (hs : (1 : ℝ) < s.re) :
    (-deriv riemannZeta s / riemannZeta s).re =
      -(logDeriv xi s).re + (1 / (s - 1)).re - (1 / 2 : ℝ) * (Complex.log (Real.pi : ℂ)).re
        + (1 / 2 : ℝ) * (Complex.digamma (1 + s / 2)).re := by
  have h1 : (-deriv riemannZeta s / riemannZeta s).re = -(logDeriv riemannZeta s).re := by
    have hid : (-deriv riemannZeta s / riemannZeta s) = -(logDeriv riemannZeta s) := by
      rw [logDeriv_apply]
      ring
    rw [hid]
    simp
  rw [h1]
  have hld := logDeriv_riemannZeta_eq s hs
  have hre : (logDeriv riemannZeta s).re =
      (logDeriv xi s - 1 / (s - 1) + (Complex.log (Real.pi : ℂ)) / 2
        - Complex.digamma (1 + s / 2) / 2).re := by
    rw [hld]
  rw [hre]
  simp only [Complex.sub_re, Complex.add_re]
  rw [re_div_two (Complex.log (Real.pi : ℂ))]
  rw [re_div_two (Complex.digamma (1 + s / 2))]
  ring

/-- For `s = σ + i t` with `1 < σ`: `Re(1/(s−1)) ≤ 1/(2|t|)`. -/
lemma re_inv_sub_one_le (σ t : ℝ) (hσ : (1 : ℝ) < σ) (ht : t ≠ 0) :
    (1 / ((((σ : ℂ) + (t : ℂ) * Complex.I)) - 1)).re ≤ 1 / (2 * |t|) := by
  let a : ℝ := σ - 1
  have ha : 0 < a := by dsimp [a]; linarith
  have hdiff : (((σ : ℂ) + (t : ℂ) * Complex.I) - 1) = ((a : ℂ) + (t : ℂ) * Complex.I) := by
    dsimp [a]
    apply Complex.ext <;> simp <;> ring
  have hre : (1 / ((a : ℂ) + (t : ℂ) * Complex.I)).re = a / (a ^ 2 + t ^ 2) := by
    rw [Complex.div_re]
    simp [Complex.normSq]
    ring
  have hb : a / (a ^ 2 + t ^ 2) ≤ 1 / (2 * |t|) := by
    have hdenpos : 0 < a ^ 2 + t ^ 2 := by positivity
    have hgt : 0 < 2 * a * |t| := by positivity
    have hAM : 2 * a * |t| ≤ a ^ 2 + t ^ 2 := by
      have hsq : 0 ≤ (a - |t|) ^ 2 := sq_nonneg (a - |t|)
      have ht2 : t ^ 2 = |t| ^ 2 := by rw [sq_abs]
      nlinarith
    calc
      a / (a ^ 2 + t ^ 2) ≤ a / (2 * a * |t|) := by
        rw [div_le_div_iff₀ hdenpos hgt]
        nlinarith [ha]
      _ = 1 / (2 * |t|) := by
        field_simp [ha.ne']
  calc
    (1 / (((σ : ℂ) + (t : ℂ) * Complex.I) - 1)).re
        = (1 / ((a : ℂ) + (t : ℂ) * Complex.I)).re := by rw [hdiff]
    _ = a / (a ^ 2 + t ^ 2) := hre
    _ ≤ 1 / (2 * |t|) := hb

/-- `log π > 0`, so `−(1/2)·Re(log π) ≤ 0`. -/
lemma neg_half_log_pi_re_le_zero :
    -((1 / 2 : ℝ) * (Complex.log (Real.pi : ℂ)).re) ≤ 0 := by
  have hpi : (1 : ℝ) < Real.pi := by nlinarith [Real.pi_gt_three]
  have hlog : 0 < Real.log Real.pi := Real.log_pos hpi
  have hre : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
    have h : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
      (Complex.ofReal_log (le_of_lt (by nlinarith [Real.pi_gt_three] : (0 : ℝ) < Real.pi))).symm
    rw [h]
    simp
  rw [hre]
  linarith

/-! ## The analytic core

The deep classical input `Commons.NumberTheory.Zeta.xi_logDeriv_re_lower` (published in the
shared commons; Hadamard partial fraction of the completed zeta, see that module) gives
`∃ C0 > 0, ∃ H0 ≥ 2: ∀ |t| ≥ H0, ∀ 1 < σ ≤ 2: Re(ξ′/ξ)(σ+i·t) ≥ −C0`.  The target
`zeta_logDeriv_re_regular_bound` below is deduced from it. -/

/-! ## The target theorem, assembled from the core -/

theorem zeta_logDeriv_re_regular_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℝ, (2 : ℝ) ≤ H ∧
      ∀ t : ℝ, H ≤ |t| → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
            riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re ≤
          C + (1 / 2) * (Complex.digamma
            (1 + (((σ : ℂ) + (t : ℂ) * Complex.I) / 2))).re := by
  rcases xi_logDeriv_re_lower with ⟨C0, hC0pos, H0, hH0, hCore⟩
  refine ⟨C0 + 2, by linarith, H0, hH0, ?_⟩
  intro t ht σ hσ1 hσ2
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hsσ : (1 : ℝ) < s.re := by
    dsimp [s]
    simpa using hσ1
  have ht2 : (2 : ℝ) ≤ |t| := le_trans hH0 ht
  have htt : t ≠ 0 := by
    intro htz
    have : |t| = 0 := by simp [htz]
    linarith
  have hcore0 := hCore t ht σ hσ1 hσ2
  have hcore : -C0 ≤ (logDeriv xi s).re := by
    change -C0 ≤ (logDeriv (fun s0 : ℂ => (1 / 2 : ℂ) * s0 * (s0 - 1) * completedRiemannZeta s0) s).re
    simpa [s] using hcore0
  have hre := logDerivRe_eq s hsσ
  have hR : (1 / (s - 1)).re ≤ 1 / (2 * |t|) := by
    simpa [s] using (re_inv_sub_one_le σ t hσ1 htt)
  have hD : -(logDeriv xi s).re ≤ C0 := by linarith [hcore]
  have hL : -((1 / 2 : ℝ) * (Complex.log (Real.pi : ℂ)).re) ≤ 0 := neg_half_log_pi_re_le_zero
  have hC : C0 + 1 / (2 * |t|) ≤ C0 + 1 / 4 := by
    have hh : (1 : ℝ) / (2 * |t|) ≤ 1 / 4 := by
      have hpos : 0 < 2 * |t| := by positivity
      have hge : (4 : ℝ) ≤ 2 * |t| := by nlinarith
      rw [one_div, one_div]
      exact (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 4)).mpr hge
    linarith
  calc
    (-deriv riemannZeta s / riemannZeta s).re
        = -(logDeriv xi s).re + (1 / (s - 1)).re
            - (1 / 2 : ℝ) * (Complex.log (Real.pi : ℂ)).re
            + (1 / 2 : ℝ) * (Complex.digamma (1 + s / 2)).re := hre
    _ ≤ C0 + 1 / (2 * |t|) + (1 / 2 : ℝ) * (Complex.digamma (1 + s / 2)).re := by
          linarith
    _ ≤ C0 + 1 / 4 + (1 / 2 : ℝ) * (Complex.digamma (1 + s / 2)).re := by linarith
    _ ≤ (C0 + 2) + (1 / 2 : ℝ) * (Complex.digamma (1 + s / 2)).re := by linarith
    _ = (C0 + 2) + (1 / 2) * (Complex.digamma (1 + (((σ : ℂ) + (t : ℂ) * Complex.I) / 2))).re := by
          simpa [s]

end Commons.NumberTheory.Zeta
