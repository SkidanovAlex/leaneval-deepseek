import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs

/-!
# The manifest Abel numerators agree with the paper's on the diagonal

`Work.OddVolterra.J1` and `J2` (the paper's numerators `J₁`, `J₂` of the two Abel
kernels) are defined with a case split: on the diagonal `σ = s` they are set to the
explicit limit values `(2n+1)!! (-L ∂_sL)^{n+1}` and `(2n-1)!! (-L ∂_sL)^n ∂_sL`, while
off the diagonal they are the differentiated moment integrands.

`J1M`/`J2M` are the manifest (polynomial) representatives obtained from the recursion
`R_{m+1} = Z ∂_s R_m + (ν - m) (∂_s Z) R_m`, where `Z = Zrad` is the radicand.  This file
proves that on the diagonal the recursion collapses to the limit values:

`R_m(s,s,t) = (∏_{i<m} (ν - i)) · (∂_s Z(s,s,t))^m · init(s,s,t)`  (because `Z = 0` there),

`∂_s Z(s,s,t) = -2 L ∂_sL`, and the resulting falling-factorial products are the double
factorials `(2n+1)!!`, `(2n-1)!!`.
-/

namespace Work.OddVolterra.KernelExt

open Work.OddVolterra Work.OddVolterra.KernelExt
open scoped BigOperators

noncomputable section

/-! ### Slice derivative of a function on `ℝ × ℝ × ℝ` -/

/-- The Fréchet derivative at `(a,b,c)` in the first coordinate direction `(1,0,0)`
is the derivative of the one-variable slice `u ↦ F (u, b, c)` at `a`. -/
lemma fderiv_apply_fst (F : ℝ × ℝ × ℝ → ℝ) (a b c : ℝ)
    (hF : DifferentiableAt ℝ F (a, b, c)) :
    (fderiv ℝ F (a, b, c)) (1, 0, 0) = deriv (fun u : ℝ => F (u, b, c)) a := by
  have h1 : HasDerivAt (fun u : ℝ => u) (1 : ℝ) a := hasDerivAt_id a
  have h2 : HasDerivAt (fun _ : ℝ => (b, c)) (0 : ℝ × ℝ) a := hasDerivAt_const a (b, c)
  have hg : HasDerivAt (fun u : ℝ => (u, b, c)) ((1, (0, 0)) : ℝ × (ℝ × ℝ)) a :=
    h1.prodMk h2
  have hcomp := hF.hasFDerivAt.comp_hasDerivAt a hg
  rw [← hcomp.deriv]
  rfl

/-- `Zrad h` is smooth when `h` is. -/
lemma Zrad_contDiff (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) : ContDiff ℝ (⊤ : ℕ∞) (Zrad h) := by
  unfold Zrad line
  fun_prop

/-- The `s`-derivative of the radicand on the diagonal is `-2 L ∂_sL`. -/
lemma ZradS_diag (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s t : ℝ) :
    ZradS h (s, s, t) = -2 * (line h s t * lineSlope h s t) := by
  have hZ : DifferentiableAt ℝ (Zrad h) (s, s, t) :=
    ((Zrad_contDiff h hh).differentiable (by simp)).differentiableAt
  rw [ZradS, fderiv_apply_fst (Zrad h) s s t hZ]
  have h1 : HasDerivAt (fun u : ℝ => u * t) t s := hasDerivAt_mul_const t
  have h2 : HasDerivAt (fun u : ℝ => h u) (deriv h s) s :=
    (hh.differentiable (by simp)).differentiableAt.hasDerivAt
  have hl : HasDerivAt (fun u : ℝ => line h u t) (t + deriv h s) s := h1.add h2
  have hsub := (hasDerivAt_const s (line h s t ^ 2)).sub (hl.pow 2)
  have hfun : ((fun _ : ℝ => line h s t ^ 2) - (fun u : ℝ => line h u t) ^ 2)
      = (fun u : ℝ => Zrad h (u, s, t)) := by
    funext u
    simp [Zrad]
  rw [← hfun, hsub.deriv]
  simp only [lineSlope]
  ring

/-! ### The recursion at a zero of the radicand -/

/-- On the zero set of `Zrad`, the recursion `R_{m+1} = Z ∂_sR_m + (ν-m) (∂_sZ) R_m`
solves explicitly: `R_m = (∏_{i<m}(ν-i)) · (∂_sZ)^m · init`, since the `Z ∂_sR_m` term
drops out. -/
lemma Rnu_of_Zrad_eq_zero (h : ℝ → ℝ) (ν : ℝ) (init : ℝ × ℝ × ℝ → ℝ) :
    ∀ (m : ℕ) (p : ℝ × ℝ × ℝ), Zrad h p = 0 →
      Rnu ν h init m p =
        (∏ i ∈ Finset.range m, (ν - (i : ℝ))) * (ZradS h p) ^ m * init p := by
  intro m
  induction m with
  | zero =>
    intro p _
    simp [Rnu]
  | succ k ih =>
    intro p hp
    have hZS : (fderiv ℝ (Zrad h) p) (1, 0, 0) = ZradS h p := rfl
    simp only [Rnu]
    rw [hp, zero_mul, zero_add, hZS]
    rw [ih p hp, Finset.prod_range_succ, pow_succ]
    ring

/-! ### The double-factorial products -/

/-- `(2n+1)!! = (2n+1) (2n-1)!!`, valid also for `n = 0`. -/
lemma doubleFactorial_odd_succ (n : ℕ) :
    Nat.doubleFactorial (2 * n + 1) = (2 * n + 1) * Nat.doubleFactorial (2 * n - 1) := by
  cases n with
  | zero => simp [Nat.doubleFactorial]
  | succ k =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
        Nat.doubleFactorial_add_two,
        show 2 * (k + 1) - 1 = 2 * k + 1 by omega]

/-- The falling factorial `(n+1/2)(n-1/2)···(1/2)` equals `(2n+1)!!/2^{n+1}`. -/
lemma prod_half_succ (n : ℕ) :
    (∏ i ∈ Finset.range (n + 1), ((n : ℝ) + 1 / 2 - (i : ℝ))) * 2 ^ (n + 1) =
      (Nat.doubleFactorial (2 * n + 1) : ℝ) := by
  induction n with
  | zero => norm_num [Nat.doubleFactorial]
  | succ k ih =>
    rw [Finset.prod_range_succ']
    have hcongr : (∏ i ∈ Finset.range (k + 1), ((↑(k+1) : ℝ) + 1 / 2 - (↑(i+1) : ℝ)))
        = (∏ i ∈ Finset.range (k + 1), ((k : ℝ) + 1 / 2 - (i : ℝ))) := by
      apply Finset.prod_congr rfl
      intro i _
      push_cast
      ring
    rw [hcongr, Nat.cast_zero, sub_zero]
    have expand : (∏ i ∈ Finset.range (k + 1), ((k : ℝ) + 1 / 2 - (i : ℝ))) *
          (↑(k+1) + 1 / 2) * 2 ^ (k + 1 + 1)
        = ((∏ i ∈ Finset.range (k + 1), ((k : ℝ) + 1 / 2 - (i : ℝ))) * 2 ^ (k + 1)) *
          ((↑(k+1) + 1 / 2) * 2) := by
      rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ]
      ring
    rw [expand, ih]
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, Nat.doubleFactorial_add_two]
    push_cast
    ring

/-- The falling factorial `(n-1/2)(n-3/2)···(1/2)` equals `(2n-1)!!/2^n`. -/
lemma prod_half (n : ℕ) :
    (∏ i ∈ Finset.range n, ((n : ℝ) - 1 / 2 - (i : ℝ))) * 2 ^ n =
      (Nat.doubleFactorial (2 * n - 1) : ℝ) := by
  induction n with
  | zero => norm_num [Nat.doubleFactorial]
  | succ k ih =>
    rw [Finset.prod_range_succ']
    have hcongr : (∏ i ∈ Finset.range k, ((↑(k+1) : ℝ) - 1 / 2 - (↑(i+1) : ℝ)))
        = (∏ i ∈ Finset.range k, ((k : ℝ) - 1 / 2 - (i : ℝ))) := by
      apply Finset.prod_congr rfl
      intro i _
      push_cast
      ring
    rw [hcongr, Nat.cast_zero, sub_zero]
    have expand : (∏ i ∈ Finset.range k, ((k : ℝ) - 1 / 2 - (i : ℝ))) *
          ((↑(k+1) : ℝ) - 1 / 2) * 2 ^ (k + 1)
        = ((∏ i ∈ Finset.range k, ((k : ℝ) - 1 / 2 - (i : ℝ))) * 2 ^ k) *
          ((↑(k+1) - 1 / 2) * 2) := by
      rw [pow_succ]
      ring
    rw [expand, ih]
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, doubleFactorial_odd_succ k]
    push_cast
    ring

/-! ### The diagonal identities -/

lemma J1M_diag (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s t : ℝ) :
    J1M n h s s t = J1 n h s s t := by
  rw [J1, if_pos rfl, J1M]
  rw [Rnu_of_Zrad_eq_zero h ((n : ℝ) + 1 / 2) (fun _ => (1 : ℝ)) (n + 1) (s, s, t)
        (by unfold Zrad line; ring)]
  rw [ZradS_diag h hh s t]
  have h2d : (-2 : ℝ) * (line h s t * lineSlope h s t)
      = 2 * (-(line h s t * lineSlope h s t)) := by ring
  rw [h2d, mul_pow]
  rw [show (∏ i ∈ Finset.range (n + 1), ((n : ℝ) + 1 / 2 - (i : ℝ))) *
        (2 ^ (n + 1) * (-(line h s t * lineSlope h s t)) ^ (n + 1)) * 1
      = ((∏ i ∈ Finset.range (n + 1), ((n : ℝ) + 1 / 2 - (i : ℝ))) * 2 ^ (n + 1)) *
        (-(line h s t * lineSlope h s t)) ^ (n + 1) by ring]
  rw [prod_half_succ n]

lemma J2M_diag (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s t : ℝ) :
    J2M n h s s t = J2 n h s s t := by
  rw [J2, if_pos rfl, J2M]
  rw [Rnu_of_Zrad_eq_zero h ((n : ℝ) - 1 / 2) (fun p => lineSlope h p.1 p.2.2) n (s, s, t)
        (by unfold Zrad line; ring)]
  rw [ZradS_diag h hh s t]
  have h2d : (-2 : ℝ) * (line h s t * lineSlope h s t)
      = 2 * (-(line h s t * lineSlope h s t)) := by ring
  rw [h2d, mul_pow]
  rw [show (∏ i ∈ Finset.range n, ((n : ℝ) - 1 / 2 - (i : ℝ))) *
        (2 ^ n * (-(line h s t * lineSlope h s t)) ^ n) * lineSlope h s t
      = ((∏ i ∈ Finset.range n, ((n : ℝ) - 1 / 2 - (i : ℝ))) * 2 ^ n) *
        (-(line h s t * lineSlope h s t)) ^ n * lineSlope h s t by ring]
  rw [prod_half n]

theorem JM_diag (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s t : ℝ) :
    Work.OddVolterra.KernelExt.J1M n h s s t = Work.OddVolterra.J1 n h s s t ∧
    Work.OddVolterra.KernelExt.J2M n h s s t = Work.OddVolterra.J2 n h s s t :=
  ⟨J1M_diag n hh s t, J2M_diag n hh s t⟩

end

end Work.OddVolterra.KernelExt
