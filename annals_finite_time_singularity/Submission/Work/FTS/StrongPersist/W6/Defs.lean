/-
# The `f = z^4 κ` substitution, at order six

The level-six `WtoH` transfer (`Work.FTS.StrongPersist.wtoh6`) needs the substitution
`f = z^4 κ` (`divZ4 f = f/z^4`) rather than the level-four `f = z^2 κ`: the hypothesis of the
level-six statement controls the `𝒲^{6,∞}`-norm of `(z+1)^5/z^4 · f = (z+1)^5 · divZ4 f`, and
all the weights of the estimate follow from the *reciprocal* identity
`divZ4 f = ((z+1)^5/z^4 · f)·(1+z)^{-5}`.

This module contains the analytic core:

* `divZ4`, its basic identities, and its smoothness on the open quadrant;
* `pzIter_inv5` — the exact `n`-th `z`-derivative of `(1+z)^{-5}`;
* `kappa_bound_of_recip` — from `κ = G·(1+z)^{-5}` and `|(1+z)^k ∂_z^k G| ≤ M` (`k ≤ c ≤ 6`)
  deduce `|(1+z)^{c+5} ∂_z^c κ| ≤ 3·10^5 M` (the reciprocal Leibniz bound — no triangular
  inversion is needed, which is what keeps the constants small);
* `pzIter_zpow4_mul_sm` — the Leibniz expansion of `∂_z^k (z^4 κ)` with the falling-factorial
  coefficients `(4)_r = 4·3···(4-r+1)`;
* `wz_pzIter_le` / `wDzIter_le` — the two weighted bounds that turn the `κ`-bounds into bounds
  on `w·z^k∂_z^k f` and on `w·D_z^i f`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.H2.Q.Base
import Submission.Work.FTS.OpenPkg.ScoefOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.H2.STSigma
import Submission.Work.FTS.H2.STBasic
import Submission.Work.Elliptic.WtoH_Mixed_g_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.W6

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The substitution `f = z^4 κ` -/

/-- `divZ4 f z θ = f z θ / z^4`. -/
def divZ4 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => f z θ / z ^ 4

theorem divZ4_mul {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ≠ 0) : z ^ 4 * divZ4 f z θ = f z θ := by
  rw [divZ4]; field_simp

theorem divZ4_eq_mul {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ≠ 0) : f z θ = z ^ 4 * divZ4 f z θ :=
  (divZ4_mul hz).symm

/-- `((z+1)^5/z^4)·f = (z+1)^5 · divZ4 f`, as functions (the identity also holds at `z = 0`
and at `z = -1`, where both sides vanish). -/
theorem g_divZ4_eq (f : ℝ → ℝ → ℝ) :
    (fun z θ => (z + 1) ^ 5 / z ^ 4 * f z θ) = fun z θ => (z + 1) ^ 5 * divZ4 f z θ := by
  funext z θ
  rw [divZ4]
  by_cases hz : z = 0
  · subst hz; simp
  · field_simp

/-- The reciprocal form of the substitution, on `(0,∞)`. -/
theorem divZ4_recip (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) :
    divZ4 f z θ = ((z + 1) ^ 5 / z ^ 4 * f z θ) * ((z + 1) ^ 5)⁻¹ := by
  have hz0 : z ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hz)
  have h1z : (z + 1) ^ 5 ≠ 0 := pow_ne_zero 5 (by positivity)
  rw [divZ4]
  field_simp

theorem contDiffOn_divZ4_QO {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (divZ4 f) := by
  have hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      Work.FTS.EllipticEst.Q0 := hsm
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 4)
      Work.FTS.EllipticEst.Q0 := contDiffOn_fst.pow 4
  have hdiv := hf.div hden (fun p hp => pow_ne_zero 4 (ne_of_gt hp.1))
  refine hdiv.congr fun p hp => ?_
  rfl

theorem smoothOpen_g5 {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) ^ 5 / z ^ 4 * f z θ) := by
  rw [g_divZ4_eq]
  have hpoly : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (p.1 + 1) ^ 5)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_fst.add contDiffOn_const).pow 5
  have hmul := hpoly.mul (contDiffOn_divZ4_QO hsm)
  refine hmul.congr fun p hp => ?_
  rfl

theorem contDiffOn_divZ4_slice {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => divZ4 f z' θ) (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z (contDiffOn_divZ4_QO hsm) hθ

/-- `D_θ^i f = z^4 · D_θ^i (divZ4 f)` away from the axis (the factor `z^4` is constant in `θ`). -/
theorem DthIter_divZ4_eq {f : ℝ → ℝ → ℝ} (i : ℕ) {z θ : ℝ} (hz : z ≠ 0) :
    Work.Spaces.DthIter i f z θ = z ^ 4 * Work.Spaces.DthIter i (divZ4 f) z θ := by
  rw [Work.Spaces.DthIter_eq_iterate_Lop i f z,
    Work.Spaces.DthIter_eq_iterate_Lop i (divZ4 f) z]
  have hfun : (fun θ' => f z θ') = fun θ' => z ^ 4 * divZ4 f z θ' := by
    funext θ'; exact divZ4_eq_mul hz
  rw [hfun, Work.Elliptic.Lop_iter_const_mul]

/-- `D_θ^i` of the level-six weight times `f` equals `(z+1)^5` times `D_θ^i (divZ4 f)`,
as functions. -/
theorem DthIter_g5_eq (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 5 / z ^ 4 * f z θ)
      = fun z θ => (z + 1) ^ 5 * Work.Spaces.DthIter i (divZ4 f) z θ := by
  rw [g_divZ4_eq, Work.Elliptic.DthIter_const_mul]

/-! ## The derivatives of `(1+z)^{-5}` -/

/-- `∂_z (((z'+1)^m)⁻¹) = -(m·((z+1)^{m+1})⁻¹)` at `z > 0`. -/
theorem hasDerivAt_inv_pow (m : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => ((z' + 1) ^ m)⁻¹) (-((m : ℝ) * ((z + 1) ^ (m + 1))⁻¹)) z := by
  have h1z : z + 1 ≠ 0 := by positivity
  have houter := hasDerivAt_zpow (-(m : ℤ)) (z + 1) (Or.inl h1z)
  have hbase : HasDerivAt (fun z' : ℝ => z' + 1) 1 z := (hasDerivAt_id z).add_const 1
  have hcomp : HasDerivAt (fun z' : ℝ => (z' + 1) ^ (-(m : ℤ)))
      (((-(m : ℤ) : ℤ) : ℝ) * (z + 1) ^ (-(m : ℤ) - 1) * 1) z :=
    HasDerivAt.comp (h := fun z' : ℝ => z' + 1) z houter hbase
  have hfun : (fun z' : ℝ => (z' + 1) ^ (-(m : ℤ))) = fun z' : ℝ => ((z' + 1) ^ m)⁻¹ := by
    funext z'; rw [zpow_neg, zpow_natCast]
  rw [hfun] at hcomp
  convert hcomp using 1
  have hexp : (-(m : ℤ) - 1) = -(((m + 1 : ℕ)) : ℤ) := by push_cast; ring
  rw [hexp]
  simp only [zpow_neg, zpow_natCast, mul_one]
  push_cast
  ring

/-- The exact `n`-th `z`-derivative of `(1+z)^{-5}`:
`∂_z^n ((1+z)^5)⁻¹ = (-1)^n · (n+4)!/4! · ((1+z)^{n+5})⁻¹` for `z > 0`. -/
theorem pzIter_inv5 : ∀ (n : ℕ) (z θ : ℝ), 0 < z →
    Work.Spaces.pzIter n (fun z _ => ((z + 1) ^ 5)⁻¹) z θ
      = (-1 : ℝ) ^ n * ((Nat.factorial (n + 4) : ℝ) / 24) * ((z + 1) ^ (n + 5))⁻¹ := by
  intro n
  induction n with
  | zero => intro z θ hz; norm_num
  | succ n ih =>
    intro z θ hz
    show deriv (fun z' : ℝ => Work.Spaces.pzIter n (fun z _ => ((z + 1) ^ 5)⁻¹) z' θ) z = _
    have hev : (fun z' : ℝ => Work.Spaces.pzIter n (fun z _ => ((z + 1) ^ 5)⁻¹) z' θ)
        =ᶠ[𝓝 z] (fun z' : ℝ =>
          (-1 : ℝ) ^ n * ((Nat.factorial (n + 4) : ℝ) / 24) * ((z' + 1) ^ (n + 5))⁻¹) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih z' θ hz'
    rw [Filter.EventuallyEq.deriv_eq hev]
    have hder := (hasDerivAt_inv_pow (n + 5) hz).const_mul
      ((-1 : ℝ) ^ n * ((Nat.factorial (n + 4) : ℝ) / 24))
    rw [hder.deriv]
    have hfac : (Nat.factorial (n + 1 + 4) : ℝ) = ((n : ℝ) + 5) * (Nat.factorial (n + 4) : ℝ) := by
      have h1 : n + 1 + 4 = (n + 4) + 1 := by omega
      rw [h1, Nat.factorial_succ]; push_cast; ring
    have hpow : (n + 5 + 1 : ℕ) = n + 1 + 5 := by omega
    rw [hfac, hpow, pow_succ]
    push_cast
    ring

/-- The weighted form of `pzIter_inv5`: the weight `(z+1)^{n+5}` cancels the derivative. -/
theorem inv5_weight (n : ℕ) {z θ : ℝ} (hz : 0 < z) :
    (z + 1) ^ (n + 5) * Work.Spaces.pzIter n (fun z _ => ((z + 1) ^ 5)⁻¹) z θ
      = (-1 : ℝ) ^ n * ((Nat.factorial (n + 4) : ℝ) / 24) := by
  rw [pzIter_inv5 n z θ hz]
  have h1z : (z + 1) ^ (n + 5) ≠ 0 := pow_ne_zero _ (by positivity)
  field_simp

/-! ## The reciprocal Leibniz bound -/

/-- The coefficient sum `∑_{e ≤ c} C(c,e)·(c-e+4)!/24` is at most `3·10^5` for `c ≤ 6`
(it equals `271801` for `c = 6`). -/
theorem choose_fact_sum_le {c : ℕ} (hc : c ≤ 6) :
    ∑ e ∈ Finset.range (c + 1), ((c.choose e : ℝ) * ((Nat.factorial (c - e + 4) : ℝ) / 24))
      ≤ 3 * 10 ^ 5 := by
  interval_cases c <;> norm_num [Finset.sum_range_succ, Nat.choose, Nat.factorial]

/-- **The reciprocal Leibniz bound.**  If `κ = G·(1+z)^{-5}` on `(0,∞)` and
`|(1+z)^k ∂_z^k G| ≤ M` for `k ≤ c ≤ 6` at `(z,θ)`, then `|(1+z)^{c+5} ∂_z^c κ| ≤ 3·10^5·M`. -/
theorem kappa_bound_of_recip {G κ : ℝ → ℝ → ℝ} {M z θ : ℝ} {c : ℕ} (hc : c ≤ 6) (hz : 0 < z)
    (hident : ∀ z' ∈ Set.Ioi (0 : ℝ), ∀ θ' : ℝ,
      κ z' θ' = G z' θ' * ((z' + 1) ^ 5)⁻¹)
    (hG : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => G z' θ) z)
    (hM : 0 ≤ M)
    (hbd : ∀ k ≤ c, |(z + 1) ^ k * Work.Spaces.pzIter k G z θ| ≤ M) :
    |(z + 1) ^ (c + 5) * Work.Spaces.pzIter c κ z θ| ≤ 3 * 10 ^ 5 * M := by
  have h1z : (0 : ℝ) < z + 1 := by linarith
  have hsm5 : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' : ℝ => ((z' + 1) ^ 5)⁻¹) z :=
    (Work.FTS.H2.Q.contDiffAt_sm_of_top
      (((contDiffAt_id (x := z)).add (contDiffAt_const (x := z) (c := (1 : ℝ)))).pow 5)).inv
      (pow_ne_zero 5 (ne_of_gt h1z))
  -- replace `κ` by `G · (1+z)^{-5}` locally
  have hev : (fun z' => κ z' θ) =ᶠ[𝓝 z]
      (fun z' => G z' θ * ((z' + 1) ^ 5)⁻¹) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact hident z' hz' θ
  rw [Work.Elliptic.pzIter_congr_nhds (u := κ) (v := fun z θ => G z θ * ((z + 1) ^ 5)⁻¹)
      c hev,
    Work.FTS.H2.Q.pzIter_mul_local_sm c hG hsm5]
  -- per-term bound
  have hterm : ∀ e ≤ c,
      |(z + 1) ^ (c + 5) * (Work.Spaces.pzIter e G z θ
          * Work.Spaces.pzIter (c - e) (fun z _ => ((z + 1) ^ 5)⁻¹) z θ)|
        ≤ ((Nat.factorial (c - e + 4) : ℝ) / 24) * M := by
    intro e he
    have hsplit : (z + 1) ^ (c + 5) = (z + 1) ^ (c - e + 5) * (z + 1) ^ e := by
      rw [← pow_add]
      congr 1
      omega
    have hw := inv5_weight (c - e) hz (θ := θ)
    have hbd' := hbd e he
    rw [hsplit]
    calc |(z + 1) ^ (c - e + 5) * (z + 1) ^ e
          * (Work.Spaces.pzIter e G z θ
            * Work.Spaces.pzIter (c - e) (fun z _ => ((z + 1) ^ 5)⁻¹) z θ)|
        = |(((z + 1) ^ (c - e + 5)
              * Work.Spaces.pzIter (c - e) (fun z _ => ((z + 1) ^ 5)⁻¹) z θ)
            * ((z + 1) ^ e * Work.Spaces.pzIter e G z θ))| := by
          congr 1
          ring
      _ = |(-1 : ℝ) ^ (c - e) * ((Nat.factorial (c - e + 4) : ℝ) / 24)
            * ((z + 1) ^ e * Work.Spaces.pzIter e G z θ)| := by rw [hw]
      _ = ((Nat.factorial (c - e + 4) : ℝ) / 24) * |(z + 1) ^ e * Work.Spaces.pzIter e G z θ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤
            (Nat.factorial (c - e + 4) : ℝ) / 24), abs_pow]
          simp
      _ ≤ ((Nat.factorial (c - e + 4) : ℝ) / 24) * M := by
          refine mul_le_mul_of_nonneg_left hbd' (by positivity)
  have hcoef : ∑ e ∈ Finset.range (c + 1),
      ((c.choose e : ℝ) * ((Nat.factorial (c - e + 4) : ℝ) / 24)) ≤ 3 * 10 ^ 5 :=
    choose_fact_sum_le hc
  have h1 : ∑ e ∈ Finset.range (c + 1),
      ((z + 1) ^ (c + 5)) * ((c.choose e : ℝ) * (Work.Spaces.pzIter e G z θ
        * Work.Spaces.pzIter (c - e) (fun z _ => ((z + 1) ^ 5)⁻¹) z θ))
      = ∑ e ∈ Finset.range (c + 1), (c.choose e : ℝ) * ((z + 1) ^ (c + 5)
        * (Work.Spaces.pzIter e G z θ
          * Work.Spaces.pzIter (c - e) (fun z _ => ((z + 1) ^ 5)⁻¹) z θ)) := by
    refine Finset.sum_congr rfl fun e he => ?_
    ring
  rw [Finset.mul_sum, h1]
  calc |∑ e ∈ Finset.range (c + 1), (c.choose e : ℝ) * ((z + 1) ^ (c + 5)
        * (Work.Spaces.pzIter e G z θ
          * Work.Spaces.pzIter (c - e) (fun z _ => ((z + 1) ^ 5)⁻¹) z θ))|
      ≤ ∑ e ∈ Finset.range (c + 1), |(c.choose e : ℝ) * ((z + 1) ^ (c + 5)
          * (Work.Spaces.pzIter e G z θ
            * Work.Spaces.pzIter (c - e) (fun z _ => ((z + 1) ^ 5)⁻¹) z θ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ e ∈ Finset.range (c + 1), (c.choose e : ℝ) * |(z + 1) ^ (c + 5)
          * (Work.Spaces.pzIter e G z θ
            * Work.Spaces.pzIter (c - e) (fun z _ => ((z + 1) ^ 5)⁻¹) z θ)| := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (c.choose e))]
    _ ≤ ∑ e ∈ Finset.range (c + 1),
          (c.choose e : ℝ) * (((Nat.factorial (c - e + 4) : ℝ) / 24) * M) := by
        refine Finset.sum_le_sum fun e he => ?_
        exact mul_le_mul_of_nonneg_left
          (hterm e (Nat.lt_succ_iff.mp (Finset.mem_range.mp he))) (Nat.cast_nonneg _)
    _ = (∑ e ∈ Finset.range (c + 1),
          ((c.choose e : ℝ) * ((Nat.factorial (c - e + 4) : ℝ) / 24))) * M := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun e he => ?_
        ring
    _ ≤ 3 * 10 ^ 5 * M := mul_le_mul_of_nonneg_right hcoef hM

/-! ## The Leibniz expansion of `∂_z^k (z^4 κ)` and the weighted bounds -/

/-- `∂_z^r (z^4) = (4)_r z^{4-r}` (the falling factorial `(4)_r = 4·3···(4-r+1)`, zero for
`r ≥ 5`). -/
theorem pzIter_zpow4_eq (r : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter r (fun z _ => z ^ 4) z θ
      = (((Nat.descFactorial 4 r : ℕ)) : ℝ) * z ^ (4 - r) := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv]
  simpa using iteratedDeriv_pow (𝕜 := ℝ) (x := z) 4 r

/-- The falling factorial `(4)_r` vanishes for `r ≥ 5`. -/
theorem descFactorial_four_eq_zero {r : ℕ} (hr : 5 ≤ r) : Nat.descFactorial 4 r = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction t with
  | zero =>
      rw [Nat.add_zero, show (5 : ℕ) = 4 + 1 from rfl, Nat.descFactorial_succ, Nat.sub_self,
        zero_mul]
  | succ t ih =>
      rw [show 5 + (t + 1) = (5 + t) + 1 by omega, Nat.descFactorial_succ, ih (by omega),
        mul_zero]

/-- `∂_z^k (z^4 κ) = ∑_{r≤k} C(k,r)·(4)_r·z^{4-r}·∂_z^{k-r} κ`. -/
theorem pzIter_zpow4_mul_sm (k : ℕ) {κ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hκ : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => κ z' θ) z) :
    Work.Spaces.pzIter k (fun z θ => z ^ 4 * κ z θ) z θ
      = ∑ r ∈ Finset.range (k + 1),
          (k.choose r : ℝ) * ((((Nat.descFactorial 4 r : ℕ)) : ℝ) * z ^ (4 - r)
            * Work.Spaces.pzIter (k - r) κ z θ) := by
  have hu : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' : ℝ => z' ^ 4) z :=
    Work.FTS.H2.Q.contDiffAt_sm_of_top ((contDiffAt_id (x := z)).pow 4)
  rw [Work.FTS.H2.Q.pzIter_mul_local_sm k hu hκ]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [pzIter_zpow4_eq]

/-- The coefficient sum `∑_{r≤k} C(k,r)·(4)_r ≤ 1100` for `k ≤ 6` (`1045` for `k = 6`). -/
theorem choose_desc_le {k : ℕ} (hk : k ≤ 6) :
    ∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ) * (((Nat.descFactorial 4 r : ℕ)) : ℝ)
      ≤ 1100 := by
  interval_cases k <;> norm_num [Finset.sum_range_succ, Nat.choose, Nat.descFactorial]

/-- The elementary weighted inequality: `(z+1)²z^{s+2}|∂_z^s κ| ≤ M/(1+z)` from
`|(z+1)^{s+5}∂_z^s κ| ≤ M`. -/
theorem wz_le {κ : ℝ → ℝ → ℝ} {M z θ : ℝ} {s : ℕ} (hz : 0 < z)
    (hbd : |(z + 1) ^ (s + 5) * Work.Spaces.pzIter s κ z θ| ≤ M) :
    (z + 1) ^ 2 * z ^ (s + 2) * |Work.Spaces.pzIter s κ z θ| ≤ M / (1 + z) := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have h1 : (z + 1) ^ 2 * z ^ (s + 2) ≤ (z + 1) ^ (s + 4) := by
    calc (z + 1) ^ 2 * z ^ (s + 2) ≤ (z + 1) ^ 2 * (z + 1) ^ (s + 2) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ z) (by linarith : z ≤ z + 1) _)
            (by positivity)
      _ = (z + 1) ^ (s + 4) := by rw [← pow_add]; congr 1; omega
  have h2 : (z + 1) ^ (s + 4) * |Work.Spaces.pzIter s κ z θ| ≤ M / (1 + z) := by
    rw [le_div_iff₀ h1z]
    calc (z + 1) ^ (s + 4) * |Work.Spaces.pzIter s κ z θ| * (1 + z)
        = (z + 1) ^ (s + 5) * |Work.Spaces.pzIter s κ z θ| := by
          rw [show s + 5 = (s + 4) + 1 by omega, pow_succ]
          ring
      _ = |(z + 1) ^ (s + 5) * Work.Spaces.pzIter s κ z θ| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (z + 1) ^ (s + 5))]
      _ ≤ M := hbd
  exact le_trans (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2

/-- **The weighted `z`-derivative bound.**  From the `κ`-bounds
`|(z+1)^{c+5} ∂_z^c κ| ≤ M` (`c ≤ 6`) at `(z,θ)`, the weighted derivative of `z^4 κ`
satisfies `|w(z)·z^k·∂_z^k(z^4 κ)| ≤ 1100·M/(1+z)`. -/
theorem wz_pzIter_le {κ : ℝ → ℝ → ℝ} {M z θ : ℝ} {k C : ℕ} (hk : k ≤ 6) (hkC : k ≤ C)
    (hz : 0 < z)
    (hκ : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => κ z' θ) z)
    (hbd : ∀ c ≤ C, |(z + 1) ^ (c + 5) * Work.Spaces.pzIter c κ z θ| ≤ M) :
    |Work.Spaces.w z * z ^ k * Work.Spaces.pzIter k (fun z θ => z ^ 4 * κ z θ) z θ|
      ≤ 1100 * M / (1 + z) := by
  have hzn : z ≠ 0 := ne_of_gt hz
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbd 0 (by omega))
  rw [pzIter_zpow4_mul_sm k hκ, Finset.mul_sum]
  have hterm : ∀ r ≤ k,
      |(Work.Spaces.w z * z ^ k)
          * ((k.choose r : ℝ) * ((((Nat.descFactorial 4 r : ℕ)) : ℝ) * z ^ (4 - r)
              * Work.Spaces.pzIter (k - r) κ z θ))|
        ≤ ((k.choose r : ℝ) * (((Nat.descFactorial 4 r : ℕ)) : ℝ)) * (M / (1 + z)) := by
    intro r hr
    by_cases hc0 : ((Nat.descFactorial 4 r : ℕ) : ℝ) = 0
    · rw [hc0]; simp
    · have hr4 : r ≤ 4 := by
        by_contra h
        exact hc0 (by rw [descFactorial_four_eq_zero (by omega)]; norm_num)
      have hkey : Work.Spaces.w z * z ^ k * z ^ (4 - r) = (z + 1) ^ 2 * z ^ (k - r + 2) := by
        have hzk : z ^ k * z ^ (4 - r) = z ^ (k + (4 - r)) := by rw [pow_add]
        have hdiv : z ^ (k + (4 - r)) / z ^ 2 = z ^ (k - r + 2) := by
          rw [div_eq_iff (pow_ne_zero 2 hzn), ← pow_add]
          congr 1
          omega
        calc Work.Spaces.w z * z ^ k * z ^ (4 - r)
            = (z + 1) ^ 2 * ((z ^ k * z ^ (4 - r)) / z ^ 2) := by
              rw [Work.Spaces.w]; field_simp; ring
          _ = (z + 1) ^ 2 * z ^ (k - r + 2) := by rw [hzk, hdiv]
      rw [show (Work.Spaces.w z * z ^ k)
            * ((k.choose r : ℝ) * ((((Nat.descFactorial 4 r : ℕ)) : ℝ) * z ^ (4 - r)
                * Work.Spaces.pzIter (k - r) κ z θ))
          = ((k.choose r : ℝ) * (((Nat.descFactorial 4 r : ℕ)) : ℝ))
            * ((Work.Spaces.w z * z ^ k * z ^ (4 - r))
                * Work.Spaces.pzIter (k - r) κ z θ) from by ring]
      rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)), hkey]
      calc ((k.choose r : ℝ) * (((Nat.descFactorial 4 r : ℕ)) : ℝ))
            * |(z + 1) ^ 2 * z ^ (k - r + 2) * Work.Spaces.pzIter (k - r) κ z θ|
          = ((k.choose r : ℝ) * (((Nat.descFactorial 4 r : ℕ)) : ℝ))
            * ((z + 1) ^ 2 * z ^ (k - r + 2)
                * |Work.Spaces.pzIter (k - r) κ z θ|) := by
            rw [abs_mul,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ (z + 1) ^ 2 * z ^ (k - r + 2))]
        _ ≤ ((k.choose r : ℝ) * (((Nat.descFactorial 4 r : ℕ)) : ℝ)) * (M / (1 + z)) :=
            mul_le_mul_of_nonneg_left
              (wz_le (s := k - r) hz (hbd (k - r) (by omega)))
              (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc |∑ r ∈ Finset.range (k + 1), (Work.Spaces.w z * z ^ k)
        * ((k.choose r : ℝ) * ((((Nat.descFactorial 4 r : ℕ)) : ℝ) * z ^ (4 - r)
            * Work.Spaces.pzIter (k - r) κ z θ))|
      ≤ ∑ r ∈ Finset.range (k + 1), |(Work.Spaces.w z * z ^ k)
          * ((k.choose r : ℝ) * ((((Nat.descFactorial 4 r : ℕ)) : ℝ) * z ^ (4 - r)
              * Work.Spaces.pzIter (k - r) κ z θ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.range (k + 1),
          ((k.choose r : ℝ) * (((Nat.descFactorial 4 r : ℕ)) : ℝ)) * (M / (1 + z)) :=
        Finset.sum_le_sum fun r hr =>
          hterm r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
    _ = (∑ r ∈ Finset.range (k + 1),
          (k.choose r : ℝ) * (((Nat.descFactorial 4 r : ℕ)) : ℝ)) * (M / (1 + z)) := by
        rw [Finset.sum_mul]
    _ ≤ 1100 * (M / (1 + z)) :=
        mul_le_mul_of_nonneg_right (choose_desc_le hk) (by positivity)
    _ = 1100 * M / (1 + z) := by ring

/-- `bell n ≤ 250` for `n ≤ 6` (the values are `1,1,2,5,15,52,203`). -/
theorem bell_le_six {n : ℕ} (hn : n ≤ 6) : Work.Spaces.bell n ≤ 250 := by
  interval_cases n <;> decide

/-- **The weighted `D_z`-bound.**  From `|w(z)·z^k·∂_z^k f| ≤ M` for `k ≤ i ≤ 6`, the Stirling
expansion gives `|w(z)·D_z^i f| ≤ 250·M`. -/
theorem wDzIter_le {f : ℝ → ℝ → ℝ} {M z θ : ℝ} {i : ℕ} (hi : i ≤ 6) (hz : 0 < z)
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi 0))
    (hM : 0 ≤ M)
    (hbd : ∀ k ≤ i, |Work.Spaces.w z * z ^ k * Work.Spaces.pzIter k f z θ| ≤ M) :
    |Work.Spaces.w z * Work.Spaces.DzIter i f z θ| ≤ 250 * M := by
  have hsum : Work.Spaces.w z * Work.Spaces.DzIter i f z θ
      = ∑ k ∈ Finset.range (i + 1),
          (Work.Spaces.scoef i k : ℝ)
            * (Work.Spaces.w z * z ^ k * Work.Spaces.pzIter k f z θ) := by
    rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open hsm i z hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    ring
  rw [hsum]
  calc |∑ k ∈ Finset.range (i + 1), (Work.Spaces.scoef i k : ℝ)
        * (Work.Spaces.w z * z ^ k * Work.Spaces.pzIter k f z θ)|
      ≤ (Work.Spaces.bell i : ℝ) * M :=
        Work.Spaces.abs_sum_scoef_mul_le i M (fun k => Work.Spaces.w z * z ^ k
          * Work.Spaces.pzIter k f z θ) (fun k hk => hbd k (by omega))
    _ ≤ 250 * M := by
        have hb : (Work.Spaces.bell i : ℝ) ≤ 250 := by
          exact_mod_cast bell_le_six (by omega)
        linarith [mul_le_mul_of_nonneg_right hb hM]

end Work.FTS.StrongPersist.W6
