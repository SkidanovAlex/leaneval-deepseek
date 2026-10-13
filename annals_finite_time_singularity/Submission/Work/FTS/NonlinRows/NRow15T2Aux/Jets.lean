/-
# Row 15: the radial factor `ψ` and its jet bounds

`ψ(z) = z²/(1+z)³ = u(z)·k(z)` with `u(z) = z/(1+z)` and `k(z) = z/(1+z)²`.  The two
factors have closed-form iterated derivatives

* `deriv^[j] u = (-1)^{j-1} j!/(1+z)^{j+1}` (`j ≥ 1`), and
* `deriv^[m] k = (-1)^m m! (z-m)/(1+z)^{m+2}` (`Work.Spaces.iter_deriv_hKerClosed`),

so the Leibniz rule (`iteratedDeriv_mul`) and the `z`-vanishing of `u` give the bounds

  `(1+z)^{j+1}·|deriv^[j] u| ≤ C`,  `(1+z)^{m+1}·|deriv^[m] k| ≤ C`  (`j ≥ 1`, `m ≤ 4`),

hence `(1+z)^{c+1}|deriv^[c] ψ| ≤ C` for `c ≤ 4`, `z > 0`, and finally, for `c ≤ m ≤ 4`,

  `(1+z)·w(z)·z^m·|deriv^[c] ψ(z)| ≤ C·(1+z)^{m-c}`.

This is the radial input of the row-15 pointwise estimate (the weight `(1+z)w z z^m`
carries a `z^{m-2}` which is cancelled by the `z²`-vanishing of `ψ`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Defs
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open
import Submission.Work.Spaces.pzIter_hKer_bound
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## The radial factor and its two pieces -/

/-- `u(z) = z/(1+z)`. -/
def u15 (z : ℝ) : ℝ := z / (1 + z)

/-- `k(z) = z/(1+z)²` (the kernel `Work.Spaces.hKer`). -/
def k15 (z : ℝ) : ℝ := z / (1 + z) ^ 2

/-- The radial factor of row 15: `ψ = u·k = z²/(1+z)³`. -/
def psi15 (z : ℝ) : ℝ := u15 z * k15 z

theorem psi15_eq (z : ℝ) : psi15 z = z ^ 2 / (1 + z) ^ 3 := by
  rw [psi15, u15, k15]
  rcases eq_or_ne (1 + z) 0 with h | h
  · have hz : z = -1 := by linarith
    subst hz
    norm_num
  · field_simp

theorem smoothOpen_u15 : Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => u15 z) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => z / (1 + z)) (Set.Ioi 0) := by
    refine ContDiffOn.div contDiffOn_id (contDiffOn_const.add contDiffOn_id) ?_
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity
  have hfun : (fun z : ℝ => z / (1 + z)) = fun z : ℝ => u15 z := by
    funext z; rw [u15]
  rw [hfun] at h
  exact smoothOpen_z_only h

theorem smoothOpen_k15 : Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => k15 z) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi 0) := by
    refine ContDiffOn.div contDiffOn_id ((contDiffOn_const.add contDiffOn_id).pow 2) ?_
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity
  have hfun : (fun z : ℝ => z / (1 + z) ^ 2) = fun z : ℝ => k15 z := by
    funext z; rw [k15]
  rw [hfun] at h
  exact smoothOpen_z_only h

theorem smoothOpen_psi15 : Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => psi15 z) := by
  have h := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl smoothOpen_u15 smoothOpen_k15
  have hfun : (fun z θ : ℝ => u15 z * k15 z) = fun z _ => psi15 z := by
    funext z θ; rw [psi15]
  rw [hfun] at h
  exact h

/-! ## Iterated derivatives of a `z`-only function -/

/-- The iterated `∂_z`-derivatives of a `z`-only function are the iterated derivatives of the
one-variable function. -/
theorem pzIter_radial_fn (r : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => r z) z θ = deriv^[k] r z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      have hfun : (fun z' => Work.Spaces.pzIter k (fun z _ => r z) z' θ) = deriv^[k] r :=
        funext fun z' => ih z'
      rw [hfun, Function.iterate_succ_apply']

/-! ## The explicit iterated derivatives -/

/-- `∂_z (z/(1+z)) = 1/(1+z)²`. -/
theorem deriv_u15 (z : ℝ) (hz : (1 : ℝ) + z ≠ 0) :
    deriv (fun w : ℝ => u15 w) z = 1 / (1 + z) ^ 2 := by
  have hfun : (fun w : ℝ => u15 w) = fun w : ℝ => w / (1 + w) := by
    funext w; rw [u15]
  rw [hfun]
  have h1 : HasDerivAt (fun w : ℝ => w) 1 z := hasDerivAt_id z
  have h2 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := (hasDerivAt_id z).const_add 1
  have h3 := h1.div h2 hz
  rw [show (fun w : ℝ => w / (1 + w)) = (fun w : ℝ => w) / fun w : ℝ => 1 + w from rfl,
    h3.deriv]
  field_simp
  ring

/-- `∂_z (c/(1+z)^n) = -c·n/(1+z)^{n+1}`. -/
theorem deriv_const_div_pow (c : ℝ) (n : ℕ) (z : ℝ) (hz : (1 : ℝ) + z ≠ 0) :
    deriv (fun w : ℝ => c / (1 + w) ^ n) z = -c * (n : ℝ) / (1 + z) ^ (n + 1) := by
  have h1 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ n) ((n : ℝ) * (1 + z) ^ (n - 1) * 1) z :=
    h1.pow n
  have h3 : HasDerivAt (fun w : ℝ => c / (1 + w) ^ n)
      ((0 * (1 + z) ^ n - c * ((n : ℝ) * (1 + z) ^ (n - 1) * 1)) / ((1 + z) ^ n) ^ 2) z :=
    (hasDerivAt_const z c).div h2 (by positivity)
  rw [h3.deriv]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; norm_num
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hpow : (1 + z) ^ (n - 1) * (1 + z) ^ (n + 1) = (1 + z) ^ (2 * n) := by
      rw [← pow_add]; congr 1; omega
    have hsq : ((1 + z) ^ n) ^ 2 = (1 + z) ^ (2 * n) := by
      rw [show 2 * n = n + n from by ring, pow_add, pow_two]
    rw [hsq]
    rw [show (0 * (1 + z) ^ n - c * ((n : ℝ) * (1 + z) ^ (n - 1) * 1)) / (1 + z) ^ (2 * n)
        = -(c * (n : ℝ) * (1 + z) ^ (n - 1)) / (1 + z) ^ (2 * n) from by ring]
    rw [div_eq_iff (by positivity : (1 + z) ^ (2 * n) ≠ 0)]
    rw [show -c * (n : ℝ) / (1 + z) ^ (n + 1) * (1 + z) ^ (2 * n)
        = (-c * (n : ℝ)) * ((1 + z) ^ (2 * n) / (1 + z) ^ (n + 1)) from by ring]
    rw [show (1 + z) ^ (2 * n) / (1 + z) ^ (n + 1) = (1 + z) ^ (n - 1) from by
      rw [div_eq_iff (by positivity : (1 + z) ^ (n + 1) ≠ 0), ← hpow]]
    ring

/-- The iterated derivatives of `u`: `deriv^[j] u = (-1)^{j-1} j!/(1+z)^{j+1}` for `j ≥ 1`. -/
theorem iter_deriv_u15_pos (j : ℕ) (hj : 1 ≤ j) :
    ∀ z : ℝ, (1 : ℝ) + z ≠ 0 →
      deriv^[j] (fun z : ℝ => u15 z) z
        = (-1 : ℝ) ^ (j - 1) * (j.factorial : ℝ) / (1 + z) ^ (j + 1) := by
  induction j with
  | zero => omega
  | succ j ih =>
      intro z hz
      rcases eq_or_ne j 0 with hj0 | hj0
      · subst hj0
        rw [Function.iterate_one, deriv_u15 z hz]
        norm_num
      · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
        rw [Function.iterate_succ_apply']
        have hev : deriv^[j] (fun z : ℝ => u15 z)
            =ᶠ[𝓝 z] fun w => (-1 : ℝ) ^ (j - 1) * ((j.factorial : ℝ)) / (1 + w) ^ (j + 1) := by
          have hset : IsOpen {w : ℝ | (1 : ℝ) + w ≠ 0} := isOpen_ne.preimage (by continuity)
          filter_upwards [hset.mem_nhds (by simpa using hz)] with w hw
          exact ih hj1 w hw
        rw [hev.deriv_eq, deriv_const_div_pow _ _ z hz]
        have hsign : (-1 : ℝ) ^ j = (-1) ^ (j - 1) * (-1) := by
          rw [show j = (j - 1) + 1 from by omega, pow_succ]
          rw [show j - 1 + 1 - 1 = j - 1 from by omega]
        have hnum : -((-1 : ℝ) ^ (j - 1) * ((j.factorial : ℝ))) * ((j + 1 : ℕ) : ℝ)
            = (-1 : ℝ) ^ (j + 1 - 1) * (((j + 1).factorial : ℝ)) := by
          rw [Nat.factorial_succ]
          push_cast
          rw [hsign]
          ring
        rw [hnum]

/-! ## The two refined jet bounds -/

/-- `(1+z)^{j+1}|∂_z^j u| ≤ C` for `1 ≤ j ≤ 4`, `z > 0`. -/
theorem deriv_iter_u15_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ), 1 ≤ j → j ≤ 4 → ∀ z : ℝ, 0 < z →
      (1 + z) ^ (j + 1) * |deriv^[j] (fun z : ℝ => u15 z) z| ≤ C := by
  refine ⟨1000, by norm_num, ?_⟩
  intro j hj hj4 z hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
  have hz2 : (0 : ℝ) < 1 + z := by linarith
  have h1 : |deriv^[j] (fun z : ℝ => u15 z) z| = (j.factorial : ℝ) / (1 + z) ^ (j + 1) := by
    rw [iter_deriv_u15_pos j hj z hz1, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_nonneg (Nat.cast_nonneg (j.factorial)), abs_of_pos (pow_pos hz2 _)]
  rw [h1, div_eq_mul_inv]
  rw [show (1 + z) ^ (j + 1) * ((j.factorial : ℝ) * ((1 + z) ^ (j + 1))⁻¹) = (j.factorial : ℝ) from by
    rw [← mul_assoc, mul_comm ((1 + z) ^ (j + 1)) (j.factorial : ℝ), mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hz1), mul_one]]
  have hfac : ((j.factorial : ℕ) : ℝ) ≤ 1000 := by
    have h24 : ((j.factorial : ℕ) : ℝ) ≤ 24 := by
      have : j.factorial ≤ 24 := by interval_cases j <;> norm_num
      exact_mod_cast this
    linarith
  linarith

/-- `(1+z)^{m+1}|∂_z^m k| ≤ C` for `m ≤ 4`, `z > 0`. -/
theorem deriv_iter_k15_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), m ≤ 4 → ∀ z : ℝ, 0 < z →
      (1 + z) ^ (m + 1) * |deriv^[m] (fun z : ℝ => k15 z) z| ≤ C := by
  refine ⟨1000, by norm_num, ?_⟩
  intro m hm z hz
  have hz1 : -1 < z := by linarith
  have hz1' : (0 : ℝ) < 1 + z := by linarith
  have hfun : (fun z : ℝ => k15 z) = fun z : ℝ => z / (1 + z) ^ 2 := by funext w; rw [k15]
  have hk : deriv^[m] (fun z : ℝ => z / (1 + z) ^ 2) z
      = (-1 : ℝ) ^ m * (m.factorial : ℝ)
          * ((z - (m : ℝ)) * ((1 + z) ^ (m + 2))⁻¹) := by
    rw [Work.Spaces.iter_deriv_hKerClosed m z hz1]
    rw [Work.Spaces.hKerClosed, inv_pow]
  rw [hfun, hk]
  have h1 : |(-1 : ℝ) ^ m * (m.factorial : ℝ) * ((z - (m : ℝ)) * ((1 + z) ^ (m + 2))⁻¹)|
      = (m.factorial : ℝ) * |(z - (m : ℝ)) * ((1 + z) ^ (m + 2))⁻¹| := by
    rw [abs_mul]
    congr 1
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (Nat.cast_nonneg m.factorial)]
  rw [h1]
  have h2 : |(z - (m : ℝ)) * ((1 + z) ^ (m + 2))⁻¹| = |z - (m : ℝ)| * ((1 + z) ^ (m + 2))⁻¹ := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hz1' _))]
  rw [h2]
  have hkey : |z - (m:ℝ)| / (1 + z) ≤ (m : ℝ) + 1 := by
    rcases le_total (m : ℝ) z with hmz | hmz
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ z - m)]
      rw [div_le_iff₀ hz1']
      nlinarith
    · rw [abs_of_nonpos (by linarith : z - m ≤ 0), neg_sub]
      rw [div_le_iff₀ hz1']
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
  have hpowa : (1 + z) ^ (m + 1) * ((1 + z) ^ (m + 2))⁻¹ = (1 + z)⁻¹ := by
    have h1 : (1 + z) ^ (m + 2) = (1 + z) ^ (m + 1) * (1 + z) := by
      have h2 : m + 2 = (m + 1) + 1 := by omega
      rw [h2, pow_succ]
    rw [h1, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hz1')), one_mul]
  have hshape : (1 + z) ^ (m + 1) * ((m.factorial : ℝ) * (|z - (m:ℝ)| * ((1 + z) ^ (m + 2))⁻¹))
      = (m.factorial : ℝ) * (|z - (m:ℝ)| / (1 + z)) := by
    rw [show (1 + z) ^ (m + 1) * ((m.factorial : ℝ) * (|z - (m:ℝ)| * ((1 + z) ^ (m + 2))⁻¹))
        = (m.factorial : ℝ) * (|z - (m:ℝ)| * ((1 + z) ^ (m + 1) * ((1 + z) ^ (m + 2))⁻¹))
        from by ring]
    rw [hpowa, div_eq_mul_inv]
  rw [hshape]
  have hfac : (m.factorial : ℝ) * ((m : ℝ) + 1) ≤ 1000 := by
    have h : m.factorial * (m + 1) ≤ 120 := by interval_cases m <;> norm_num
    have h2 : ((m.factorial * (m + 1) : ℕ) : ℝ) ≤ 120 := by exact_mod_cast h
    push_cast at h2
    linarith
  calc (m.factorial : ℝ) * (|z - (m:ℝ)| / (1 + z))
      ≤ (m.factorial : ℝ) * ((m : ℝ) + 1) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ 1000 := hfac

/-! ## The jet bound of `ψ` -/

/-- **The jet bound of `ψ`**: `(1+z)^{c+1}|∂_z^c ψ(z)| ≤ C` for `c ≤ 4`, `z > 0`. -/
theorem pzIter_psi15_main :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ), c ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      (1 + z) ^ (c + 1) * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ| ≤ C := by
  obtain ⟨Cu0, hCu0, hCu0b⟩ := deriv_iter_u15_le
  obtain ⟨Ck0, hCk0, hCk0b⟩ := deriv_iter_k15_le
  set Cu : ℝ := max Cu0 1 with hCud
  set Ck : ℝ := max Ck0 1 with hCkd
  have hCu1 : (1 : ℝ) ≤ Cu := le_max_right _ _
  have hCk1 : (1 : ℝ) ≤ Ck := le_max_right _ _
  have hCupos : (0 : ℝ) < Cu := lt_of_lt_of_le zero_lt_one hCu1
  have hCkpos : (0 : ℝ) < Ck := lt_of_lt_of_le zero_lt_one hCk1
  have hCu : ∀ (j : ℕ), 1 ≤ j → j ≤ 4 → ∀ z : ℝ, 0 < z →
      (1 + z) ^ (j + 1) * |deriv^[j] (fun z : ℝ => u15 z) z| ≤ Cu :=
    fun j hj hj4 z hz => le_trans (hCu0b j hj hj4 z hz) (le_max_left _ _)
  have hCk : ∀ (m : ℕ), m ≤ 4 → ∀ z : ℝ, 0 < z →
      (1 + z) ^ (m + 1) * |deriv^[m] (fun z : ℝ => k15 z) z| ≤ Ck :=
    fun m hm z hz => le_trans (hCk0b m hm z hz) (le_max_left _ _)
  refine ⟨16 * (Cu * Ck + 1), by positivity, ?_⟩
  intro c hc z hz θ
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hcont : ContDiffAt ℝ ((c : ℕ) : WithTop ℕ∞) (fun z : ℝ => u15 z) z ∧
      ContDiffAt ℝ ((c : ℕ) : WithTop ℕ∞) (fun z : ℝ => k15 z) z := by
    constructor
    · have hfun : (fun z : ℝ => u15 z) = fun z : ℝ => z / (1 + z) := by funext w; rw [u15]
      rw [hfun]
      refine ContDiffAt.div ?_ ?_ (by linarith : (1 : ℝ) + z ≠ 0)
      · fun_prop
      · fun_prop
    · have hfun : (fun z : ℝ => k15 z) = fun z : ℝ => z / (1 + z) ^ 2 := by funext w; rw [k15]
      rw [hfun]
      refine ContDiffAt.div ?_ ?_ (pow_ne_zero 2 (by linarith : (1 : ℝ) + z ≠ 0))
      · fun_prop
      · fun_prop
  have hleib : deriv^[c] ((fun z : ℝ => u15 z) * fun z : ℝ => k15 z) z
      = ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * deriv^[i] (fun z : ℝ => u15 z) z
          * deriv^[c - i] (fun z : ℝ => k15 z) z := by
    have h := iteratedDeriv_mul (n := c) (x := z) (f := fun z : ℝ => u15 z)
      (g := fun z : ℝ => k15 z) (by simpa using hcont.1) (by simpa using hcont.2)
    simpa only [iteratedDeriv_eq_iterate] using h
  have hpsi : Work.Spaces.pzIter c (fun z _ => psi15 z) z θ
      = deriv^[c] ((fun z : ℝ => u15 z) * fun z : ℝ => k15 z) z := by
    rw [pzIter_radial_fn]
    rfl
  rw [hpsi, hleib]
  have hterm : ∀ i ∈ Finset.range (c + 1),
      (1 + z) ^ (c + 1) * |(c.choose i : ℝ) * deriv^[i] (fun z : ℝ => u15 z) z
          * deriv^[c - i] (fun z : ℝ => k15 z) z|
        ≤ (c.choose i : ℝ) * (Cu * Ck + 1) := by
    intro i hi
    have hic : i ≤ c := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hk' : |deriv^[c - i] (fun z : ℝ => k15 z) z| ≤ Ck / (1 + z) ^ (c - i + 1) := by
      rw [le_div_iff₀ (pow_pos hz1 _), mul_comm]
      exact hCk (c - i) (by omega) z hz
    have hmain : (1 + z) ^ (c + 1) * (|deriv^[i] (fun z : ℝ => u15 z) z|
        * |deriv^[c - i] (fun z : ℝ => k15 z) z|) ≤ Cu * Ck + 1 := by
      rcases eq_or_ne i 0 with hi0 | hi0
      · subst hi0
        rw [Function.iterate_zero, id_eq]
        have hu' : |u15 z| ≤ 1 := by
          rw [u15, abs_div, abs_of_pos hz1, abs_of_nonneg hz.le, div_le_one hz1]
          linarith
        have hck : |deriv^[c] (fun z : ℝ => k15 z) z| ≤ Ck / (1 + z) ^ (c + 1) := by
          simpa using hk'
        calc (1 + z) ^ (c + 1) * (|u15 z| * |deriv^[c] (fun z : ℝ => k15 z) z|)
            ≤ (1 + z) ^ (c + 1) * (1 * (Ck / (1 + z) ^ (c + 1))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hu' hck (abs_nonneg _) (by norm_num)) (by positivity)
          _ = Ck := by
              rw [one_mul, div_eq_mul_inv]
              rw [show (1 + z) ^ (c + 1) * ((Ck : ℝ) * ((1 + z) ^ (c + 1))⁻¹) = Ck from by
                rw [← mul_assoc, mul_comm ((1 + z) ^ (c + 1)) (Ck : ℝ), mul_assoc,
                  mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hz1)), mul_one]]
          _ ≤ Cu * Ck + 1 := by nlinarith [hCu1, hCk1]
      · have hu' : |deriv^[i] (fun z : ℝ => u15 z) z| ≤ Cu / (1 + z) ^ (i + 1) := by
          rw [le_div_iff₀ (pow_pos hz1 _), mul_comm]
          exact hCu i (Nat.one_le_iff_ne_zero.mpr hi0) (by omega) z hz
        calc (1 + z) ^ (c + 1) * (|deriv^[i] (fun z : ℝ => u15 z) z|
              * |deriv^[c - i] (fun z : ℝ => k15 z) z|)
            ≤ (1 + z) ^ (c + 1) * ((Cu / (1 + z) ^ (i + 1)) * (Ck / (1 + z) ^ (c - i + 1))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hu' hk' (abs_nonneg _)
                  (div_nonneg hCupos.le (pow_nonneg hz1.le _))) (by positivity)
          _ ≤ Cu * Ck + 1 := by
              have heq : (1 + z) ^ (c + 1) * ((Cu / (1 + z) ^ (i + 1))
                    * (Ck / (1 + z) ^ (c - i + 1))) = Cu * Ck / (1 + z) := by
                field_simp
                rw [← pow_succ', ← pow_add,
                  show i + 1 + (c - i + 1) = c + 1 + 1 from by omega]
              rw [heq]
              have hCK : (0 : ℝ) ≤ Cu * Ck := mul_nonneg hCupos.le hCkpos.le
              have hlt : Cu * Ck / (1 + z) ≤ Cu * Ck := by
                rw [div_le_iff₀ hz1]
                nlinarith [hCK, hz]
              linarith
    have habs : |(c.choose i : ℝ) * deriv^[i] (fun z : ℝ => u15 z) z
          * deriv^[c - i] (fun z : ℝ => k15 z) z|
        = (c.choose i : ℝ) * (|deriv^[i] (fun z : ℝ => u15 z) z|
          * |deriv^[c - i] (fun z : ℝ => k15 z) z|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (c.choose i))]
      ring
    rw [habs,
      show (1 + z) ^ (c + 1) * ((c.choose i : ℝ) * (|deriv^[i] (fun z : ℝ => u15 z) z|
            * |deriv^[c - i] (fun z : ℝ => k15 z) z|))
          = (c.choose i : ℝ) * ((1 + z) ^ (c + 1) * (|deriv^[i] (fun z : ℝ => u15 z) z|
            * |deriv^[c - i] (fun z : ℝ => k15 z) z|)) from by ring]
    exact mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _)
  have hsum : (∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * (Cu * Ck + 1))
      = (2 : ℝ) ^ c * (Cu * Ck + 1) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  calc (1 + z) ^ (c + 1) * |∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ)
        * deriv^[i] (fun z : ℝ => u15 z) z * deriv^[c - i] (fun z : ℝ => k15 z) z|
      ≤ (1 + z) ^ (c + 1) * ∑ i ∈ Finset.range (c + 1), |(c.choose i : ℝ)
          * deriv^[i] (fun z : ℝ => u15 z) z * deriv^[c - i] (fun z : ℝ => k15 z) z| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = ∑ i ∈ Finset.range (c + 1), (1 + z) ^ (c + 1) * |(c.choose i : ℝ)
          * deriv^[i] (fun z : ℝ => u15 z) z * deriv^[c - i] (fun z : ℝ => k15 z) z| := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * (Cu * Ck + 1) :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ c * (Cu * Ck + 1) := hsum
    _ ≤ 16 * (Cu * Ck + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h2 : (2 : ℕ) ^ c ≤ 16 := by interval_cases c <;> norm_num
        exact_mod_cast h2

/-- `∂_z ψ(z) = (2z - z²)/(1+z)^4`. -/
theorem deriv_psi15 (z : ℝ) (hz : (1 : ℝ) + z ≠ 0) :
    deriv (fun w : ℝ => psi15 w) z = (2 * z - z ^ 2) / (1 + z) ^ 4 := by
  have hev : (fun w : ℝ => psi15 w) =ᶠ[𝓝 z] fun w : ℝ => w ^ 2 / (1 + w) ^ 3 := by
    have hset : IsOpen {w : ℝ | (1 : ℝ) + w ≠ 0} := isOpen_ne.preimage (by continuity)
    filter_upwards [hset.mem_nhds (by simpa using hz)] with w hw
    rw [psi15_eq]
  rw [hev.deriv_eq]
  change deriv ((fun w : ℝ => w ^ 2) / (fun w : ℝ => (1 + w) ^ 3)) z
      = (2 * z - z ^ 2) / (1 + z) ^ 4
  rw [deriv_div]
  · rw [show deriv (fun w : ℝ => w ^ 2) z = 2 * z from by simp]
    have h2 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have h3 : deriv (fun w : ℝ => (1 + w) ^ 3) z = 3 * (1 + z) ^ 2 * 1 := (h2.pow 3).deriv
    rw [h3]
    field_simp
    ring
  · fun_prop
  · fun_prop
  · exact pow_ne_zero 3 hz

/-- **The radial bound for `ψ`**: for `c ≤ m ≤ 4`, `z > 0`,
`(1+z)·w(z)·z^m·|∂_z^c ψ(z)| ≤ C·(1+z)^{m-c}`. -/
theorem pzIter_psi15_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (c m : ℕ), c ≤ m → m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      (1 + z) * Work.Spaces.w z * z ^ m * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ|
        ≤ C * (1 + z) ^ (m - c) := by
  obtain ⟨C1, hC1pos, hC1⟩ := pzIter_psi15_main
  refine ⟨max (C1 + 1000) 10, lt_of_lt_of_le (by positivity) (le_max_right _ _), ?_⟩
  intro c m hcm hm z hz θ
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hCmax : (1000 : ℝ) ≤ max (C1 + 1000) 10 := le_trans (by linarith) (le_max_left _ _)
  rcases lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · -- `m = 0`
      have hc0 : c = 0 := by omega
      subst hc0
      rw [pow_zero, mul_one, pzIter_radial_fn, Function.iterate_zero, id_eq, psi15_eq,
        Work.Spaces.w]
      have hval : (1 + z) * ((1 + z) ^ 2 / z ^ 2) * |z ^ 2 / (1 + z) ^ 3| = 1 := by
        rw [abs_of_pos (div_pos (pow_pos hz 2) (pow_pos hz1 3))]
        field_simp
      have hexp : (1 + z) ^ (0 - 0) = 1 := by norm_num
      rw [hval, hexp, mul_one]
      exact le_trans (by norm_num : (1 : ℝ) ≤ 1000) hCmax
    · -- `m = 1`
      have hc1 : c = 0 ∨ c = 1 := by omega
      rcases hc1 with hc | hc
      · subst hc
        rw [pow_one, pzIter_radial_fn, Function.iterate_zero, id_eq, psi15_eq, Work.Spaces.w]
        have hval : (1 + z) * ((1 + z) ^ 2 / z ^ 2) * z * |z ^ 2 / (1 + z) ^ 3| = z := by
          rw [abs_of_pos (div_pos (pow_pos hz 2) (pow_pos hz1 3))]
          field_simp
        have hexp : (1 + z) ^ (1 - 0) = 1 + z := by norm_num
        rw [hval, hexp]
        have hl : z ≤ 1000 * (1 + z) := by nlinarith
        have h2 : z ≤ max (C1 + 1000) 10 * (1 + z) :=
          le_trans hl (mul_le_mul_of_nonneg_right hCmax (by positivity))
        linarith
      · subst hc
        rw [pow_one, pzIter_radial_fn, Function.iterate_one,
          deriv_psi15 z (by linarith : (1 : ℝ) + z ≠ 0), Work.Spaces.w]
        have hval : (1 + z) * ((1 + z) ^ 2 / z ^ 2) * z * |(2 * z - z ^ 2) / (1 + z) ^ 4|
            = |2 - z| / (1 + z) := by
          rw [abs_div, abs_of_pos (pow_pos hz1 4),
            show |2 * z - z ^ 2| = z * |2 - z| from by
              rw [show (2 * z - z ^ 2) = z * (2 - z) from by ring, abs_mul,
                abs_of_nonneg hz.le]]
          field_simp
        have hexp : (1 + z) ^ (1 - 1) = 1 := by norm_num
        rw [hval, hexp, mul_one]
        have h2 : |2 - z| / (1 + z) ≤ 2 := by
          rw [div_le_iff₀ hz1]
          rcases le_total z 2 with h | h
          · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - z)]; linarith
          · rw [abs_of_nonpos (by linarith : 2 - z ≤ 0)]; linarith
        have h3 : (2 : ℝ) ≤ max (C1 + 1000) 10 :=
          le_trans (by norm_num) (le_trans (le_add_of_nonneg_left hC1pos.le) (le_max_left _ _))
        linarith
  · -- `m ≥ 2`
    have hstep : (1 + z) * Work.Spaces.w z * z ^ m ≤ (1 + z) ^ (m + 1) := by
      rw [Work.Spaces.w]
      have hzm : z ^ m = z ^ 2 * z ^ (m - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hzm]
      rw [show (1 + z) * ((1 + z) ^ 2 / z ^ 2) * (z ^ 2 * z ^ (m - 2))
          = (1 + z) ^ 3 * z ^ (m - 2) from by
        field_simp]
      have h1 : z ^ (m - 2) ≤ (1 + z) ^ (m - 2) :=
        pow_le_pow_left₀ hz.le (by linarith) _
      calc (1 + z) ^ 3 * z ^ (m - 2) ≤ (1 + z) ^ 3 * (1 + z) ^ (m - 2) :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) 3)
        _ = (1 + z) ^ (m + 1) := by
            rw [← pow_add, show 3 + (m - 2) = m + 1 from by omega]
    have hpow : (1 + z) ^ (m - c) * (1 + z) ^ (c + 1) = (1 + z) ^ (m + 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc (1 + z) * Work.Spaces.w z * z ^ m * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ|
        ≤ (1 + z) ^ (m + 1) * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ| :=
          mul_le_mul_of_nonneg_right hstep (abs_nonneg _)
      _ = (1 + z) ^ (m - c) * ((1 + z) ^ (c + 1)
            * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ|) := by
          rw [hpow.symm, mul_assoc]
      _ ≤ (1 + z) ^ (m - c) * (C1 + 1000) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)
          exact le_trans (hC1 c (by omega) z hz θ) (by linarith)
      _ ≤ max (C1 + 1000) 10 * (1 + z) ^ (m - c) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)

end Work.FTS.NonlinRows
