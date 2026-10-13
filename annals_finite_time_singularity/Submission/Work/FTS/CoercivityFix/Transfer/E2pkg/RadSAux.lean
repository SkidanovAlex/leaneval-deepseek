/-
# `Transfer/E2pkg/RadSAux.lean` — auxiliary calculus for the `D_z`-iterates of `radS`

The radial profile of the second summand of the transfer defect `E2 α f` is

  `radS α f = −(D_z a)·L₁₂ f + a·Qang f 0 + (D_z b / c)·L₁₂(Transport f)(0)`   on `(0,∞)`,

with `a(z) = 2z/(c(1+z)²)`, `b(z) = 2z²/(1+z)³`.  This file collects the elementary inputs of
the Leibniz expansion of `D_z^j (radS α f)`:

* `DzdIter_Qang_zero` — `D_z^i (Qang f ·) = Qang f i` on `(0,∞)`, `i ≤ 3`;
* the differentiability of `D_z^c` of a product/sum of profiles whose iterates are
  differentiable (`differentiableAt_dzdIter_mul_of`, `differentiableAt_dzdIter_add_of`);
* the decomposition `radS_split` of `radS` on `(0,∞)`;
* the smoothness of the coefficient profiles `ampA`, `ampB`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.H2.QangDiff
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The open half-line `(0,∞)`. -/
abbrev IoiA : Set ℝ := Set.Ioi (0 : ℝ)

/-! ## The `D_z`-iterates of `Qang f 0` -/

/-- **`D_z^i (Qang f ·) = Qang f i` on `(0,∞)`** for `i ≤ 3`. -/
theorem DzdIter_Qang_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ∀ i ≤ 3, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang f 0 z) z = Work.Elliptic.Qang f i z := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hf.reg.2.1
  have hderiv := (Work.FTS.H2.QangDiff α f hα hα1 hsm hmem).1
  intro i
  induction i with
  | zero => intro _ z _; rfl
  | succ i ih =>
      intro hi z hz
      have hprev : Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang f 0 z)
          =ᶠ[𝓝 z] (fun w => Work.Elliptic.Qang f i w) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih (by omega) w hw
      show z * deriv (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang f 0 z)) z
        = Work.Elliptic.Qang f (i + 1) z
      rw [hprev.deriv_eq, (hderiv i (by omega) z hz).deriv]
      field_simp

/-- The angular moments `Qang f i` are differentiable on `(0,∞)` for `i ≤ 2`. -/
theorem differentiableAt_Qang_of_le_two (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) {i : ℕ} (hi : i ≤ 2) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (fun z => Work.Elliptic.Qang f i z) z := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hf.reg.2.1
  exact ((Work.FTS.H2.QangDiff α f hα hα1 hsm hmem).1 i hi z hz).differentiableAt

/-! ## Differentiability of the iterates of products and sums -/

/-- `D_z^c` of a product is differentiable on `(0,∞)` when both factors' iterates are. -/
theorem differentiableAt_dzdIter_mul_of {j : ℕ} {u v : ℝ → ℝ}
    (hu : ∀ c ≤ j, ∀ z ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter c u) z)
    (hv : ∀ c ≤ j, ∀ z ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter c v) z)
    {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter j (fun z => u z * v z)) z := by
  have hub : ∀ c < j, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter c u) z' :=
    fun c hc => hu c (le_of_lt hc)
  have hvb : ∀ c < j, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter c v) z' :=
    fun c hc => hv c (le_of_lt hc)
  have hev : Work.Elliptic.DzdIter j (fun z => u z * v z) =ᶠ[𝓝 z]
      (fun z' => ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b u z' * Work.Elliptic.DzdIter (j - b) v z')) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j u v hub hvb z' hz'
  have hdiff : DifferentiableAt ℝ (fun z' : ℝ => ∑ b ∈ Finset.range (j + 1),
      (j.choose b : ℝ) * (Work.Elliptic.DzdIter b u z' * Work.Elliptic.DzdIter (j - b) v z')) z := by
    refine DifferentiableAt.fun_sum fun b hb => ?_
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hjb : j - b ≤ j := Nat.sub_le _ _
    exact (differentiableAt_const _).mul ((hu b hbj z hz).mul (hv (j - b) hjb z hz))
  exact hdiff.congr_of_eventuallyEq hev

/-- `D_z^j` of a sum is differentiable on `(0,∞)` when both summands' iterates are. -/
theorem differentiableAt_dzdIter_add_of {j : ℕ} {u v : ℝ → ℝ}
    (hu : ∀ b ≤ j, ∀ z ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z)
    (hv : ∀ b ≤ j, ∀ z ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b v) z)
    {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter j (fun z => u z + v z)) z := by
  induction j with
  | zero =>
      have h := (hu 0 le_rfl z hz).add (hv 0 le_rfl z hz)
      change DifferentiableAt ℝ (fun z' => u z' + v z') z
      exact h
  | succ k ih =>
      have hku : ∀ b ≤ k, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z' :=
        fun b hb => hu b (by omega)
      have hkv : ∀ b ≤ k, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b v) z' :=
        fun b hb => hv b (by omega)
      have hub : ∀ b < k, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z' :=
        fun b hb => hu b (by omega)
      have hvb : ∀ b < k, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b v) z' :=
        fun b hb => hv b (by omega)
      have hfun : (fun z' => z' * deriv (Work.Elliptic.DzdIter k u) z'
              + z' * deriv (Work.Elliptic.DzdIter k v) z')
          =ᶠ[𝓝 z] (fun z' => z' * deriv (Work.Elliptic.DzdIter k (fun z => u z + v z)) z') := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        have h1 : Work.Elliptic.DzdIter k (fun z => u z + v z)
            =ᶠ[𝓝 z'] (Work.Elliptic.DzdIter k u + Work.Elliptic.DzdIter k v) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz'] with w hw
          exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff k u v hub hvb w hw
        rw [h1.deriv_eq, deriv_add (hu k (by omega) z' hz') (hv k (by omega) z' hz')]
        ring
      have h2u : Work.Elliptic.DzdIter (k + 1) u
          = fun z' => z' * deriv (Work.Elliptic.DzdIter k u) z' := by
        rw [Work.Elliptic.DzdIter_succ]; rfl
      have h2v : Work.Elliptic.DzdIter (k + 1) v
          = fun z' => z' * deriv (Work.Elliptic.DzdIter k v) z' := by
        rw [Work.Elliptic.DzdIter_succ]; rfl
      have hA : DifferentiableAt ℝ (fun z' => z' * deriv (Work.Elliptic.DzdIter k u) z') z := by
        rw [← h2u]; exact hu (k + 1) (by omega) z hz
      have hB : DifferentiableAt ℝ (fun z' => z' * deriv (Work.Elliptic.DzdIter k v) z') z := by
        rw [← h2v]; exact hv (k + 1) (by omega) z hz
      show DifferentiableAt ℝ (fun z' => z' * deriv (Work.Elliptic.DzdIter k (fun z => u z + v z)) z') z
      exact (hA.add hB).congr_of_eventuallyEq hfun.symm

/-! ## `radS` as an explicit three-term sum on `(0,∞)` -/

/-- **The decomposition of `radS` on `(0,∞)`**: with `z·(L₁₂ f)' = −Qang f 0`
(`E1Parts.DzdIter_L12f_eq_neg_Qang` at `c = 1`), the middle term `−a(z)·z·(L₁₂ f)'(z)` becomes
`+a(z)·Qang f 0 z`. -/
theorem radS_split (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ∀ z ∈ IoiA,
      Work.FTS.CoercivityFix.Transfer.radS α f z
        = -(Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z)
          + Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Elliptic.Qang f 0 z
          + (Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
  intro z hz
  have hQ := Work.FTS.CoercivityFix.Transfer.E1Parts.Qang_zero_eq_integral f z
  have h := Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_L12f_eq_neg_Qang α hα hα1 hf
    1 le_rfl (by norm_num) z hz
  have h1 : Work.Elliptic.DzdIter 1 (Work.Coercivity.L12f f) z
      = z * deriv (Work.Coercivity.L12f f) z := rfl
  rw [h1] at h
  simp only [Work.FTS.CoercivityFix.Transfer.radS]
  rw [h, show (1 : ℕ) - 1 = 0 from rfl, hQ]
  ring_nf

/-! ## Smoothness of the coefficient profiles -/

/-- `ampA α` is `C^5` on `(0,∞)` (it is the rational function `2z/(c(1+z)²)`). -/
theorem contDiffOn_ampA_five (α : ℝ) :
    ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) IoiA := by
  rcases eq_or_ne (Work.Spaces.c α) 0 with hc | hc
  · have h0 : Work.FTS.CoercivityFix.Transfer.ampA α = fun _ : ℝ => (0 : ℝ) := by
      funext z
      simp only [Work.FTS.CoercivityFix.Transfer.ampA, hc, zero_mul, div_zero]
    rw [h0]
    exact contDiffOn_const
  · have hnum : ContDiffOn ℝ 5 (fun z : ℝ => 2 * z) IoiA :=
      contDiffOn_const.mul contDiffOn_id
    have hden : ContDiffOn ℝ 5 (fun z : ℝ => Work.Spaces.c α * (1 + z) ^ 2) IoiA :=
      contDiffOn_const.mul ((contDiffOn_const.add contDiffOn_id).pow 2)
    have hne : ∀ z ∈ IoiA, Work.Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
      intro z hz
      have h1 : (0 : ℝ) < z := hz
      exact mul_ne_zero hc (pow_ne_zero 2 (by linarith))
    show ContDiffOn ℝ 5 (fun z : ℝ => 2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) IoiA
    exact hnum.div hden hne

/-- `ampB α` is `C^5` on `(0,∞)`. -/
theorem contDiffOn_ampB_five (α : ℝ) :
    ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampB α) IoiA := by
  have hnum : ContDiffOn ℝ 5 (fun z : ℝ => 2 * z ^ 2) IoiA :=
    contDiffOn_const.mul (contDiffOn_id.pow 2)
  have hden : ContDiffOn ℝ 5 (fun z : ℝ => (1 + z) ^ 3) IoiA :=
    (contDiffOn_const.add contDiffOn_id).pow 3
  have hne : ∀ z ∈ IoiA, (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have h1 : (0 : ℝ) < z := hz
    exact pow_ne_zero 3 (by linarith)
  show ContDiffOn ℝ 5 (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) IoiA
  exact hnum.div hden hne

/-- Every iterate of order `c` of a `C^{c+1}` function is differentiable on `(0,∞)`. -/
theorem differentiableAt_dzdIter_of_contDiffOn_general {N : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ N u IoiA) {c : ℕ} (hc : c + 1 ≤ N) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter c u) z := by
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
  exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
    (b := c) (hu := hu.of_le (Nat.cast_le.mpr hc)) hz

/-- Every `D_z`-iterate up to order `4` of a `C^5` function is differentiable on `(0,∞)`. -/
theorem differentiableAt_dzdIter_of_contDiffOn_five {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 5 u IoiA) {c : ℕ} (hc : c ≤ 4) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter c u) z := by
  have hc5 : c + 1 ≤ 5 := by omega
  exact differentiableAt_dzdIter_of_contDiffOn_general (c := c) (N := 5) hu hc5 hz

/-- `D_z^c` commutes with multiplication by a constant. -/
theorem dzdIter_const_mul (c : ℝ) (j : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter j (fun z => c * u z)
      = fun z => c * Work.Elliptic.DzdIter j u z := by
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
  exact Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul j c u

/-- `D_z^c` commutes with negation. -/
theorem dzdIter_neg (j : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter j (fun z => -u z) = fun z => -Work.Elliptic.DzdIter j u z := by
  rw [show (fun z => -u z) = fun z => (-1 : ℝ) * u z from by funext z; ring,
    dzdIter_const_mul]
  funext z; ring

end Work.FTS.CoercivityFix.Transfer.E2pkg
