/-
Copyright: work module for the Elgindi finite-time singularity project.

# The iterated Leibniz rule for `Zop u = z·u'` on a general open set

`Work.Spaces.Zop u = fun z => z * deriv u z` is the radial derivation `z ∂_z`.  For `u, v`
of class `C^N` on an open set `U ⊆ ℝ` the iterates of `Zop` satisfy the binomial Leibniz
rule
`Zop^[N] (u*v) = ∑_{b ≤ N} (N.choose b) • (Zop^[b] u * Zop^[N-b] v)`
on `U`.  The proof is the usual induction: one `Zop`-step is the product rule (the derivative
of `z ↦ z` is `1`, whence the coefficients stay binomial), and the transition from level `N`
to level `N+1` is Pascal's identity (`Work.Spaces.leibniz_step`).  The only smoothness input
beyond `C^N` on `U` is that the `b`-th iterate `Zop^[b] u` is differentiable on `U` for
`b ≤ N - 1`, which follows from `u ∈ C^N(U)` (`Zop_contDiffOn_iter`): `Zop^[b] u` is a
polynomial in `z` and `u', …, u^(b)`, hence of class `C^{N-b}`.

Unlike the `C^∞` version `Work.Spaces.Zop_DerivLike` (which is tied to the fixed set
`Ioi (-1)` and to the full smooth class) this chapter works with an arbitrary open `U` and a
finite order `N`, which is exactly the hypothesis of `ZopIterLeibniz`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.DerivLikeBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.FinalClock

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {U : Set ℝ}

/-! ## `Zop`-calculus on an open set -/

/-- The derivative of a `C^{n+1}` function on an open set is `C^n` there. -/
theorem contDiffOn_deriv_of_succ_open {u : ℝ → ℝ} (hU : IsOpen U) (n : ℕ)
    (hu : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞ω) u U) :
    ContDiffOn ℝ (((n : ℕ)) : ℕ∞ω) (deriv u) U := by
  have hfd : ContDiffOn ℝ (((n : ℕ)) : ℕ∞ω) (fderiv ℝ u) U :=
    hu.fderiv_of_isOpen hU (by push_cast; exact le_rfl)
  have hev : ContDiffOn ℝ (((n : ℕ)) : ℕ∞ω) (fun z : ℝ => (fderiv ℝ u z) 1) U :=
    hfd.clm_apply contDiffOn_const
  refine hev.congr (fun z _ => ?_)
  rw [fderiv_apply_one_eq_deriv]

/-- A `C^{b+k}` function has `C^k` `Zop`-iterates of order `b`. -/
theorem Zop_contDiffOn_iter {u : ℝ → ℝ} (hU : IsOpen U) (b k : ℕ)
    (hu : ContDiffOn ℝ (((b + k : ℕ)) : ℕ∞ω) u U) :
    ContDiffOn ℝ (((k : ℕ)) : ℕ∞ω) (Work.Spaces.Zop^[b] u) U := by
  induction b generalizing k with
  | zero => simpa [Nat.zero_add] using hu
  | succ b ih =>
    have hu' : ContDiffOn ℝ (((b + (k + 1) : ℕ)) : ℕ∞ω) u U :=
      hu.of_le (by exact_mod_cast (by omega : b + (k + 1) ≤ (b + 1) + k))
    have h1 : ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞ω) (Work.Spaces.Zop^[b] u) U := ih (k + 1) hu'
    have h2 : ContDiffOn ℝ (((k : ℕ)) : ℕ∞ω) (deriv (Work.Spaces.Zop^[b] u)) U :=
      contDiffOn_deriv_of_succ_open hU k h1
    have h3 : ContDiffOn ℝ (((k : ℕ)) : ℕ∞ω)
        (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z) U :=
      (contDiff_id.contDiffOn).mul h2
    rw [Function.iterate_succ_apply']
    change ContDiffOn ℝ (((k : ℕ)) : ℕ∞ω)
      (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z) U
    exact h3

/-- `Zop` respects `EqOn` on an open set. -/
theorem Zop_congr_open {A B : ℝ → ℝ} (hU : IsOpen U) (h : Set.EqOn A B U) :
    Set.EqOn (Work.Spaces.Zop A) (Work.Spaces.Zop B) U := by
  intro z hz
  show Work.Spaces.Zop A z = Work.Spaces.Zop B z
  simp only [Work.Spaces.Zop]
  rw [h.deriv hU hz]

/-- `Zop` is additive on differentiable functions. -/
theorem Zop_add_open {A B : ℝ → ℝ} {z : ℝ} (hA : DifferentiableAt ℝ A z)
    (hB : DifferentiableAt ℝ B z) :
    Work.Spaces.Zop (A + B) z = Work.Spaces.Zop A z + Work.Spaces.Zop B z := by
  simp only [Work.Spaces.Zop]
  rw [deriv_add hA hB]
  ring

/-- `Zop` satisfies the Leibniz rule on differentiable functions. -/
theorem Zop_mul_open {A B : ℝ → ℝ} {z : ℝ} (hA : DifferentiableAt ℝ A z)
    (hB : DifferentiableAt ℝ B z) :
    Work.Spaces.Zop (A * B) z = Work.Spaces.Zop A z * B z + A z * Work.Spaces.Zop B z := by
  simp only [Work.Spaces.Zop]
  rw [deriv_mul hA hB]
  ring

/-- The combined product/scalar rule needed for the summands of the Leibniz sum. -/
theorem Zop_const_mul_mul_open (c : ℝ) {X Y : ℝ → ℝ} {z : ℝ}
    (hX : DifferentiableAt ℝ X z) (hY : DifferentiableAt ℝ Y z) :
    Work.Spaces.Zop (fun w => c * (X w * Y w)) z
      = c * (Work.Spaces.Zop X z * Y z + X z * Work.Spaces.Zop Y z) := by
  have hXY : DifferentiableAt ℝ (fun w : ℝ => X w * Y w) z := hX.mul hY
  have h1 : deriv (fun w : ℝ => c * (X w * Y w)) z
      = c * deriv (fun w : ℝ => X w * Y w) z :=
    deriv_const_mul c hXY
  have h2 : deriv (fun w : ℝ => X w * Y w) z = deriv X z * Y z + X z * deriv Y z :=
    deriv_mul hX hY
  simp only [Work.Spaces.Zop]
  rw [h1, h2]
  ring

/-- `Zop` is linear over finite sums of differentiable functions. -/
theorem Zop_sum_range_open (K : ℕ) (A : ℕ → ℝ → ℝ) {z : ℝ}
    (hA : ∀ b ≤ K, DifferentiableAt ℝ (A b) z) :
    Work.Spaces.Zop (fun w => ∑ b ∈ Finset.range (K + 1), A b w) z
      = ∑ b ∈ Finset.range (K + 1), Work.Spaces.Zop (A b) z := by
  have hd : ∀ b ∈ Finset.range (K + 1), DifferentiableAt ℝ (A b) z :=
    fun b hb => hA b (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
  simp only [Work.Spaces.Zop]
  rw [deriv_fun_sum hd, Finset.mul_sum]

/-! ## The Leibniz sum and the induction -/

/-- The binomial Leibniz sum for `Zop^[N]`. -/
def Zsum (N : ℕ) (u v : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∑ b ∈ Finset.range (N + 1),
    (N.choose b : ℝ) * (Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N - b] v z)

/-- The iterated Leibniz rule for `Zop` on an open set, at finite order `N`. -/
theorem Zop_iter_mul_open (hU : IsOpen U) (N : ℕ) :
    ∀ {u v : ℝ → ℝ}, ContDiffOn ℝ N u U → ContDiffOn ℝ N v U →
      Set.EqOn (Work.Spaces.Zop^[N] (u * v)) (Zsum N u v) U := by
  induction N with
  | zero =>
    intro u v _ _ z _
    show (u * v) z = Zsum 0 u v z
    simp [Zsum]
  | succ N ih =>
    intro u v hu hv z hz
    have huN : ContDiffOn ℝ N u U := hu.of_le (by exact_mod_cast Nat.le_succ N)
    have hvN : ContDiffOn ℝ N v U := hv.of_le (by exact_mod_cast Nat.le_succ N)
    have hIH : Set.EqOn (Work.Spaces.Zop^[N] (u * v)) (Zsum N u v) U := ih huN hvN
    -- differentiability of the individual iterates
    have hdiff_u : ∀ b ≤ N, DifferentiableAt ℝ (Work.Spaces.Zop^[b] u) z := by
      intro b hb
      have hcast : (((b + (N + 1 - b) : ℕ)) : ℕ∞ω) = (((N + 1 : ℕ)) : ℕ∞ω) := by
        rw [show b + (N + 1 - b) = N + 1 from by omega]
      have hu'' : ContDiffOn ℝ (((b + (N + 1 - b) : ℕ)) : ℕ∞ω) u U := by
        rw [hcast]; exact hu
      have h1 : ContDiffOn ℝ (((N + 1 - b : ℕ)) : ℕ∞ω) (Work.Spaces.Zop^[b] u) U :=
        Zop_contDiffOn_iter hU b (N + 1 - b) hu''
      have h2 : (1 : ℕ) ≤ N + 1 - b := by omega
      exact ((h1.of_le (by exact_mod_cast h2)).differentiableOn_one).differentiableAt
        (hU.mem_nhds hz)
    have hdiff_v : ∀ b ≤ N, DifferentiableAt ℝ (Work.Spaces.Zop^[N - b] v) z := by
      intro b hb
      have hcast : ((((N - b) + (b + 1) : ℕ)) : ℕ∞ω) = (((N + 1 : ℕ)) : ℕ∞ω) := by
        rw [show (N - b) + (b + 1) = N + 1 from by omega]
      have hv'' : ContDiffOn ℝ ((((N - b) + (b + 1) : ℕ)) : ℕ∞ω) v U := by
        rw [hcast]; exact hv
      have h1 : ContDiffOn ℝ (((b + 1 : ℕ)) : ℕ∞ω) (Work.Spaces.Zop^[N - b] v) U :=
        Zop_contDiffOn_iter hU (N - b) (b + 1) hv''
      have h2 : (1 : ℕ) ≤ b + 1 := by omega
      exact ((h1.of_le (by exact_mod_cast h2)).differentiableOn_one).differentiableAt
        (hU.mem_nhds hz)
    have hdiff_XY : ∀ b ≤ N, DifferentiableAt ℝ
        (fun w => Work.Spaces.Zop^[b] u w * Work.Spaces.Zop^[N - b] v w) z :=
      fun b hb => (hdiff_u b hb).mul (hdiff_v b hb)
    have hdiff_A : ∀ b ≤ N, DifferentiableAt ℝ
        (fun w => (N.choose b : ℝ)
          * (Work.Spaces.Zop^[b] u w * Work.Spaces.Zop^[N - b] v w)) z :=
      fun b hb => (hdiff_XY b hb).const_mul _
    calc Work.Spaces.Zop^[N + 1] (u * v) z
        = Work.Spaces.Zop (Work.Spaces.Zop^[N] (u * v)) z := by
          rw [Function.iterate_succ_apply']
      _ = Work.Spaces.Zop (Zsum N u v) z := by
          show z * deriv (Work.Spaces.Zop^[N] (u * v)) z = z * deriv (Zsum N u v) z
          rw [hIH.deriv hU hz]
      _ = ∑ b ∈ Finset.range (N + 1), Work.Spaces.Zop
            (fun w => (N.choose b : ℝ)
              * (Work.Spaces.Zop^[b] u w * Work.Spaces.Zop^[N - b] v w)) z := by
          exact Zop_sum_range_open N
            (fun b w => (N.choose b : ℝ)
              * (Work.Spaces.Zop^[b] u w * Work.Spaces.Zop^[N - b] v w))
            (z := z) hdiff_A
      _ = ∑ b ∈ Finset.range (N + 1), (N.choose b : ℝ)
            * (Work.Spaces.Zop^[b + 1] u z * Work.Spaces.Zop^[N - b] v z
              + Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N - b + 1] v z) := by
          apply Finset.sum_congr rfl
          intro b hb
          have hbN : b ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
          have hstep : Work.Spaces.Zop
              (fun w => (N.choose b : ℝ)
                * (Work.Spaces.Zop^[b] u w * Work.Spaces.Zop^[N - b] v w)) z
              = (N.choose b : ℝ)
                * (Work.Spaces.Zop^[b + 1] u z * Work.Spaces.Zop^[N - b] v z
                  + Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N - b + 1] v z) := by
            rw [Zop_const_mul_mul_open (N.choose b : ℝ) (hdiff_u b hbN) (hdiff_v b hbN),
              ← Function.iterate_succ_apply' Work.Spaces.Zop b u,
              ← Function.iterate_succ_apply' Work.Spaces.Zop (N - b) v]
          exact hstep
      _ = ∑ b ∈ Finset.range (N + 1 + 1), ((N + 1).choose b : ℝ)
            * (Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N + 1 - b] v z) :=
          Work.Spaces.leibniz_step N (fun i => Work.Spaces.Zop^[i] u z)
            (fun i => Work.Spaces.Zop^[i] v z)
      _ = Zsum (N + 1) u v z := by
          simp only [Zsum]

/-- **The iterated Leibniz rule for `Zop u = z·u'`.**  For `u, v` of class `C^N` on an open
set `U`, the `N`-th iterate of `Zop` of the product is the binomial convolution of the
iterates. -/
theorem ZopIterLeibniz {N : ℕ} {U : Set ℝ} (hU : IsOpen U) {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ N u U) (hv : ContDiffOn ℝ N v U) :
    Set.EqOn (Work.Spaces.Zop^[N] (u * v))
      (fun z => ∑ b ∈ Finset.range (N + 1),
        (N.choose b : ℝ) * (Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N - b] v z)) U := by
  intro z hz
  have hz' := Zop_iter_mul_open hU N hu hv hz
  show Work.Spaces.Zop^[N] (u * v) z = ∑ b ∈ Finset.range (N + 1),
    (N.choose b : ℝ) * (Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N - b] v z)
  rw [hz']
  simp only [Zsum]

end Work.FTS.FinalClock
