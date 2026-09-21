import Mathlib
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Commons.Geometry.Ulam

open scoped ContDiff Topology
open Finset

noncomputable section

/-- The explicit Faà-di-Bruno polynomial for the `m`-th derivative of `u ^ α`.
It is written in the polynomial form obtained from
`iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` and
`Real.iter_deriv_rpow_const`.  This is the canonical replacement for the
`Classical.choose` witness in `exists_iteratedDeriv_rpow`. -/
def faaDiBrunoJ (m : ℕ) (α : ℝ) (s : ℝ) (v : Fin (m + 1) → ℝ) : ℝ :=
  ∑ c : OrderedFinpartition m,
    (Polynomial.eval α (descPochhammer ℝ c.length)) *
      (∏ j : Fin c.length, v ⟨c.partSize j, Nat.lt_succ_of_le (c.partSize_le j)⟩) *
      v 0 ^ (m - c.length)

/-- The explicit Faà-di-Bruno `J` represents the `m`-th derivative of `u ^ α`
on the positive region. -/
lemma faaDiBrunoJ_spec (m : ℕ) (α : ℝ) :
    ∀ (u : ℝ → ℝ) (s : ℝ),
      ContDiff ℝ ∞ u → 0 < u s →
      iteratedDeriv m (fun x : ℝ => u x ^ α) s =
        faaDiBrunoJ m α s (fun i : Fin (m + 1) => iteratedDeriv i.1 u s) *
          u s ^ (α - m) := by
  intro u s hu hpos
  have hg : ContDiffAt ℝ ∞ (fun x : ℝ => x ^ α) (u s) :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hpos)
  have hf : ContDiffAt ℝ ∞ u s := hu.contDiffAt
  have hfaa := iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    (g := fun x : ℝ => x ^ α) (f := u) (x := s) (n := ∞) (i := m) hg hf
    (WithTop.coe_le_coe.mpr le_top)
  have hcomp : ((fun x : ℝ => x ^ α) ∘ u) = fun x : ℝ => u x ^ α := rfl
  rw [hcomp] at hfaa
  rw [hfaa]
  -- Rewrite each Faà-di-Bruno summand into the polynomial form.
  have hterm : ∀ c : OrderedFinpartition m,
      (iteratedFDeriv ℝ c.length (fun x : ℝ => x ^ α) (u s))
          (fun j : Fin c.length => iteratedDeriv (c.partSize j) u s) =
        (Polynomial.eval α (descPochhammer ℝ c.length)) *
          (∏ j : Fin c.length, iteratedDeriv (c.partSize j) u s) *
          u s ^ (α - c.length) := by
    intro c
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
    ring
  calc
    (∑ c : OrderedFinpartition m,
        (iteratedFDeriv ℝ c.length (fun x : ℝ => x ^ α) (u s))
          (fun j : Fin c.length => iteratedDeriv (c.partSize j) u s))
        = ∑ c : OrderedFinpartition m,
            (Polynomial.eval α (descPochhammer ℝ c.length)) *
              (∏ j : Fin c.length, iteratedDeriv (c.partSize j) u s) *
              u s ^ (α - c.length) := by
          apply sum_congr rfl
          intro c _
          exact hterm c
    _ = (∑ c : OrderedFinpartition m,
            (Polynomial.eval α (descPochhammer ℝ c.length)) *
              (∏ j : Fin c.length, iteratedDeriv (c.partSize j) u s) *
              u s ^ (m - c.length)) * u s ^ (α - m) := by
          rw [sum_mul]
          apply sum_congr rfl
          intro c _
          have hcl : c.length ≤ m := c.length_le
          have hcast : ((m - c.length : ℕ) : ℝ) = (m : ℝ) - (c.length : ℝ) :=
            Nat.cast_sub hcl
          have hsplit : (α - (c.length : ℝ)) =
              ((m - c.length : ℕ) : ℝ) + (α - (m : ℝ)) := by
            rw [hcast]
            ring
          rw [hsplit, Real.rpow_add hpos]
          rw [Real.rpow_natCast]
          ring
    _ = faaDiBrunoJ m α s (fun i : Fin (m + 1) => iteratedDeriv i.1 u s) *
          u s ^ (α - m) := by
          simp [faaDiBrunoJ]

/-- The explicit Faà-di-Bruno `J` is smooth in the jet variable on the positive
region `0 < v 0`. -/
lemma faaDiBrunoJ_contDiffOn (m : ℕ) (α s : ℝ) :
    ContDiffOn ℝ ∞ (fun v : Fin (m + 1) → ℝ => faaDiBrunoJ m α s v)
      {v | 0 < v 0} := by
  unfold faaDiBrunoJ
  apply ContDiffOn.sum
  intro c _
  apply ContDiffOn.mul
  · apply ContDiffOn.mul
    · exact contDiffOn_const
    · apply contDiffOn_prod
      intro j _
      fun_prop
  · apply ContDiffOn.pow
    fun_prop

end

end Commons.Geometry.Ulam
