import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseB7.sum_a_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7

/-- `Work.BoseB7.sum_a_bound`, restricted to an arbitrary finite set of modes:
the weighted sum `Σ_{i∈s} c_i a_i` is controlled, in the Fock form `bp`, by
`(Σ_{i∈s}|c_i|)·(Σ_{i∈s}|c_i| ⟨a_i f, a_i f⟩)`.  The proof is identical to
`sum_a_bound`'s (pair bound + bilinear expansion + the AM–GM double sum); only
the index set changes from `Finset.univ` to `s`, and no `DecidableEq Mode` is
needed. -/
theorem sum_a_bound_finset {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) (c : Mode → ℝ) (s : Finset Mode) (f : F.H) :
    F.bp ((∑ i ∈ s, (c i) • F.a i) f) ((∑ i ∈ s, (c i) • F.a i) f) ≤
      (∑ i ∈ s, |c i|) * (∑ i ∈ s, |c i| * F.bp (F.a i f) (F.a i f)) := by
  have hval : (∑ i ∈ s, (c i) • F.a i) f = ∑ i ∈ s, (c i) • F.a i f := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [hval]
  rw [SumABound.bp_sum_sum F s c (fun i => F.a i f)]
  have hterm : ∀ i ∈ s, ∀ j ∈ s,
      c i * c j * F.bp (F.a i f) (F.a j f) ≤
        |c i| * |c j| *
          ((F.bp (F.a i f) (F.a i f) + F.bp (F.a j f) (F.a j f)) / 2) := by
    intro i _ j _
    have h := SumABound.bp_abs_le F (F.a i f) (F.a j f)
    calc c i * c j * F.bp (F.a i f) (F.a j f)
        ≤ |c i * c j * F.bp (F.a i f) (F.a j f)| := le_abs_self _
      _ = |c i| * |c j| * |F.bp (F.a i f) (F.a j f)| := by rw [abs_mul, abs_mul]
      _ ≤ |c i| * |c j| *
            ((F.bp (F.a i f) (F.a i f) + F.bp (F.a j f) (F.a j f)) / 2) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc ∑ i ∈ s, ∑ j ∈ s, (c i * c j) * F.bp (F.a i f) (F.a j f)
      ≤ ∑ i ∈ s, ∑ j ∈ s,
          |c i| * |c j| *
            ((F.bp (F.a i f) (F.a i f) + F.bp (F.a j f) (F.a j f)) / 2) :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hterm i hi j hj))
    _ = (∑ i ∈ s, |c i|) * (∑ i ∈ s, |c i| * F.bp (F.a i f) (F.a i f)) :=
        SumABound.weighted_amgm s (fun i => |c i|)
          (fun i => F.bp (F.a i f) (F.a i f))

end Work.BoseB7
