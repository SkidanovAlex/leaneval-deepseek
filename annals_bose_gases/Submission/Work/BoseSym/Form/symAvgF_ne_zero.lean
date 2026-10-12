import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Form — the symmetrisation average of a nonzero a.e. nonnegative function

`symAvgF N f` is the symmetrisation average `(N!)⁻¹ · ∑_σ f(σ · x)` of `f`.
The point of this file is that the operation `f ↦ symAvgF N f` cannot kill an
almost-everywhere nonnegative function that is not almost-everywhere zero:

`AENonneg N f → ¬ AEEq N f 0 → ¬ AEEq N (symAvgF N f) 0`.

The proof is purely almost-everywhere.  Assume `symAvgF N f =ᵐ 0`, i.e.
`(N!)⁻¹ · ∑_σ f(σ · x) = 0` for almost every `x`; since `(N!)⁻¹ ≠ 0` this
gives `∑_σ f(σ · x) = 0` a.e.  Permutations of the particle labels preserve
Lebesgue measure, so each summand `f(σ · x)` is again a.e. nonnegative.  A sum
of a.e. nonnegative terms that vanishes a.e. has each term vanishing a.e.
(`Finset.sum_eq_zero_iff_of_nonneg`), applied at `σ = 1` gives `f =ᵐ 0`,
contradicting `hf0`.
-/

namespace Work.BoseSym.Form

open MeasureTheory Filter
open scoped Topology Real ENNReal

theorem symAvgF_ne_zero {N : ℕ} {f : Conf N → ℝ} (hfnn : AENonneg N f)
    (hf0 : ¬ AEEq N f 0) : ¬ AEEq N (symAvgF N f) 0 := by
  intro h
  refine hf0 ?_
  have hfnn' : ∀ᵐ x ∂(volC N), 0 ≤ f x := hfnn
  simp only [AEEq, Pi.zero_apply] at h ⊢
  simp only [symAvgF, Submission.BoseGases.symAvg] at h
  -- `h : ∀ᵐ x, (N!)⁻¹ * ∑ σ, f (actPerm σ x) = 0`
  have hS : ∀ᵐ x ∂(volC N),
      ∑ σ : Equiv.Perm (Fin N), f (Submission.BoseGases.actPerm N σ x) = 0 := by
    filter_upwards [h] with x hx
    have hc : (Nat.factorial N : ℝ) ≠ 0 := by positivity
    rcases mul_eq_zero.mp hx with h1 | h2
    · exact absurd h1 (one_div_ne_zero hc)
    · exact h2
  have hterm : ∀ᵐ x ∂(volC N),
      ∀ σ : Equiv.Perm (Fin N), 0 ≤ f (Submission.BoseGases.actPerm N σ x) := by
    rw [Filter.eventually_all]
    intro σ
    exact (measurePreserving_tauPerm N σ).quasiMeasurePreserving.ae
      (p := fun y => 0 ≤ f y) hfnn'
  filter_upwards [hterm, hS] with x hxterm hxS
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun σ : Equiv.Perm (Fin N) => f (Submission.BoseGases.actPerm N σ x))
      (fun σ _ => hxterm σ)).mp hxS
  have h2 : f (Submission.BoseGases.actPerm N (1 : Equiv.Perm (Fin N)) x) = 0 :=
    h1 1 (Finset.mem_univ 1)
  have h3 : Submission.BoseGases.actPerm N (1 : Equiv.Perm (Fin N)) x = x := by
    ext i
    simp [Submission.BoseGases.actPerm]
  rwa [h3] at h2

end Work.BoseSym.Form
