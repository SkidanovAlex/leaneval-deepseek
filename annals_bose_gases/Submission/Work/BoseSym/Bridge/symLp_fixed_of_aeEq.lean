import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Bridge.SymLpDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The symmetrisation average fixes a.e.-invariant functions

If a square integrable function `f` on configuration space agrees almost
everywhere with its symmetrisation average `symAvgF N f`, then the class
`MemLp.toLp f hf` is a fixed point of the symmetrisation average `symLp N` on
`L²`.

The point is that the hypothesis is much stronger than it looks: since the
symmetrisation average is invariant under every relabelling of the particles
(`Submission.BoseGases.symAvg_sym`), `f` itself agrees almost everywhere with a
permutation invariant function, hence `f` is almost everywhere invariant.  At
the level of `L²` this says `permLp N σ (toLp f) = toLp f` for every `σ`, using
`Perm.permLp_toLp`; averaging over the `N!` permutations and multiplying by
`(N!)⁻¹` produces the identity.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory

theorem symLp_fixed_of_aeEq {N : ℕ} {f : Work.BoseSym.Conf N → ℝ}
    (hf : MeasureTheory.MemLp f 2 (Work.BoseSym.volC N))
    (h : Work.BoseSym.AEEq N f (Work.BoseSym.symAvgF N f)) :
    Work.BoseSym.symLp N (MeasureTheory.MemLp.toLp f hf) =
      MeasureTheory.MemLp.toLp f hf := by
  have hh : f =ᵐ[Work.BoseSym.volC N] Work.BoseSym.symAvgF N f := h
  -- `f` is a.e. invariant: it agrees a.e. with the a.e. permutation invariant
  -- function `symAvgF N f`.
  have hfix : ∀ σ : Equiv.Perm (Fin N),
      Work.BoseSym.permLp N σ (MeasureTheory.MemLp.toLp f hf) =
        MeasureTheory.MemLp.toLp f hf := by
    intro σ
    rw [Work.BoseSym.Perm.permLp_toLp σ hf]
    refine MeasureTheory.MemLp.toLp_congr _ _ ?_
    have h1 : (fun x => f (Work.BoseSym.tauPerm N σ x)) =ᵐ[Work.BoseSym.volC N]
        (fun x => Work.BoseSym.symAvgF N f (Work.BoseSym.tauPerm N σ x)) :=
      ((Work.BoseSym.measurePreserving_tauPerm N σ).quasiMeasurePreserving).ae_eq hh
    have h2 : (fun x => Work.BoseSym.symAvgF N f (Work.BoseSym.tauPerm N σ x))
        =ᵐ[Work.BoseSym.volC N] Work.BoseSym.symAvgF N f :=
      Filter.EventuallyEq.of_eq (funext fun x => Submission.BoseGases.symAvg_sym N f σ x)
    exact (h1.trans h2).trans hh.symm
  -- Average the fixed points over the symmetric group.
  rw [Work.BoseSym.symLp_apply]
  have hsum : (∑ σ : Equiv.Perm (Fin N),
        Work.BoseSym.permLp N σ (MeasureTheory.MemLp.toLp f hf))
      = (∑ _σ : Equiv.Perm (Fin N), MeasureTheory.MemLp.toLp f hf) :=
    Finset.sum_congr rfl (fun σ _ => hfix σ)
  rw [hsum]
  have hcard : ((Fintype.card (Equiv.Perm (Fin N)) : ℕ) : ℝ) = (Nat.factorial N : ℝ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, hcard, smul_smul,
    inv_mul_cancel₀ (by positivity : (Nat.factorial N : ℝ) ≠ 0), one_smul]

end Work.BoseSym.Bridge
