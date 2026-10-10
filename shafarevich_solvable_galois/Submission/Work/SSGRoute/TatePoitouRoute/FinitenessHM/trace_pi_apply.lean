import Mathlib.RingTheory.Trace.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Module

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

noncomputable section

/-- **Trace on a finite product.**  The trace of a pointwise multiplication on a finite product of
`R`-algebras is the sum of the traces of its components. -/
theorem trace_pi_apply {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] [∀ i, Module.Free R (B i)]
    [∀ i, Module.Finite R (B i)] (x : ∀ i, B i) :
    Algebra.trace R (∀ i, B i) x = ∑ i, Algebra.trace R (B i) (x i) := by
  classical
  have hb : ∀ i, Basis (Module.Free.ChooseBasisIndex R (B i)) R (B i) :=
    fun i => Module.Free.chooseBasis R (B i)
  have hdiag : ∀ (i : ι) (k : Module.Free.ChooseBasisIndex R (B i)),
      Algebra.leftMulMatrix (Pi.basis hb) x ⟨i, k⟩ ⟨i, k⟩
        = Algebra.leftMulMatrix (hb i) (x i) k k := by
    intro i k
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
    simp only [Pi.basis_repr, Pi.basis_apply, Pi.mul_apply, Pi.single_eq_same]
  have hsum : Matrix.trace (Algebra.leftMulMatrix (Pi.basis hb) x)
      = ∑ i, Matrix.trace (Algebra.leftMulMatrix (hb i) (x i)) := by
    rw [Matrix.trace]
    rw [show (Finset.univ : Finset (Σ i, Module.Free.ChooseBasisIndex R (B i)))
        = Finset.univ.sigma (fun _ => Finset.univ) from Finset.univ_sigma_univ]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun k _ => ?_
    simpa using hdiag i k
  rw [Algebra.trace_eq_matrix_trace (Pi.basis hb), hsum]
  exact Finset.sum_congr rfl fun i _ =>
    (Algebra.trace_eq_matrix_trace (hb i) (x i)).symm

end

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
