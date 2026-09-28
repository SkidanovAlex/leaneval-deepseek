import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.Serre.relEZDefs

/-!
# Degreewise exactness for short complexes of chain complexes

A short complex of chain complexes of `ℤ`-modules is exact if and only if it is exact in every
degree, and a chain complex is zero if and only if all its components are zero.  These are the
elementary facts that let the relative Eilenberg–Zilber theorem be proved by the degreewise
computation of the tensor product with a degreewise flat complex.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **A chain complex of `ℤ`-modules is zero if and only if all its components are zero.** -/
theorem isZero_iff_forall_X (K : ChainComplex (ModuleCat ℤ) ℕ) :
    IsZero K ↔ ∀ n, IsZero (K.X n) := by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h n
    rw [IsZero.iff_id_eq_zero]
    have h' := congrArg (fun (g : K ⟶ K) => g.f n) h
    simpa only [HomologicalComplex.id_f, HomologicalComplex.zero_f] using h'
  · intro h
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.id_f, HomologicalComplex.zero_f]
    exact (IsZero.iff_id_eq_zero _).mp (h n)

/-- **A short complex of chain complexes of `ℤ`-modules is exact if and only if its evaluation in
every degree is exact.** -/
theorem shortComplex_exact_iff_forall_eval (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) :
    S.Exact ↔ ∀ n, (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).Exact := by
  constructor
  · intro h n
    exact ShortComplex.Exact.map h _
  · intro h
    rw [S.exact_iff_isZero_homology, isZero_iff_forall_X]
    intro n
    have h1 : IsZero ((S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).homology) :=
      (ShortComplex.exact_iff_isZero_homology _).mp (h n)
    exact IsZero.of_iso h1
      (S.mapHomologyIso (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).symm

/-- The evaluation of a short complex of chain complexes in degree `n`, with its maps exposed as
the degree-`n` components of the maps of the short complex. -/
theorem eval_exact_iff_function_exact (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) (n : ℕ) :
    (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).Exact ↔
      Function.Exact ((S.f).f n).hom ((S.g).f n).hom := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

end

end Work.Serre
