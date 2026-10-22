import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.SINGMV.Defs
import Submission.Work.SingMV.mono_pushout_desc

/-!
# AREA SINGMV — small simplices: from an acyclic cokernel to the Mayer–Vietoris quasi-isomorphism

This file contains the final bookkeeping step of the small-simplex (Hatcher Proposition 2.21)
argument: if the pushout map of an open cover is injective and its cokernel is acyclic, then it is
a quasi-isomorphism. The acyclicity itself (which is where the barycentric subdivision and the
Lebesgue number argument are used) is proven in `Submission/Work/SingMV/acyclic_coker_pushout.lean`.
-/

open CategoryTheory Limits HomologicalComplex

noncomputable section

namespace Work.SingMV

/-- **From an acyclic cokernel to a quasi-isomorphism.** For open `U, V ⊆ X` with `U ∪ V = X`, if
the cokernel of the pushout map `C(U) + C(V) → C(X)` is acyclic, then this map is a
quasi-isomorphism. -/
theorem quasiIso_of_acyclic_coker (X : TopCat) (U V : Set X)
    (h : (cokernel (pushoutMap X U V)).Acyclic) : QuasiIso (pushoutMap X U V) := by
  have hf : Mono (pushoutMap X U V) := mono_pushout_desc X U V
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (pushoutMap X U V) (cokernel.π (pushoutMap X U V))
      (cokernel.condition (pushoutMap X U V))
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel (pushoutMap X U V))
      mono_f := hf
      epi_g := inferInstance }
  have hQ : S.X₃.Acyclic := h
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hQj : IsZero (S.X₃.homology j) := (exactAt_iff_isZero_homology S.X₃ j).mp (hQ j)
  have hQj1 : IsZero (S.X₃.homology (j + 1)) :=
    (exactAt_iff_isZero_homology S.X₃ (j + 1)).mp (hQ (j + 1))
  haveI : Epi (homologyMap S.f j) := by
    refine ShortComplex.Exact.epi_f (hS.homology_exact₂ j) ?_
    exact IsZero.eq_of_tgt hQj (homologyMap S.g j) 0
  haveI : Mono (homologyMap S.f j) := by
    refine ShortComplex.Exact.mono_g (hS.homology_exact₁ (j + 1) j (by simp)) ?_
    exact IsZero.eq_of_src hQj1 (hS.δ (j + 1) j (by simp)) 0
  exact CategoryTheory.Balanced.isIso_of_mono_of_epi (homologyMap S.f j)

end Work.SingMV
