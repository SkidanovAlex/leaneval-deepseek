import Submission.Work.TMComp.Kotani.Assembly
import Submission.Work.TMComp.Kotani.kotani_core_of_local
import Submission.Work.TMComp.RedC8.ae_jump_of_lyap_eq_zero
import Submission.Work.TMComp.RedC8.exists_local_continuation_of_ae_jump

/-!
# C8 (`P_Kotani`) assembled inside C9's own area

The frozen component C8 is produced here from the two halves of the Kotani continuation
argument that the `RedC8`/`LocCantor`/`Kotani` subprojects supply:

* `Work.TMComp.RedC8.ae_jump_of_lyap_eq_zero` — under `lyap = 0` on `(a,b)`, for a.e. phase `y`
  there is `ε_j ↓ 0` along which the `L¹`-in-energy jump of `cayley ∘ Psi` tends to `0`;
* `Work.TMComp.RedC8.exists_local_continuation_of_ae_jump` — that a.e. jump statement gives, for
  every `E₀` of the interval and every phase `x`, a germ of continuation of `mfun α lam · x`
  with the reflection formula below the axis (the `hloc` input of
  `Work.TMComp.Kotani.kotani_core_of_local`).

`ae_jump_of_lyap_eq_zero` controls the jump on a *strict* subinterval `(a',b') ⊂ (a,b)`, so for a
given `E₀ ∈ (a,b)` we apply the pair with the auxiliary interval `((a+E₀)/2, (E₀+b)/2) ∋ E₀`.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMComp.C9Aux

/-- The frozen Kotani component, assembled from `RedC8`'s two halves. -/
theorem P_Kotani_own : Work.TMContract.P_Kotani := by
  refine Work.TMComp.Kotani.prove_Kotani_of_core fun α lam a b hα h0 hab hL => ?_
  refine Work.TMComp.Kotani.kotani_core_of_local α lam a b hα h0 hab hL
    fun E₀ hE₀ x => ?_
  obtain ⟨hE₀a, hE₀b⟩ := hE₀
  have ha' : a < (a + E₀) / 2 := by linarith
  have hb' : (E₀ + b) / 2 < b := by linarith
  have hab' : (a + E₀) / 2 < (E₀ + b) / 2 := by linarith
  have hE₀' : E₀ ∈ Set.Ioo ((a + E₀) / 2) ((E₀ + b) / 2) := by
    refine ⟨by linarith, by linarith⟩
  exact Work.TMComp.RedC8.exists_local_continuation_of_ae_jump α lam ((a + E₀) / 2)
    ((E₀ + b) / 2) hα hab'
    (Work.TMComp.RedC8.ae_jump_of_lyap_eq_zero α lam a b ((a + E₀) / 2) ((E₀ + b) / 2)
      hab ha' hb' hab' hL)
    E₀ hE₀' x

end Work.TMComp.C9Aux

#print axioms Work.TMComp.C9Aux.P_Kotani_own
