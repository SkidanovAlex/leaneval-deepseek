import Submission.Work.Stems.Hur2c.T_endpoint
import Submission.Work.Stems.Hur2c.degenCube_boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The identity `Ψ = Λ ∘ ∂` on degenerate `2`-cubes

The structural step of `PsiLin_eq_zero_of_degen_cycle`: a degenerate `2`-chain lies in the span of
the cubes `degenCube k δ`, and on those we have the *linear* identity
`Ψ (single (degenCube k δ) 1) = Λ (∂ (single (degenCube k δ) 1))` for the `ℤ`-linear functional

`Λ (single e 1) := -φ (e 0)`,   `φ v := T x₀ 0 (cubeOfPath (K₀ x₀ v))`

(the sign is chosen so that `Λ ∘ ∂` reproduces `Ψ`, cf. `T_endpoint`).  Because `Ψ` and `Λ ∘ ∂` are
both additive and `ℤ`-linear, the identity extends from the generators to the whole span, and then
`∂ d = 0` gives `Ψ d = 0`.  — that is the inductive step, so no explicit decomposition of `d` is
needed.

(Formalisation note: the two cases `k = 0`, `k = 1` are proved as separate lemmas with *literal*
indices, and the general `k : Fin 2` is obtained by `fin_cases` + `exact`.  Rewriting directly under
`fin_cases` fails because the elaborated index has the shape `(fun i => i) ⟨0, ⋯⟩`, which `rw` does
not match against the literal `0`.)
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2c

open Work.Stems.Cubical
open Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- **The linear functional on `1`-chains** whose pull-back along `∂` is `Ψ` on degenerate
`2`-cubes: `Λ (single e 1) = -φ (e 0)`. -/
def Lambda (x₀ : X) : Cub 1 X →ₗ[ℤ] Additive (HomotopyGroup (Fin 2) X x₀) :=
  Finsupp.linearCombination ℤ fun e => - T x₀ 0 (cubeOfPath (Hur2.K₀ x₀ (e 0)))

@[simp] theorem Lambda_single (x₀ : X) (e : C(IC 1, X)) :
    Lambda x₀ (Finsupp.single e 1) = - T x₀ 0 (cubeOfPath (Hur2.K₀ x₀ (e 0))) := by
  rw [Lambda, Finsupp.linearCombination_single, one_smul]

/-- **The identity `Ψ = Λ ∘ ∂` on the generator** `degenCube 0 δ`. -/
theorem PsiLin_single_degen_zero (x₀ : X) (δ : C(IC 1, X)) :
    Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (degenCube 0 δ) 1)
      = Lambda x₀ (cubD 1 X (Finsupp.single (degenCube 0 δ) 1)) := by
  letI : CommGroup (HomotopyGroup (Fin 2) X x₀) := HomotopyGroup.commGroup
  rw [← T_def]
  rw [(degenCube_boundary δ).1, map_sub, Lambda_single, Lambda_single,
      ContinuousMap.const_apply, ContinuousMap.const_apply, T_endpoint x₀ δ]
  abel

/-- **The identity `Ψ = Λ ∘ ∂` on the generator** `degenCube 1 δ`. -/
theorem PsiLin_single_degen_one (x₀ : X) (δ : C(IC 1, X)) :
    Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (degenCube 1 δ) 1)
      = Lambda x₀ (cubD 1 X (Finsupp.single (degenCube 1 δ) 1)) := by
  letI : CommGroup (HomotopyGroup (Fin 2) X x₀) := HomotopyGroup.commGroup
  rw [← T_def]
  rw [(degenCube_boundary δ).2, map_sub, Lambda_single, Lambda_single,
      ContinuousMap.const_apply, ContinuousMap.const_apply, T_coord x₀ δ, T_endpoint x₀ δ]
  abel

/-- **The identity `Ψ = Λ ∘ ∂` on the generators** `degenCube k δ`. -/
theorem PsiLin_single_degen (x₀ : X) (k : Fin 2) (δ : C(IC 1, X)) :
    Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (degenCube k δ) 1)
      = Lambda x₀ (cubD 1 X (Finsupp.single (degenCube k δ) 1)) := by
  fin_cases k
  · exact PsiLin_single_degen_zero x₀ δ
  · exact PsiLin_single_degen_one x₀ δ

end

end Work.Stems.Hur2c
