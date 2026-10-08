import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The torus `Λ ≤ Aut(A(K,θ))` is `Kˣ`
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki.SzA

variable {K : Type*} [Field K] (θ : K ≃+* K)

theorem hLamHom_injective : Function.Injective (hLamHom θ) := by
  intro lam mu h
  have h' : (hLamHom θ lam) (⟨1, 0⟩ : SzA K θ) = (hLamHom θ mu) (⟨1, 0⟩ : SzA K θ) :=
    congrArg (fun (f : MulAut (SzA K θ)) => f (⟨1, 0⟩ : SzA K θ)) h
  have h2 : (lam : K) = (mu : K) := by
    simpa [hLamHom_apply] using congrArg SzA.a h'
  exact Units.ext h2

end Work.ZassenhausSuzuki.SzA
