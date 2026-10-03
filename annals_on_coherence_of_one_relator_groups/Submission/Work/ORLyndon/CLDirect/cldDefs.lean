import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.LyndonIndependenceDefs
import Submission.Work.ORLyndon.Magnus
import Submission.Work.ORLyndon.Fox.fundamental_identity
import Submission.Work.ORLyndon.lyndon_range_theta
import Submission.Work.ORLocInd.FKSKernel.cohenLyndonBasis
import Submission.Work.ORLocInd.CohenLyndon.isProperPower_bridge
import Submission.Work.OROneRel.ne_one_of_not_isProperPower

/-!
# Cohen--Lyndon descent, definitions

This is the definitions file of the `CLDirect` route to `LyndonIndependence` (see
`Submission/Work/ORLyndon/CASE2INPUT_LEAD.md`).

Let `F = F(X)`, `u ∈ F` not a proper power, `l ≥ 1`, `r = u^l`, `G = ⟨X | r⟩` and let
`M = ⟪u⟫_F`, `N = ⟪r⟫_F ≤ M`.  N4's Cohen--Lyndon basis (`Work.ORLocInd.FKSKernel.cohenLyndonBasis`)
gives `e : F(F/M) ≃* M` with `e (of q) = s_q u s_q⁻¹` for a section `s` of the coset projection.
We package that data as `CLData u`, and then define

* `clChi`   : `M →* Multiplicative (ZMod l)`, one basis element per coset (used for the order);
* `clPi`    : `K[F(F/M)] →+* K[G]` induced by `e` and the presentation;
* `clDelta` : the crossed homomorphism `Δ g = Σ_q π(∂g/∂q) s̄_q` on `K[F(F/M)]`;
* `clPhi`   : `Δ ∘ e⁻¹` on `M`, transported along the Cohen--Lyndon basis;
* `presentSec`, `thetaFun`, `thetaLin`: the Fox-kernel (Magnus embedding) machinery.

Nothing in this file (or in the files importing it) may import `powDefs`,
`annAtDefs`/`annChain*`/`CLAssembly`, or anything that reaches
`Submission.Work.OROneRel.magnus_step_root`: those pull in `mrslAux`, which re-declares
`Work.OROneRel.toWord_pow_of_isCyclicallyReduced` and so cannot be loaded together with the
N4 Cohen--Lyndon modules.
-/

set_option autoImplicit false

namespace Work.ORLyndon.CLDirect

open MonoidAlgebra

universe u v

section CL

variable {X : Type u}

/-- The data provided by N4's Cohen--Lyndon basis theorem for a non-proper-power `u ≠ 1`:
an isomorphism `e : F(F/M) ≃* M` (where `M = ⟪u⟫`), together with a section `s` of the coset
projection such that `e (of q) = s q * u * (s q)⁻¹`. -/
structure CLData (u : FreeGroup X) where
  e : FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))) ≃*
        ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))
  s : FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X)) → FreeGroup X
  mk_s : ∀ q, (QuotientGroup.mk (s q) :
      FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))) = q
  e_of : ∀ q, ((e (FreeGroup.of q) : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) :
      FreeGroup X) = s q * u * (s q)⁻¹

/-- The character `M →* Multiplicative (ZMod l)` sending every Cohen--Lyndon basis element to `1`:
the composite of `e⁻¹` with the map `F(F/M) →* Multiplicative (ZMod l)` that sends every generator
to `ofAdd 1`. -/
noncomputable def clChi {u : FreeGroup X} (D : CLData u) (l : ℕ) :
    ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X))) →* Multiplicative (ZMod l) :=
  (FreeGroup.lift (fun _ => Multiplicative.ofAdd (1 : ZMod l))).comp D.e.symm.toMonoidHom

end CL

section Delta

variable {X : Type u} [DecidableEq X] {K : Type v} [Field K]

/-- The ring homomorphism `K[F(F/M)] →+* K[G]` induced by the Cohen--Lyndon isomorphism `e` and the
presentation `F(X) →* G`. -/
noncomputable def clPi {u : FreeGroup X} (D : CLData u) (l : ℕ) :
    MonoidAlgebra K (FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X))))
      →+* MonoidAlgebra K (OneRelatorGroup (u ^ l)) :=
  MonoidAlgebra.mapDomainRingHom K
    ((presentRho (u ^ l)).comp
      ((Subgroup.normalClosure ({u} : Set (FreeGroup X))).subtype.comp D.e.toMonoidHom))

/-- The crossed homomorphism `Δ` on `K[F(F/M)]`:
`Δ g = Σ_q π (∂g/∂q) · s̄_q`, where `∂/∂q` is the Fox derivative on the free group `F(F/M)` and
`s̄_q` is the image of `s q` in `G`. -/
noncomputable def clDelta {u : FreeGroup X} (D : CLData u) (l : ℕ)
    (m : FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X)))) :
    MonoidAlgebra K (OneRelatorGroup (u ^ l)) :=
  letI := Classical.decEq (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X)))
  (foxFD (K := K) m).sum (fun q c =>
    clPi (K := K) D l c * MonoidAlgebra.of K _ (presentRho (u ^ l) (D.s q)))

/-- The additive map `φ = Δ ∘ e⁻¹` on the normal closure `M = ⟪u⟫`, extended by `0` outside `M`. -/
noncomputable def clPhi {u : FreeGroup X} (D : CLData u) (l : ℕ) (n : FreeGroup X) :
    MonoidAlgebra K (OneRelatorGroup (u ^ l)) := by
  classical
  exact if h : n ∈ Subgroup.normalClosure ({u} : Set (FreeGroup X)) then
    clDelta (K := K) D l (D.e.symm ⟨n, h⟩) else 0

end Delta

section FoxKernel

variable {X : Type u} [DecidableEq X] {K : Type v} [Field K]

/-- A section of the presentation map `F(X) →* G`. -/
noncomputable def presentSec (r : FreeGroup X) : OneRelatorGroup r → FreeGroup X :=
  Function.surjInv (PresentedGroup.mk_surjective ({r} : Set (FreeGroup X)))

/-- The pointwise formula for the Magnus-embedding map `Θ`, before linear extension:
`Θ f = f̄ · φ (σ(f̄)⁻¹ f)`. -/
noncomputable def thetaFun (r : FreeGroup X)
    (φ : FreeGroup X → MonoidAlgebra K (OneRelatorGroup r)) (f : FreeGroup X) :
    MonoidAlgebra K (OneRelatorGroup r) :=
  MonoidAlgebra.of K _ (presentRho r f) * φ ((presentSec r (presentRho r f))⁻¹ * f)

/-- The `K`-linear extension of `Θ` to the group algebra `K[F(X)]`. -/
noncomputable def thetaLin (r : FreeGroup X)
    (φ : FreeGroup X → MonoidAlgebra K (OneRelatorGroup r)) :
    MonoidAlgebra K (FreeGroup X) →ₗ[K] MonoidAlgebra K (OneRelatorGroup r) :=
  (Finsupp.linearCombination K (thetaFun (K := K) r φ)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv K).toLinearMap

end FoxKernel

end Work.ORLyndon.CLDirect
