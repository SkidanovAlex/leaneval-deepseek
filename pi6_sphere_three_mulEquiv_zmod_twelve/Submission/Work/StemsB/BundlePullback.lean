import Mathlib
import Submission.Work.StemsB.Fibrations

/-!
# The pullback of the path–loop fibration over an arbitrary parameter space

`Submission/Work/StemsB/PathSpaceTrivial.lean` defines `cubePullback X x₀ n s`, the pullback of the
path–loop fibration `evalOne X x₀ : PathSpace X x₀ → X` over a map `s : I^n → X` (paths in `X` run
from `x₀` to `s u`).  `Submission/Work/StemsB/cubePullback_homotopyEquiv.lean` proves that, for a
*contractible* parameter cube with a based contraction, this pullback is homotopy equivalent to the
fibre `Path x₀ (s u₀)` — the "triviality of the path–loop fibration over a cube".

For the sphere-specific route to the crux (`CONTRACTS.md` §F, Step I) the parameter is not a cube
but a *disc* `D ⊆ Sⁿ` whose interior contains the base point; the same argument applies, with
`I^n` replaced by an arbitrary space `D` equipped with a based contraction.  This file fixes the
vocabulary for that general statement:

* `Work.StemsB.bundlePullback X x₀ D s` — the pullback over `s : C(D,X)`,
* `Work.StemsB.bundlePullbackFst`, `bundlePullbackSnd`, `mem_bundlePullback`.

The triviality statement to be proved about it is

  `∀ (D) [TopologicalSpace D] (s : C(D,X)) (d₀ : D) (c : C(D × I, D)),
     c (u,0) = u → c (u,1) = d₀ → (∀ t, c (d₀,t) = d₀) →
     Nonempty (bundlePullback X x₀ D s ≃ₕ Path x₀ (s d₀))`

(an exact generalisation of `Work.StemsB.cubePullback_homotopyEquiv'`, whose proof — the explicit
transport `Φ : (u,γ) ↦ γ * (t ↦ s (c (u,t)))`, the section `Ψ : δ ↦ (d₀,δ)` and the two explicit
homotopies — is transcribed word for word).
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

variable (X : Type) [TopologicalSpace X] (x₀ : X)

/-- **The pullback of the path–loop fibration** `evalOne X x₀ : PathSpace X x₀ → X` over a map
`s : D → X` (for an arbitrary parameter space `D`): the space of pairs `(u,γ)` with `γ` a path in
`X` from `x₀` to `s u`. -/
def bundlePullback (D : Type) [TopologicalSpace D] (s : C(D, X)) : Type _ :=
  {p : D × PathSpace X x₀ // (evalOne X x₀) p.2 = s p.1}

instance instTopologicalSpaceBundlePullback (D : Type) [TopologicalSpace D] (s : C(D, X)) :
    TopologicalSpace (bundlePullback X x₀ D s) :=
  inferInstanceAs (TopologicalSpace {p : D × PathSpace X x₀ // (evalOne X x₀) p.2 = s p.1})

variable {X x₀}

@[simp]
theorem mem_bundlePullback {D : Type} [TopologicalSpace D] {s : C(D, X)}
    (p : bundlePullback X x₀ D s) : (evalOne X x₀) p.1.2 = s p.1.1 := p.2

/-- The first projection `bundlePullback X x₀ D s → D`. -/
def bundlePullbackFst (D : Type) [TopologicalSpace D] (s : C(D, X)) :
    C(bundlePullback X x₀ D s, D) where
  toFun p := p.1.1
  continuous_toFun := continuous_fst.comp continuous_subtype_val

/-- The second projection `bundlePullback X x₀ D s → PathSpace X x₀`. -/
def bundlePullbackSnd (D : Type) [TopologicalSpace D] (s : C(D, X)) :
    C(bundlePullback X x₀ D s, PathSpace X x₀) where
  toFun p := p.1.2
  continuous_toFun := continuous_snd.comp continuous_subtype_val

end

end Work.StemsB
