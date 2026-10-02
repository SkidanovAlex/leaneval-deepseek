import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.bundlePullback_homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The homotopy fibre of the path–loop fibration is the loop space

`Work.RatHurewicz.homotopyFibre (evalOne X x₀) (pathSpaceConst X x₀)` is the space of pairs
`(γ, δ)` of paths in `X` starting at `x₀` and having the same endpoint, i.e. the pullback of the
path–loop fibration `evalOne : PathSpace X x₀ → X` along itself over the constant path.  It is
homotopy equivalent to the loop space `Ω X = Path x₀ x₀`, by the triviality of the path–loop
fibration over a based-contractible parameter space
(`Work.StemsB.bundlePullback_homotopyEquiv`) applied to the parameter space
`D = PathSpace X x₀` itself — which is contractible (`Work.StemsB.contractible_pathSpace`) —
and the map `s = evalOne X x₀ : D → X`.

The based contraction used is the *reversed* reparametrisation of the path space,
`c (γ,t) = γ ((1-t)·-)`, which starts at the identity (`t = 0`) and ends at the constant path
(`t = 1`), the orientation required by `bundlePullback_homotopyEquiv`.
-/

open scoped Topology unitInterval

namespace Work.Stems

noncomputable section

/-- The reparametrisation of the based path space, run backwards: `c (γ,t) = γ ((1-t)·-)`.  At
`t = 0` this is `γ`, at `t = 1` the constant path at `x₀`, and the constant path is fixed — the
based contraction of `Work.StemsB.PathSpace X x₀` onto `constPath X x₀` in the orientation used by
`Work.StemsB.bundlePullback_homotopyEquiv`. -/
def pathSpaceContractionRev (X : Type) [TopologicalSpace X] (x₀ : X) :
    C(Work.StemsB.PathSpace X x₀ × unitInterval, Work.StemsB.PathSpace X x₀) where
  toFun q := (Work.StemsB.pathReparam X x₀) (q.1, unitInterval.symm q.2)
  continuous_toFun := (Work.StemsB.pathReparam X x₀).continuous.comp
    (Continuous.prodMk continuous_fst (unitInterval.continuous_symm.comp continuous_snd))

theorem pathSpaceContractionRev_apply (X : Type) [TopologicalSpace X] (x₀ : X)
    (γ : Work.StemsB.PathSpace X x₀) (t s : unitInterval) :
    (pathSpaceContractionRev X x₀ (γ, t)).1 s = γ.1 (unitInterval.symm t * s) :=
  Work.StemsB.pathReparam_apply X x₀ γ (unitInterval.symm t) s

theorem pathSpaceContractionRev_zero (X : Type) [TopologicalSpace X] (x₀ : X)
    (γ : Work.StemsB.PathSpace X x₀) :
    pathSpaceContractionRev X x₀ (γ, 0) = γ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rw [pathSpaceContractionRev_apply, unitInterval.symm_zero, one_mul]

theorem pathSpaceContractionRev_one (X : Type) [TopologicalSpace X] (x₀ : X)
    (γ : Work.StemsB.PathSpace X x₀) :
    pathSpaceContractionRev X x₀ (γ, 1) = Work.StemsB.constPath X x₀ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rw [pathSpaceContractionRev_apply, unitInterval.symm_one, zero_mul]
  exact γ.2

theorem pathSpaceContractionRev_const (X : Type) [TopologicalSpace X] (x₀ : X) (t : unitInterval) :
    pathSpaceContractionRev X x₀ (Work.StemsB.constPath X x₀, t) = Work.StemsB.constPath X x₀ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rw [pathSpaceContractionRev_apply]
  rfl

/-- **The homotopy fibre of the path–loop fibration is the loop space.**  For a space `X` and a
point `x₀`, the homotopy fibre (the pullback of the path–loop fibration `evalOne X x₀` along itself,
i.e. `Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne X x₀) (pathSpaceConst X x₀)` — the space of
pairs `(γ, δ)` of paths starting at `x₀` with the same endpoint) is homotopy equivalent to the loop
space `Path x₀ x₀`.

This is the standard statement that for a fibration the homotopy fibre is homotopy equivalent to the
fibre, specialised to the path–loop fibration.  The honest route (a *reparametrisation* rather than
`(γ, δ) ↦ γ ⬝ δ⁻¹`, whose composite with `λ ↦ (const, λ)` is inversion and not null-homotopic in
general) is: the map `(γ, δ) ↦ (γ, δ ⬝ γ⁻¹)` reparametrises the homotopy fibre as
`PathSpace X x₀ × Path x₀ x₀` (the pair `(γ, λ)` with `λ` a genuine loop, `δ := λ ⬝ γ`), and
`Work.StemsB.contractible_pathSpace X x₀` makes the first factor contractible; the genuine fibre
`fibre (evalOne X x₀) x₀` is `Path x₀ x₀` up to `Work.StemsB.fibreEvalOneHomeo`.

Uses: it converts the hypothesis of `Work.Serre.SerreE3a` (which is stated for
`Work.RatHurewicz.homotopyFibre p e₀`) into a statement about the loop space `Path x₀ x₀`, which is
what a proof of `Work.Serre.RangeEMVanAll` from `Work.Serre.RangeEMVanOne` needs (applying `E3a` to
the path–loop fibration `PathSpace X x₀ → X` and using the contractibility
`Work.StemsB.contractible_pathSpace` of the total space, together with the homotopy invariance of
rational homology, `Work.Cohomology.homologyEquiv` / `IsRatHomologyIso.of_homotopyEquiv`). -/
theorem homotopyFibre_evalOne_equiv_loop (X : Type) [TopologicalSpace X] (x₀ : X) :
    Nonempty (ContinuousMap.HomotopyEquiv
      (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne X x₀)
        (Work.RatHurewicz.pathSpaceConst X x₀))
      (Path x₀ x₀)) :=
  Work.StemsB.bundlePullback_homotopyEquiv X x₀ (Work.StemsB.PathSpace X x₀)
    (Work.StemsB.evalOne X x₀) (Work.RatHurewicz.pathSpaceConst X x₀)
    (pathSpaceContractionRev X x₀) (pathSpaceContractionRev_zero X x₀)
    (pathSpaceContractionRev_one X x₀) (pathSpaceContractionRev_const X x₀)

end

end Work.Stems
