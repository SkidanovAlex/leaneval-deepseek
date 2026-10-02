import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Endpoints of lifts of paths with the same endpoints

Two paths `γ γ' : Path x y` in the base of a covering map `p : E → X` which lift from the same
point `e ∈ E` have lifts with the same endpoint, provided that the lift of the closed path
`γ ⬝ γ'.symm` starting at `e` returns to `e`.

This is the standard monodromy statement: the monodromy of `γ ⬝ γ'.symm` sends `e` to itself, and
`γ ⬝ γ'.symm` is (up to homotopy) trivial exactly when `γ` and `γ'` have the same monodromy.
-/

open Path
open scoped unitInterval

namespace Work.Bottcher.Contraction2

noncomputable section

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- The lift of a path through a covering map does not depend on the proof that the chosen
starting point lifts the starting point of the path. -/
private lemma liftPath_congr_arg (cov : IsCoveringMap p) {γ : C(unitInterval, X)} {e : E}
    (h₁ h₂ : γ 0 = p e) : cov.liftPath γ e h₁ = cov.liftPath γ e h₂ :=
  ((cov.eq_liftPath_iff' (γ := γ) (e := e) (γ_0 := h₁) (Γ := cov.liftPath γ e h₂)).mpr
    ⟨cov.liftPath_lifts γ e h₂, cov.liftPath_zero γ e h₂⟩).symm

/-- The first component of the monodromy of a path `γ` applied to the starting point `e` is the
endpoint of the lifted path. -/
private lemma monodromy_mk_apply_one (cov : IsCoveringMap p) {x y : X} (γ : Path x y) (e : E)
    (he : x = p e) : (cov.monodromy (Path.Homotopic.Quotient.mk γ) ⟨e, he.symm⟩).1
      = cov.liftPath (γ : C(unitInterval, X)) e ((Path.source γ).trans he) 1 := by
  show cov.liftPath (γ : C(unitInterval, X)) e ((Path.source γ).trans (he.symm).symm) 1 = _
  exact congrArg (fun F : C(unitInterval, E) => F 1) (liftPath_congr_arg cov _ _)

/-- **General form** of the lemma, for an arbitrary covering map `p : E → X`. -/
theorem liftPath_endpoint_eq_of_loop_general (cov : IsCoveringMap p) {x y : X}
    (γ γ' : Path x y) (e : E) (he : x = p e)
    (hloop : cov.liftPath ((γ.trans γ'.symm : Path x x) : C(unitInterval, X)) e
        ((Path.source (γ.trans γ'.symm)).trans he) 1 = e) :
    cov.liftPath (γ : C(unitInterval, X)) e ((Path.source γ).trans he) 1
      = cov.liftPath (γ' : C(unitInterval, X)) e ((Path.source γ').trans he) 1 := by
  let E₀ : p ⁻¹' {x} := ⟨e, he.symm⟩
  -- the lift of the closed path `γ ⬝ γ'.symm` from `e` is a loop
  have hl : cov.monodromy (Path.Homotopic.Quotient.mk (γ.trans γ'.symm)) E₀ = E₀ := by
    refine Subtype.ext ?_
    show (cov.monodromy (Path.Homotopic.Quotient.mk (γ.trans γ'.symm)) ⟨e, he.symm⟩).1 = e
    rw [monodromy_mk_apply_one cov (γ.trans γ'.symm) e he]
    exact hloop
  -- monodromy is multiplicative
  have hstep : cov.monodromy (Path.Homotopic.Quotient.mk γ'.symm)
      (cov.monodromy (Path.Homotopic.Quotient.mk γ) E₀) = E₀ := by
    rw [← IsCoveringMap.monodromy_trans_apply, ← Path.Homotopic.Quotient.mk_trans γ γ'.symm]
    exact hl
  -- conversely, `γ'` undoes `γ'.symm`
  have h1 : cov.monodromy (Path.Homotopic.Quotient.mk γ'.symm)
      (cov.monodromy (Path.Homotopic.Quotient.mk γ') E₀) = E₀ := by
    rw [← IsCoveringMap.monodromy_trans_apply, Path.Homotopic.Quotient.mk_symm γ',
      Path.Homotopic.Quotient.trans_symm, IsCoveringMap.monodromy_refl]
    rfl
  have hfinal : cov.monodromy (Path.Homotopic.Quotient.mk γ) E₀
      = cov.monodromy (Path.Homotopic.Quotient.mk γ') E₀ :=
    (cov.monodromy_bijective (Path.Homotopic.Quotient.mk γ'.symm)).1 (hstep.trans h1.symm)
  rw [← monodromy_mk_apply_one cov γ e he, ← monodromy_mk_apply_one cov γ' e he]
  exact congrArg Subtype.val hfinal

end

end Work.Bottcher.Contraction2

namespace Work.Bottcher.Contraction2

theorem liftPath_endpoint_eq_of_loop {x y : {z : ℂ // z ≠ 0}} (γ γ' : Path x y) (e : ℂ)
    (he : x = ⟨Complex.exp e, Complex.exp_ne_zero e⟩)
    (hloop : Complex.isCoveringMap_exp.liftPath (γ.trans γ'.symm : C(unitInterval, {z : ℂ // z ≠ 0})) e
        ((Path.source (γ.trans γ'.symm)).trans he) 1 = e) :
    Complex.isCoveringMap_exp.liftPath (γ : C(unitInterval, {z : ℂ // z ≠ 0})) e
        ((Path.source γ).trans he) 1
      = Complex.isCoveringMap_exp.liftPath (γ' : C(unitInterval, {z : ℂ // z ≠ 0})) e
          ((Path.source γ').trans he) 1 :=
  liftPath_endpoint_eq_of_loop_general Complex.isCoveringMap_exp γ γ' e he hloop

end Work.Bottcher.Contraction2
