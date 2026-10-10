/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK.TwCensus
-/
import Mathlib
import Submission.Work.MotK.LinkCertGen
import Submission.Work.MotV.Defs
import Submission.Work.MotT.twistFieldTK_sup_eq_top
import Submission.Work.MotK.GenBridge

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `trdeg_K K(C_h) = 1` for the generic T-twist field `Work.MotK.twistFieldTG`

`Work.MotK.twistFieldTG K D h ⊆ K̄(E)` is the T-twist field `K(C_h)` of the Kummer class of `h`
(`Submission/Work/MotK/LinkCertGen.lean`), the generic version of `Work.MotV.twistFieldT`.  It is
definitionally the `MotT` field `Work.MotT.twistFieldTK D h`
(`Work.MotK.twistFieldTG_eq_twistFieldTK`, `Submission/Work/MotK/GenBridge.lean`), so the present
file works in the `MotT` vocabulary.

**Main result.**  `Algebra.trdeg K ↥(Work.MotK.twistFieldTG K D h) = 1` for `h ≠ 0` and good Klein
data `D` (`Work.MotK.TwCensus.TwistFieldTGTrdeg`).  This is the "the T-twist is the function field
of a curve" input of the K-route census: the residue field of the relevant height-one prime must
have transcendence degree `1` over the base before the dimension count of
`Submission/Work/MotK/AUDIT_LinkCertT.md` applies (`dim R/I = trdeg`).

## Route

Write `F := Work.MotT.twistFieldTK D h ⊆ L := Work.MotT.OmK D = K̄(E)`.  The proof has three
independent pieces, each isolated as a lemma below.

1. `trdeg_functionField_eq_one`: for **any** Weierstrass curve `W` over a field `F`,
   `trdeg_F F(W) = 1`.  Indeed `F(W) = Frac F[W]`, and `F[W]` is free of rank `2` over `F[X]`
   (`CoordinateRing.basis`), hence algebraic over `F[X]`; the function field is a fraction field of
   the coordinate ring, hence algebraic over it; and `trdeg_F F[X] = trdeg_F MvPolynomial (Fin 1) F
   = 1` (`MvPolynomial.trdeg_of_isDomain`).  No smoothness or `D.Good` is needed.
2. `isAlgebraic_of_sup_eq_top`: if `F ⊔ K' = ⊤` is a compositum in which the other factor `K'` is
   algebraic over `K`, then `L` is algebraic over `F`.  (Here `K' := K̄ = KbK K`.)
3. `trdeg_coe_eq_of_isAlgebraic`: for `K ≤ F ≤ L` with `L/F` algebraic,
   `trdeg_K F = trdeg_K L` (trdeg additivity `trdeg_add_eq` plus `trdeg_eq_zero`).

`twistFieldTK_sup_eq_top` (`Submission/Work/MotT/twistFieldTK_sup_eq_top.lean`) gives
`F ⊔ K̄ = L`, so (2) and (3) reduce the goal to `trdeg_K L = 1`; and
`trdeg_K L = trdeg_K K̄ + trdeg_K̄ L = 0 + 1` by (1) (the algebraic closure `K̄ = KbK K`
contributes nothing) plus `trdeg_add_eq`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK.TwCensus

/-- **The function field of a Weierstrass curve has transcendence degree one.**
For any Weierstrass curve `W` over a field `F` (no smoothness hypothesis is needed),
`Algebra.trdeg F F(W) = 1`.

Route.  `CoordinateRing W` is free of rank `2` over `Polynomial F` (`CoordinateRing.basis`),
hence finite and therefore algebraic over it; the function field is a fraction field of the
coordinate ring, hence algebraic over it; and `trdeg_F F[X] = 1` because `F[X] ≃ₐ[F]
MvPolynomial (Fin 1) F` and `MvPolynomial.trdeg_of_isDomain`.  The two algebraic steps are
removed with the tower law `trdeg_add_eq`. -/
lemma trdeg_functionField_eq_one (F : Type) [Field F] (W : WeierstrassCurve F) :
    Algebra.trdeg F (FunctionField W) = 1 := by
  haveI : IsDomain (CoordinateRing W) := inferInstance
  have hfin : Module.Finite (Polynomial F) (CoordinateRing W) :=
    Module.Finite.of_basis (CoordinateRing.basis W)
  haveI : Algebra.IsAlgebraic (Polynomial F) (CoordinateRing W) :=
    Algebra.IsAlgebraic.of_finite _ _
  -- `F[W]` is algebraic over `F[X]`, so it has the same transcendence degree over `F`.
  have hA : Algebra.trdeg F (CoordinateRing W) = Algebra.trdeg F (Polynomial F) := by
    have h := trdeg_add_eq F (Polynomial F) (A := CoordinateRing W)
    have h0 : Algebra.trdeg (Polynomial F) (CoordinateRing W) = 0 := trdeg_eq_zero
    rw [h0, add_zero] at h
    exact h.symm
  -- `F(W)` is algebraic over `F[W]`, so it has the same transcendence degree over `F`.
  haveI : Algebra.IsAlgebraic (CoordinateRing W) (FunctionField W) := by
    rw [← IsFractionRing.isAlgebraic_iff' (CoordinateRing W) (CoordinateRing W)
      (FractionRing (CoordinateRing W))]
    infer_instance
  have hB : Algebra.trdeg F (FunctionField W) = Algebra.trdeg F (CoordinateRing W) := by
    have h := trdeg_add_eq F (CoordinateRing W) (A := FunctionField W)
    have h0 : Algebra.trdeg (CoordinateRing W) (FunctionField W) = 0 := trdeg_eq_zero
    rw [h0, add_zero] at h
    exact h.symm
  -- `trdeg_F F[X] = 1`, via the identification `F[X] ≃ₐ[F] MvPolynomial (Fin 1) F`.
  have hpoly : Algebra.trdeg F (Polynomial F) = 1 := by
    rw [AlgEquiv.trdeg_eq (MvPolynomial.uniqueAlgEquiv F (Fin 1)).symm]
    rw [MvPolynomial.trdeg_of_isDomain]
    simp
  rw [hB, hA, hpoly]

/-- **A compositum with an algebraic extension is algebraic (relative version).**
If `F, K' ≤ L` are intermediate fields of `L/K` with `F ⊔ K' = ⊤` and every element of `K'` is
algebraic over `K`, then `L` is algebraic over `F`.

Indeed `K'` is then algebraic over `F` too (`IsAlgebraic.tower_top`), so the compositum, being
generated over `F` by `F` and `K'`, is algebraic over `F`; formally,
`(algebraicClosure ↥F L).restrictScalars K` is an intermediate field of `L/K` containing `F` and
`K'`, hence contains `⊤ = F ⊔ K'`, i.e. is everything. -/
lemma isAlgebraic_of_sup_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L]
    (F K' : IntermediateField K L) (hsup : F ⊔ K' = ⊤)
    (hK' : ∀ x, x ∈ K' → IsAlgebraic K x) : Algebra.IsAlgebraic ↥F L := by
  refine ⟨fun z => ?_⟩
  -- `A := (algebraicClosure ↥F L).restrictScalars K` is an intermediate field of `L/K`
  -- containing both `F` and `K'`, hence equal to `⊤`.
  have hAtop : (algebraicClosure ↥F L).restrictScalars K = ⊤ := by
    rw [eq_top_iff, ← hsup]
    refine sup_le ?_ ?_
    · intro x hx
      rw [IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff]
      simpa using isAlgebraic_algebraMap (R := ↥F) (A := L) (⟨x, hx⟩ : ↥F)
    · intro x hx
      rw [IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff]
      exact IsAlgebraic.tower_top ↥F (hK' x hx)
  have hz : z ∈ (algebraicClosure ↥F L).restrictScalars K := by rw [hAtop]; exact trivial
  rwa [IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff] at hz

/-- **The tower law for the transcendence degree of an intermediate field.**
If `K ≤ F ≤ L` and `L` is algebraic over `F`, then `trdeg_K F = trdeg_K L`: the tower formula
`trdeg_add_eq` reads `trdeg_K F + trdeg_F L = trdeg_K L` and `trdeg_F L = 0`. -/
lemma trdeg_coe_eq_of_isAlgebraic {K L : Type*} [Field K] [Field L] [Algebra K L]
    (F : IntermediateField K L) [Algebra.IsAlgebraic ↥F L] :
    Algebra.trdeg K ↥F = Algebra.trdeg K L := by
  have h0 : Algebra.trdeg ↥F L = 0 := trdeg_eq_zero
  have ht := trdeg_add_eq K ↥F (A := L)
  rw [h0, add_zero] at ht
  exact ht

/-- **`trdeg_K K(C_h) = 1`.**  The T-twist field `K(C_h) = Work.MotK.twistFieldTG K D h` of good
Klein data `D` at `h ≠ 0` has transcendence degree one over `K`: it is a `K`-form of `K̄(E)`,
whose transcendence degree over `K` equals `trdeg_K̄ K̄(E) = 1` because `K̄/K` is algebraic. -/
theorem TwistFieldTGTrdeg (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (h : K)
    (hh : h ≠ 0) :
    Algebra.trdeg K ↥(Work.MotK.twistFieldTG K D h) = 1 := by
  -- Work in the definitionally equal `MotT` vocabulary.
  change Algebra.trdeg K ↥(Work.MotT.twistFieldTK D h) = 1
  -- `trdeg_K K̄(E) = trdeg_K K̄ + trdeg_K̄ K̄(E) = 0 + 1`.
  have hL : Algebra.trdeg K (Work.MotT.OmK D) = 1 := by
    have hKb : Algebra.trdeg K (Work.MotT.KbK K) = 0 := trdeg_eq_zero
    have hKbL : Algebra.trdeg (Work.MotT.KbK K) (Work.MotT.OmK D) = 1 :=
      trdeg_functionField_eq_one _ _
    have h := trdeg_add_eq K (Work.MotT.KbK K) (A := Work.MotT.OmK D)
    rw [hKb, zero_add] at h
    rw [← h]
    exact hKbL
  -- `F ⊔ K̄ = K̄(E)`, and `K̄` is algebraic over `K`:  hence `K̄(E)` is algebraic over `F`.
  have h2 : Algebra.IsAlgebraic ↥(Work.MotT.twistFieldTK D h) (Work.MotT.OmK D) :=
    isAlgebraic_of_sup_eq_top _ _
      (Work.MotT.twistFieldTK_sup_eq_top D hD h hh)
      (by
        intro x hx
        rw [AlgHom.mem_fieldRange] at hx
        obtain ⟨c, hc⟩ := hx
        rw [← hc, IsScalarTower.toAlgHom_apply]
        exact IsAlgebraic.algebraMap
          (Algebra.IsAlgebraic.isAlgebraic (R := K) (A := Work.MotT.KbK K) c))
  haveI := h2
  -- Remove the algebraic top layer: `trdeg_K F = trdeg_K K̄(E) = 1`.
  have h3 := trdeg_coe_eq_of_isAlgebraic (K := K) (L := Work.MotT.OmK D)
    (Work.MotT.twistFieldTK D h)
  rw [h3, hL]

end Work.MotK.TwCensus
