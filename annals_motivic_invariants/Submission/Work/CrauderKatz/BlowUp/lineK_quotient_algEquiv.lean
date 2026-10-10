/-
Copyright (c) 2026 the annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.BlowUp.LineDefs
import Submission.Work.CrauderKatz.BlowUp.lineK_height

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.BlowUp.lineK_quotient_algEquiv`

The quotient of the chart ring `𝕜[x,t,z,ε]/(ε², x·ε)` by the prime `lineK = (x, ε)` is the
polynomial ring `𝕜[t,z]` in the overlap coordinate `t` and the line coordinate `z`.

The proof is a two step transport:

* `lineK_height.lean` provides the surjective ring hom `killEZBar 𝕜 : lineRing 𝕜 ↠ 𝕜[X₀,X₁,X₂]`
  killing `ε`, together with `lineK 𝕜 = (threeIdeal 𝕜).comap (killEZBar 𝕜)` where
  `threeIdeal 𝕜 = (X 0)`.  Hence `killEZBar` induces a bijection on the quotients, i.e. a
  `𝕜`-algebra equivalence `lineRing 𝕜 ⧸ lineK 𝕜 ≃ₐ[𝕜] 𝕜[X₀,X₁,X₂] ⧸ (X 0)`
  (`Ideal.quotientMapₐ` + `Ideal.quotientMap_injective'` / `Ideal.quotientMap_surjective`).
* `MvPolynomial.finSuccEquiv 𝕜 2` sends `X 0` to `Polynomial.X`, so by
  `Ideal.quotientEquivAlg` it identifies `𝕜[X₀,X₁,X₂] ⧸ (X 0)` with
  `(𝕜[X₁,X₂])[X] ⧸ (X - C 0)`, which `Polynomial.quotientSpanXSubCAlgEquiv` collapses to
  `𝕜[X₁,X₂]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

namespace Work.CrauderKatz.BlowUp

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-! ### `killEZBar` as a `𝕜`-algebra hom -/

/-- The surjection `killEZBar 𝕜 : R 𝕜 ↠ 𝕜[X₀,X₁,X₂]` killing `ε`, as a `𝕜`-algebra hom. -/
def killEZAlg : lineRing 𝕜 →ₐ[𝕜] MvPolynomial (Fin 3) 𝕜 :=
  AlgHom.mk' (killEZBar 𝕜) (fun c x => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    change killEZ 𝕜 (MvPolynomial.C c) = MvPolynomial.C c
    rw [killEZ_C])

/-- The underlying ring hom of `killEZAlg` is `killEZBar`. -/
lemma killEZAlg_toRingHom :
    (killEZAlg 𝕜 : lineRing 𝕜 →+* MvPolynomial (Fin 3) 𝕜) = killEZBar 𝕜 := rfl

/-- `lineK` is the preimage of `threeIdeal` under the `𝕜`-algebra hom `killEZAlg`. -/
lemma lineK_eq_comap_alg :
    lineK 𝕜 = (threeIdeal 𝕜).comap (killEZAlg 𝕜 : lineRing 𝕜 →+* MvPolynomial (Fin 3) 𝕜) :=
  lineK_eq_comap 𝕜

/-! ### Step 1: `R ⧸ (x, ε) ≃ₐ[𝕜] 𝕜[X₀,X₁,X₂] ⧸ (X₀)` -/

theorem lineK_quotient_threeIdeal_algEquiv :
    Nonempty ((lineRing 𝕜 ⧸ lineK 𝕜) ≃ₐ[𝕜] (MvPolynomial (Fin 3) 𝕜 ⧸ threeIdeal 𝕜)) := by
  refine ⟨AlgEquiv.ofBijective
    (Ideal.quotientMapₐ (threeIdeal 𝕜) (killEZAlg 𝕜) (le_of_eq (lineK_eq_comap_alg 𝕜)))
    ⟨?_, ?_⟩⟩
  · exact Ideal.quotientMap_injective' (H := le_of_eq (lineK_eq_comap_alg 𝕜))
      (le_of_eq (lineK_eq_comap_alg 𝕜).symm)
  · exact Ideal.quotientMap_surjective (H := le_of_eq (lineK_eq_comap_alg 𝕜))
      (killEZBar_surjective 𝕜)

/-! ### Step 2: `𝕜[X₀,X₁,X₂] ⧸ (X₀) ≃ₐ[𝕜] 𝕜[X₁,X₂]` -/

/-- The ideal `(X 0) ⊆ 𝕜[X₀,X₁,X₂]` is the preimage of the principal ideal `(X) ⊆ 𝕜[X₁,X₂][X]`
under `MvPolynomial.finSuccEquiv`. -/
lemma map_finSuccEquiv_threeIdeal :
    Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 2) 𝕜))) =
      Ideal.map (MvPolynomial.finSuccEquiv 𝕜 2 :
        MvPolynomial (Fin 3) 𝕜 →+* Polynomial (MvPolynomial (Fin 2) 𝕜))
        (threeIdeal 𝕜) := by
  rw [threeIdeal, Ideal.map_span, Set.image_singleton]
  congr 1
  rw [Set.singleton_eq_singleton_iff]
  exact (MvPolynomial.finSuccEquiv_X_zero (R := 𝕜) (n := 2)).symm

theorem threeIdeal_quotient_algEquiv :
    Nonempty ((MvPolynomial (Fin 3) 𝕜 ⧸ threeIdeal 𝕜) ≃ₐ[𝕜] MvPolynomial (Fin 2) 𝕜) := by
  have hmap := map_finSuccEquiv_threeIdeal 𝕜
  have hEq : Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 2) 𝕜))) =
      Ideal.span ({Polynomial.X - Polynomial.C (0 : MvPolynomial (Fin 2) 𝕜)} :
        Set (Polynomial (MvPolynomial (Fin 2) 𝕜))) := by simp
  have e1 : (MvPolynomial (Fin 3) 𝕜 ⧸ threeIdeal 𝕜) ≃ₐ[𝕜]
      (Polynomial (MvPolynomial (Fin 2) 𝕜) ⧸
        Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 2) 𝕜)))) :=
    Ideal.quotientEquivAlg (threeIdeal 𝕜) _ (MvPolynomial.finSuccEquiv 𝕜 2) hmap
  have e2 : (Polynomial (MvPolynomial (Fin 2) 𝕜) ⧸
        Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 2) 𝕜)))) ≃ₐ[𝕜]
      (Polynomial (MvPolynomial (Fin 2) 𝕜) ⧸
        Ideal.span ({Polynomial.X - Polynomial.C (0 : MvPolynomial (Fin 2) 𝕜)} :
          Set (Polynomial (MvPolynomial (Fin 2) 𝕜)))) :=
    (Ideal.quotientEquivAlgOfEq (MvPolynomial (Fin 2) 𝕜) hEq).restrictScalars 𝕜
  have e3 : (Polynomial (MvPolynomial (Fin 2) 𝕜) ⧸
        Ideal.span ({Polynomial.X - Polynomial.C (0 : MvPolynomial (Fin 2) 𝕜)} :
          Set (Polynomial (MvPolynomial (Fin 2) 𝕜)))) ≃ₐ[𝕜]
      MvPolynomial (Fin 2) 𝕜 :=
    (Polynomial.quotientSpanXSubCAlgEquiv (0 : MvPolynomial (Fin 2) 𝕜)).restrictScalars 𝕜
  exact ⟨e1.trans (e2.trans e3)⟩

/-! ### The composite -/

/-- The quotient of the chart ring `𝕜[x,t,z,ε]/(ε², x·ε)` by the prime `lineK = (x, ε)` is the
polynomial ring `𝕜[t,z]` in the overlap coordinate `t = X 1` and the line coordinate `z = X 2`.

Route: `lineK_height.lean` provides the surjective `𝕜`-algebra (indeed ring) hom
`killEZBar 𝕜 : lineRing 𝕜 ↠ MvPolynomial (Fin 3) 𝕜` (killing `ε`) together with
`lineK_eq_comap : lineK 𝕜 = (threeIdeal 𝕜).comap (killEZBar 𝕜)`, where
`threeIdeal 𝕜 = Ideal.span {MvPolynomial.X 0} ⊆ MvPolynomial (Fin 3) 𝕜`.  So
`lineRing 𝕜 ⧸ lineK 𝕜 ≃ₐ[𝕜] (MvPolynomial (Fin 3) 𝕜) ⧸ threeIdeal 𝕜` (use
`Ideal.quotientMap`/`Ideal.quotientMapₐ` with `lineK_eq_comap`, plus surjectivity/injectivity —
`Ideal.quotientMap_injective` applies since the source ideal is the comap of the target ideal), and
then `(MvPolynomial (Fin 3) 𝕜) ⧸ threeIdeal 𝕜 ≃ₐ[𝕜] (MvPolynomial (Fin 2) 𝕜)` via
`MvPolynomial.finSuccEquiv 𝕜 2 : MvPolynomial (Fin 3) 𝕜 ≃ₐ[𝕜] Polynomial (MvPolynomial (Fin 2) 𝕜)`
(`finSuccEquiv_X_zero`), `Ideal.quotientEquivAlg` and
`Polynomial.quotientSpanXSubCAlgEquiv (0 : MvPolynomial (Fin 2) 𝕜)`.  It is fine to build the
composite ring hom `lineRing 𝕜 →+* MvPolynomial (Fin 2) 𝕜` and show its kernel is `lineK 𝕜` and it is
surjective, then use `RingHom.quotientKerEquivOfSurjective` and prove `𝕜`-linearity separately. -/
theorem lineK_quotient_algEquiv (𝕜 : Type) [Field 𝕜] :
    Nonempty ((Work.CrauderKatz.BlowUp.lineRing 𝕜 ⧸ Work.CrauderKatz.BlowUp.lineK 𝕜) ≃ₐ[𝕜]
      MvPolynomial (Fin 2) 𝕜) := by
  obtain ⟨e1⟩ := lineK_quotient_threeIdeal_algEquiv 𝕜
  obtain ⟨e2⟩ := threeIdeal_quotient_algEquiv 𝕜
  exact ⟨e1.trans e2⟩

end

end Work.CrauderKatz.BlowUp
