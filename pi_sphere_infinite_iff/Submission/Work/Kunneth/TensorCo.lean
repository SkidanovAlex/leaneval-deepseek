import Mathlib
import Submission.Work.Kunneth.TensorDefs
import Submission.Work.Kunneth.Basic
import Submission.Work.Cohomology.DualComplex

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The "cohomological" tensor product of a cochain complex with a family of modules

This file provides the cochain-level companion of `Work.Kunneth.tpC` that the Künneth theorem
for cohomology needs.  Where `tpC C D` has degree `n` the direct sum `⨁_{p+q=n} C_p ⊗ D_q` with
the Koszul differential `d x ⊗ y + (-1)^p x ⊗ d y`, the complex `ctens A T` built here has
degree `n` the direct sum `⨁_{p+q=n} A^p ⊗ T_q` and the differential `∂ x ⊗ t` — i.e. only the
*differential of the first factor*, the family `T` carrying **no** differential at all.

It is the complex that computes `H^n` with coefficients in `T`:

* `Work.Kunneth.ctensX A T n` — the plain `ℤ`-module `⨁_{p+q=n} A^p ⊗ T_q`;
* `Work.Kunneth.ctensLof` — its structure maps;
* `Work.Kunneth.ctensDpq`, `Work.Kunneth.ctensD` — the differential;
* `Work.Kunneth.ctensD_comp_ctensD` — the differential squares to zero;
* `Work.Kunneth.ctens A T` — the resulting cochain complex of `ℤ`-modules.

The intended use (`Submission/Work/Kunneth/README.md`, "cohomology side") is: for a chain
complex `C` and a family of *finite free* `ℤ`-modules `M q`, the `ℤ`-dual of the chain complex
`tpC C (sumShift M)` is isomorphic to `ctens (dualComplex ℤ C) (fun q => Hom(M q, ℤ))`, so that
the Künneth isomorphism in cohomology becomes the homology computation of `ctens`, which is
`⨁_{p+q=n} H^p(dualComplex C) ⊗ T q` as soon as every `T q` is flat.

Note the *absence* of a Koszul sign here: since `T` has no differential, the differential of the
dual of `tpC C (sumShift M)` is simply `φ ∘ (d ⊗ 1)`.

## A note on instances

As everywhere in this chapter, the generic `AddCommGroup.toIntModule` instance is removed, so
that the `ℤ`-module structures occurring in the tensor products are the ones of the `ModuleCat`
objects at hand.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The `ℤ`-module `A^p ⊗_ℤ T q`, the summand of bidegree `(p,q)`. -/
abbrev ctensSummand (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) (p q : ℕ) :
    Type :=
  ↥(A.X p ⊗ T q)

/-- The degree-`n` module `⨁_{p+q=n} A^p ⊗_ℤ T q`, as a plain `ℤ`-module. -/
abbrev ctensX (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) (n : ℕ) : Type :=
  DirectSum (tpIdx n) (fun pq => ctensSummand A T pq.1.1 pq.1.2)

/-- The `pq`-th structure map of the direct sum defining `ctensX`. -/
abbrev ctensLof (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) (n : ℕ)
    (pq : tpIdx n) : ctensSummand A T pq.1.1 pq.1.2 →ₗ[ℤ] ctensX A T n :=
  DirectSum.lof ℤ (tpIdx n) (fun rs => ctensSummand A T rs.1.1 rs.1.2) pq

/-- The `pq`-summand of the differential `∂ x ⊗ t = ∂x ⊗ t` of `ctens`. -/
def ctensDpq (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) (n : ℕ)
    (pq : tpIdx n) : ctensSummand A T pq.1.1 pq.1.2 →ₗ[ℤ] ctensX A T (n + 1) :=
  (ctensLof A T (n + 1) ⟨(pq.1.1 + 1, pq.1.2), by omega⟩).comp
    (TensorProduct.map ((A.d pq.1.1 (pq.1.1 + 1)).hom) (LinearMap.id) :
      ctensSummand A T pq.1.1 pq.1.2 →ₗ[ℤ] ctensSummand A T (pq.1.1 + 1) pq.1.2)

/-- The differential `∂` of `ctens A T`: on the summand `A^p ⊗ T q` it is `∂_A ⊗ 1`. -/
def ctensD (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) (n : ℕ) :
    ctensX A T n →ₗ[ℤ] ctensX A T (n + 1) :=
  DirectSum.toModule ℤ (tpIdx n) (ctensX A T (n + 1)) (ctensDpq A T n)

/-- The value of the differential on a summand generator `x ⊗ t`. -/
theorem ctensD_lof_tmul (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) (n : ℕ)
    (pq : tpIdx n) (x : ↥(A.X pq.1.1)) (t : ↥(T pq.1.2)) :
    ctensD A T n (ctensLof A T n pq (x ⊗ₜ[ℤ] t))
      = ctensLof A T (n + 1) ⟨(pq.1.1 + 1, pq.1.2), by omega⟩
          (((A.d pq.1.1 (pq.1.1 + 1)).hom x) ⊗ₜ[ℤ] t) := by
  rw [ctensD, DirectSum.toModule_lof, ctensDpq, LinearMap.comp_apply]
  erw [TensorProduct.map_tmul]
  rw [LinearMap.id_apply]

/-- The differential of `ctens` squares to zero. -/
theorem ctensD_comp_ctensD (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) (n : ℕ) :
    (ctensD A T (n + 1)).comp (ctensD A T n) = 0 := by
  apply DirectSum.linearMap_ext
  intro pq
  rw [LinearMap.comp_assoc, LinearMap.zero_comp]
  have h : (ctensD A T n).comp (DirectSum.lof ℤ (tpIdx n)
      (fun rs => ctensSummand A T rs.1.1 rs.1.2) pq) = ctensDpq A T n pq := by
    rw [ctensD]
    apply LinearMap.ext
    intro a
    rw [LinearMap.comp_apply, DirectSum.toModule_lof]
  rw [h, ctensDpq]
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      erw [TensorProduct.map_tmul]
      rw [LinearMap.id_apply, ctensD_lof_tmul]
      have hd : (A.d (pq.1.1 + 1) (pq.1.1 + 1 + 1)).hom ((A.d pq.1.1 (pq.1.1 + 1)).hom a) = 0 := by
        have h2 := congrArg ModuleCat.Hom.hom
          (HomologicalComplex.d_comp_d A pq.1.1 (pq.1.1 + 1) (pq.1.1 + 1 + 1))
        simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
        exact LinearMap.congr_fun h2 a
      rw [hd, TensorProduct.zero_tmul]
      simp
  | add x y hx hy => rw [map_add, hx, hy, map_add]

/-- **The "coefficient" cochain complex** `⨁_{p+q=n} A^p ⊗ T q` with differential `∂_A ⊗ 1`. -/
def ctens (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℤ (ctensX A T n))
    (fun n => ModuleCat.ofHom (ctensD A T n))
    (fun n => by
      apply ModuleCat.hom_ext
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero]
      exact ctensD_comp_ctensD A T n)

@[simp]
theorem ctens_X (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) (n : ℕ) :
    (ctens A T).X n = ModuleCat.of ℤ (ctensX A T n) := rfl

theorem ctens_d (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) (n : ℕ) :
    (ctens A T).d n (n + 1) = ModuleCat.ofHom (ctensD A T n) := by
  unfold ctens
  exact CochainComplex.of_d (fun n => ModuleCat.of ℤ (ctensX A T n))
    (fun n => ModuleCat.ofHom (ctensD A T n)) n


/-- The family of `ℤ`-duals of a family of `ℤ`-modules: `Work.Kunneth.homDual M q = Hom(M q, ℤ)`. -/
abbrev homDual (M : ℕ → ModuleCat ℤ) (q : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (↥(M q) →ₗ[ℤ] ℤ)

/-- The target `⨁_{p+q=n} H^p(A) ⊗ T q` of the cohomological Künneth isomorphism, as a
`ModuleCat ℤ`. -/
abbrev ctensH (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) (n : ℕ) :
    ModuleCat ℤ :=
  ModuleCat.of ℤ (∀ pq : tpIdx n, ↥(A.homology pq.1.1 ⊗ T pq.1.2))


/-- The workspace's singular cochain complex (`Work.Cohomology.cochainC`) of a simplicial set is
the `ℤ`-dual of its singular chain complex, in the sense of `Work.Cohomology.dualComplex`. -/
theorem cochainC_eq_dualComplex (X : SSet) :
    Work.Cohomology.cochainC ℤ X = Work.Cohomology.dualComplex ℤ (Work.Kunneth.sChain X) := rfl

end

end Work.Kunneth
