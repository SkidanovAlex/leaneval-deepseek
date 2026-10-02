import Mathlib
import Submission.Work.Cohomology.exists_capH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The tensor product of two chain complexes of `ℤ`-modules: definitions

This file provides the chain-level tensor product on which the Eilenberg–Zilber and Künneth
theorems of the `Work.Kunneth` chapter rest.  It is written out explicitly (rather than taken
from the monoidal structure on `HomologicalComplex`) so that its elements and its differential
are directly available in the "generators and Koszul signs" form in which the Alexander–Whitney
and shuffle maps are stated.

* `tpIdx n` — the index set `{pq : ℕ × ℕ // pq.1 + pq.2 = n}` of the bidegrees;
* `tpSummand C D p q` — the plain `ℤ`-module `C_p ⊗_ℤ D_q`;
* `tpX C D n` — the degree-`n` module `⨁_{p+q=n} C_p ⊗_ℤ D_q`;
* `tpLof C D n pq` — the `pq`-th structure map of that direct sum;
* `tpι C D p q n h` — the inclusion of the summand `C_p ⊗ D_q` into `tpX C D n`;
* `tpD C D n` — the Koszul differential `x ⊗ y ↦ d x ⊗ y + (-1)^p x ⊗ d y`;
* `tpC C D` — the tensor product chain complex (in `Tensor.lean`).

## A note on instances (IMPORTANT for importers)

`ModuleCat ℤ` objects carry an `isModule`-based `ℤ`-action, which is *propositionally* equal to,
but not *definitionally* equal to, the generic `AddCommGroup.toIntModule` structure.  Since
`TensorProduct` records its scalar structure among its implicit arguments, the presence of the
generic instance makes typeclass search pick the generic structure in one subterm and the
structure's own one in another, so that otherwise identical `LinearMap`s fail to be
definitionally equal.  Every file of this chapter therefore begins with

```
attribute [-instance] AddCommGroup.toIntModule
```

which removes the generic `ℤ`-module structure, forcing every `Module ℤ` structure to come from
the term at hand.  Files importing this chapter and writing statements about tensor products of
`ℤ`-modules are advised to include the same line.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The bidegree index set of the tensor product in total degree `n`. -/
abbrev tpIdx (n : ℕ) : Type := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

instance (n : ℕ) : DecidableEq (tpIdx n) :=
  inferInstanceAs (DecidableEq {pq : ℕ × ℕ // pq.1 + pq.2 = n})

/-- The `ℤ`-module `C_p ⊗_ℤ D_q`, the summand of the tensor product of bidegree `(p,q)`. -/
abbrev tpSummand (C D : ChainComplex (ModuleCat ℤ) ℕ) (p q : ℕ) : Type :=
  ↥(C.X p ⊗ D.X q)

/-- The degree-`n` module of the tensor product of two chain complexes:
`⨁_{p+q=n} C_p ⊗_ℤ D_q`, as a plain `ℤ`-module. -/
abbrev tpX (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) : Type :=
  DirectSum (tpIdx n) (fun pq => tpSummand C D pq.1.1 pq.1.2)

/-- The `pq`-th structure map of the direct sum defining `tpX`. -/
abbrev tpLof (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n) :
    tpSummand C D pq.1.1 pq.1.2 →ₗ[ℤ] tpX C D n :=
  DirectSum.lof ℤ (tpIdx n) (fun rs => tpSummand C D rs.1.1 rs.1.2) pq

/-- The inclusion `C_p ⊗_ℤ D_q ⟶ ⨁_{p+q=n} C_p ⊗ D_q` of a summand of the tensor product. -/
def tpι (C D : ChainComplex (ModuleCat ℤ) ℕ) (p q n : ℕ) (h : p + q = n) :
    tpSummand C D p q →ₗ[ℤ] tpX C D n :=
  tpLof C D n ⟨(p, q), h⟩

/-- The inclusion `tpι C D p q n h` written with `DirectSum.of`. -/
theorem tpι_apply (C D : ChainComplex (ModuleCat ℤ) ℕ) (p q n : ℕ) (h : p + q = n)
    (x : tpSummand C D p q) :
    tpι C D p q n h x
      = DirectSum.of (fun pq : tpIdx n => tpSummand C D pq.1.1 pq.1.2)
          ⟨(p, q), h⟩ x := rfl

/-- The `(p,q)`-summand of the Koszul differential of the tensor product of two chain
complexes: `x ⊗ y ↦ d x ⊗ y + (-1)^p x ⊗ d y`. -/
def tpDpq (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx (n + 1)) :
    tpSummand C D pq.1.1 pq.1.2 →ₗ[ℤ] tpX C D n :=
  (if hp : 1 ≤ pq.1.1 then
    (tpLof C D n ⟨(pq.1.1 - 1, pq.1.2), by omega⟩).comp
      (TensorProduct.map ((C.d pq.1.1 (pq.1.1 - 1)).hom) (LinearMap.id) :
        tpSummand C D pq.1.1 pq.1.2 →ₗ[ℤ] tpSummand C D (pq.1.1 - 1) pq.1.2)
    else 0)
  + (if hq : 1 ≤ pq.1.2 then
      (-1 : ℤ) ^ pq.1.1 •
        ((tpLof C D n ⟨(pq.1.1, pq.1.2 - 1), by omega⟩).comp
          (TensorProduct.map (LinearMap.id) ((D.d pq.1.2 (pq.1.2 - 1)).hom) :
            tpSummand C D pq.1.1 pq.1.2 →ₗ[ℤ] tpSummand C D pq.1.1 (pq.1.2 - 1)))
      else 0)

/-- The Koszul differential of the tensor product of two chain complexes:
`x ⊗ y ↦ d x ⊗ y + (-1)^p x ⊗ d y` on the summand `C_p ⊗ D_q`. -/
def tpD (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    tpX C D (n + 1) →ₗ[ℤ] tpX C D n :=
  DirectSum.toModule ℤ (tpIdx (n + 1)) (tpX C D n) (tpDpq C D n)

/-- The value of the `(p,q)`-summand of the Koszul differential on a generator `x ⊗ y`. -/
theorem tpDpq_tmul (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx (n + 1))
    (x : ↥(C.X pq.1.1)) (y : ↥(D.X pq.1.2)) :
    tpDpq C D n pq (x ⊗ₜ[ℤ] y)
      = (if hp : 1 ≤ pq.1.1 then
          tpLof C D n ⟨(pq.1.1 - 1, pq.1.2), by omega⟩
            (((C.d pq.1.1 (pq.1.1 - 1)).hom x) ⊗ₜ[ℤ] y)
        else 0)
      + (if hq : 1 ≤ pq.1.2 then
          (-1 : ℤ) ^ pq.1.1 •
            (tpLof C D n ⟨(pq.1.1, pq.1.2 - 1), by omega⟩
              (x ⊗ₜ[ℤ] ((D.d pq.1.2 (pq.1.2 - 1)).hom y)))
        else 0) := by
  rw [tpDpq]
  simp only [LinearMap.add_apply]
  congr 1
  · split_ifs with hp
    · rw [LinearMap.comp_apply]; exact congrArg _ (TensorProduct.map_tmul _ _ x y)
    · rfl
  · split_ifs with hq
    · show (-1 : ℤ) ^ pq.1.1 •
          ((tpLof C D n ⟨(pq.1.1, pq.1.2 - 1), by omega⟩)
            ((TensorProduct.map (LinearMap.id) ((D.d pq.1.2 (pq.1.2 - 1)).hom)) (x ⊗ₜ[ℤ] y)))
        = (-1 : ℤ) ^ pq.1.1 •
          ((tpLof C D n ⟨(pq.1.1, pq.1.2 - 1), by omega⟩)
            (x ⊗ₜ[ℤ] ((D.d pq.1.2 (pq.1.2 - 1)).hom y)))
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
    · rfl

/-- The value of the Koszul differential on a summand generator `x ⊗ y`. -/
theorem tpD_lof_tmul (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx (n + 1))
    (x : ↥(C.X pq.1.1)) (y : ↥(D.X pq.1.2)) :
    tpD C D n (tpLof C D (n + 1) pq (x ⊗ₜ[ℤ] y))
      = (if hp : 1 ≤ pq.1.1 then
          tpLof C D n ⟨(pq.1.1 - 1, pq.1.2), by omega⟩
            (((C.d pq.1.1 (pq.1.1 - 1)).hom x) ⊗ₜ[ℤ] y)
        else 0)
      + (if hq : 1 ≤ pq.1.2 then
          (-1 : ℤ) ^ pq.1.1 •
            (tpLof C D n ⟨(pq.1.1, pq.1.2 - 1), by omega⟩
              (x ⊗ₜ[ℤ] ((D.d pq.1.2 (pq.1.2 - 1)).hom y)))
        else 0) := by
  rw [tpD, DirectSum.toModule_lof, tpDpq_tmul]

/-- The differential of a chain complex applied twice is zero, on elements. -/
theorem d_d_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (p : ℕ) (x : ↥(C.X p)) :
    (C.d (p - 1) (p - 1 - 1)).hom ((C.d p (p - 1)).hom x) = 0 := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    have h : C.d 0 (0 - 1) = 0 := HomologicalComplex.shape C 0 0 (by simp [ComplexShape.down])
    rw [h, ModuleCat.hom_zero]
    rfl
  · rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      HomologicalComplex.d_comp_d C p (p - 1) (p - 1 - 1), ModuleCat.hom_zero]
    rfl

end

end Work.Kunneth
