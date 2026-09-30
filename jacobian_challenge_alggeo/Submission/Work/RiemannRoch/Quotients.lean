/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR, layer 2: the basic quotient modules of the adelic theory

This file names the families of `k`-modules that Riemann–Roch is about, so that statements
about them stay readable.  Everything is expressed inside the ambient product
`X = (C.Place → K)`, not inside the adèle space, so that the quotient notation is well
behaved.

* `Aquot C D E = A(E)/A(D)` — the quotient whose dimension is `deg (E - D)` (Riemann's
  theorem, the "elementary" part of Serre II §5);
* `Lquot C D E = (A(E) ∩ K)/(A(D) ∩ K) = L(E)/L(D)` — the quotient of Riemann–Roch spaces;
* `Kquot C D E = (A(E) + K)/(A(D) + K)` — the quotient measuring `i(D) - i(E)`;
* `KquotAd C D E` — the image of `A(E) + K` in `A_K/(A(D) + K)`; its dimension is `i(D)-i(E)`.

For `D ≤ E` there is a short exact sequence of finite dimensional `k`-modules
`0 → L(E)/L(D) → A(E)/A(D) → (A(E)+K)/(A(D)+K) → 0`, so
`deg (E - D) = dim A(E)/A(D) = (l(E) - l(D)) + dim (A(E)+K)/(A(D)+K)`,
and `dim (A(E)+K)/(A(D)+K) = i(D) - i(E)`.  Adding gives
`i(D) - l(D) + deg D = i(E) - l(E) + deg E`, the constancy of the "defect" which is
Riemann–Roch.
-/
import Submission.Work.RiemannRoch.Adeles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The relative quotient `T/(S ∩ T)` of two submodules of a `k`-module, the quotient shape
used throughout this area: `relQuot (Asub C D) (Asub C E)` is `A(E)/A(D)` for `D ≤ E` and
`relQuot (Asub C D ⊔ diagK C) (Asub C E ⊔ diagK C)` is `(A(E)+K)/(A(D)+K)`. -/
abbrev relQuot {M : Type*} [AddCommGroup M] [Module k M] (S T : Submodule k M) : Type _ :=
  ↥T ⧸ S.comap T.subtype

/-- The second isomorphism theorem in the form used throughout: `T/(S ∩ T)` is linearly
equivalent to the image of `T` in `M/S`. -/
def relQuotEquivMap {M : Type*} [AddCommGroup M] [Module k M] (S T : Submodule k M) :
    relQuot S T ≃ₗ[k] ↥(T.map (Submodule.mkQ S)) := by
  let f : ↥T →ₗ[k] (M ⧸ S) := (Submodule.mkQ S).domRestrict T
  have hker : f.ker = S.comap T.subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, f, LinearMap.domRestrict_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rfl
  have hrange : f.range = T.map (Submodule.mkQ S) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : M), x.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have h := f.quotKerEquivRange
  rw [hker, hrange] at h
  exact h

/-- The `k`-module `A(E)/A(D)`: adèles with poles bounded by `E`, modulo those bounded by
`D`.  For `D ≤ E` this is the quotient by `A(D)`. -/
abbrev Aquot (C : Curve k) (D E : C.Div) : Type u :=
  ↥(A C E) ⧸ (A C D).comap (A C E).subtype

/-- The `k`-module `L(E)/L(D) = (A(E) ∩ K)/(A(D) ∩ K)`. -/
abbrev Lquot (C : Curve k) (D E : C.Div) : Type u :=
  ↥(A C E ⊓ Kdiag C) ⧸ (A C D ⊓ Kdiag C).comap (A C E ⊓ Kdiag C).subtype

/-- The `k`-module `(A(E) + K)/(A(D) + K)`. -/
abbrev Kquot (C : Curve k) (D E : C.Div) : Type u :=
  ↥(A C E ⊔ Kdiag C) ⧸ (A C D ⊔ Kdiag C).comap (A C E ⊔ Kdiag C).subtype

/-- The image of `A(E) + K` in `A_K/(A(D) + K)`: a submodule of `H1 C D` whose dimension is
`i(D) - i(E)` for `D ≤ E`. -/
abbrev KquotAd (C : Curve k) (D E : C.Div) : Submodule k (H1 C D) :=
  (Asub C E ⊔ diagK C).map (Submodule.mkQ (Asub C D ⊔ diagK C))

end

end Curve

end Work.RiemannRoch
