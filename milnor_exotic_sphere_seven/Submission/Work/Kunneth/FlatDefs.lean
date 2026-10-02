import Mathlib
import Submission.Work.Kunneth.HomValue
import Submission.Work.Kunneth.HomProd

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The generators of the flat Künneth computation

For a chain complex `C` and a family `M` of `ℤ`-modules, the `(p,q)`-summand of the homological
Künneth complex `homTens C M` has generators `u ⊗ m` with `u` a cycle of `C` and `m ∈ M q`.  This
file names the two objects these generators determine:

* `Work.Kunneth.hQuotOf C M p q u m` — their class in `ker ∂_p ⧸ im ∂_{p+1}`, the `(p,q)`-summand
  of the "cycles modulo boundaries" description of `H_n (homTens C M)`;
* `Work.Kunneth.hHTensOf C M p q u m` — the corresponding element `[u] ⊗ m` of `H_p(C) ⊗ M q`.

The flat Künneth isomorphism is the statement that these correspond
(`Work.Kunneth.flatBase_exists`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

variable (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)

/-- The generator `iCycles u ⊗ m` of the `(p,q)`-summand is a cycle of the coefficient complex:
the differential is `∂ ⊗ 1` and `∂ u = 0`. -/
theorem hDIn_tmul (p q : ℕ) (a : ↥(C.X p)) (m : ↥((sumShift M).X q)) :
    hDIn C M p q (a ⊗ₜ[ℤ] m) = (C.d p (p - 1)).hom a ⊗ₜ[ℤ] m := by
  rw [hDIn]
  erw [LinearMap.rTensor_tmul]

/-- The generator `iCycles u ⊗ m` of the `(p,q)`-summand is a cycle of the coefficient complex:
the differential is `∂ ⊗ 1` and `∂ u = 0`. -/
theorem hDIn_tmul_cycle (p q : ℕ) (u : ↥(C.cycles p)) (m : ↥((sumShift M).X q)) :
    hDIn C M p q ((C.iCycles p).hom u ⊗ₜ[ℤ] m) = 0 := by
  rw [hDIn_tmul, d_iCycles, TensorProduct.zero_tmul]

/-- The class of the generator `u ⊗ m` in the `(p,q)`-summand `ker ∂_p ⧸ im ∂_{p+1}` of the
Künneth computation. -/
noncomputable def hQuotOf (p q : ℕ) (u : ↥(C.cycles p)) (m : ↥((sumShift M).X q))
    (h : hDIn C M p q ((C.iCycles p).hom u ⊗ₜ[ℤ] m) = 0) : ↥(hQuot C M p q) :=
  ((LinearMap.range (hDOut C M p q)).comap (LinearMap.ker (hDIn C M p q)).subtype).mkQ
    ⟨(C.iCycles p).hom u ⊗ₜ[ℤ] m, h⟩

/-- The corresponding element `[u] ⊗ m` of `H_p(C) ⊗ M q`. -/
def hHTensOf (p q : ℕ) (u : ↥(C.cycles p)) (m : ↥((sumShift M).X q)) : ↥(hHTens C M p q) :=
  (C.homologyπ p).hom u ⊗ₜ[ℤ] m

/-- The summand generator of the homological Künneth complex `homTens C M = tpC C (sumShift M)`,
as an element of its degree-`n` part. -/
def flatElem (n p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p)) (m : ↥((sumShift M).X q)) :
    tpX C (sumShift M) n :=
  tpLof C (sumShift M) n ⟨(p, q), hpq⟩ ((C.iCycles p).hom u ⊗ₜ[ℤ] m)

/-- The corresponding summand generator `[u] ⊗ m` of the Künneth target
`tpC (sumShift H) (sumShift M)`, i.e. of `⊕_{p+q=n} H_p(C) ⊗ M q`. -/
def flatHT (n p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p)) (m : ↥((sumShift M).X q)) :
    tpX (sumShift (fun p => C.homology p)) (sumShift M) n :=
  tpLof (sumShift (fun p => C.homology p)) (sumShift M) n ⟨(p, q), hpq⟩
    ((C.homologyπ p).hom u ⊗ₜ[ℤ] m)

end

end Work.Kunneth
