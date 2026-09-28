import Mathlib
import Submission.Work.SSS.Packet

/-!
# The bottom-row chain of the spectral sequence of a saturated filtration

This file sets up the explicit objects of the "bottom row" argument for the spectral sequence of a
saturated filtration `ξ` of a chain complex `C` of `ℤ`-modules.

For `m : ℕ` (the total degree of the `E¹` page under consideration), the relevant objects are:

* `Psi ξ m s ⊆ H_m(F_m)` is the `s`-th step of the image filtration of `H_m(F_m)` under the
  inclusions `F_s ⊆ F_m`;
* `baseJ ξ m r ⊆ H_m(F_m)` is `Psi ξ m (m+1-r)`, with the convention `F_{-1} = 0` (so that
  `baseJ ξ m r = ⊥` for `r ≥ m+2`);
* `baseZ ξ m r ⊆ E¹_{m+1,0}` is the preimage of `baseJ ξ m r` under the connecting map
  `k : E¹_{m+1,0} → H_m(F_m)`;
* `baseB ξ m ⊆ E¹_{m+1,0}` is the image of `d¹ : E¹_{m+2,0} → E¹_{m+1,0}`.

The bottom row argument shows `E²_{m+1,0} = baseZ ξ m 2 / baseB ξ m`, that the quotients
`baseZ ξ m r / baseZ ξ m (r+1)` are the strata of the image filtration of `H_m(F_m)`, and that the
latter are subquotients of the `E²` page in total degree `m`.

`FgQuot B Z` expresses that `Z / B` is finitely generated, inside the lattice of submodules of an
ambient module `A`; it is stated for a general commutative ring so as to be usable over `ℤ`
(where the `ℤ`-module structures coming from `AddCommGroup` and from `Submodule` quotients are only
propositionally equal).
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- `FgQuot B Z` means that the quotient `Z / B` is finitely generated (here `B ≤ Z` is expected,
and `Z.map (mkQ B)` is the image of `Z` in the quotient of the ambient module by `B`). -/
def FgQuot {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (B Z : Submodule R A) : Prop :=
  (Z.map (Submodule.mkQ B)).FG

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- The `s`-th stratum of the image filtration of `H_m(F_m)`: the image of the map induced by the
inclusion `F_s ⊆ F_m`, and `⊥` when `s > m`. -/
def Psi (ξ : Filtration C) (m s : ℕ) : Submodule ℤ ((ξ.F.obj m).homology m) :=
  if h : s ≤ m then (HomologicalComplex.homologyMap (ξ.F.map (homOfLE h)) m).hom.range else ⊥

/-- `baseJ ξ m r = Ψ_{m+1-r} ⊆ H_m(F_m)`, with `Ψ_{-1} = 0`; thus `baseJ ξ m r = ⊥` for `r ≥ m+2`
and `baseJ ξ m 2 = ker(jF ξ m 0)`. -/
def baseJ (ξ : Filtration C) (m r : ℕ) : Submodule ℤ ((ξ.F.obj m).homology m) :=
  if _ : r ≤ m + 1 then Psi ξ m (m + 1 - r) else ⊥

/-- `baseZ ξ m r ⊆ E¹_{m+1,0}` is the preimage of `baseJ ξ m r` under the connecting map
`k : E¹_{m+1,0} → H_m(F_m)`. -/
def baseZ (ξ : Filtration C) (m r : ℕ) : Submodule ℤ (E1 ξ (m + 1) 0) :=
  Submodule.comap (kF ξ m 0).hom (baseJ ξ m r)

/-- `baseB ξ m ⊆ E¹_{m+1,0}` is the image of the first differential
`d¹ : E¹_{m+2,0} → E¹_{m+1,0}`. -/
def baseB (ξ : Filtration C) (m : ℕ) : Submodule ℤ (E1 ξ (m + 1) 0) :=
  (d1 ξ (m + 1) 0).hom.range

/-- `E2quot ξ s t` expresses `E²_{s,t}` as the quotient `ker (d¹_{s,t}) / im (d¹_{s+1,t})` of the
`E¹` page, via the explicit description of the complex `E1Complex ξ t`. -/
def E2quot (ξ : Filtration C) (s t : ℕ) : Prop :=
  FgQuot (LinearMap.range ((E1Complex ξ t).d (s + 1) s).hom)
    (LinearMap.ker ((E1Complex ξ t).d s (s - 1)).hom)

end

end Work.SSS
