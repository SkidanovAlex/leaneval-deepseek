import Mathlib
import Submission.Work.Pi6.MSS.Pages
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The page data of the spectral sequence of a filtered cochain complex

`PagesData 𝕜 W` bundles the products and the projections on the pages `pEraw 𝕜 W r s n` of a
filtered cochain complex with a product `W : CohFilt 𝕜`, together with their characteristic
properties (naturality on representatives, the Leibniz rule, and the identification
`E_{r+1} ≅ ker d_r / im d_r`).

Indices are `ℕ`-indices `(s, n)` = (filtration degree, cohomological degree); the bidegree indexing
`(s, q)` of `Work.Pi6.CohSS` is `n = s + q`.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

variable (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜)

/-- Transport of a page along equalities of both indices. -/
def pEcast (r : ℕ) {a b : ℕ} {m k : ℕ} (h : a = b) (h' : m = k) :
    pEraw 𝕜 W r a m ≅ pEraw 𝕜 W r b k :=
  eqToIso (by subst h; subst h'; rfl)

/-- Transport of a page along an equality of the filtration index. -/
def pEcastS (r : ℕ) {a b : ℕ} (m : ℕ) (h : a = b) :
    pEraw 𝕜 W r a m ≅ pEraw 𝕜 W r b m :=
  eqToIso (by subst h; rfl)

/-- Transport of a page along an equality of the cohomological degree. -/
def pEcastN (r : ℕ) {m k : ℕ} (a : ℕ) (h : m = k) :
    pEraw 𝕜 W r a m ≅ pEraw 𝕜 W r a k :=
  eqToIso (by subst h; rfl)

/-- **The page data**: the product and the projection on the pages, with their characteristic
properties. -/
structure PagesData where
  /-- the product on the cycles `Z_r^s × Z_r^{s'} → Z_r^{s+s'}` -/
  mulZ : ∀ (r s n s' n' : ℕ), ↥(pZ 𝕜 W r s n) →ₗ[𝕜] ↥(pZ 𝕜 W r s' n') →ₗ[𝕜]
    ↥(pZ 𝕜 W r (s+s') (n+n'))
  /-- its underlying value -/
  mulZ_val : ∀ (r s n s' n' : ℕ) (x : ↥(pZ 𝕜 W r s n)) (y : ↥(pZ 𝕜 W r s' n')),
    ((mulZ r s n s' n') x y : W.C.X (n+n')) = W.mul n n' (x : W.C.X n) (y : W.C.X n')
  /-- the product on the pages -/
  mul : ∀ (r s n s' n' : ℕ), pEraw 𝕜 W r s n →ₗ[𝕜] pEraw 𝕜 W r s' n' →ₗ[𝕜]
    pEraw 𝕜 W r (s+s') (n+n')
  /-- the product on the pages is induced by the product on the cycles -/
  mul_nat : ∀ (r s n s' n' : ℕ) (x : ↥(pZ 𝕜 W r s n)) (y : ↥(pZ 𝕜 W r s' n')),
    (mul r s n s' n') (Submodule.mkQ _ x) (Submodule.mkQ _ y)
      = Submodule.mkQ _ ((mulZ r s n s' n') x y)
  /-- the Leibniz rule for the differential -/
  mul_leib : ∀ (r s n s' n' : ℕ)
      (e₁ : s+r+s' = s+s'+r) (e₁' : n+1+n' = n+n'+1)
      (e₂ : s+(s'+r) = s+s'+r) (e₂' : n+(n'+1) = n+n'+1)
      (x : pEraw 𝕜 W r s n) (y : pEraw 𝕜 W r s' n'), 2 ≤ r →
    pD 𝕜 W r (s+s') (n+n') ((mul r s n s' n') x y) =
      (pEcast 𝕜 W r e₁ e₁').hom ((mul r (s+r) (n+1) s' n') ((pD 𝕜 W r s n) x) y) +
      (-1 : 𝕜)^n •
        (pEcast 𝕜 W r e₂ e₂').hom ((mul r s n (s'+r) (n'+1)) x ((pD 𝕜 W r s' n') y))
  /-- the projection `E_r^s → E_{r+1}^s` -/
  proj : ∀ (r s n : ℕ), (LinearMap.ker (pD 𝕜 W r s n).hom) →ₗ[𝕜] pEraw 𝕜 W (r+1) s n
  /-- the projection is surjective -/
  proj_surj : ∀ (r s n : ℕ), 2 ≤ r → Function.Surjective (proj r s n)
  /-- the kernel of the projection is the image of the incoming differential -/
  proj_ker : ∀ (r s n : ℕ), 2 ≤ r → ∀ (s' n' : ℕ) (hs : s' + r = s) (hn : n' + 1 = n)
      (x : LinearMap.ker (pD 𝕜 W r s n).hom),
    proj r s n x = 0 ↔ ∃ w : pEraw 𝕜 W r s' n',
      (pEcast 𝕜 W r hs hn).hom ((pD 𝕜 W r s' n') w) = (x : pEraw 𝕜 W r s n)
  /-- the descent of the product: `proj_mul` -/
  proj_mul : ∀ (r : ℕ), 2 ≤ r → ∀ (s n s' n' : ℕ)
      (x : LinearMap.ker (pD 𝕜 W r s n).hom) (y : LinearMap.ker (pD 𝕜 W r s' n').hom)
      (z : LinearMap.ker (pD 𝕜 W r (s+s') (n+n')).hom),
      (z : pEraw 𝕜 W r (s+s') (n+n')) = (mul r s n s' n') x y →
      proj r (s+s') (n+n') z = (mul (r+1) s n s' n') (proj r s n x) (proj r s' n' y)

end

end Work.Pi6.MSS
