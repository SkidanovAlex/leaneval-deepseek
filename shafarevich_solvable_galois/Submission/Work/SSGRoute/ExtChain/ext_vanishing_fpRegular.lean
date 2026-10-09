import Mathlib
import Submission.Work.SSGRoute.ExtH1Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dévissage base case: `Ext^{≥2}_G(𝔽_p[G], A) = 0` — plumbing brick

The coefficient SES `0 → ℤ --p--> ℤ → 𝔽_p → 0` of *trivial* representations
(`Work.SSGRoute.Phi1.coeffSES`, `coeffSES_shortExact`) tensored with the group algebra gives the
short exact sequence of **regular** representations

    `0 → ℤ[G] --p--> ℤ[G] → 𝔽_p[G] → 0`;

its middle term `ℤ[G]` is projective, so the connecting map of the long exact sequence in the first
variable gives `Ext^{n+1}_G(𝔽_p[G], A) ≅ Ext^n_G(ℤ[G], A) = 0` for `n ≥ 1`, i.e.
`Ext^{≥2}_G(𝔽_p[G], A) = 0`.  This is the "vacuous" base case of the dévissage in the coefficient
`E`: for `E = 𝔽_p[G]` (the free `𝔽_p[G]`-module of rank one) there is no class of
`Ext²_G(E^∨(1), Kˣ)` to check.

The *statement* of the base case is delegated as
`SSGRoute/ExtChain/subsingleton_ext_fpRegular`; this file contains the coefficient-level brick that
its proof needs (the reduction `ℤ[G] → 𝔽_p[G]` with its coefficient computation rule), together with
the API map for the rest of the plumbing (all verified to elaborate):

* `MonoidAlgebra` is a **structure** with field `MonoidAlgebra.coeff : MonoidAlgebra R M → M →₀ R`
  and constructor `MonoidAlgebra.ofCoeff` (it is NOT a `Finsupp` abbreviation) — so the reduction
  must be written with `coeff`/`ofCoeff`;
* `Representation.coeff_ofMulAction g f h : (((Representation.ofMulAction k G H) g) f).coeff h
  = f.coeff (g⁻¹ • h)` is the computation rule of the regular action; note
  `Representation.leftRegular k G = Representation.ofMulAction k G G` and
  `Rep.leftRegular k G = Rep.of (Representation.leftRegular k G)`;
* `Rep.leftRegular Coeff G` is `Projective` (from `Rep.free_projective`);
* `Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise` is the
  short-exactness criterion for a `Rep`-sequence (`Work.SSGRoute.Phi1.coeffSES_shortExact` is the
  template);
* `Abelian.Ext.contravariant_sequence_exact₃` is the exactness of the long exact sequence in the
  first variable at `Ext^{n₁}(S.X₃, Y)` (it produces `x₁` with `hS.extClass.comp x₁ hn₀ = x₃`);
* `SSGRoute.PTExt.ext_subsingleton_of_projective (P := Rep.leftRegular Coeff G) (hr : 1 ≤ r)` is
  `Ext^{≥1}_G(ℤ[G], A) = 0`;
* when a `Rep`-morphism is built with `Rep.ofHom`, the structure's `X`, `Y`, `ρ`, `σ` must be given
  **explicitly** (`Rep.ofHom (X := …) (Y := …) (ρ := …) (σ := …) {…}`); otherwise instance search
  unfolds `Representation.leftRegular` and asks for a spurious `SMul Coeff G`.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable (p : ℕ) (G : Type) [Group G]

/-- **The coefficientwise reduction** `ℤ[G] → 𝔽_p[G]`. -/
def leftRegularReduceFun : MonoidAlgebra Coeff G → MonoidAlgebra (ZMod p) G :=
  fun x => MonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun c : Coeff => (c.down : ZMod p)) (by simp) x.coeff)

/-- The computation rule of the reduction, coefficientwise: this is what turns the elementwise
short-exactness proof of `0 → ℤ[G] --p--> ℤ[G] → 𝔽_p[G] → 0` into a coefficientwise computation. -/
@[simp] theorem leftRegularReduceFun_coeff (x : MonoidAlgebra Coeff G) (a : G) :
    (leftRegularReduceFun p G x).coeff a = ((x.coeff a).down : ZMod p) := by
  simp [leftRegularReduceFun]

end

end Work.SSGRoute.ExtChain
