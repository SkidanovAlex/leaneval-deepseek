import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.SSS.ExpTens
import Submission.Work.Cohomology.singularChains_free
import Submission.Work.Pi6.SRANGE.rTensor_injective_of_torsionFree_quotient
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Pi6.K2Z.baseChangeFlat
import Submission.Work.Pi6.SRANGE.QuotModel
import Submission.Work.Cohomology.uctDefs
import Submission.Work.Pi6.EMM2.hrExtendScalars
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMM2

/-- **Change of coefficients `ℤ → 𝕜` for singular homology, one degree above a torsion-free group.**

Let `X` be a topological space and `𝕜` a commutative ring.  If the integral homology `H_m(X;ℤ)` is
torsion-free, then the `𝕜`-homology in degree `m+1` is the extension of scalars of the integral one:
`H_{m+1}(X;𝕜) ≅ 𝕜 ⊗[ℤ] H_{m+1}(X;ℤ)`.

This is the universal coefficient theorem `H_{m+1}(X;𝕜) ≅ H_{m+1}(X;ℤ) ⊗ 𝕜 ⊕ Tor_1(H_m(X;ℤ),𝕜)`
in the case where the `Tor` term vanishes (because `H_m(X;ℤ)` is torsion-free, hence flat over `ℤ`).

Route.  Put `C := C_*(X;ℤ)` (the integral singular chains, degreewise free, so torsion-free), and
`F := ModuleCat.extendScalars (Int.castRingHom 𝕜)`, so that `F.obj M = 𝕜 ⊗[ℤ] M` and the `𝕜`-singular
chains are `F.mapHomologicalComplex C` up to the identification
`Work.StemsB.SphRat.chainComplexBaseChange F (TopCat.toSSet.obj (TopCat.of X)) (ModuleCat.of ℤ ℤ)`
composed with `Work.StemsB.SphRat.chainComplexCoeffIso` for the unitor `F.obj ℤ ≅ 𝕜` (exactly the
`hΦ` of `Work.Pi6.K2Z.baseChangeFlat`; that file does this without any flatness).

Let `Z_n := ker (C.d n (n-1))` and `B_n := range (C.d (n+1) n)`, so
`0 → Z_n → C_n → B_{n-1} → 0` and `0 → B_n → Z_n → H_n → 0` are exact, and every `Z_n`, `B_n` is a
submodule of a torsion-free ℤ-module, hence torsion-free, hence flat over ℤ
(`Module.IsTorsionFree → Module.Flat` over the Dedekind domain `ℤ`; see
`Work.Pi6.SRANGE.rTensor_injective_of_torsionFree_quotient` for the exactness step, with
`LinearMap.lTensor_inj_iff_rTensor_inj` to pass between the two tensor conventions).

Then `(F.mapHomologicalComplex C).homology (m+1)` is
`ker (d_{m+1} ⊗ 1) / im (d_{m+2} ⊗ 1)`, and:

* `ker (d_{m+1} ⊗ 1) = F(Z_{m+1})`: the differential factors as
  `F(C_{m+1}) ↠ F(B_m) → F(C_m)` with kernel of the first map `F(Z_{m+1})` (flatness of `B_m`), and
  `ker (F(B_m) → F(C_m)) = ker (F(B_m) → F(Z_m)) = Tor_1(H_m,𝕜) = 0` — the last equality is exactly
  where the hypothesis `hH` is used (`F(Z_m) → F(C_m)` is injective by flatness of `B_{m-1}`);
* `im (d_{m+2} ⊗ 1) = image (F(B_{m+1}) → F(Z_{m+1}))`, using right exactness of `F` to factor
  `F(C_{m+2}) ↠ F(B_{m+1})`;
* hence `H_{m+1}(F C) = coker (F(B_{m+1}) → F(Z_{m+1}))`, and right exactness of `F` gives
  `coker (F(B_{m+1}) → F(Z_{m+1})) ≅ F (coker (B_{m+1} → Z_{m+1})) = F(H_{m+1}(C))`. -/
theorem HRisoExtendScalars (𝕜 : Type) [CommRing 𝕜] {X : Type} [TopologicalSpace X] (m : ℕ)
    (hH : Module.IsTorsionFree ℤ (Work.Pi6.HR ℤ X m)) :
    Nonempty (Work.Pi6.HR 𝕜 X (m + 1) ≅
      (ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (Work.Pi6.HR ℤ X (m + 1))) :=
  HRisoExtendScalarsTF 𝕜 m hH

end Work.Pi6.EMM2
