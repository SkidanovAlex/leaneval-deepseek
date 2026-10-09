import Mathlib
import Submission.Work.SSGRoute.coindU_H1_subsingleton_v2
import Submission.Work.SSGRoute.homCoind_H1_free
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹(Gal(Ω/k), Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)) = 0` for the conjugation action

Let `k` be a field, `Ω` an algebraic closure of `k`, `K/k` a finite Galois subextension and `ι` a
finite type.  This file proves the vanishing of `H¹` of `Γ = Gal(Ω/k)` with coefficients the
`Γ`-module

`homCoind k Ω K (Rep.free Coeff Gal(K/k) ι) = Hom_ℤ(ι →₀ ℤ[Gal(K/k)], Ωˣ)`

for the **conjugation** action `(σ · φ) x = σ · φ (σ⁻¹ · x)` (the instance
`homCoind.instDistribMulActionAlgEquiv`, the one used by the bridge `H¹(k,E) ≅ Ext¹_G(E',Kˣ)`),
rather than for the pointwise action treated in `homCoind_H1_free`.

The proof is Shapiro's lemma in coordinates.  As an abelian group the coefficient module is the
product `∏_{i ∈ ι} ∏_{g ∈ Gal(K/k)} Ωˣ`; the additive equivalence is `freeHomEquiv`, and for the
conjugation action it is equivariant for the coinduced action on
`ι → CoindU k Ω K = ∏_{i ∈ ι} Maps(Gal(K/k), Ωˣ)` (`freeHomEquiv_conjSmul_v2`: the conjugation
action moves the basis element `e_{i,g}` to `e_{i,(σ|_K)⁻¹ g}`).  Hence `H¹` of the coefficient
module is `H¹` of a finite product of copies of the coinduced module, which vanishes by Shapiro's
lemma plus Hilbert 90 for the subgroup `Gal(Ω/K)` (`coindU_H1_subsingleton_v2`, a self-contained
proof that avoids the heavier dependency chain of `coindU_H1_subsingleton`).

The type class arguments of the transfer lemma `subsingleton_H1_of_addEquiv` and of the product
lemma `subsingleton_H1_pi` are supplied explicitly: instance synthesis for the *unfolded* type
`M.V →+ Additive Ωˣ` (an `AddMonoidHom`) prefers Mathlib's pointwise action over the conjugation
action of `homCoindDefs`, and for `ι → (Gal(K/k) → Ωˣ)` it prefers the pointwise action over the
coinduced one.

The helper definitions/lemmas are named with a `_v2` suffix so that this module can be imported
together with `homCoind_H1_free_conj` (which contains the same argument under the plain names).
-/

open CategoryTheory

namespace Work.SSGRoute

open SSGRoute.PTExt

noncomputable section

section Conjugation

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] {ι : Type} [Finite ι]

/-- The conjugation action of `Γ = Gal(Ω/k)` on `homCoind k Ω K M = Hom_ℤ(M.V, Ωˣ)`,
`(σ · φ) x = σ · φ (σ⁻¹ · x)`, written out as an explicit function (so that no type class
instance is involved in its statement).  It is definitionally the `smul` of the instance
`homCoind.instDistribMulActionAlgEquiv`. -/
def conjSmul_v2 (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (σ : Ω ≃ₐ[k] Ω) (φ : homCoind k Ω K M) :
    homCoind k Ω K M :=
  (homCoind.smulHom σ).comp (φ.comp ((M.ρ (SSGRoute.res k K σ)⁻¹).toAddMonoidHom))

/-- The coinduced action of `Γ = Gal(Ω/k)` on `CoindU k Ω K = Maps(Gal(K/k), Ωˣ)`,
`(σ · ψ) x = σ · ψ ((σ|_K)⁻¹ x)`, written out as an explicit function.  It is definitionally the
`smul` of the instance `CoindU.instDistribMulAction`. -/
def coindAct_v2 (σ : Ω ≃ₐ[k] Ω) (ψ : CoindU k Ω K) : CoindU k Ω K :=
  fun x => σ • ψ ((SSGRoute.res k K σ)⁻¹ * x)

/-- **Equivariance of the product decomposition.**  `freeHomEquiv` is `Γ`-equivariant from
`homCoind k Ω K (Rep.free Coeff Gal(K/k) ι)` with the conjugation action to `ι → CoindU k Ω K`
with the coinduced action: the conjugation action sends the basis element `e_{i,g}` to
`e_{i,(σ|_K)⁻¹ g}`, which is exactly the permutation built into the coinduced action. -/
theorem freeHomEquiv_conjSmul_v2 (σ : Ω ≃ₐ[k] Ω)
    (φ : homCoind k Ω K (Rep.free Coeff (K ≃ₐ[k] K) ι)) :
    freeHomEquiv (conjSmul_v2 _ σ φ) = fun i => coindAct_v2 (K := K) σ (freeHomEquiv φ i) := by
  funext i g
  rw [freeHomEquiv_apply]
  rw [show (coindAct_v2 (K := K) σ (freeHomEquiv φ i)) g
      = σ • ((freeHomEquiv φ) i ((SSGRoute.res k K σ)⁻¹ * g)) from rfl]
  rw [freeHomEquiv_apply]
  rw [show conjSmul_v2 (Rep.free Coeff (K ≃ₐ[k] K) ι) σ φ
        (Finsupp.single i (MonoidAlgebra.single g 1))
      = σ • (φ ((Rep.free Coeff (K ≃ₐ[k] K) ι).ρ ((SSGRoute.res k K σ))⁻¹
          (Finsupp.single i (MonoidAlgebra.single g 1)))) from rfl]
  rw [Representation.free_single_single]

end Conjugation

/-- `H¹(Gal(Ω/k), Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)) = 0` for the conjugation action. -/
theorem homCoind_H1_free_conj_v2 {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] {ι : Type} [Finite ι] : Subsingleton (@Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)) _ _ (Work.SSGRoute.homCoind.instAddCommGroup (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)) (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  have hN := subsingleton_H1_pi (fun _ : ι =>
    coindU_H1_subsingleton_v2 (k := k) (Ω := Ω) (K := K))
  let instN : DistribMulAction (Ω ≃ₐ[k] Ω) (ι → CoindU k Ω K) :=
    Pi.distribMulAction (Ω ≃ₐ[k] Ω)
  exact @subsingleton_H1_of_addEquiv (Ω ≃ₐ[k] Ω) _ _
    (Work.SSGRoute.homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))
    (ι → CoindU k Ω K)
    (Work.SSGRoute.homCoind.instAddCommGroup (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))
    (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv
      (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))
    _ instN freeHomEquiv (fun σ φ => freeHomEquiv_conjSmul_v2 σ φ) hN

end

end Work.SSGRoute
