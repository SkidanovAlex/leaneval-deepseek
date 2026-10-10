import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Work.SSGRoute.E9Nodes.e9_inertia_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.Sha2Lib

/-- **An automorphism of `L` which is inertial at a prime fixes every subfield unramified there.**

Let `k ⊆ E ⊆ L` be an extension of number fields with `L/k` and `E/k` finite Galois; let `q` be a
nonzero prime of `𝓞 L` and `qE = q ∩ 𝓞 E` its contraction (`hqE : q.asIdeal.LiesOver qE.asIdeal`).
Assume `E/k` is *unramified* at `qE` (`hunr : e(qE | qE ∩ 𝓞 k) = 1`).  Then every `σ : L ≃ₐ[k] L`
lying in the inertia group of `q` (`SSGRoute.PTExt.IsInertiaAt q σ`, i.e.
`q.valuation L (σ x - x) < 1` for all `x : 𝓞 L`) restricts to the identity of `E`:
`AlgEquiv.restrictNormalHom E σ = 1`.

Proof: `IsInertiaAt q σ` is membership in `Ideal.inertia Gal(L/k) q.asIdeal`
(`Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia`, in `Submission/Work/SSGRoute/E9Nodes/e9_baseS.lean`);
the restriction step `IsInertiaAt q σ → IsInertiaAt qE (σ|_E)` is already proved in
`Submission/Work/SSGRoute/E9Nodes/e9_inertia_restrict.lean` — reuse it.  Then `σ|_E` lies in
`Ideal.inertia Gal(E/k) qE.asIdeal`, which is trivial because `e(qE | qE ∩ 𝓞 k) = 1`
(`Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one`, or
`Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.eq_one_of_residue_mk_eq_one`).  Use `hqE.over`
and instantiate the E-side bridge at `qE.asIdeal.under (𝓞 k)`. -/
theorem restrictNormalHom_eq_one_of_isInertiaAt {k E L : Type} [Field k] [NumberField k]
    [Field E] [NumberField E] [Algebra k E] [Field L] [NumberField L] [Algebra k L]
    [Algebra E L] [IsScalarTower k E L] [FiniteDimensional k L] [FiniteDimensional k E]
    [IsGalois k L] [IsGalois k E]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (qE : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hqE : q.asIdeal.LiesOver qE.asIdeal)
    (hunr : qE.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1)
    (σ : L ≃ₐ[k] L) (hσ : SSGRoute.PTExt.IsInertiaAt q σ) :
    AlgEquiv.restrictNormalHom E σ = 1 := by
  -- The image of `σ` in `Gal(E/k)`.
  let τ : E ≃ₐ[k] E := AlgEquiv.restrictNormalHom E σ
  -- `σ` restricts to `τ`: the two agree on the image of `E`.
  have hcomm : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (τ x) := by
    intro x
    have h := AlgEquiv.restrictNormal_commutes σ E x
    rw [← h]
    congr 1
  -- `L` is finite over the intermediate field `E`.
  haveI : FiniteDimensional E L := FiniteDimensional.right k E L
  -- Inertia restricts to the subfield.
  have hτin : SSGRoute.PTExt.IsInertiaAt qE τ :=
    Work.SSGRoute.E9Nodes.e9_inertia_restrict k E L qE q hqE σ τ hcomm hσ
  -- `τ` therefore lies in the inertia subgroup of `qE` inside `Gal(E/k)`.
  have hmem : τ ∈ Ideal.inertia (E ≃ₐ[k] E) qE.asIdeal :=
    (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := E) qE τ).mp hτin
  -- which is trivial, because `qE` is unramified over `k`.
  have hbot : Ideal.inertia (E ≃ₐ[k] E) qE.asIdeal = ⊥ :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      (qE.asIdeal.under (NumberField.RingOfIntegers k)) qE.asIdeal).mpr hunr
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

end Work.SSGRoute.Sha2Lib
