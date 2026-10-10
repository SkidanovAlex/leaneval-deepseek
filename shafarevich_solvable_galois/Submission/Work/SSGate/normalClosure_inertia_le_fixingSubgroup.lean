import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Work.SSGRoute.E9Nodes.e9_inertia_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inertia group at `q'` lies in the fixing subgroup of an unramified subextension

Let `k ⊆ E ⊆ L` be number fields with `L/k` finite Galois and `E/k` finite Galois, let `q'` be a
finite place of `L`, and suppose that *every* prime of `E` lying over the prime `𝔭 = q' ∩ k` of `k`
is unramified over `k` (ramification index `1`).

Then the inertia group `I_{q'} ≤ Gal(L/k)` of `q'` (the elements of `Gal(L/k)` acting trivially on
the residue field at `q'`, here spelled `SSGRoute.PTExt.IsInertiaAt q'`) is contained in the
fixing subgroup of `E`, and hence -- since `E/k` is Galois, so that the fixing subgroup is normal
in `Gal(L/k)` -- so is its normal closure.

The arithmetic input is the standard fact that *inertia restricts*: for `σ ∈ Gal(L/k)` inertial at
`q'`, its restriction `τ ∈ Gal(E/k)` is inertial at the prime `𝔮 = q' ∩ E` below `q'`. This is
`Work.SSGRoute.E9Nodes.e9_inertia_restrict`. The inertia subgroup of `E/k` at `𝔮` is
`Ideal.inertia (↥E ≃ₐ[k] ↥E) 𝔮.asIdeal`, which has order the ramification index `e(𝔮|𝔭)`
(`Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one`), hence is
trivial by hypothesis, so `τ = 1`, i.e. `σ` fixes `E` pointwise.
-/

namespace Work.SSGate

open scoped Pointwise

set_option linter.style.haveILetI false

/-- **Inertia is contained in the fixing subgroup of an unramified Galois subextension.**

If `k ⊆ E ⊆ L` are number fields with `L/k` and `E/k` finite Galois and every prime of `E` above
`q' ∩ k` is unramified over `k`, then every element of `Gal(L/k)` inertial at `q'` fixes `E`
pointwise. -/
theorem isInertiaAt_le_fixingSubgroup {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (E : IntermediateField k L) [FiniteDimensional k ↥E] [IsGalois k ↥E]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hunr : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
        𝔮.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) :
    ∀ σ : L ≃ₐ[k] L, SSGRoute.PTExt.IsInertiaAt q' σ → σ ∈ E.fixingSubgroup := by
  -- The three rings of integers form a tower, so that the prime `q' ∩ E` of `E` lies over the
  -- prime `q' ∩ k` of `k`.
  haveI htow : IsScalarTower (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers ↥E)
      (NumberField.RingOfIntegers L) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro σ hσ
  -- The prime `𝔮 = q' ∩ E` of `E` below `q'`.
  let 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E) :=
    ⟨q'.asIdeal.under (NumberField.RingOfIntegers ↥E), inferInstance,
      Ideal.under_ne_bot _ q'.ne_bot⟩
  have h𝔮lies : 𝔮.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) :=
    Ideal.LiesOver.mk (Ideal.under_under (A := NumberField.RingOfIntegers k)
      (B := NumberField.RingOfIntegers ↥E) q'.asIdeal).symm
  have hq'lies : q'.asIdeal.LiesOver 𝔮.asIdeal :=
    Ideal.over_under (A := NumberField.RingOfIntegers ↥E) q'.asIdeal
  -- Inertia restricts: the restriction `τ` of `σ` to `E` is inertial at `𝔮`.
  have hτin : SSGRoute.PTExt.IsInertiaAt 𝔮 (AlgEquiv.restrictNormalHom ↥E σ) :=
    Work.SSGRoute.E9Nodes.e9_inertia_restrict k ↥E L 𝔮 q' hq'lies σ
      (AlgEquiv.restrictNormalHom ↥E σ)
      (fun x => (AlgEquiv.restrictNormal_commutes σ ↥E x).symm) hσ
  have hmem : AlgEquiv.restrictNormalHom ↥E σ ∈
      Ideal.inertia (↥E ≃ₐ[k] ↥E) 𝔮.asIdeal :=
    (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k) (K := ↥E) 𝔮 _).mp hτin
  -- The inertia subgroup of `E/k` at `𝔮` is trivial, because `e(𝔮|𝔭) = 1`.
  haveI : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
  haveI : (q'.asIdeal.under (NumberField.RingOfIntegers k)).IsPrime := inferInstance
  haveI : 𝔮.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) := h𝔮lies
  have hbot : Ideal.inertia (↥E ≃ₐ[k] ↥E) 𝔮.asIdeal = ⊥ :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      (F := k) (K := ↥E) (q'.asIdeal.under (NumberField.RingOfIntegers k)) 𝔮.asIdeal).mpr
      (hunr 𝔮 h𝔮lies)
  -- Hence `τ = 1`, so `σ` lies in the kernel of restriction to `E`, i.e. in the fixing subgroup.
  have hmem' : AlgEquiv.restrictNormalHom ↥E σ ∈ (⊥ : Subgroup (↥E ≃ₐ[k] ↥E)) := by
    rw [← hbot]; exact hmem
  have h1 : AlgEquiv.restrictNormalHom ↥E σ = 1 := Subgroup.mem_bot.mp hmem'
  have hker : σ ∈ (AlgEquiv.restrictNormalHom ↥E).ker := MonoidHom.mem_ker.mpr h1
  rwa [IntermediateField.restrictNormalHom_ker] at hker

theorem normalClosure_inertia_le_fixingSubgroup {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (E : IntermediateField k L) [FiniteDimensional k ↥E] [IsGalois k ↥E]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hunr : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
        𝔮.asIdeal.LiesOver (q'.asIdeal.under (NumberField.RingOfIntegers k)) →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) :
    ∀ σ : L ≃ₐ[k] L,
      σ ∈ Subgroup.normalClosure {σ : L ≃ₐ[k] L | SSGRoute.PTExt.IsInertiaAt q' σ} →
      σ ∈ E.fixingSubgroup := by
  -- The fixing subgroup of `E` is normal (`E/k` Galois), and it contains the inertia group, so it
  -- contains the normal closure of the inertia group.
  intro σ hσ
  refine Subgroup.normalClosure_le_normal (N := E.fixingSubgroup)
    (s := {σ : L ≃ₐ[k] L | SSGRoute.PTExt.IsInertiaAt q' σ}) ?_ hσ
  exact isInertiaAt_le_fixingSubgroup E q' hunr

end Work.SSGate
