import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Submission.Work.SSGRoute.E9Nodes.e9_baseS
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E9Nodes

/-!
# Restriction of the inertia condition along a place

Let `q` be a finite place of a number field `L`, `q'` a finite place of a number field `L'`
extending `q` (`q'.asIdeal.LiesOver q.asIdeal`), and let `σ : Gal(L'/k)` restrict to
`τ : Gal(L/k)`, in the sense that `σ (algebraMap L L' x) = algebraMap L L' (τ x)` for all `x : L`.

The claim below is the standard fact that *inertia restricts*: if `σ` acts trivially on the
residue field of `q'`, then `τ` acts trivially on the residue field of `q`.

In the `valuation` formulation of `SSGRoute.PTExt.IsInertiaAt` the proof is one local
computation.  For `x ∈ 𝓞 L` put `z = τ x - x ∈ 𝓞 L`.  Then

`algebraMap (𝓞 L) (𝓞 L') z = σ (algebraMap (𝓞 L) (𝓞 L') x) - algebraMap (𝓞 L) (𝓞 L') x`

because `σ` restricts to `τ`; the right-hand side lies in `q'` (with `σ` and `x` in `𝓞 L'`) since
`σ` is in the inertia group of `q'`.  As `q'` lies over `q`, this means `z ∈ q`, i.e.
`q.valuation L (τ x - x) < 1`.  No Galois-ness of `L/k` or of `L'/L` is used: everything takes
place in `𝓞 L' / q'` and is pulled back along `q'.asIdeal.under (𝓞 L) = q.asIdeal`.
-/

theorem e9_inertia_restrict (k L L' : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [Field L'] [NumberField L'] [Algebra k L'] [Algebra L L']
    [IsScalarTower k L L'] [FiniteDimensional L L']
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'))
    (hq : q'.asIdeal.LiesOver q.asIdeal)
    (σ : L' ≃ₐ[k] L') (τ : L ≃ₐ[k] L)
    (hcomm : ∀ x : L, σ (algebraMap L L' x) = algebraMap L L' (τ x))
    (hσ : SSGRoute.PTExt.IsInertiaAt q' σ) :
    SSGRoute.PTExt.IsInertiaAt q τ := by
  intro x
  -- `z = τ x - x`, made an element of `𝓞 L` by integrality of `τ x`.
  set z : NumberField.RingOfIntegers L :=
    NumberField.RingOfIntegers.mapRingEquiv (τ : L ≃+* L) x - x with hz
  have hzL : (z : L) = τ (x : L) - (x : L) := by
    simp [hz]
  -- It suffices to rewrite `τ x - x` as `↑z` and to test membership of `q`.
  rw [← hzL]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  -- The prime of `L` is the contraction of the prime of `L'`.
  have hunder : q.asIdeal = Ideal.under (NumberField.RingOfIntegers L) q'.asIdeal := hq.over
  rw [hunder, Ideal.under, Ideal.mem_comap]
  -- `y = algebraMap (𝓞 L) (𝓞 L') x`, which lies in `𝓞 L'`.
  set y : NumberField.RingOfIntegers L' :=
    algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers L') x with hy
  have hyL : (y : L') = algebraMap L L' (x : L) := rfl
  refine (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L') q'
    (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers L') z)).mp ?_
  show q'.valuation L' (algebraMap L L' (z : L)) < 1
  -- The key computation: `algebraMap L L' z = σ y - y`.
  have harg : algebraMap L L' (z : L) = σ (y : L') - (y : L') := by
    rw [hyL, hzL, map_sub, hcomm (x : L)]
  rw [harg]
  exact hσ y

end Work.SSGRoute.E9Nodes
