import Mathlib
import Submission.Work.SSGRoute.TPatom.inertia_le_fixingSubgroup_of_ramificationIdx_eq_one
import Submission.Work.SSGRoute.E9Nodes.e9_baseS
import Submission.Work.SSGRoute.E9b.isUnramifiedClassAt_conj
import Submission.Work.SSGRoute.Sha2Lib.smulHeightOneSpectrum_inv_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

namespace Work.SSGRoute.TPatom

/-- **The normal closure of the inertia group at `q'` fixes any intermediate field which is
unramified at the prime `l` below `q'`.**

Let `k ⊆ E0 ⊆ L` be number fields with `L/k` finite Galois, `q'` a nonzero prime of `𝓞 L` above a
prime `l` of `𝓞 k`, and suppose that `E0/k` is unramified at `l`: every prime of `𝓞 E0` above `l`
has ramification index `1` over `k`.  Then the normal closure (in `Gal(L/k)`) of the inertia
subgroup of `q'` is contained in the fixing subgroup of `E0`; equivalently, every element of that
normal closure fixes `E0` pointwise.

The proof has three parts.

* `hpt` : every element of `Gal(L/k)` which is inertial at *some* prime `Q` of `𝓞 L` above `l`
  fixes `E0`.  This is the ideal-theoretic inertia inclusion
  `inertia_le_fixingSubgroup_of_ramificationIdx_eq_one` (Hilbert theory: `#I = e`), applied to the
  prime `Q`: the hypothesis needed there, `e(Q ∩ 𝓞 E0 / k) = 1`, is `hEunr` evaluated at the
  height one prime `Q.under 𝓞 E0`, which lies over `l` because `Q` does.
* `hconj` : the set of inertial elements is closed under conjugation *into the fixing subgroup*:
  a conjugate `c a c⁻¹` of an inertia element `a` at `q'` is inertial at the conjugate prime
  `c • q'` (`isInertiaAt_smulHeightOneSpectrum_iff`), which still lies over `l`
  (`under_smulHeightOneSpectrum`), so it fixes `E0` by `hpt`.
* `Subgroup.normalClosure s = closure (Group.conjugatesOfSet s)`, and a subgroup containing all the
  conjugates of `s` contains that closure. -/
theorem inertiaClosure_le_fixingSubgroup {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (l : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (E0 : IntermediateField k L) [FiniteDimensional k E0] [NumberField ↥E0]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq'l : q'.asIdeal.LiesOver l.asIdeal)
    (hEunr : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E0),
      (𝔮.asIdeal.under (NumberField.RingOfIntegers k)).LiesOver l.asIdeal →
      𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) :
    ∀ x : L ≃ₐ[k] L, x ∈ Subgroup.normalClosure {σ : L ≃ₐ[k] L | SSGRoute.PTExt.IsInertiaAt q' σ} →
      ∀ z : L, z ∈ E0 → x z = z := by
  classical
  -- ### Every element inertial at a prime above `l` fixes `E0`
  have hpt : ∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
      Q.asIdeal.LiesOver l.asIdeal →
      ∀ σ : L ≃ₐ[k] L, SSGRoute.PTExt.IsInertiaAt Q σ → σ ∈ E0.fixingSubgroup := by
    intro Q hQ σ hσ
    have hram : (Q.asIdeal.under (NumberField.RingOfIntegers ↥E0)).ramificationIdx
        (NumberField.RingOfIntegers k) = 1 := by
      have h1 := hEunr (Q.under (NumberField.RingOfIntegers ↥E0)) (by
        refine ⟨?_⟩
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
        simpa using hQ.over)
      simpa using h1
    exact inertia_le_fixingSubgroup_of_ramificationIdx_eq_one E0 Q hram
      ((Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia Q σ).mp hσ)
  -- ### The conjugates of inertia elements at `q'` all lie in the fixing subgroup
  have hconj : Group.conjugatesOfSet {σ : L ≃ₐ[k] L | SSGRoute.PTExt.IsInertiaAt q' σ} ⊆
      (E0.fixingSubgroup : Set (L ≃ₐ[k] L)) := by
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hconjax⟩ := hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconjax
    -- the conjugate prime `c • q'` still lies over `l`
    have hQ : (NK.GlobalCFT.Place.smulHeightOneSpectrum c q').asIdeal.LiesOver l.asIdeal :=
      ⟨hq'l.over.trans (Work.SSGRoute.Sha2Lib.under_smulHeightOneSpectrum c q').symm⟩
    -- and `c * a * c⁻¹` is inertial there
    exact hpt _ hQ _ ((Work.SSGRoute.E9b.isInertiaAt_smulHeightOneSpectrum_iff q' c
      (c * a * c⁻¹)).mpr (by rw [show c⁻¹ * (c * a * c⁻¹) * c = a by group]; exact ha))
  -- ### assemble: the normal closure is the closure of the conjugates
  intro x hx z hz
  have hle : Subgroup.normalClosure {σ : L ≃ₐ[k] L | SSGRoute.PTExt.IsInertiaAt q' σ} ≤
      E0.fixingSubgroup := by
    show Subgroup.closure (Group.conjugatesOfSet
      {σ : L ≃ₐ[k] L | SSGRoute.PTExt.IsInertiaAt q' σ}) ≤ E0.fixingSubgroup
    exact (Subgroup.closure_le E0.fixingSubgroup).mpr hconj
  exact (IntermediateField.mem_fixingSubgroup_iff E0 x).mp (hle hx) z hz

end Work.SSGRoute.TPatom
