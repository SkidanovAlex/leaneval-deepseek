import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.Sha2Lib.detector_of_submodule
import Submission.Work.SSGRoute.Sha2Lib.unramifiedDetector_trivial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory SSGRoute.PTExt

/-- **The invariant case of the unramified detector, in `Ext¹(·,ℤ)` form.**

Let `k ⊆ K` be number fields with `K/k` finite Galois, `w = ofFinite q` a place with `p ∉ q`, `M` a
finite `p`-torsion `Gal(K/k)`-module with the inertia of `q` acting trivially, and let `m₀ ∈ M` be
fixed by `Gal(K/k)`.  If `φ ∈ Ext¹_{D_w}(res M, ℤ)` is such that the *pull-back of `φ` along some
`Gal(K/k)`-module map `ι : 𝔽_p ⟶ M` with `ι 1 = m₀`* is nonzero — equivalently, by
`Ext¹_{D_w}(res M,ℤ) ≅ Hom_{D_w}(M,ℚ/ℤ)`, if the functional `φ` is nonzero on the trivial
summand spanned by `m₀` — then `φ` is *detected*: at some level `L ⊇ K`, place `q' | q` with
`e(q'|q)` prime to `p`, and some class `h ∈ H¹(Gal(L/k), res M)` unramified at `q'`, the Yoneda
pairing `levelPair φ (h|_{D_{q'}})` is nonzero.

This is the first case of the case analysis of `Work.SSGRoute.E7cC.exists_unramifiedDetector_ExtZ`
(case 1, "invariant", of `Work.SSGRoute.E7cOmega.NOTE_assemblies_H7_L2960.md` §4), in the *form the
final assembly consumes* (`isUnramifiedExt_of_levelPair_unramified_aux` /
`isUnramifiedExt_of_detector` take their detector hypothesis in exactly this `φ`-form), as opposed to
the `π`-form of `Work.SSGRoute.E7cOmega.unramifiedDetector_dwQuotientInvariant` (which has to be
transported across `Ext¹ ≅ Hom(·,ℚ/ℤ)` by the consumer).

Proof: `detector_of_submodule` (proved) with `N = 𝔽_p`, whose `ι : 𝔽_p → M` is supplied by the
hypothesis, and `Work.SSGRoute.Sha2Lib.unramifiedDetector_trivial` (proved) as the detector for
`N`.  The hypothesis `hφι` says precisely that `φ` does not vanish on the image of `ι`; the
dévissage then pushes the detecting class of `𝔽_p` forward along `ι`. -/
theorem detectorInvariantCaseExtZ (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (m₀ : M) (hm₀ : ∀ σ : K ≃ₐ[k] K, M.ρ σ m₀ = m₀)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hφ : φ ≠ 0)
    (hφι : ∃ ι : Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ M,
      ι.hom 1 = m₀ ∧ (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype ι)).comp φ
        (zero_add 1) ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p ∧
      SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv
          (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff)
        φ
        (SSGRoute.PTExt.extHRestrict
          (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0 := by
  obtain ⟨ι, _hι1, hφι'⟩ := hφι
  exact detector_of_submodule p k K M (Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p))
    Ω hM (fun m => by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]) w q hwq hpq hI ι
    (fun φN hφN => unramifiedDetector_trivial p k K Ω w q hwq hpq φN hφN)
    φ hφ hφι'

end Work.SSGRoute.Sha2Lib
