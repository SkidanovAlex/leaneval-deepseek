import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.E9Nodes.e9_inertia_restrict
import Submission.Work.SSGRoute.extHRestrict_inflHIn_eq_zero_of_forall
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.extHRestrict_eq_zero_of_le
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E9b

open CategoryTheory

/-- **Unramified classes stay unramified under inflation between levels.**  Let `k ⊆ K ⊆ L ⊆ L' ≤ Ω`
be finite Galois levels, `M` a `Gal(K/k)`-module.  If `h ∈ H¹(Gal(L/k), M)` is unramified at every
finite place of `L` above a place `v` of `K`, then `inflHIn h ∈ H¹(Gal(L'/k), M)` is unramified at
every finite place of `L'` above `v`. -/
theorem unramified_inflHIn (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (L L' : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField L'] [FiniteDimensional k L'] [IsGalois k L'] (hLL : L ≤ L')
    (v : NK.GlobalCFT.Place K)
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1)
    (hzero : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v →
      SSGRoute.PTExt.IsUnramifiedClassAt q h) :
    ∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'),
      NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') v →
      SSGRoute.PTExt.IsUnramifiedClassAt q' (SSGRoute.PTExt.inflHIn (k := k) (K := K) hLL h) := by
  intro q' hq'v
  -- the tower `k ⊆ L ⊆ L'` of levels, with `L` viewed inside `L'`
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion hLL).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ↥L ↥L' := Module.Finite.of_restrictScalars_finite k ↥L ↥L'
  -- the finite place `q` of `L` lying below `q'`
  obtain ⟨w, hw'w⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := ↥L) (L := ↥L')
      (NK.GlobalCFT.Place.ofFinite q')
  obtain ⟨q, hwq, hq'q⟩ :=
    (Work.SSGRoute.place_liesOver_ofFinite_iff (K := ↥L) (L := ↥L') q' w).mp hw'w
  -- `w` lies over `v`, hence so does `ofFinite q`
  obtain ⟨v', hwv'⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥L) w
  have hv' : v' = v :=
    Work.SSGRoute.place_liesOver_unique (K := K) (L := ↥L')
      (NK.GlobalCFT.Place.ofFinite q') (Work.SSGRoute.place_liesOver_trans hw'w hwv') hq'v
  have hwv : NK.GlobalCFT.Place.LiesOver w v := hv' ▸ hwv'
  have hqv : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v := hwq ▸ hwv
  have hq_unram : SSGRoute.PTExt.IsUnramifiedClassAt q h := hzero q hqv
  -- it remains to show that `inflHIn h` restricts to zero on the inertia of `q'`
  intro D' hD'
  -- the image of `D'` in `Gal(L/k)` consists of inertia elements at `q`
  let p : (↥L' ≃ₐ[k] ↥L') →* (↥L ≃ₐ[k] ↥L) := SSGRoute.PTExt.galRes k ↥L ↥L'
  let D : Subgroup (↥L ≃ₐ[k] ↥L) := D'.map p
  have hDmap : ∀ σ ∈ D, SSGRoute.PTExt.IsInertiaAt q σ := by
    intro σ hσ
    rw [Subgroup.mem_map] at hσ
    obtain ⟨y, hy, rfl⟩ := hσ
    exact Work.SSGRoute.E9Nodes.e9_inertia_restrict k ↥L ↥L' q q' hq'q y (p y)
      (fun x => (AlgEquiv.restrictNormal_commutes y ↥L x).symm) (hD' y hy)
  have hDzero : SSGRoute.PTExt.extHRestrict D h = 0 := hq_unram D hDmap
  -- the induced map `D' →* D` and the formal restriction/inflation identity
  let f : D' →* D :=
    MonoidHom.codRestrict (p.comp D'.subtype) D (fun x => Subgroup.mem_map_of_mem p x.2)
  have hf : p.comp D'.subtype = D.subtype.comp f := by
    ext x; rfl
  have key := Work.SSGRoute.extHRestrict_extHMap_gen p (SSGRoute.PTExt.resResHom M) D' D f hf h
  simp only [SSGRoute.PTExt.inflHIn, SSGRoute.PTExt.inflHLevel]
  rw [key, hDzero]
  exact Work.SSGRoute.E6Util.extHMap_zero f _

end Work.SSGRoute.E9b
